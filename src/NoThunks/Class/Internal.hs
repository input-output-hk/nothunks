{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module NoThunks.Class.Internal (
    -- * Check a value for unexpected thunks
    NoThunks(..)
  , ThunkInfo(..)
  , Context
  , unsafeNoThunks
    -- * Helpers for defining instances
  , allNoThunks
  , noThunksInValues
  , noThunksInKeysAndValues
    -- * Deriving-via wrappers
  , OnlyCheckWhnf(..)
  , OnlyCheckWhnfNamed(..)
  , InspectHeap(..)
  , InspectHeapNamed(..)
  , AllowThunk(..)
  , AllowThunksIn(..)
    -- * Generic class
  , GWNoThunks(..)
  ) where

import Data.Proxy
import Data.Typeable
import System.IO.Unsafe (unsafePerformIO)

import GHC.Exts.Heap
import GHC.Generics
import GHC.Records
import GHC.TypeLits
import GHC.Conc.Sync (ThreadId (..))

-- For instances

import Data.Foldable (toList)
import Data.Int
import Data.IntMap (IntMap)
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map (Map)
import Data.Ratio
import Data.Sequence (Seq)
import Data.Set (Set)
import Data.Time
import Data.Void (Void)
import Data.Word
import GHC.Stack
-- base-4.16 exports 'Natural' from 'GHC.TypeLits'
#if !MIN_VERSION_base(4,16,0)
import Numeric.Natural
#endif

import qualified Control.Concurrent.MVar       as MVar
import qualified Control.Concurrent.STM.TVar   as TVar
import qualified Data.IntMap                   as IntMap
import qualified Data.IORef                    as IORef
import qualified Data.Map                      as Map
import qualified Data.Set                      as Set

#ifdef MIN_VERSION_bytestring
import Data.ByteString.Short (ShortByteString)
import qualified Data.ByteString               as BS.Strict
import qualified Data.ByteString.Lazy          as BS.Lazy
import qualified Data.ByteString.Lazy.Internal as BS.Lazy.Internal
#endif

#ifdef MIN_VERSION_text
import qualified Data.Text                     as Text.Strict
import qualified Data.Text.Internal.Lazy       as Text.Lazy.Internal
import qualified Data.Text.Lazy                as Text.Lazy
#endif

#ifdef MIN_VERSION_vector
import qualified Data.Vector                   as Vector.Boxed
import qualified Data.Vector.Unboxed           as Vector.Unboxed
#endif

{-------------------------------------------------------------------------------
  Check a value for unexpected thunks
-------------------------------------------------------------------------------}

-- | Check a value for unexpected thunks
class NoThunks a where
  -- | Check if the argument does not contain any unexpected thunks
  --
  -- For most datatypes, we should have that
  --
  -- > noThunks ctxt x == Nothing
  --
  -- if and only if
  --
  -- > checkContainsThunks x
  --
  -- For some datatypes however, some thunks are expected. For example, the
  -- internal fingertree 'Data.Sequence.Sequence' might contain thunks (this is
  -- important for the asymptotic complexity of this data structure). However,
  -- we should still check that the /values/ in the sequence don't contain any
  -- unexpected thunks.
  --
  -- This means that we need to traverse the sequence, which might force some of
  -- the thunks in the tree. In general, it is acceptable for
  -- 'noThunks' to force such "expected thunks", as long as it always
  -- reports the /unexpected/ thunks.
  --
  -- The default implementation of 'noThunks' checks that the argument is in
  -- WHNF, and if so, adds the type into the context (using 'showTypeOf'), and
  -- calls 'wNoThunks'. See 'ThunkInfo' for a detailed discussion of the type
  -- context.
  --
  -- See also discussion of caveats listed for 'checkContainsThunks'.
  noThunks :: Context -> a -> IO (Maybe ThunkInfo)
  noThunks ctxt x = do
      isThunk <- checkIsThunk x
      if isThunk
        then return $ Just ThunkInfo { thunkContext = ctxt' }
        else wNoThunks ctxt' x
    where
      ctxt' :: Context
      ctxt' = showTypeOf (Proxy @a) : ctxt

  -- | Check that the argument is in normal form, assuming it is in WHNF.
  --
  -- The context will already have been extended with the type we're looking at,
  -- so all that's left is to look at the thunks /inside/ the type. The default
  -- implementation uses GHC Generics to do this.
  wNoThunks :: Context -> a -> IO (Maybe ThunkInfo)
  default wNoThunks :: (Generic a, GWNoThunks '[] (Rep a))
                    => Context -> a -> IO (Maybe ThunkInfo)
  wNoThunks ctxt x = gwNoThunks (Proxy @'[]) ctxt fp
    where
      -- Force the result of @from@ to WHNF: we are not interested in thunks
      -- that arise from the translation to the generic representation.
      fp :: Rep a x
      !fp = from x

  -- | Show type @a@ (to add to the context)
  --
  -- We try hard to avoid 'Typeable' constraints in this module: there are types
  -- with no 'Typeable' instance but with a 'NoThunks' instance (most
  -- important example are types such as @ST s@ which rely on parametric
  -- polymorphism). By default we should therefore only show the "outer layer";
  -- for example, if we have a type
  --
  -- > Seq (ST s ())
  --
  -- then 'showTypeOf' should just give @Seq@, leaving it up to the instance for
  -- @ST@ to decide how to implement 'showTypeOf'; this keeps things
  -- compositional. The default implementation does precisely this using the
  -- metadata that GHC Generics provides.
  --
  -- For convenience, however, some of the @deriving via@ newtype wrappers we
  -- provide /do/ depend on @Typeable@; see below.
  showTypeOf :: Proxy a -> String
  default showTypeOf :: (Generic a, GShowTypeOf (Rep a)) => Proxy a -> String
  showTypeOf _ = gShowTypeOf (from x)
    where
      x :: a
      x = x

-- | Context where a thunk was found
--
-- This is intended to give a hint about which thunk was found. For example,
-- a thunk might be reported with context
--
-- > ["Int", "(,)", "Map", "AppState"]
--
-- telling you that you have an @AppState@ containing a @Map@ containing a pair,
-- all of which weren't thunks (were in WHNF), but that pair contained an
-- @Int@ which was a thunk.
type Context = [String]

{-------------------------------------------------------------------------------
  Results of the check
-------------------------------------------------------------------------------}

-- | Information about unexpected thunks
--
-- TODO: The ghc-debug work by Matthew Pickering includes some work that allows
-- to get source spans from closures. If we could take advantage of that, we
-- could not only show the type of the unexpected thunk, but also where it got
-- allocated.
newtype ThunkInfo = ThunkInfo {
      -- The @Context@ argument is intended to give a clue to add debugging.
      -- For example, suppose we have something of type @(Int, [Int])@. The
      -- various contexts we might get are
      --
      -- > Context                  The thunk is..
      -- > ---------------------------------------------------------------------
      -- > ["(,)"]                  the pair itself
      -- > ["Int","(,)"]            the Int in the pair
      -- > ["List","(,)"]           the [Int] in the pair
      -- > ["Int","List","(,)"]     an Int in the [Int] in the pair
      --
      -- Note: prior to `ghc-9.6` a list was indicated by `[]`.
      thunkContext :: Context
    }
  deriving (Show)

{-# NOINLINE unsafeNoThunks #-}
-- | Call 'noThunks' in a pure context (relies on 'unsafePerformIO').
unsafeNoThunks :: NoThunks a => a -> Maybe ThunkInfo
unsafeNoThunks a = unsafePerformIO $ noThunks [] a

{-------------------------------------------------------------------------------
  Helpers for defining NoThunks instances
-------------------------------------------------------------------------------}

-- | Short-circuit a list of checks
allNoThunks :: [IO (Maybe ThunkInfo)] -> IO (Maybe ThunkInfo)
allNoThunks = go
  where
    go :: [IO (Maybe ThunkInfo)] -> IO (Maybe ThunkInfo)
    go []     = return Nothing
    go (a:as) = do
        nf <- a
        case nf of
          Nothing    -> go as
          Just thunk -> return $ Just thunk

-- | Check that all elements in the list are thunk-free
--
-- Does not check the list itself. Useful for checking the elements of a
-- container.
--
-- See also 'noThunksInKeysAndValues'
noThunksInValues :: NoThunks a => Context -> [a] -> IO (Maybe ThunkInfo)
noThunksInValues ctxt = allNoThunks . map (noThunks ctxt)

-- | Variant on 'noThunksInValues' for keyed containers.
--
-- Neither the list nor the tuples are checked for thunks.
noThunksInKeysAndValues :: (NoThunks k, NoThunks v)
                        => Context -> [(k, v)] -> IO (Maybe ThunkInfo)
noThunksInKeysAndValues ctxt =
      allNoThunks
    . concatMap (\(k, v) -> [ noThunks ctxt k
                            , noThunks ctxt v
                            ])

{-------------------------------------------------------------------------------
  Newtype wrappers for deriving via
-------------------------------------------------------------------------------}

-- | Newtype wrapper for use with @deriving via@ to check for WHNF only
--
-- For some types we don't want to check for nested thunks, and we only want
-- check if the argument is in WHNF, not in NF. A typical example are functions;
-- see the instance of @(a -> b)@ for detailed discussion. This should be used
-- sparingly.
--
-- Example:
--
-- > deriving via OnlyCheckWhnf T instance NoThunks T
newtype OnlyCheckWhnf a = OnlyCheckWhnf a

-- | Variant on 'OnlyCheckWhnf' that does not depend on 'Generic'
--
-- Example:
--
-- > deriving via OnlyCheckWhnfNamed "T" T instance NoThunks T
newtype OnlyCheckWhnfNamed (name :: Symbol) a = OnlyCheckWhnfNamed a

-- | Newtype wrapper for values that should be allowed to be a thunk
--
-- This should be used /VERY/ sparingly, and should /ONLY/ be used on values
-- (or, even rarer, types) which you are /SURE/ cannot retain any data that they
-- shouldn't. Bear in mind allowing a value of type @T@ to be a thunk might
-- cause a value of type @S@ to be retained if @T@ was computed from @S@.
newtype AllowThunk a = AllowThunk a

-- | Newtype wrapper for records where some of the fields are allowed to be
-- thunks.
--
-- Example:
--
-- > deriving via AllowThunksIn '["foo","bar"] T instance NoThunks T
--
-- This will create an instance that skips the thunk checks for the "foo" and
-- "bar" fields.
newtype AllowThunksIn (fields :: [Symbol]) a = AllowThunksIn a

-- | Newtype wrapper for use with @deriving via@ to inspect the heap directly
--
-- This bypasses the class instances altogether, and inspects the GHC heap
-- directly, checking that the value does not contain any thunks /anywhere/.
-- Since we can do this without any type classes instances, this is useful for
-- types that contain fields for which 'NoThunks' instances are not available.
--
-- Since the primary use case for 'InspectHeap' then is to give instances
-- for 'NoThunks' from third party libraries, we also don't want to
-- rely on a 'Generic' instance, which may likewise not be available. Instead,
-- we will rely on 'Typeable', which is available for /all/ types. However, as
-- 'showTypeOf' explains, requiring 'Typeable' may not always be suitable; if
-- it isn't, 'InspectHeapNamed' can be used.
--
-- Example:
--
-- > deriving via InspectHeap T instance NoThunks T
newtype InspectHeap a = InspectHeap a

-- | Variant on 'InspectHeap' that does not depend on 'Typeable'.
--
-- > deriving via InspectHeapNamed "T" T instance NoUnexpecedThunks T
newtype InspectHeapNamed (name :: Symbol) a = InspectHeapNamed a

{-------------------------------------------------------------------------------
  Internal: instances for the deriving-via wrappers
-------------------------------------------------------------------------------}

instance Typeable a => NoThunks (OnlyCheckWhnf a) where
  showTypeOf _  = show $ typeRep (Proxy @a)
  wNoThunks _ _ = return Nothing

instance KnownSymbol name => NoThunks (OnlyCheckWhnfNamed name a) where
  showTypeOf _  = symbolVal (Proxy @name)
  wNoThunks _ _ = return Nothing

instance NoThunks (AllowThunk a) where
  showTypeOf _ = "<never used since never fails>"
  noThunks _ _ = return Nothing
  wNoThunks    = noThunks

instance (HasFields s a, Generic a, Typeable a, GWNoThunks s (Rep a))
      => NoThunks (AllowThunksIn s a) where
  showTypeOf _ = show $ typeRep (Proxy @a)
  wNoThunks ctxt (AllowThunksIn x) = gwNoThunks (Proxy @s) ctxt fp
    where
      fp :: Rep a x
      !fp = from x

instance Typeable a => NoThunks (InspectHeap a) where
  showTypeOf _ = show $ typeRep (Proxy @a)
  wNoThunks = inspectHeap

instance KnownSymbol name => NoThunks (InspectHeapNamed name a) where
  showTypeOf _ = symbolVal (Proxy @name)
  wNoThunks = inspectHeap

-- | Internal: implementation of 'wNoThunks' for 'InspectHeap'
-- and 'InspectHeapNamed'
inspectHeap :: Context -> a -> IO (Maybe ThunkInfo)
inspectHeap ctxt x = do
    containsThunks <- checkContainsThunks x
    return $ if containsThunks
               then Just $ ThunkInfo { thunkContext = "..." : ctxt }
               else Nothing

{-------------------------------------------------------------------------------
  Internal: generic infrastructure
-------------------------------------------------------------------------------}

-- | Generic infrastructure for checking for unexpected thunks
--
-- The @a@ argument records which record fields are allowed to contain thunks;
-- see 'AllowThunksIn' and 'GWRecordField', below.
class GWNoThunks (a :: [Symbol]) f where
  -- | Check that the argument does not contain any unexpected thunks
  --
  -- Precondition: the argument is in WHNF.
  gwNoThunks :: proxy a -> Context -> f x -> IO (Maybe ThunkInfo)

instance GWNoThunks a f => GWNoThunks a (D1 c f) where
  gwNoThunks a ctxt (M1 fp) = gwNoThunks a ctxt fp

instance GWNoThunks a f => GWNoThunks a (C1 c f) where
  gwNoThunks a ctxt (M1 fp) = gwNoThunks a ctxt fp

instance GWNoThunks a f => GWNoThunks a (S1 ('MetaSel ('Nothing) su ss ds) f) where
  gwNoThunks a ctxt (M1 fp) = gwNoThunks a ctxt fp

instance (GWNoThunks a f, GWNoThunks a g) => GWNoThunks a (f :*: g) where
  gwNoThunks a ctxt (fp :*: gp) = allNoThunks [
        gwNoThunks a ctxt fp
      , gwNoThunks a ctxt gp
      ]

instance (GWNoThunks a f, GWNoThunks a g) => GWNoThunks a (f :+: g) where
  gwNoThunks a ctxt (L1 fp) = gwNoThunks a ctxt fp
  gwNoThunks a ctxt (R1 gp) = gwNoThunks a ctxt gp

instance NoThunks c => GWNoThunks a (K1 i c) where
  gwNoThunks _a ctxt (K1 c) = noThunks ctxt' c
    where
      -- If @c@ is a recursive occurrence of the type itself, we want to avoid
      -- accumulating context. For example, suppose we are dealing with @[Int]@,
      -- and we have an unexpected thunk as the third @Int@ in the list. If
      -- we use the generic instance, then without this correction, the final
      -- context will look something like
      --
      -- > ["Int", "[]", "[]", "[]"]
      --
      -- While that is more informative (it's the /third/ element that is a
      -- thunk), it's not that helpful (typically we just want /all/ elements
      -- to be in NF). We strip the context here so that we just get
      --
      -- > ["Int", "[]"]
      --
      -- which is a bit easier to interpret.
      ctxt' = case ctxt of
                hd : tl | hd == showTypeOf (Proxy @c) -> tl
                _otherwise                            -> ctxt

instance GWNoThunks a U1 where
  gwNoThunks _a _ctxt U1 = return Nothing

instance GWNoThunks a V1 where
  -- By assumption, the argument is already in WHNF. Since every inhabitant of
  -- this type is bottom, this code is therefore unreachable.
  gwNoThunks _a _ctxt _ = error "unreachable gwNoThunks @V1"

{-------------------------------------------------------------------------------
  Skip fields with allowed thunks
-------------------------------------------------------------------------------}

-- | If @fieldName@ is allowed to contain thunks, skip it.
instance ( GWRecordField f (Elem fieldName a)
         , KnownSymbol fieldName
         )
      => GWNoThunks a (S1 ('MetaSel ('Just fieldName) su ss ds) f) where
  gwNoThunks _ ctxt (M1 fp) =
      gwRecordField (Proxy @(Elem fieldName a)) (symbolVal @fieldName Proxy : ctxt) fp

class GWRecordField f (b :: Bool) where
  gwRecordField :: proxy b -> Context -> f x -> IO (Maybe ThunkInfo)

-- | If the field is allowed to contain thunks, don't check anything.
instance GWRecordField f 'True where
  gwRecordField _ _ _ = return Nothing

instance GWNoThunks '[] f => GWRecordField f 'False where
  gwRecordField _ ctxt f = gwNoThunks (Proxy @'[]) ctxt f

{-------------------------------------------------------------------------------
  Internal: generic function to get name of a type
-------------------------------------------------------------------------------}

class GShowTypeOf f where
  gShowTypeOf :: f x -> String

instance Datatype c => GShowTypeOf (D1 c f) where
  gShowTypeOf = datatypeName

{-------------------------------------------------------------------------------
  Type level symbol comparison logic
-------------------------------------------------------------------------------}

type family Same s t where
  Same s t = IsSame (CmpSymbol s t)

type family IsSame (o :: Ordering) where
  IsSame 'EQ = 'True
  IsSame _x  = 'False

type family Or (a :: Bool) (b :: Bool) where
  Or 'False 'False = 'False
  Or _a     _b     = 'True

type family Elem (s :: Symbol) (xs :: [Symbol]) where
  Elem s  (x ': xs) = Or (Same s x) (Elem s xs)
  Elem _s '[]       = 'False

{-------------------------------------------------------------------------------
  Check that all mentioned record fields are known fields
-------------------------------------------------------------------------------}

-- | Check that type @a@ has all record fields listed in @s@
--
-- This exists to catch mismatches between the arguments to `AllowThunksIn` and
-- the fields of a record. If any of the symbols is not the name of a field then
-- this constraint won't be satisfied.
class HasFields (s :: [Symbol]) (a :: Type)
instance HasFields '[] a
instance (HasField x a t, HasFields xs a) => HasFields (x ': xs) a

{-------------------------------------------------------------------------------
  Internal: low level magic
-------------------------------------------------------------------------------}

-- | Is the argument a (top-level thunk)?
checkIsThunk :: a -> IO Bool
checkIsThunk x = closureIsThunk <$> getBoxedClosureData (asBox x)

-- | Is the argument a thunk, or does it (recursively) contain any?
checkContainsThunks :: a -> IO Bool
checkContainsThunks x = go (asBox x)
  where
    go :: Box -> IO Bool
    go b = do
        c <- getBoxedClosureData b
        if closureIsThunk c then
          return True
        else do
          c' <- getBoxedClosureData b
          anyM go (allClosures c')

-- | Check if the given 'Closure' is a thunk.
--
-- Indirections are not considered to be thunks.
closureIsThunk :: Closure -> Bool
closureIsThunk ThunkClosure{}    = True
closureIsThunk APClosure{}       = True
closureIsThunk SelectorClosure{} = True
closureIsThunk BCOClosure{}      = True
closureIsThunk _                 = False

anyM :: Monad m => (a -> m Bool) -> [a] -> m Bool
anyM _ []       = return False
anyM p (x : xs) = do
    q <- p x
    if q then return True
         else anyM p xs
