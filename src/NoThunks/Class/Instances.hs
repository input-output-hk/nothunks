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

{-# OPTIONS_GHC -Wno-orphans #-}

module NoThunks.Class.Instances () where

import NoThunks.Class.Internal

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
  Instances for primitive types
-------------------------------------------------------------------------------}

deriving via OnlyCheckWhnf Bool    instance NoThunks Bool
deriving via OnlyCheckWhnf Natural instance NoThunks Natural
deriving via OnlyCheckWhnf Integer instance NoThunks Integer
deriving via OnlyCheckWhnf Float   instance NoThunks Float
deriving via OnlyCheckWhnf Double  instance NoThunks Double
deriving via OnlyCheckWhnf Char    instance NoThunks Char

deriving via OnlyCheckWhnf Int   instance NoThunks Int
deriving via OnlyCheckWhnf Int8  instance NoThunks Int8
deriving via OnlyCheckWhnf Int16 instance NoThunks Int16
deriving via OnlyCheckWhnf Int32 instance NoThunks Int32
deriving via OnlyCheckWhnf Int64 instance NoThunks Int64

deriving via OnlyCheckWhnf Word   instance NoThunks Word
deriving via OnlyCheckWhnf Word8  instance NoThunks Word8
deriving via OnlyCheckWhnf Word16 instance NoThunks Word16
deriving via OnlyCheckWhnf Word32 instance NoThunks Word32
deriving via OnlyCheckWhnf Word64 instance NoThunks Word64

{-------------------------------------------------------------------------------
  Mutable Vars
-------------------------------------------------------------------------------}

instance NoThunks a => NoThunks (IORef.IORef a) where
    showTypeOf _ = "IORef"
    wNoThunks ctx ref = do
        val <- IORef.readIORef ref
        noThunks ctx val

instance NoThunks a => NoThunks (MVar.MVar a) where
    showTypeOf _ = "MVar"
    wNoThunks ctx ref = do
        val <- MVar.tryReadMVar ref
        maybe (return Nothing) (noThunks ctx) val

instance NoThunks a => NoThunks (TVar.TVar a) where
    showTypeOf _ = "TVar"
    wNoThunks ctx ref = do
        -- An alternative is to use
        --
        --   val <- STM.atomically $ TVar.readTVar ref
        --
        -- but that would cause nested atomically failures with
        -- unsafeNoThunks. Fortunately, readTVarIO doesn't make a transaction.
        --
        -- See related tests.
        --
        val <- TVar.readTVarIO ref
        noThunks ctx val

{-------------------------------------------------------------------------------
  Time
-------------------------------------------------------------------------------}

deriving via InspectHeap Day              instance NoThunks Day
deriving via InspectHeap DiffTime         instance NoThunks DiffTime
deriving via InspectHeap LocalTime        instance NoThunks LocalTime
deriving via InspectHeap NominalDiffTime  instance NoThunks NominalDiffTime
deriving via InspectHeap TimeLocale       instance NoThunks TimeLocale
deriving via InspectHeap TimeOfDay        instance NoThunks TimeOfDay
deriving via InspectHeap TimeZone         instance NoThunks TimeZone
deriving via InspectHeap UniversalTime    instance NoThunks UniversalTime
deriving via InspectHeap UTCTime          instance NoThunks UTCTime
deriving via InspectHeap ZonedTime        instance NoThunks ZonedTime

{-------------------------------------------------------------------------------
  ByteString
-------------------------------------------------------------------------------}

#ifdef MIN_VERSION_bytestring

-- | Instance for string bytestrings
--
-- Strict bytestrings /shouldn't/ contain any thunks, but could, due to
-- <https://gitlab.haskell.org/ghc/ghc/issues/17290>. However, such thunks can't
-- retain any data that they shouldn't, and so it's safe to ignore such thunks.
deriving via OnlyCheckWhnfNamed "Strict.ByteString" BS.Strict.ByteString
         instance NoThunks BS.Strict.ByteString

-- | Instance for short bytestrings
--
-- We have
--
-- > data ShortByteString = SBS ByteArray#
--
-- Values of this type consist of a tag followed by an _unboxed_ byte array,
-- which can't contain thunks. Therefore we only check WHNF.
deriving via OnlyCheckWhnfNamed "ShortByteString" ShortByteString
         instance NoThunks ShortByteString

-- | Instance for lazy bytestrings
--
-- Defined manually so that it piggy-backs on the one for strict bytestrings.
instance NoThunks BS.Lazy.ByteString where
  showTypeOf _      = "Lazy.ByteString"
  wNoThunks ctxt bs =
      case bs of
        BS.Lazy.Internal.Empty           -> return Nothing
        BS.Lazy.Internal.Chunk chunk bs' -> allNoThunks [
              noThunks ctxt chunk
            , noThunks ctxt bs'
            ]

#endif

{-------------------------------------------------------------------------------
  Instances for text types

  For consistency, we follow the same pattern as for @ByteString@.
-------------------------------------------------------------------------------}

#ifdef MIN_VERSION_text

deriving via OnlyCheckWhnfNamed "Strict.Text" Text.Strict.Text
         instance NoThunks Text.Strict.Text

instance NoThunks Text.Lazy.Text where
  showTypeOf _      = "Lazy.Text"
  wNoThunks ctxt bs =
      case bs of
        Text.Lazy.Internal.Empty           -> return Nothing
        Text.Lazy.Internal.Chunk chunk bs' -> allNoThunks [
              noThunks ctxt chunk
            , noThunks ctxt bs'
            ]

#endif

{-------------------------------------------------------------------------------
  Tuples
-------------------------------------------------------------------------------}

instance ( NoThunks a
         , NoThunks b
         ) => NoThunks (a, b)

instance ( NoThunks a
         , NoThunks b
         , NoThunks c
         ) => NoThunks (a, b, c)

instance ( NoThunks a
         , NoThunks b
         , NoThunks c
         , NoThunks d
         ) => NoThunks (a, b, c, d)

instance ( NoThunks a
         , NoThunks b
         , NoThunks c
         , NoThunks d
         , NoThunks e
         ) => NoThunks (a, b, c, d, e)

instance ( NoThunks a
         , NoThunks b
         , NoThunks c
         , NoThunks d
         , NoThunks e
         , NoThunks f
         ) => NoThunks (a, b, c, d, e, f)

instance ( NoThunks a
         , NoThunks b
         , NoThunks c
         , NoThunks d
         , NoThunks e
         , NoThunks f
         , NoThunks g
         ) => NoThunks (a, b, c, d, e, f, g)

{-------------------------------------------------------------------------------
  Base types (other than tuples)
-------------------------------------------------------------------------------}

instance NoThunks Void
instance NoThunks ()

instance NoThunks a => NoThunks [a]
instance NoThunks a => NoThunks (Maybe a)
instance NoThunks a => NoThunks (NonEmpty a)

instance (NoThunks a, NoThunks b) => NoThunks (Either a b)

deriving via InspectHeap ThreadId instance NoThunks ThreadId

{-------------------------------------------------------------------------------
  Spine-strict container types

  Such types can /only/ contain thunks in the values, so that's all we check.
  Note that containers using keys are typically strict in those keys, but that
  forces them to WHNF only, not NF; in /most/ cases the @Ord@ instance on those
  keys will force them to NF, but not /always/ (for example, when using lists
  as keys); this means we must check keys for thunks to be sure.
-------------------------------------------------------------------------------}

instance (NoThunks k, NoThunks v) => NoThunks (Map k v) where
  showTypeOf _   = "Map"
  wNoThunks ctxt = noThunksInKeysAndValues ctxt . Map.toList

instance NoThunks a => NoThunks (Set a) where
  showTypeOf _   = "Set"
  wNoThunks ctxt = noThunksInValues ctxt . Set.toList

instance NoThunks a => NoThunks (IntMap a) where
  showTypeOf _   = "IntMap"
  wNoThunks ctxt = noThunksInValues ctxt . IntMap.toList

{-------------------------------------------------------------------------------
  Vector
-------------------------------------------------------------------------------}

#ifdef MIN_VERSION_vector

instance NoThunks a => NoThunks (Vector.Boxed.Vector a) where
  showTypeOf _   = "Boxed.Vector"
  wNoThunks ctxt = noThunksInValues ctxt . Vector.Boxed.toList

-- | Unboxed vectors can't contain thunks
--
-- Implementation note: defined manually rather than using 'OnlyCheckWhnf'
-- due to ghc limitation in deriving via, making it impossible to use with it
-- with data families.
instance NoThunks (Vector.Unboxed.Vector a) where
  showTypeOf _  = "Unboxed.Vector"
  wNoThunks _ _ = return Nothing

#endif

{-------------------------------------------------------------------------------
  Function types
-------------------------------------------------------------------------------}

-- | We do NOT check function closures for captured thunks by default
--
-- Since we have no type information about the values captured in a thunk, the
-- only check we could possibly do is 'checkContainsThunks': we can't
-- recursively call 'noThunks' on those captured values, which is problematic if
-- any of those captured values /requires/ a custom instance (for example, data
-- types that depend on laziness, such as 'Seq').
--
-- By default we therefore /only/ check if the function is in WHNF, and don't
-- check the captured values at all. If you want a stronger check, you can
-- use @'InspectHeap' (a -> b)@ instead.
deriving via OnlyCheckWhnfNamed "->" (a -> b) instance NoThunks (a -> b)

-- | We do not check IO actions for captured thunks by default
--
-- See instance for @(a -> b)@ for detailed discussion.
deriving via OnlyCheckWhnfNamed "IO" (IO a) instance NoThunks (IO a)

{-------------------------------------------------------------------------------
  Special cases
-------------------------------------------------------------------------------}

-- | Since CallStacks can't retain application data, we don't want to check
-- them for thunks /at all/
deriving via AllowThunk CallStack instance NoThunks CallStack

-- | Instance for 'Seq' checks elements only
--
-- The internal fingertree in 'Seq' might have thunks, which is essential for
-- its asymptotic complexity.
instance NoThunks a => NoThunks (Seq a) where
  showTypeOf _ = "Seq"
  wNoThunks ctxt = noThunksInValues ctxt . toList

instance NoThunks a => NoThunks (Ratio a) where
  showTypeOf _ = "Ratio"
  wNoThunks ctxt r = noThunksInValues ctxt [n, d]
   where
     -- The 'Ratio' constructor is not exported: we only have two accessor
     -- functions. However, @numerator r@ is obviously trivially a trunk
     -- (due to the unevaluated call to @numerator@). By forcing the values of
     -- @n@ and @d@ where we get rid of these function calls, leaving only the
     -- values inside the @Ratio@. Note that @Ratio@ is strict in both of these
     -- fields, so forcing them to WHNF won't change them.
     !n = numerator   r
     !d = denominator r

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
