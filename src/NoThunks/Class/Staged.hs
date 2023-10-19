{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE DeriveGeneric #-}

{-# OPTIONS_GHC -ddump-splices #-}

-- | Staged, generic infrastructure
module NoThunks.Class.Staged where

import Generics.SOP.Staged hiding (hd)
import Language.Haskell.TH hiding (Type)
import Data.SOP.NS
import NoThunks.Class.Internal
import Generics.SOP.Staged.TH
import GHC.Generics as GHC (Generic)


-- For instances

import Data.Foldable (toList)
import Data.Int
import Data.IntMap (IntMap)
import Data.Kind (Type)
import Generics.SOP.Staged.TH
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


-- | Example for some type T:
--
-- @
-- ''deriveGeneric 'T
-- instance NoThunks a => NoThunks (T a) where
--   wNoThunks =
--     let c = constraints @(T a)
--     in  $$(sgwNoThunks' (allC [|| c ||]))
-- @
sgwNoThunks' ::
     forall a. SGeneric a
  => POP (C :.: Dict NoThunks) (SDescription a)
  -> CodeQ (Context -> a -> IO (Maybe ThunkInfo))
sgwNoThunks' dicts = [|| \ctxt x -> $$(sgwNoThunks dicts [|| ctxt ||] [|| x ||]) ||]

sgwNoThunks ::
     forall a. SGeneric a
  => POP (C :.: Dict NoThunks) (SDescription a)
  -> CodeQ Context -> CodeQ a -> CodeQ (IO (Maybe ThunkInfo))
sgwNoThunks dicts ctxt c = sfrom c $ \a ->
    foldr (\x r -> [|| $$x >>= maybe $$r (pure . Just) ||]) [|| pure Nothing ||] (f a)
  where
    f :: SRep a -> [CodeQ (IO (Maybe ThunkInfo))]
    f a = collapse_SOP $ selectWith_SOP g dicts a

    g :: forall b. (C :.: Dict NoThunks) b -> C b -> K (CodeQ (IO (Maybe ThunkInfo))) b
    g (Comp (C d)) (C x) = K [|| withDict $$d (noThunks (updctxt $$ctxt $$d) $$x) ||]

updctxt :: NoThunks a => Context -> proxy a -> Context
updctxt ctxt p = case ctxt of
    hd : tl | hd == showTypeOf (toProxy p) -> tl
    _otherwise                             -> ctxt

toProxy :: proxy a -> Proxy a
toProxy _ = Proxy


deriveGeneric ''(,)
deriveGeneric ''(,,)
deriveGeneric ''(,,,)
deriveGeneric ''(,,,,)
deriveGeneric ''(,,,,,)
deriveGeneric ''(,,,,,,)

deriveGeneric ''Void
deriveGeneric ''()
deriveGeneric ''[]
deriveGeneric ''Maybe
deriveGeneric ''NonEmpty
deriveGeneric ''Either