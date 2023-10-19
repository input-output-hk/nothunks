module NoThunks.Class (
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

import NoThunks.Class.Internal
import NoThunks.Class.Instances ()
