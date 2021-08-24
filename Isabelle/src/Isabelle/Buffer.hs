{- generated by Isabelle -}

{-  Title:      Isabelle/Buffer.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Efficient buffer of byte strings.

See "$ISABELLE_HOME/src/Pure/General/buffer.ML".
-}

module Isabelle.Buffer (T, empty, add, content)
where

import qualified Isabelle.Bytes as Bytes
import Isabelle.Bytes (Bytes)


newtype T = Buffer [Bytes]

empty :: T
empty = Buffer []

add :: Bytes -> T -> T
add b (Buffer bs) = Buffer (if Bytes.null b then bs else b : bs)

content :: T -> Bytes
content (Buffer bs) = Bytes.concat (reverse bs)
