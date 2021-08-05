{- generated by Isabelle -}

{- generated by Isabelle -}

{-  Title:      Isabelle/XML/Classes.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Type classes for XML data representation.
-}

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Isabelle.XML.Classes
  (Encode_Atom(..), Decode_Atom(..), Encode (..), Decode (..))
where

import qualified Isabelle.XML as XML
import qualified Isabelle.XML.Encode as Encode
import qualified Isabelle.XML.Decode as Decode
import qualified Isabelle.Term_XML.Encode as Encode
import qualified Isabelle.Term_XML.Decode as Decode
import qualified Isabelle.Properties as Properties
import Isabelle.Bytes (Bytes)
import Isabelle.Term (Typ, Term)


class Encode_Atom a where encode_atom :: Encode.A a
class Decode_Atom a where decode_atom :: Decode.A a

instance Encode_Atom Int where encode_atom = Encode.int_atom
instance Decode_Atom Int where decode_atom = Decode.int_atom

instance Encode_Atom Bool where encode_atom = Encode.bool_atom
instance Decode_Atom Bool where decode_atom = Decode.bool_atom

instance Encode_Atom () where encode_atom = Encode.unit_atom
instance Decode_Atom () where decode_atom = Decode.unit_atom


class Encode a where encode :: Encode.T a
class Decode a where decode :: Decode.T a

instance Encode Bytes where encode = Encode.string
instance Decode Bytes where decode = Decode.string

instance Encode Int where encode = Encode.int
instance Decode Int where decode = Decode.int

instance Encode Bool where encode = Encode.bool
instance Decode Bool where decode = Decode.bool

instance Encode () where encode = Encode.unit
instance Decode () where decode = Decode.unit

instance (Encode a, Encode b) => Encode (a, b)
  where encode = Encode.pair encode encode
instance (Decode a, Decode b) => Decode (a, b)
  where decode = Decode.pair decode decode

instance (Encode a, Encode b, Encode c) => Encode (a, b, c)
  where encode = Encode.triple encode encode encode
instance (Decode a, Decode b, Decode c) => Decode (a, b, c)
  where decode = Decode.triple decode decode decode

instance Encode a => Encode [a] where encode = Encode.list encode
instance Decode a => Decode [a] where decode = Decode.list decode

instance Encode a => Encode (Maybe a) where encode = Encode.option encode
instance Decode a => Decode (Maybe a) where decode = Decode.option decode

instance Encode XML.Tree where encode = Encode.tree
instance Decode XML.Tree where decode = Decode.tree

instance Encode Properties.T where encode = Encode.properties
instance Decode Properties.T where decode = Decode.properties

instance Encode Typ where encode = Encode.typ
instance Decode Typ where decode = Decode.typ

instance Encode Term where encode = Encode.term
instance Decode Term where decode = Decode.term
