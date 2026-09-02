module
import Mathlib
universe u v
structure C (G : Type u) : Type (max u v + 1) where
  Vertex : Type v
  adj : Vertex → Vertex → Prop
structure D {G : Type u} (c : C G) where
  a : c.Vertex
  a' : c.Vertex
  x : c.adj a a'
