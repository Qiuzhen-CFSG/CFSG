module
import Stellmacher.SectionsOneToFourDefs
open Stellmacher Stellmacher.SectionOne
universe u
variable {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
  [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
variable (S : Subgroup G)
#synth Nonempty (LemmaOneSixConclusion (G := G) (V := V) S)
#check Classical.choice
