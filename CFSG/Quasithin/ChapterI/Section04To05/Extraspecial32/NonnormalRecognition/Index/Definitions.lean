module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Fusion
public import Theory.GroupTheory.TwoInvolutionClassOrder
public import Theory.GroupTheory.PResidual.Defs

/-!
# Markings for the index calculation in the nonnormal quaternion case

The marked elements are literal permutations: `z8` and `z9` have four
transpositions; `t8` and `t9` have two. The source marking must identify the
distinguished involution with `z8` and prove that the two classes stay distinct
in the ambient group. The second centralizer comparison is an actual group
isomorphism preserving its distinguished element and both ambient classes.
These structures are explicit intermediate inputs, not source hypotheses.

Source: Aschbacher, “A 2-local characterization of M12”, Proposition 3.3,
printed p.38. Its J and X are two-residuals O², not two-cores O₂.
-/

@[expose] public section

namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index

open Subgroup Equiv Equiv.Perm
open Theory.GroupTheory.TwoInvolutionClassOrder

abbrev Eight := alternatingGroup (Fin 8)
abbrev Nine := alternatingGroup (Fin 9)

/-- The fixed-point-free involution of the eight-point model. -/
def z8 : Eight := ⟨swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7, by simp [mem_alternatingGroup, map_mul]⟩
/-- The double transposition of the eight-point model. -/
def t8 : Eight := ⟨swap 0 1 * swap 2 3, by simp [mem_alternatingGroup, map_mul]⟩
/-- The four-transposition involution of the nine-point model. -/
def z9 : Nine := ⟨swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7, by simp [mem_alternatingGroup, map_mul]⟩
/-- The double transposition of the nine-point model. -/
def t9 : Nine := ⟨swap 0 1 * swap 2 3, by simp [mem_alternatingGroup, map_mul]⟩

variable {G : Type*} [Group G]

/-- The marked A₈ subgroup and the two distinct ambient involution classes.
The equivalence may relabel the initially supplied A₈ action. -/
structure InvolutionData (z : G) (L : Subgroup G) where
  equiv : L ≃* Eight
  z_mem : z ∈ L
  z_image : equiv ⟨z, z_mem⟩ = z8
  not_conjugate : ¬ IsConj z (equiv.symm t8 : G)
  classes : ∀ a : L, orderOf a = 2 →
    IsConj (⟨z, z_mem⟩ : L) a ∨ IsConj (equiv.symm t8) a

/-- The second marked involution, as an element of the actual subgroup L. -/
def InvolutionData.t {z : G} {L : Subgroup G} (d : InvolutionData z L) : L :=
  d.equiv.symm t8

/-- The actual second involution centralizer in the ambient group. -/
abbrev InvolutionData.K {z : G} {L : Subgroup G} (d : InvolutionData z L) :=
  Centralizer (d.t : G)

/-- J = O²(C_G(t)), embedded in G. -/
def InvolutionData.J {z : G} {L : Subgroup G} (d : InvolutionData z L) : Subgroup G :=
  (pResidual 2 d.K).map d.K.subtype

/-- X = O²(C_L(t)), embedded in G through both literal inclusions. -/
def InvolutionData.X {z : G} {L : Subgroup G} (d : InvolutionData z L) : Subgroup G :=
  ((pResidual 2 (centralizer ({d.t} : Set L))).map
    (centralizer ({d.t} : Set L)).subtype).map L.subtype

/-- The actual A₉ comparison of the second centralizer, with ambient fusion.
An unmarked isomorphism does not supply this interface. -/
structure SecondCentralizerData {z : G} {L : Subgroup G} (d : InvolutionData z L) where
  equiv : d.K ≃* Centralizer t9
  involution_image : equiv (distinguished (d.t : G)) = distinguished t9
  z_fusion : ∀ a : d.K, IsConj z (a : G) ↔ IsConj z9 (equiv a : Nine)
  t_fusion : ∀ a : d.K, IsConj (d.t : G) (a : G) ↔ IsConj t9 (equiv a : Nine)

/-- The finite model calculations consumed by Thompson's order formula.
No ambient order or index conclusion is part of this interface. -/
structure ModelCounts : Prop where
  eight_z : kappa z8 t8 z8 = 156
  nine_t : kappa z9 t9 t9 = 555
  nine_centralizer : Nat.card (Centralizer t9) = 480

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index
end
