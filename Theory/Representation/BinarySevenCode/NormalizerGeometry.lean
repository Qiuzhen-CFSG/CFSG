module
public import Theory.Representation.BinarySevenCode.Normalizer
public import Theory.ElementaryAbelian.BinaryRankDifference
public import Theory.Representation.BinarySevenCode.WeightFourGeometry

/-!
# Constant-weight subgroups in the actual seven-point normalizer model

Map a literal ambient subgroup into the marked binary core, preserving its
cardinality and binary rank. The rank-three code theorem then identifies its
pointwise centralizer inside N(V) with C(V). These statements retain the actual
conjugation action and apply to every weight-four subgroup, not just the displayed
simplex code. Their source consumer is the repaired weak-closure argument in
Aschbacher--Smith, 12.3.9--10, printed p.810.
-/

@[expose] public section
namespace BinarySevenCode.NormalizerModel
open Subgroup Module
open BinaryPermutation.SevenParabolic (Space)
variable {G : Type*} [Group G] {V : Subgroup G} (D : NormalizerModel V)

/-- The same coordinates in the standard core used for its dot product. -/
def coreCoordinates : V ≃* Multiplicative Space :=
  D.coordinates.trans evenWordsEquivCore.toAddEquiv.toMultiplicative

def wordSpace (U : Subgroup G) : Submodule (ZMod 2) Space :=
  AddSubgroup.toZModSubmodule 2
    (((U.subgroupOf V).map D.coreCoordinates.toMonoidHom).toAddSubgroup')

theorem mem_wordSpace (U : Subgroup G) (v : Space) :
    v ∈ D.wordSpace U ↔ (D.coreCoordinates.symm (Multiplicative.ofAdd v)).val ∈ U := by
  change Multiplicative.ofAdd v ∈ (U.subgroupOf V).map D.coreCoordinates.toMonoidHom ↔ _
  rw [mem_map_equiv]
  rfl

theorem coreCoordinates_mem_wordSpace {U : Subgroup G} (v : V) (hv : v.val ∈ U) :
    (D.coreCoordinates v).toAdd ∈ D.wordSpace U := by
  rw [D.mem_wordSpace]
  change (D.coreCoordinates.symm (D.coreCoordinates v)).val ∈ U
  simpa only [MulEquiv.symm_apply_apply] using hv

theorem card_wordSpace {U : Subgroup G} (hUV : U ≤ V) :
    Nat.card (D.wordSpace U) = Nat.card U := by
  change Nat.card ((U.subgroupOf V).map D.coreCoordinates.toMonoidHom) = Nat.card U
  rw [Subgroup.card_map_of_injective D.coreCoordinates.injective]
  exact Nat.card_congr (subgroupOfEquivOfLe hUV).toEquiv

theorem finrank_wordSpace {U : Subgroup G} (hUV : U ≤ V) :
    finrank (ZMod 2) (D.wordSpace U) = Nat.log 2 (Nat.card U) := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D.wordSpace U)
  rw [D.card_wordSpace hUV, Nat.card_zmod] at hc
  rw [hc, Nat.log_pow (by decide)]

include D in
theorem log_card_eq_six : Nat.log 2 (Nat.card V) = 6 := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Space)
  rw [Nat.card_zmod, BinaryPermutation.SevenParabolic.finrank_space] at hc
  have he : Nat.card V = Nat.card Space := Nat.card_congr (D.coreCoordinates).toEquiv
  rw [he, hc, Nat.log_pow (by decide)]

/-- The actual conjugation action in the core coordinates. -/
theorem coreCoordinates_equivariant (n : normalizer (V : Set G)) (v : V) :
    (D.coreCoordinates (V.normalizerMonoidHom n v)).toAdd =
      BinaryPermutation.SevenParabolic.action (D.permutation n) (D.coreCoordinates v).toAdd :=
  Subtype.ext (congrArg (fun x : EvenWord => x.val) (D.equivariant n v))

/-- The nonidentity elements of this literal subgroup all have weight four. -/
def WeightFour (U : Subgroup G) : Prop :=
  ∀ v : V, v.val ∈ U → v ≠ 1 → weight (D.coordinates v).toAdd.val = 4

theorem weight_four_wordSpace {U : Subgroup G} (hw : D.WeightFour U) :
    ∀ v ∈ D.wordSpace U, v ≠ 0 → weight v.val = 4 := by
  intro v hv hv0
  let x : V := D.coreCoordinates.symm (Multiplicative.ofAdd v)
  have hx : x.val ∈ U := (D.mem_wordSpace U v).mp hv
  have hx1 : x ≠ 1 := by
    intro he
    have he' := congrArg D.coreCoordinates he
    have hv1 : Multiplicative.ofAdd v = 1 := by
      simpa only [x, MulEquiv.apply_symm_apply, map_one] using he'
    exact hv0 (congrArg Multiplicative.toAdd hv1)
  have hh := hw x hx hx1
  change weight (D.coreCoordinates x).toAdd.val = 4 at hh
  simpa only [x, MulEquiv.apply_symm_apply, toAdd_ofAdd] using hh

/-- The corrected universal rank estimate for constant-weight subgroups. -/
theorem log_card_le_three_of_weight_four {U : Subgroup G}
    (hUV : U ≤ V) (hw : D.WeightFour U) : Nat.log 2 (Nat.card U) ≤ 3 := by
  rw [← D.finrank_wordSpace hUV]
  exact finrank_le_three_of_weight_four (D.wordSpace U) (D.weight_four_wordSpace hw)

/-- Every rank-three weight-four subgroup has the same local centralizer as V. -/
theorem normalizer_inf_centralizer_of_weight_four_rank_three {U : Subgroup G}
    (hUV : U ≤ V) (hw : D.WeightFour U) (hd : Nat.log 2 (Nat.card U) = 3) :
    normalizer (V : Set G) ⊓ centralizer (U : Set G) = centralizer (V : Set G) := by
  have hdim : finrank (ZMod 2) (D.wordSpace U) = 3 := by
    rw [D.finrank_wordSpace hUV, hd]
  apply le_antisymm
  · intro n hn
    let n' : normalizer (V : Set G) := ⟨n, hn.1⟩
    have hp : D.permutation n' = 1 := by
      apply perm_eq_one_of_fixes_weight_four_rank_three (D.wordSpace U)
        (D.weight_four_wordSpace hw) hdim
      intro w hwU i
      let v : V := D.coreCoordinates.symm (Multiplicative.ofAdd w)
      have hvU : v.val ∈ U := (D.mem_wordSpace U w).mp hwU
      have hfix : V.normalizerMonoidHom n' v = v := by
        apply Subtype.ext
        exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp hn.2) _ hvU).symm
      have he := D.coreCoordinates_equivariant n' v
      rw [hfix] at he
      simp only [v, MulEquiv.apply_symm_apply, toAdd_ofAdd] at he
      have hi := congrArg (fun x : Space => x.val (D.permutation n' i)) he
      simpa only [BinaryPermutation.coreRepresentation_apply,
        BinaryPermutation.representation_apply, Equiv.symm_apply_apply] using hi
    apply mem_centralizer_iff.mpr
    intro v hv
    have he := D.equivariant n' ⟨v, hv⟩
    rw [hp, map_one] at he
    have hfix : V.normalizerMonoidHom n' ⟨v, hv⟩ = ⟨v, hv⟩ :=
      D.coordinates.injective (Multiplicative.toAdd.injective he)
    exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hfix)).symm
  · exact le_inf (centralizer_le_normalizer _) (centralizer_le hUV)

end BinarySevenCode.NormalizerModel
