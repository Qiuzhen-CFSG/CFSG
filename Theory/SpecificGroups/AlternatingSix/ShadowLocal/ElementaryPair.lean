module
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.ElementaryRank
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.SylowGeometry
public import Theory.ElementaryAbelian.Quotient

/-!
# The two elementary eight-groups in a Sylow subgroup of Aut(A₆)

The two inner Klein four-groups, multiplied by the marked transposition,
give elementary eight-groups in the natural S₆ intersection. Every elementary
eight-group lies in that intersection; its involutions lie in the union of
the two constructed groups, so the subgroup union lemma gives exhaustion.
The rotation interchanges the groups, and each normalizer is the natural
intersection. All finite tables are checked by the kernel.

The marked holomorph equivalence transports the groups, conjugator, and
normalizers to an actual Sylow subgroup of MulAut(A₆), preserving the
natural S₆ subgroup. This is the quotient geometry used in the full case
of Aschbacher–Smith 16.4.9(2), printed p.1192 (PDF p.1209), combined
manuscript of 1 March 2004.
-/

@[expose] public section
open Subgroup
namespace AlternatingSix.ShadowLocal.Holomorph.ElementaryPair
set_option maxRecDepth 10000
set_option synthInstance.maxSize 2048

abbrev Eight := C2 × E4

instance eight_elementary : IsElementaryAbelian 2 Eight where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by decide +kernel)

def zeroEmbedding : Eight →* Model where
  toFun i := transpositionEmbedding i.1 * kleinZeroEmbedding i.2
  map_one' := rfl
  map_mul' := by decide +kernel

def oneEmbedding : Eight →* Model where
  toFun i := transpositionEmbedding i.1 * kleinOneEmbedding i.2
  map_one' := rfl
  map_mul' := by decide +kernel

def zero : Subgroup Model := zeroEmbedding.range
def one : Subgroup Model := oneEmbedding.range

theorem zeroEmbedding_injective : Function.Injective zeroEmbedding := by decide +kernel
theorem oneEmbedding_injective : Function.Injective oneEmbedding := by decide +kernel

instance zero_elementary : IsElementaryAbelian 2 zero :=
  IsElementaryAbelian.of_surjective zeroEmbedding.rangeRestrict
    zeroEmbedding.rangeRestrict_surjective
instance one_elementary : IsElementaryAbelian 2 one :=
  IsElementaryAbelian.of_surjective oneEmbedding.rangeRestrict
    oneEmbedding.rangeRestrict_surjective

theorem card_zero : Nat.card zero = 8 := by
  rw [zero, ← Nat.card_congr (MonoidHom.ofInjective zeroEmbedding_injective).toEquiv]
  simp [Eight, E4, C2]

theorem card_one : Nat.card one = 8 := by
  rw [one, ← Nat.card_congr (MonoidHom.ofInjective oneEmbedding_injective).toEquiv]
  simp [Eight, E4, C2]

theorem zero_ne_one : zero ≠ one := by
  intro he
  have hc : reflection ∈ zero := ⟨(1, 1, .ofAdd 1), by decide +kernel⟩
  rw [he] at hc
  have hn : ¬ ∃ i, oneEmbedding i = reflection := by decide +kernel
  exact hn hc

theorem rotation_conjugates :
    zero.map (MulAut.conj rotation).toMonoidHom = one := by
  ext x
  simp only [mem_map_equiv]
  change (∃ i, zeroEmbedding i = (MulAut.conj rotation).symm x) ↔ ∃ i, oneEmbedding i = x
  revert x
  decide +kernel

theorem rotation_conjugates_one :
    one.map (MulAut.conj rotation).toMonoidHom = zero := by
  ext x
  simp only [mem_map_equiv]
  change (∃ i, oneEmbedding i = (MulAut.conj rotation).symm x) ↔ ∃ i, zeroEmbedding i = x
  revert x
  decide +kernel

theorem normalizer_zero : normalizer (zero : Set Model) = natural := by
  ext x
  simp only [mem_normalizer_iff, zero, MonoidHom.mem_range, mem_natural]
  revert x
  decide +kernel

theorem normalizer_one : normalizer (one : Set Model) = natural := by
  ext x
  simp only [mem_normalizer_iff, one, MonoidHom.mem_range, mem_natural]
  revert x
  decide +kernel

private theorem natural_involution_cover : ∀ x : Model,
    (∃ i, naturalEmbedding i = x) → x ^ 2 = 1 →
    (∃ i, zeroEmbedding i = x) ∨ ∃ i, oneEmbedding i = x := by decide +kernel

theorem elementary_eight_cases (E : Subgroup Model) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) : E = zero ∨ E = one := by
  have hEn := elementary_le_natural_of_eight_le E hE.ge
  have hsub : (E : Set Model) ⊆ (zero : Set Model) ∪ (one : Set Model) := by
    intro x hx
    exact natural_involution_cover x ((mem_natural x).mp (hEn hx))
      (elemPow_eq_one_of_isElementaryAbelian x hx)
  rcases SubgroupClass.subset_union.mp hsub with h | h
  · exact Or.inl (eq_of_le_of_card_ge h (by rw [card_zero, hE]))
  · exact Or.inr (eq_of_le_of_card_ge h (by rw [card_one, hE]))

end AlternatingSix.ShadowLocal.Holomorph.ElementaryPair

namespace AlternatingSix.ShadowLocal.ElementaryPair
open Identification
namespace ModelPair
abbrev zero := Holomorph.ElementaryPair.zero
abbrev one := Holomorph.ElementaryPair.one
end ModelPair

noncomputable def zero (P : Sylow 2 AutA6) : Subgroup P :=
  ModelPair.zero.map (sylowEquiv P).toMonoidHom

noncomputable def one (P : Sylow 2 AutA6) : Subgroup P :=
  ModelPair.one.map (sylowEquiv P).toMonoidHom

instance zero_elementary (P : Sylow 2 AutA6) : IsElementaryAbelian 2 (zero P) :=
  IsElementaryAbelian.map _
instance one_elementary (P : Sylow 2 AutA6) : IsElementaryAbelian 2 (one P) :=
  IsElementaryAbelian.map _

theorem card_zero (P : Sylow 2 AutA6) : Nat.card (zero P) = 8 := by
  rw [zero, card_map_of_injective (sylowEquiv P).injective]
  exact Holomorph.ElementaryPair.card_zero

theorem card_one (P : Sylow 2 AutA6) : Nat.card (one P) = 8 := by
  rw [one, card_map_of_injective (sylowEquiv P).injective]
  exact Holomorph.ElementaryPair.card_one

theorem zero_ne_one (P : Sylow 2 AutA6) : zero P ≠ one P := by
  intro he
  exact Holomorph.ElementaryPair.zero_ne_one ((sylowEquiv P).mapSubgroup.injective he)

theorem rotation_conjugates (P : Sylow 2 AutA6) :
    (zero P).map (MulAut.conj (sylowEquiv P Holomorph.rotation)).toMonoidHom = one P := by
  have h := congrArg (Subgroup.map (sylowEquiv P).toMonoidHom)
    Holomorph.ElementaryPair.rotation_conjugates
  rw [map_map] at h
  rw [zero, one, map_map]
  convert h using 2
  ext x
  simp

theorem rotation_conjugates_one (P : Sylow 2 AutA6) :
    (one P).map (MulAut.conj (sylowEquiv P Holomorph.rotation)).toMonoidHom = zero P := by
  have h := congrArg (Subgroup.map (sylowEquiv P).toMonoidHom)
    Holomorph.ElementaryPair.rotation_conjugates_one
  rw [map_map] at h
  rw [zero, one, map_map]
  convert h using 2
  ext x
  simp

theorem normalizer_zero (P : Sylow 2 AutA6) :
    normalizer (zero P : Set P) = sylowNatural P := by
  rw [zero, ← map_equiv_normalizer_eq, Holomorph.ElementaryPair.normalizer_zero,
    sylowEquiv_natural]

theorem normalizer_one (P : Sylow 2 AutA6) :
    normalizer (one P : Set P) = sylowNatural P := by
  rw [one, ← map_equiv_normalizer_eq, Holomorph.ElementaryPair.normalizer_one,
    sylowEquiv_natural]

theorem elementary_eight_cases (P : Sylow 2 AutA6) (E : Subgroup P)
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 8) : E = zero P ∨ E = one P := by
  let W := E.map (sylowEquiv P).symm.toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hW : Nat.card W = 8 := by
    rw [card_map_of_injective (sylowEquiv P).symm.injective]
    exact hE
  have hmap : W.map (sylowEquiv P).toMonoidHom = E := (sylowEquiv P).mapSubgroup.apply_symm_apply E
  rcases Holomorph.ElementaryPair.elementary_eight_cases W hW with h | h
  · exact Or.inl (hmap.symm.trans (congrArg (Subgroup.map (sylowEquiv P).toMonoidHom) h))
  · exact Or.inr (hmap.symm.trans (congrArg (Subgroup.map (sylowEquiv P).toMonoidHom) h))

theorem normalizer_elementary_eight (P : Sylow 2 AutA6) (E : Subgroup P)
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 8) :
    normalizer (E : Set P) = sylowNatural P := by
  rcases elementary_eight_cases P E hE with rfl | rfl
  · exact normalizer_zero P
  · exact normalizer_one P

end AlternatingSix.ShadowLocal.ElementaryPair
