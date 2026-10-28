module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Structure
public import Theory.SpecificGroups.SymmetricSix.Parabolics

/-!
# The unique syntheme four-group in a two-group

Degree-six best offenders in the alternating natural row are conjugates of
D ∩ A6. The proved Sylow list makes any two such subgroups contained in a
common two-group equal. The marked syntheme stabilizer normalizes this
four-group, by its four explicit permutation words.

Source: Aschbacher--Smith B.3.2 and the C.2.7 placement, pp.83--85,146.
-/
public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterB.Offenders.Six

theorem evenPart_conjugates_eq_in_twoGroup
    (R : Subgroup Perm) (hR : IsPGroup 2 R)
    {A B : Subgroup Perm} (hA : IsConjugateTo A (evenPart 6))
    (hB : IsConjugateTo B (evenPart 6)) (hAR : A ≤ R) (hBR : B ≤ R) : A = B := by
  obtain ⟨P,hRP⟩ := hR.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Perm P sylow
  let e := (MulAut.conj g).mapSubgroup
  have hP : e (P : Subgroup Perm) = sylowCarrier := by
    change ((g • P : Sylow 2 Perm) : Subgroup Perm) = _
    rw [hg,sylow_coe]
  have eqn (X : Subgroup Perm) (hX : IsConjugateTo X (evenPart 6)) (hXP : X ≤ P) :
      e X = evenPart 6 := by
    have hc : IsConjugateTo (e X) (evenPart 6) := (show IsConjugateTo (e X) X from ⟨g,rfl⟩).trans hX
    exact (caseBFamily_even_le_sylowCarrier_iff _).mp
      ⟨Or.inr (Or.inr (Or.inl hc)),hP ▸ e.monotone hXP,hc.le_alternating_iff.mpr inf_le_right⟩
  exact e.injective ((eqn A hA (hAR.trans hRP)).trans (eqn B hB (hBR.trans hRP)).symm)

open Theory.SpecificGroups.SymmetricSix

private theorem syntheme_conjugates_words :
    ∀ g : A6, g ∈ a6SynthemeStabilizer → ∀ i : Fin 4,
      ∃ j : Fin 4, (g : Perm) * planeWords 4 i * (g : Perm)⁻¹ = planeWords 4 j := by
  decide +kernel

theorem syntheme_le_normalizer_evenPart :
    a6SynthemeStabilizer ≤ normalizer ((evenPart 6).subgroupOf A6 : Set A6) := by
  apply le_normalizer_iff_commutator_le_left.mpr
  apply commutator_le.mpr
  intro a ha g hg
  change ⁅(a : Perm),(g : Perm)⁆ ∈ evenPart 6
  have hg' : (g : Perm) * (a : Perm) * (g : Perm)⁻¹ ∈ evenPart 6 := by
    obtain ⟨i,hi⟩ := (mem_evenPart_iff a).mp ha
    obtain ⟨j,hj⟩ := syntheme_conjugates_words g hg i
    apply (mem_evenPart_iff _).mpr
    exact ⟨j,by rw [←hj,hi]⟩
  have hh := (evenPart 6).mul_mem ha ((evenPart 6).inv_mem hg')
  simpa only [commutatorElement_def,mul_inv_rev,inv_inv,mul_assoc, Subgroup.subtype_apply] using hh
end CFSG.Quasithin.ChapterB.Offenders.Six

