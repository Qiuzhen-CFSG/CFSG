module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd.FixedPlane
public import Theory.Representation.BinaryPermutation.FivePairOrbits
public import Theory.Representation.NormalElementaryQuotient.BestOffender
public import Theory.Representation.BinaryOffender.FixedCodimTransport
public import Theory.GroupAction.NormalPChiefSeries.Linear

/-!
# A common pair group for the actual five-point Thompson action

Maximum elementary subgroups of S induce best offenders on any faithful
normal elementary module contained in S. On the deleted five-point module,
the odd-degree offender classification puts all their images in a common
conjugate of the disjoint-transposition four group. This retains that actual
conjugator, allowing the fixed plane to meet both alternating vector orbits.

Source: Aschbacher–Smith B.2.5, B.3.2 and 10.2.9(1), pp.76,83–84,750.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.Offenders
open BinaryPermutation.FivePairFixedSpaces

private theorem five_disjoint_eq_pair : D 5 = pairClosure := by
  unfold D disjointTranspositions pairClosure
  congr 1
  ext p
  constructor
  · rintro ⟨i, hi, rfl⟩
    fin_cases i <;> simp [pairSwap, first, second]
  · rintro (rfl | hp)
    · exact ⟨0, by decide, rfl⟩
    · have hp : p = second := hp
      subst p
      exact ⟨1, by decide, rfl⟩

theorem exists_five_offender_pair_bound (P : Subgroup Perm) (hP : IsPGroup 2 P) :
    ∃ a : Perm, ∀ A, IsBestOffender (BinaryPermutation.naturalRepresentation (Fin 5)) A →
      A ≤ P → A ≤ pairClosure.map (MulAut.conj a).toMonoidHom := by
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  obtain ⟨R, hDR, _⟩ := Odd.exists_sylow_containing_D (Or.inl rfl : 5 = 5 ∨ 5 = 7)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Perm R S
  have hcancel (A : Subgroup Perm) :
      (A.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = A := by
    change (A.conjBy g⁻¹).conjBy g = A
    rw [conjBy_conjBy, mul_inv_cancel, conjBy_one]
  have hgmap : (R : Subgroup Perm).map (MulAut.conj g).toMonoidHom = S :=
    congrArg (fun U : Sylow 2 Perm => (U : Subgroup Perm)) hg
  refine ⟨g, ?_⟩
  intro A hA hAP
  have hinv : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ R := by
    apply (map_le_map_iff_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective).mp
    rw [hcancel, hgmap]
    exact hAP.trans hPS
  have hB := Odd.caseAFamily_le_D_of_le_sylow (Or.inl rfl) R hDR
    ((Odd.isBestOffender_natural_iff_caseAFamily (Or.inl rfl) _).mp
      (hA.map_conj _ g⁻¹)) hinv
  have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hB
  rwa [hcancel, five_disjoint_eq_pair] at hh

variable {H : Type*} [Group H] [Finite H]

theorem thompson_image_le_pair
    (W S : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W]
    (hWS : W ≤ S) (hS : IsPGroup 2 S)
    (π : H →* Perm) (hker : π.ker = centralizer (W : Set H))
    (E : Additive W ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5))
    (he : ∀ h w, E (normalRepresentation W h w) =
      BinaryPermutation.naturalRepresentation (Fin 5) (π h) (E w)) :
    ∃ a : Perm, (elementaryAbelianMaxJ S).map π ≤
      pairClosure.map (MulAut.conj a).toMonoidHom := by
  let q := π.rangeRestrict
  have hk : q.ker = centralizer (W : Set H) := π.ker_rangeRestrict.trans hker
  let ρ := NormalElementaryQuotient.representation W q π.rangeRestrict_surjective hk
  let σ := BinaryPermutation.naturalRepresentation (Fin 5)
  have heq : ∀ g w, E (ρ g w) = σ g.val (E w) := by
    intro g w
    obtain ⟨h, rfl⟩ := π.rangeRestrict_surjective g
    have hrep : ρ (q h) w = normalRepresentation W h w := by
      apply Additive.toMul.injective
      apply Subtype.ext
      exact NormalElementaryQuotient.representation_apply W q π.rangeRestrict_surjective hk h w
    rw [hrep]
    exact he h w
  obtain ⟨a, ha⟩ := exists_five_offender_pair_bound (S.map π) (hS.map π)
  refine ⟨a, ?_⟩
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro A hA
  apply map_le_iff_le_comap.mp
  have hmap : (A.map q).map π.range.subtype = A.map π := by
    rw [Subgroup.map_map]
    rfl
  by_cases hb : A.map q = ⊥
  · rw [← hmap, hb, Subgroup.map_bot]
    exact bot_le
  have hbA := NormalElementaryQuotient.maxElementary_isBestOffender W q
    π.rangeRestrict_surjective hk S A hWS hA hb
  have hmodel := hbA.map_of_fixedCodim ρ σ π.range.subtype π.range.subtype_injective
    (fixedCodim_map_equivariant ρ σ π.range.subtype E heq)
  rw [hmap] at hmodel
  exact ha _ hmodel (map_mono hA.1)
end CFSG.Quasithin.ChapterB.Offenders
