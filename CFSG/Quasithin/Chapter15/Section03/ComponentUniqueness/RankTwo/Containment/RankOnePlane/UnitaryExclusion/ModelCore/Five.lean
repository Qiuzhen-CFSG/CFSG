module

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary
public import Theory.SpecificGroups.SU3.BorelTorus.Basic

/-!
# A genuine five-element in every PSU₃(4) component Borel

The actual projective diagonal torus has order fifteen, so Cauchy's theorem
supplies an element of order five in the matrix Borel. The proved Hermitian
basis change and Sylow conjugacy transport that element to every Sylow
normalizer of every stored form. A genuine model equivalence and the component
embedding then put it in the ambient subgroup L ∩ N_G(S ∩ L).

The fixed field has order four; the matrix field has order sixteen. Neither
the model equivalence nor the Sylow marking is discarded in the transport.

Source: Huppert II.10.12; Aschbacher--Smith, proof of 15.3.40, printed p.1138.
This establishes the five-element input, not the remaining two-core control.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.Unitary
open scoped Matrix

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane.UnitaryExclusion

/-- Every intrinsic Sylow normalizer in the actual PSU₃(4) model has a five-element. -/
theorem psu_four_normalizer_has_five
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4)
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ x : ProjectiveSpecialUnitaryMatrixGroup J,
      x ∈ normalizer (P : Set _) ∧ orderOf x = 5 := by
  obtain ⟨C, hC, g, hN⟩ := psu_sylow_normalizer_eq_matrix_borel
    J 2 (by decide) hcard hconj P
  let J0 := FormTransport.standardForm J
  let e := FormTransport.projectiveEquiv J C hC
  let D := (hermitianTorusPSU J0 rfl).range
  have hD : Nat.card D = 15 := by
    have hc := HermitianForm.BorelTorus.projective_card J0 rfl (q := 4) hcard hconj
    norm_num at hc
    exact hc
  let : Finite D := Nat.finite_of_card_ne_zero (by omega)
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hdvd : 5 ∣ Nat.card D := by rw [hD]; decide
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 5 hdvd
  refine ⟨e.symm ((MulAut.conj g) t.val), ?_, ?_⟩
  · rw [hN]
    change e (e.symm ((MulAut.conj g) t.val)) ∈
      (((hermitianUnipotentPSU J0 rfl).range ⊔ D).map (MulAut.conj g).toMonoidHom)
    rw [e.apply_symm_apply]
    exact mem_map_of_mem _ ((show D ≤ (hermitianUnipotentPSU J0 rfl).range ⊔ D
      from le_sup_right) t.property)
  · exact (orderOf_injective e.symm.toMonoidHom e.symm.injective _).trans
      ((orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective _).trans
        ((orderOf_injective D.subtype D.subtype_injective t).trans ht))

/-- The specified ambient component Borel contains an element of order five. -/
theorem unitary_four_borel_has_five {G : Type*} [Group G] [Finite G]
    {L S : Subgroup G} (hm : ClassicalGroup.IsPSU L 3 4) (P : Sylow 2 L)
    (hP : (P : Subgroup L).map L.subtype = S ⊓ L) :
    ∃ x : G, x ∈ borel L S ∧ orderOf x = 5 := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hm
  obtain ⟨x, hx, hx5⟩ := psu_four_normalizer_has_five J hcard hconj
    (P.mapSurjective (f := e.toMonoidHom) e.surjective)
  have hy : e.symm x ∈ normalizer (P : Set L) := by
    have he := map_equiv_normalizer_eq (P : Subgroup L) e
    change x ∈ normalizer (((P : Subgroup L).map e.toMonoidHom) : Set _) at hx
    rw [← he] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  have hn : (normalizer (P : Set L)).map L.subtype = borel L S := by
    have hc : (S ⊓ L).subgroupOf L = (P : Subgroup L) := by
      rw [← hP]
      exact comap_map_eq_self_of_injective L.subtype_injective _
    change (normalizer ((P : Subgroup L) : Set L)).map L.subtype = _
    rw [← hc, ← subgroupOf_normalizer_eq inf_le_right,
      subgroupOf, map_comap_eq, range_subtype]
    rfl
  refine ⟨e.symm x, hn ▸ mem_map_of_mem L.subtype hy, ?_⟩
  rw [Subgroup.orderOf_coe]
  exact (orderOf_injective e.symm.toMonoidHom e.symm.injective x).trans hx5

end CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane.UnitaryExclusion
