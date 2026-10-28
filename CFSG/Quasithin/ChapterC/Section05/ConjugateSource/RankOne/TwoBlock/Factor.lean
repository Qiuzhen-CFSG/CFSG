module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.Product
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Family.Pair

/-!
# The conjugate-generated natural factor with its central cover

For F=UUˣ the intersection F∩Q is precisely U. Thus F∩D=U∩D;
this central overlap is retained. The marked shear action determines the
full fixed subgroup of every actor outside Q, before any quotient is taken.

Source: Aschbacher–Smith, C.5.6(7), printed p.159.
-/
public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R K : Subgroup G} {𝔽 : Type*} [Field 𝔽]

omit [Finite G] in
private theorem inverse_map (A : Subgroup G) (x : G) :
    (A.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = A := by
  rw [map_map]
  have he : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom = MonoidHom.id G := by
    ext g
    simp [MulAut.conj_apply, mul_assoc]
  rw [he, map_id]

theorem Setup.conjugate_fixed_intersection (h : Setup R K 𝔽) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    (U K).map (MulAut.conj x⁻¹).toMonoidHom ⊓ centralizer (U K : Set G) =
      U K ⊓ (U K).map (MulAut.conj x⁻¹).toMonoidHom := by
  have hi := inverse_not_centralizing (U K) x⁻¹ hnc
  simp only [inv_inv] at hi
  have hh := h.commutator_eq_fixed ((normalizer (R : Set G)).inv_mem hx)
    (by simpa only [inv_inv] using hi)
  simp only [inv_inv] at hh
  have he := congrArg (map (MulAut.conj x⁻¹).toMonoidHom) (hh.1.symm.trans hh.2)
  rw [map_inf _ _ _ (MulAut.conj x⁻¹).injective,
    map_inf _ _ _ (MulAut.conj x⁻¹).injective, inverse_map] at he
  have hc : (centralizer ((U K).map (MulAut.conj x).toMonoidHom : Set G)).map
      (MulAut.conj x⁻¹).toMonoidHom = centralizer (U K : Set G) := by
    apply le_antisymm
    · have hm := map_centralizer_le_centralizer_image
        ((U K).map (MulAut.conj x).toMonoidHom : Set G) (MulAut.conj x⁻¹).toMonoidHom
      simpa only [← Subgroup.coe_map, inverse_map] using hm
    · intro z hz
      refine ⟨(MulAut.conj x) z, ?_, ?_⟩
      · rintro _ ⟨u, hu, rfl⟩
        exact (map_mul (MulAut.conj x) u z).symm.trans
          ((congrArg (MulAut.conj x) (hz u hu)).trans (map_mul (MulAut.conj x) z u))
      · simp [MulAut.conj_apply, mul_assoc]
  rw [hc] at he
  exact he.trans (inf_comm _ _)

theorem Setup.conjugate_factor_structure (h : Setup R K 𝔽) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    let V := (U K).map (MulAut.conj x⁻¹).toMonoidHom
    let A := U K ⊔ V
    S R = A ⊔ D R K ∧ D R K ≤ centralizer (A : Set G) ∧
      A ⊓ Q R K = U K ∧ A ⊓ D R K = U K ⊓ D R K ∧
      A ⊓ centralizer (A : Set G) ≤ U K := by
  let V := (U K).map (MulAut.conj x⁻¹).toMonoidHom
  let A := U K ⊔ V
  have hp := h.factorization hx hnc
  have hAS : A ≤ S R := sup_le h.module_le (h.conjugate_le hx)
  have hDA : D R K ≤ centralizer (A : Set G) := by
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp (inf_le_right.trans (centralizer_le (map_subtype_le _))))
      (le_centralizer_iff.mp hp.centralizes)
  have hAQ : A ⊓ Q R K = U K := by
    apply le_antisymm
    · rintro g ⟨hg, hgQ⟩
      have hm : g ∈ (U K : Set G) * (V : Set G) := by
        rw [← coe_mul_of_right_le_normalizer_left (U K) V
          ((h.conjugate_le hx).trans h.coordinates.normalizes)]
        exact hg
      obtain ⟨u, hu, v, hv, rfl⟩ := hm
      have hvQ : v ∈ Q R K := by
        simpa using (Q R K).mul_mem ((Q R K).inv_mem (h.module_le_core hu)) hgQ
      have hvU : v ∈ U K := ((h.conjugate_fixed_intersection hx hnc).le
        ⟨hv, (h.core.le hvQ).2⟩).1
      exact (U K).mul_mem hu hvU
    · exact le_inf le_sup_left h.module_le_core
  refine ⟨?_, hDA, hAQ, ?_, ?_⟩
  · change S R = (U K ⊔ V) ⊔ D R K
    rw [hp.span, hp.core]
    dsimp only [V]
    ac_rfl
  · apply le_antisymm
    · exact le_inf ((inf_le_inf_left A (hp.core ▸ le_sup_right)).trans hAQ.le) inf_le_right
    · exact inf_le_inf_right _ le_sup_left
  · apply (le_inf inf_le_left ?_).trans hAQ.le
    rw [h.core]
    exact le_inf (inf_le_left.trans hAS)
      (inf_le_right.trans (centralizer_le (show U K ≤ A from le_sup_left)))

theorem Setup.fixed_module_mem_conjugate (h : Setup R K 𝔽) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G))
    (s : S R) (hsq : (s : G) ∉ Q R K) (u : U K)
    (hfix : moduleConjugate h.coordinates.normalizes s u = u) :
    (u : G) ∈ (U K).map (MulAut.conj x⁻¹).toMonoidHom := by
  have hparam : (h.coordinates.parameter s).toAdd ≠ 0 := by
    intro he
    apply hsq
    rw [h.core]
    exact ⟨s.property, (h.coordinates.parameter_kernel s).mp (Multiplicative.toAdd.injective he)⟩
  have hzero : (h.coordinates.projection u).toAdd 1 = 0 := by
    have hh := congrArg (fun v : Multiplicative (Fin 2 → 𝔽) => v.toAdd 0)
      (congrArg h.coordinates.projection hfix)
    rw [h.coordinates.equivariant] at hh
    have hz : (h.coordinates.parameter s).toAdd * (h.coordinates.projection u).toAdd 1 = 0 := by
      simpa using hh
    exact (mul_eq_zero.mp hz).resolve_left hparam
  have hc := centralizes_of_second_zero h.coordinates h.fixedLift u hzero
  have hu : (u : G) ∈ U K ⊓ centralizer ((U K).map (MulAut.conj x⁻¹).toMonoidHom : Set G) :=
    ⟨u.property, centralizer_le (h.conjugate_le hx) hc⟩
  rw [← (h.commutator_eq_fixed hx hnc).1, (h.commutator_eq_fixed hx hnc).2] at hu
  exact hu.2
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
