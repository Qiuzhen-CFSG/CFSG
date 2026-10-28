module

import all Theory.SpecificGroups.PSL2.QuinticInnerFusion
public import GorensteinWalter.PGL2KleinFourSelfCentralizer
public import GorensteinWalter.KleinFourMapInjective
public import Theory.GroupTheory.PGroup.RankOneInvolution
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Quintic whole-subgroup fusion in odd PGL₂

The two-core of a Sylow supplement to a normal quintic group centralizes
that group and contains no Klein four. Its involutions are unique and
therefore fixed by the Sylow normalizer. A Klein four in the inner PSL₂
Sylow subgroup is self-centralizing in PGL₂, so these involutions are inner.
Inner involution fusion then moves the whole elementary subgroup out of the
two-core while retaining the original Sylow subgroup.

The conjugator lies in the canonical PSL₂ group. This supplies the linear
extension case of the final paragraph of Aschbacher--Smith 6.1.4, p.666.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2

private theorem exists_inner_four_in_linear_sylow
    {F : Type*} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (T : Sylow 2 (PGL2 F)) :
    ∃ V : Subgroup (PGL2 F), IsKleinFour V ∧ V ≤ (T : Subgroup (PGL2 F)) ∧
      V ≤ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  let : Finite (PGL2 F) := Finite.of_surjective Matrix.ProjGenLinGroup.mk
    Matrix.ProjGenLinGroup.mk_surjective
  let j : PSL(2,F) →* PGL2 F := Matrix.ProjectiveSpecialLinearGroup.toPGL
  have hj : Function.Injective j := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  let e : PSL(2,F) ≃* j.range := MonoidHom.ofInjective hj
  let : j.range.Normal := j.range.normal_of_index_eq_two (pgl2_psl2Range_index_eq_two F hF)
  obtain ⟨Q, hQ⟩ := T.exists_subgroupOf_eq_of_normal j.range
  let R := Q.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hRT : (R : Subgroup PSL(2,F)).map j ≤ (T : Subgroup (PGL2 F)) := by
    rintro _ ⟨r, hr, rfl⟩
    change r ∈ (Q : Subgroup j.range).map e.symm.toMonoidHom at hr
    obtain ⟨q, hq, rfl⟩ := hr
    have he : j (e.symm q) = q := congrArg Subtype.val (e.apply_symm_apply q)
    change j (e.symm q) ∈ T
    rw [he]
    rw [hQ] at hq
    exact hq
  obtain ⟨n, hn, ⟨d⟩⟩ := psl2_odd_hasDihedralSylowTwo_model F hF R
  obtain ⟨V, hVR, hV⟩ := exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
    (R : Subgroup PSL(2,F)) hn d
  exact ⟨V.map j, isKleinFour_map_of_injective V hV j hj,
    (map_mono hVR).trans hRT, map_le_range j V⟩

/-- Whole elementary subgroups of the quintic two-core fuse out under the
canonical PSL₂ group, even when the original Sylow subgroup lies in PGL₂. -/
theorem odd_quintic_linear_elementary_fusion
    {F : Type*} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F))
    (X : Subgroup (PGL2 F)) (T : Sylow 2 (PGL2 F))
    (hfive : Nat.card X = 5) (hTX : (T : Subgroup (PGL2 F)) ≤ normalizer X)
    (A : Subgroup (PGL2 F)) (hA : IsElementaryAbelian 2 A) (hAne : A ≠ ⊥)
    (hAS : A ≤ (X ⊔ (T : Subgroup (PGL2 F))).pCoreIn 2) :
    ∃ g : PSL(2,F),
      A.map (MulAut.conj (Matrix.ProjectiveSpecialLinearGroup.toPGL g)).toMonoidHom ≤
        (T : Subgroup (PGL2 F)) ∧
      ¬ A.map (MulAut.conj (Matrix.ProjectiveSpecialLinearGroup.toPGL g)).toMonoidHom ≤
        (X ⊔ (T : Subgroup (PGL2 F))).pCoreIn 2 := by
  classical
  let : Finite (PGL2 F) := Finite.of_surjective Matrix.ProjGenLinGroup.mk
    Matrix.ProjGenLinGroup.mk_surjective
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let : IsCyclic X := isCyclic_of_prime_card hfive
  have hXne : X ≠ ⊥ := by intro he; simp [he] at hfive
  have hXodd : Odd (Nat.card X) := by rw [hfive]; decide
  let H := X ⊔ (T : Subgroup (PGL2 F))
  let S := H.pCoreIn 2
  have hSC : S ≤ centralizer (X : Set (PGL2 F)) :=
    quintic_join_core_centralizes X T hfive hTX
  have hTS : (T : Subgroup (PGL2 F)) ≤ normalizer S :=
    (show (T : Subgroup (PGL2 F)) ≤ H from le_sup_right).trans
      (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hSfour (V : Subgroup S) (hV : IsElementaryAbelian 2 V) (hc : Nat.card V = 4) : False := by
    let : IsElementaryAbelian 2 V := hV
    let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    have hVK : IsKleinFour V := ⟨hc, IsElementaryAbelian.exponent_eq_prime⟩
    have hi := isKleinFour_map_of_injective V hVK S.subtype S.subtype_injective
    exact pgl2_no_kleinFour_centralizes_odd_cyclic F hF X (V.map S.subtype)
      inferInstance hXne hXodd hi ((map_subtype_le V).trans hSC)
  let : IsElementaryAbelian 2 A := hA
  let : Nontrivial A := (nontrivial_iff_ne_bot A).mpr hAne
  obtain ⟨a, ha, ha1⟩ := A.exists_ne_one_of_nontrivial
  have haS : a ∈ S := hAS ha
  have ha2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
  let : Nontrivial S := (nontrivial_iff_ne_bot S).mpr (by
    intro he
    apply ha1
    simpa only [he, mem_bot] using haS)
  obtain ⟨z, _, _, huniq⟩ := (isPGroup_pCoreIn 2 H).exists_central_involution_of_no_elementary_four hSfour
  have haz : (⟨a, haS⟩ : S) = z := (huniq ⟨a, haS⟩ (Subtype.ext ha2)).resolve_left
    (fun he => ha1 (congrArg Subtype.val he))
  have hAcyc : A = zpowers a := by
    apply le_antisymm
    · intro b hb
      rcases huniq ⟨b, hAS hb⟩ (Subtype.ext (elemPow_eq_one_of_isElementaryAbelian b hb)) with he | he
      · have hb1 : b = 1 := congrArg Subtype.val he
        simpa only [hb1] using one_mem (zpowers a)
      · have hba : b = a := congrArg Subtype.val (he.trans haz.symm)
        simpa only [hba] using mem_zpowers a
    · exact zpowers_le.mpr ha
  have hTa (t : PGL2 F) (ht : t ∈ T) : t * a * t⁻¹ = a := by
    have hm : t * a * t⁻¹ ∈ S := (mem_normalizer_iff.mp (hTS ht) a).mp haS
    have hs : (t * a * t⁻¹) ^ 2 = 1 := by
      change (MulAut.conj t a) ^ 2 = 1
      rw [← map_pow, ha2, map_one]
    have hn : t * a * t⁻¹ ≠ 1 := by
      intro he
      apply ha1
      exact (MulAut.conj t).injective (he.trans (map_one _).symm)
    have he := (huniq ⟨t * a * t⁻¹, hm⟩ (Subtype.ext hs)).resolve_left
      (fun he => hn (congrArg Subtype.val he))
    exact congrArg Subtype.val (he.trans haz.symm)
  obtain ⟨V, hV, hVT, hVJ⟩ := exists_inner_four_in_linear_sylow hF T
  have haV : a ∈ V := by
    rw [← pgl2_kleinFour_centralizer_eq_self F hF V hV]
    intro v hv
    exact mul_inv_eq_iff_eq_mul.mp (hTa v (hVT hv))
  have hVC : ¬ V ≤ centralizer (X : Set (PGL2 F)) :=
    pgl2_no_kleinFour_centralizes_odd_cyclic F hF X V inferInstance hXne hXodd hV
  obtain ⟨b, hb, hbC⟩ := Set.not_subset.mp hVC
  have hb1 : b ≠ 1 := by intro he; apply hbC; simp [he]
  have hb2 : b ^ 2 = 1 := by
    have hh := congrArg Subtype.val (hV.mul_self ⟨b, hb⟩)
    change b * b = 1 at hh
    simpa only [pow_two] using hh
  let j : PSL(2,F) →* PGL2 F := Matrix.ProjectiveSpecialLinearGroup.toPGL
  have hj : Function.Injective j := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  obtain ⟨a₀, ha₀⟩ := hVJ haV
  obtain ⟨b₀, hb₀⟩ := hVJ hb
  change j a₀ = a at ha₀
  change j b₀ = b at hb₀
  have hao : orderOf a₀ = 2 := orderOf_eq_prime_iff.mpr ⟨by
      apply hj
      simpa only [map_pow, map_one, ha₀] using ha2,
    fun he => ha1 (ha₀.symm.trans (he ▸ map_one j))⟩
  have hbo : orderOf b₀ = 2 := orderOf_eq_prime_iff.mpr ⟨by
      apply hj
      simpa only [map_pow, map_one, hb₀] using hb2,
    fun he => hb1 (hb₀.symm.trans (he ▸ map_one j))⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp (involutions_isConj a₀ b₀ hao hbo)
  have hgab : MulAut.conj (j g) a = b := by
    have hh := congrArg j hg
    change j g * a * (j g)⁻¹ = b
    simpa only [map_mul, map_inv, ha₀, hb₀] using hh
  have hmap : A.map (MulAut.conj (j g)).toMonoidHom = zpowers b := by
    rw [hAcyc, MonoidHom.map_zpowers]
    exact congrArg zpowers hgab
  refine ⟨g, ?_, ?_⟩
  · rw [hmap]
    exact zpowers_le.mpr (hVT hb)
  · rw [hmap]
    exact fun hh => hbC (hSC (hh (mem_zpowers b)))

end Theory.PSL2
