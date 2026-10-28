module

public import Theory.SpecificGroups.PSL2.ElevenConjugateBudget.Models
public import Theory.SpecificGroups.PSL2.PrimeCardInnerIndex
public import Theory.SpecificGroups.PSL2.InvolutionFusion
public import GorensteinWalter.PGL2DeterminantSquare
public import GorensteinWalter.PGL2CanonicalOuterInvolutionFusion
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.ElementaryAbelian.Join

/-!
# The four elementary actors and their actual projective actions

The faithful, surjective PGL₂(11) action identifies the full automorphism
group of the central quotient PSL₂(11). The diagonal matrix diag(-1,1)
induces exactly the published d; its nonsquare determinant makes it outer.
The published inner and mixed pairs generate Klein four-groups.

The inner group has order 660 and its four-groups are Sylow. The full
automorphism group has dihedral Sylow groups of order eight, meeting the
inner group in noncyclic subgroups. Inner and outer involution fusion and
inner Sylow conjugacy give three branches of the actor catalogue.

These facts are used for the finite-generation alternative to
Guralnick–Malle, Classification of 2F-modules I, Proposition 4.1, pp.8–9,
and Aschbacher–Smith K.2, printed p.453. The normal-Sylow intersection
transport follows GorensteinWalter.PGL2CanonicalOuterInvolutionFusion.
-/

public section
open Matrix Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2.ElevenConjugateBudget.Coverage
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

private theorem field_odd : IsOddPrimePower (Nat.card F) :=
  ⟨11, 1, by decide, by decide, by decide, by simp⟩
private theorem field_large : 3 < Nat.card F := by simp

private noncomputable def pglEquiv : PGL2 F ≃* MulAut S :=
  MulEquiv.ofBijective (pgl2InnerAutPSL2 F field_odd field_large)
    ⟨pgl2InnerAutPSL2_injective F field_odd field_large,
      primeField_pgl_coverage (by decide) (by decide)⟩

private def diagGL : GL (Fin 2) F := GeneralLinearGroup.mkOfDetNeZero !![-1,0;0,1] (by decide)

private theorem diagGL_inv : diagGL⁻¹ = diagGL := by
  apply inv_eq_of_mul_eq_one_left
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> decide

private theorem pgl_diag : pglEquiv (ProjGenLinGroup.mk diagGL) = d := by
  ext x
  obtain ⟨A, rfl⟩ := quotientMap_surjective F x
  apply ProjectiveSpecialLinearGroup.toPGL_injective
  change ProjectiveSpecialLinearGroup.toPGL
    (pgl2InnerAutPSL2 F field_odd field_large (ProjGenLinGroup.mk diagGL)
      (quotientMap F A)) = _
  rw [toPGL_pgl2InnerAutPSL2_apply, d, OuterSolvable.diagonalAutHom_apply_quotientMap]
  change ProjGenLinGroup.mk diagGL * ProjGenLinGroup.mk (SpecialLinearGroup.toGL A) *
    (ProjGenLinGroup.mk diagGL)⁻¹ =
    ProjGenLinGroup.mk (SpecialLinearGroup.toGL (OuterSolvable.slDiagonal (-1 : Fˣ) A))
  rw [← map_inv, ← map_mul, ← map_mul, diagGL_inv]
  congr 1
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [diagGL, OuterSolvable.slDiagonal_apply, vecMul, dotProduct,
      mul_apply, Fin.sum_univ_two, SpecialLinearGroup.toGL]



private theorem conj_injective : Function.Injective (MulAut.conj : S →* MulAut S) :=
  Theory.GroupTheory.conj_injective_of_center_eq_bot (psl2_center_eq_bot F)

abbrev inner : Subgroup (MulAut S) := (MulAut.conj : S →* MulAut S).range

theorem inner_index : inner.index = 2 :=
  prime_card_inner_index F (p := 11) (by decide) (by decide) (by simp)

private theorem pgl_to_inner (x : S) :
    pglEquiv (ProjectiveSpecialLinearGroup.toPGL x) = MulAut.conj x :=
  pgl2InnerAutPSL2_toPGL F field_odd field_large x

theorem d_not_inner : d ∉ inner := by
  rintro ⟨x, hx⟩
  have he : ProjectiveSpecialLinearGroup.toPGL x = ProjGenLinGroup.mk diagGL :=
    pglEquiv.injective ((pgl_to_inner x).trans (hx.trans pgl_diag.symm))
  have hs := (pgl2_mk_mem_psl2_range_iff_det_isSquare diagGL).mp ⟨x, he⟩
  have hn : ¬ IsSquare (-1 : F) := by decide
  apply hn
  convert hs using 1
  decide

private theorem s_ne_one : s ≠ 1 := by
  intro hs
  have h := (OuterSolvable.OddCoverage.quotientMap_eq_iff slS 1).mp (by simpa [s] using hs)
  rcases h with h | h <;> revert h <;> decide

private theorem s_ne_t : s ≠ t := by
  intro hs
  have h := (OuterSolvable.OddCoverage.quotientMap_eq_iff slS slT).mp hs
  rcases h with h | h <;> revert h <;> decide

private theorem klein_sup {G : Type*} [_root_.Group G]
    (a b : G) (ha : IsInvolution a) (hb : IsInvolution b)
    (habne : a ≠ b) (hab : Commute a b) :
    IsKleinFour (zpowers a ⊔ zpowers b : Subgroup G) := by
  classical
  have haord : orderOf a = 2 := orderOf_eq_prime ha.2 ha.1
  have hbOut : b ∉ zpowers a := by
    intro h
    have hf := isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, ha.2⟩
    rw [hf.mem_zpowers_iff_mem_range_orderOf, haord] at h
    have hh : b = 1 ∨ b = a := by
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
      have hil := Finset.mem_range.mp hi
      have hi' : i = 0 ∨ i = 1 := by omega
      rcases hi' with rfl | rfl
      · exact Or.inl (by simpa using he.symm)
      · exact Or.inr (by simpa using he.symm)
    exact hh.elim hb.1 (fun h => habne h.symm)
  have hbC : b ∈ centralizer (zpowers a : Set G) := by
    rw [mem_centralizer_iff]
    rintro x ⟨n, rfl⟩
    exact (hab.zpow_left n).eq
  let : IsElementaryAbelian 2 (zpowers a) := .zpowers_of_pow_eq_one ha.2
  let : IsElementaryAbelian 2 (zpowers b) := .zpowers_of_pow_eq_one hb.2
  let : IsElementaryAbelian 2 (zpowers a ⊔ zpowers b : Subgroup G) :=
    .sup_of_le_centralizer (zpowers_le.mpr hbC)
  refine ⟨?_, Nat.dvd_antisymm (IsElementaryAbelian.exponent_dvd_p 2 _) ?_⟩
  · rw [card_sup_zpowers_of_normalizing_involution _ _ hb.2 hbOut
      (Subgroup.centralizer_le_normalizer _ hbC), Nat.card_zpowers, haord]
  · let aV : (zpowers a ⊔ zpowers b : Subgroup G) := ⟨a, (le_sup_left : zpowers a ≤ zpowers a ⊔ zpowers b) (mem_zpowers a)⟩
    have ho : orderOf aV = 2 := (Subgroup.orderOf_coe aV).symm.trans haord
    simpa only [ho] using Monoid.order_dvd_exponent aV

theorem innerFour_klein : IsKleinFour innerFour := by
  apply klein_sup (MulAut.conj t) (MulAut.conj s)
  · exact ⟨fun h => t_ne_one (conj_injective (h.trans (map_one _).symm)),
      by rw [← map_pow, t_sq, map_one]⟩
  · exact ⟨fun h => s_ne_one (conj_injective (h.trans (map_one _).symm)),
      by rw [← map_pow, s_sq, map_one]⟩
  · exact fun h => s_ne_t (conj_injective h).symm
  · exact t_s_commute.map (MulAut.conj : S →* MulAut S)

theorem innerFour_le_inner : innerFour ≤ inner :=
  sup_le (zpowers_le.mpr ⟨t, rfl⟩) (zpowers_le.mpr ⟨s, rfl⟩)

theorem outerFour_klein : IsKleinFour outerFour := by
  apply klein_sup (MulAut.conj t) d
  · exact ⟨fun h => t_ne_one (conj_injective (h.trans (map_one _).symm)),
      by rw [← map_pow, t_sq, map_one]⟩
  · exact ⟨d_ne_one, by simpa only [pow_two] using d_sq⟩
  · intro h
    exact d_not_inner (h ▸ (show MulAut.conj t ∈ inner from ⟨t, rfl⟩))
  · ext x
    change t * d x * t⁻¹ = d (t * x * t⁻¹)
    simp [d_t]

theorem outerFour_not_le_inner : ¬ outerFour ≤ inner :=
  fun h => d_not_inner (h ((le_sup_right : zpowers d ≤ outerFour) (mem_zpowers d)))

private theorem inner_card : Nat.card inner = 660 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective conj_injective).toEquiv,
    psl2_card_formula F field_odd]
  simp


private noncomputable def innerEquiv : S ≃* inner := MonoidHom.ofInjective conj_injective

private theorem aut_card : Nat.card (MulAut S) = 1320 := by
  rw [← Nat.card_congr pglEquiv.toEquiv, pgl2_card_formula F]
  simp

theorem sylow_dihedral_eight (P : Sylow 2 (MulAut S)) :
    Nonempty (P ≃* DihedralGroup 4) := by
  let Q := P.mapSurjective (f := pglEquiv.symm.toMonoidHom) pglEquiv.symm.surjective
  let eP : P ≃* Q :=
    (Subgroup.equivMapOfInjective (P : Subgroup (MulAut S))
      pglEquiv.symm.toMonoidHom pglEquiv.symm.injective).trans
      (MulEquiv.subgroupCongr (Sylow.coe_mapSurjective pglEquiv.symm.surjective P).symm)
  obtain ⟨m, _, ⟨eQ⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model F field_odd Q
  have hcard : Nat.card P = 8 := by
    rw [P.card_eq_multiplicity, aut_card,
      show (1320 : ℕ).factorization 2 = 3 by
        rw [show 1320 = 2 ^ 3 * 165 by decide,
          Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
        simp [Nat.prime_two.factorization_self,
          Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 165)]]
    norm_num
  have hc := Nat.card_congr (eP.trans eQ).toEquiv
  rw [hcard, DihedralGroup.nat_card] at hc
  have hm : 2 ^ m = 4 := by omega
  exact ⟨hm ▸ eP.trans eQ⟩

theorem inner_sylow_noncyclic (P : Sylow 2 (MulAut S)) :
    ¬ IsCyclic (inner.subgroupOf (P : Subgroup (MulAut S))) := by
  let : inner.Normal := inner.normal_of_index_eq_two inner_index
  let H := inner.subgroupOf (P : Subgroup (MulAut S))
  let T : Sylow 2 inner := BenderSuzuki.External.hallSylowSubgroupOfNormal P inner
  let eHT : H ≃* T :=
    { toFun := fun x =>
        ⟨⟨((x : P) : MulAut S), x.property⟩, by
          rw [BenderSuzuki.External.hallSylowSubgroupOfNormal_coe]
          exact (x : P).property⟩
      invFun := fun y =>
        ⟨⟨((y : inner) : MulAut S), by
            let yJ : inner := y
            have hy : yJ ∈ (T : Subgroup inner) := y.property
            rw [BenderSuzuki.External.hallSylowSubgroupOfNormal_coe] at hy
            exact hy⟩, (y : inner).property⟩
      left_inv := by intro x; rfl
      right_inv := by intro y; rfl
      map_mul' := by intro x y; rfl }
  let Tmodel := T.mapSurjective (f := innerEquiv.symm.toMonoidHom) innerEquiv.symm.surjective
  let eT : T ≃* Tmodel :=
    (Subgroup.equivMapOfInjective (T : Subgroup inner)
      innerEquiv.symm.toMonoidHom innerEquiv.symm.injective).trans
      (MulEquiv.subgroupCongr (Sylow.coe_mapSurjective innerEquiv.symm.surjective T).symm)
  obtain ⟨m, hm, ⟨eD⟩⟩ := psl2_odd_hasDihedralSylowTwo_model F field_odd Tmodel
  intro hcyc
  have hDcyc : IsCyclic (DihedralGroup (2 ^ m)) :=
    ((eHT.trans eT).trans eD).isCyclic.mp hcyc
  exact DihedralGroup.not_isCyclic
    (ne_of_gt (Nat.one_lt_pow (by omega : m ≠ 0) (by decide : 1 < 2))) hDcyc


private theorem pgl_mem_inner_iff (g : PGL2 F) : pglEquiv g ∈ inner ↔
    g ∈ (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, pglEquiv.injective ((pgl_to_inner x).trans hx)⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, (pgl_to_inner x).symm⟩

theorem involution_classes (x : MulAut S) (hx : IsInvolution x) :
    IsConj (MulAut.conj t) x ∨ IsConj d x := by
  by_cases hxi : x ∈ inner
  · left
    obtain ⟨z, rfl⟩ := hxi
    have hz : IsInvolution z := ⟨fun h => hx.1 (by simp [h]),
      conj_injective (by simpa only [map_pow, map_one] using hx.2)⟩
    exact (MulAut.conj : S →* MulAut S).map_isConj
      (involutions_isConj t z (orderOf_eq_prime t_sq t_ne_one)
        (orderOf_eq_prime hz.2 hz.1))
  · right
    have liftI (a : MulAut S) (ha : IsInvolution a) : IsInvolution (pglEquiv.symm a) := by
      constructor
      · intro h
        apply ha.1
        have hh := congrArg pglEquiv h
        simpa using hh
      · simpa only [map_pow, map_one] using congrArg pglEquiv.symm ha.2
    have outside (a : MulAut S) (ha : a ∉ inner) : pglEquiv.symm a ∉
        (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
      intro h
      apply ha
      simpa only [pglEquiv.apply_symm_apply] using (pgl_mem_inner_iff _).mpr h
    have hh := pgl2_outer_involutions_conjugate_of_odd_prime_power F field_odd
      (liftI d ⟨d_ne_one, by simpa only [pow_two] using d_sq⟩) (liftI x hx)
      (outside d d_not_inner) (outside x hxi)
    simpa only [MulEquiv.coe_toMonoidHom, pglEquiv.apply_symm_apply] using
      pglEquiv.toMonoidHom.map_isConj hh

theorem inner_four_conjugate (A : Subgroup (MulAut S))
    (hAi : A ≤ inner) (hAcard : Nat.card A = 4) :
    ∃ a : MulAut S, A = innerFour.map (MulAut.congr a).toMonoidHom := by
  have card_restrict (B : Subgroup (MulAut S)) (hB : B ≤ inner)
      (hc : Nat.card B = 4) : Nat.card (B.subgroupOf inner) =
        2 ^ (Nat.card inner).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv, hc, inner_card,
      show (660 : ℕ).factorization 2 = 2 by
        rw [show 660 = 2 ^ 2 * 165 by decide,
          Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
        simp [Nat.prime_two.factorization_self,
          Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 165)]]
    norm_num
  let P : Sylow 2 inner := Sylow.ofCard (A.subgroupOf inner) (card_restrict A hAi hAcard)
  let Q : Sylow 2 inner := Sylow.ofCard (innerFour.subgroupOf inner)
    (card_restrict innerFour innerFour_le_inner innerFour_klein.card_four)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq inner Q P
  have hm := congrArg (fun R : Sylow 2 inner => (R : Subgroup inner)) hg
  change (innerFour.subgroupOf inner).map (MulAut.conj g).toMonoidHom =
    A.subgroupOf inner at hm
  refine ⟨(g : MulAut S), ?_⟩
  calc
    A = (A.subgroupOf inner).map inner.subtype := (map_subgroupOf_eq_of_le hAi).symm
    _ = ((innerFour.subgroupOf inner).map (MulAut.conj g).toMonoidHom).map inner.subtype :=
      congrArg (Subgroup.map inner.subtype) hm.symm
    _ = ((innerFour.subgroupOf inner).map inner.subtype).map
        (MulAut.congr (g : MulAut S)).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    _ = innerFour.map (MulAut.congr (g : MulAut S)).toMonoidHom := by
      rw [map_subgroupOf_eq_of_le innerFour_le_inner]

end Theory.PSL2.ElevenConjugateBudget.Coverage
