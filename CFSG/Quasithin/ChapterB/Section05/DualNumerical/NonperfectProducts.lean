module
public import CFSG.Quasithin.ChapterB.Section05.DualNumerical.SymmetricFiveProducts
public import CFSG.Quasithin.ChapterB.Section05.DualNumerical.Products
public import CFSG.Quasithin.ChapterB.Section05.DualNumerical.SmallSupport
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorPermutation
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Descent
public import Theory.Quasithin.Rank
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.SpecificGroups.PSL3.OddDegreeProjectiveComparison
/-!
# The nonperfect product branches of B.5.13

A nonperfect source factor is symmetric-three or the natural symmetric-five
row. The latter is handled by its actual alternating-five natural section.
For a symmetric-three factor, ordinary perfect complements permit restriction
of the full module and strict group-order induction. The remaining complements
are symmetric-three or the exceptional SL₃(2) row. The normal cubic subgroup
then has centralizer of two-rank at most two, so the proved Fitting plane
alternative bounds the original dual action without a splitting assumption.

Source: Aschbacher–Smith B.5.6(3) and B.5.13, printed pp.105 and 110.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.SourceB513
private abbrev Cubic := alternatingGroup (Fin 3)
private instance : DecidablePred (fun x : Equiv.Perm (Fin 3) => x ∈ Cubic) :=
  fun x => inferInstanceAs (Decidable (Equiv.Perm.sign x = 1))
private theorem cubic_card : Nat.card Cubic = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
private theorem centralizes_cubic (x : Equiv.Perm (Fin 3))
    (hx : ∀ y, y ∈ Cubic → y * x = x * y) : x ∈ Cubic := by
  have hh : ∀ x : Equiv.Perm (Fin 3),
      (∀ y, y ∈ Cubic → y * x = x * y) → x ∈ Cubic := by decide +kernel
  exact hh x hx
variable {D B V : Type*} [Group D] [Finite D] [Group B] [Finite B]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem cubic_twoRank : primeRank 2 Cubic = 0 := by
  have hp : IsPGroup 3 Cubic := IsPGroup.of_card (n := 1) (by simpa using cubic_card)
  apply Nat.eq_zero_of_le_zero
  apply (_root_.primeRank_le_iff 2 0).mpr
  intro A hA _
  have hd := hA.disjoint_of_coprime (hp.to_subgroup (⊤ : Subgroup Cubic))
    (by decide : Nat.Coprime 2 3)
  have ha : A = ⊥ := by simpa using hd
  subst A
  simp [Group.rank_eq_zero]

private theorem cubic_centralizer_rank (e : D ≃* ((Equiv.Perm (Fin 3)) × B)) :
    ∃ N : Subgroup D, N ≤ fittingSubgroup D ∧
      primeRank 2 (centralizer (N : Set D)) ≤ primeRank 2 B := by
  let C : Subgroup (Equiv.Perm (Fin 3) × B) := Cubic.prod ⊥
  let N := C.map e.symm.toMonoidHom
  let : N.Normal := (inferInstance : C.Normal).map _ e.symm.surjective
  have hp : IsPGroup 3 C := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_congr (Cubic.prodEquiv (⊥ : Subgroup B)).toEquiv,
      Nat.card_prod,cubic_card]
    simp)
  refine ⟨N,(show N ≤ pCore 3 D from le_sSup ⟨inferInstance,hp.map _⟩).trans
    (pCore_le_fitting D 3),?_⟩
  let f : centralizer (N : Set D) →* Cubic × B := {
    toFun x := (⟨(e x).1,by
      apply centralizes_cubic
      intro y hy
      have hn : e.symm (y,1) ∈ N := mem_map_of_mem _ (show (y,1) ∈ C from ⟨hy,by simp⟩)
      have hh := mem_centralizer_iff.mp x.property (e.symm (y,1)) hn
      have he := congrArg (fun d : D => (e d).1) hh
      simpa only [map_mul,MulEquiv.apply_symm_apply,Prod.fst_mul] using he⟩,(e x).2)
    map_one' := by apply Prod.ext <;> simp
    map_mul' := fun x y => by apply Prod.ext <;> simp }
  have hi : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply e.injective
    exact Prod.ext (congrArg (fun z : Cubic × B => (z.1 : Equiv.Perm (Fin 3))) hxy)
      (congrArg (fun z : Cubic × B => z.2) hxy)
  have hh := Theory.GroupTheory.primeRank_le_of_injective 2 f hi
  rwa [primeRank_prod_eq_add,cubic_twoRank,zero_add] at hh

/-- A symmetric-three factor with a complementary two-rank at most two gives
B.5.13 without any further module splitting. -/
theorem quadraticRatio_le_two_of_symmetricThree_small_product
    (ρ : Representation (ZMod 2) D V) {K : GroupClass}
    (h : SourceInduction.FFHypothesis K ρ.dual)
    (e : D ≃* ((Equiv.Perm (Fin 3)) × B)) (hr : primeRank 2 B ≤ 2) :
    quadraticRatio ρ ≤ 2 := by
  let : Nontrivial D := e.symm.injective.nontrivial
  obtain ⟨N,hN,hrN⟩ := cubic_centralizer_rank e
  exact quadraticRatio_le_two_of_fitting_centralizer_rank ρ h.faithful h.twoCore
    h.isFFModule N hN (hrN.trans hr)

open SourceInduction QuasisimpleSource
/-- The genuine exceptional four-dimensional row has complementary group SL₃(2). -/
theorem quadraticRatio_le_two_of_symmetricThree_exceptional_product
    (ρ : Representation (ZMod 2) D V) {K : GroupClass}
    (h : FFHypothesis K ρ.dual) (c : SourceTwoFactorCase ρ.dual)
    (e : c.first ≃* Equiv.Perm (Fin 3))
    (ex : FourDimensionalSource
      (((fixed ρ.dual).quotientImage c.secondSpace).toRepresentation.comp c.second.subtype)) :
    quadraticRatio ρ ≤ 2 := by
  apply quadraticRatio_le_two_of_symmetricThree_small_product ρ h
    (c.product.equiv.symm.trans (MulEquiv.prodCongr e (MulEquiv.refl c.second)))
  let f : c.second ≃* PSL(3,ZMod 2) := ex.natural.groupEquiv.trans
    (Matrix.PSL3.OddDegreeProjectiveComparison.specialProjectiveEquiv
      (n := 1) BinaryField.two.card_eq (by decide))
  rw [Theory.GroupTheory.primeRank_equiv 2 f,
    Matrix.PSL3Even.two_rank (ZMod 2) (n := 1) (by decide) (by simp)]
private theorem symmetricThree_twoRank_le : primeRank 2 (Equiv.Perm (Fin 3)) ≤ 2 := by
  apply (primeRank_le_iff_elementary_card_le (Equiv.Perm (Fin 3))).mpr
  intro A hA
  let : IsElementaryAbelian 2 A := hA
  have hd := A.card_subgroup_dvd_card
  have hc : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  rw [hc] at hd
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  rw [hn] at hd ⊢
  have hl : 2^n ≤ 6 := Nat.le_of_dvd (by decide) hd
  by_contra! hb
  have hn3 : 3 ≤ n := by
    by_contra! hnlt
    interval_cases n <;> norm_num at hb
  have hh := Nat.pow_le_pow_right (by decide : 0 < 2) hn3
  norm_num at hh
  omega
omit [Finite D] [FiniteDimensional (ZMod 2) V] in
private theorem nonperfect_factor_models {σ : Representation (ZMod 2) D V}
    {A : Subgroup D} {U : Subrepresentation σ} (c : SourceFactorCase σ A U)
    (hp : ¬ Group.IsPerfect A) :
    Nonempty (A ≃* Equiv.Perm (Fin 3)) ∨
      (U.toSubmodule = moved σ A ∧ IsSymmetricNatural
        (((fixed σ).quotientImage U).toRepresentation.comp A.subtype) 5) := by
  have three_perfect (F : BinaryField) (e : A ≃* SL(3,F.Carrier)) : False := by
    let : Group.IsPerfect SL(3,F.Carrier) := Atlas.sl_perfect 3 (by decide)
    exact hp (Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective)
  cases c with
  | natural hm hn =>
    cases hn with
    | linearTwo F hn =>
      obtain ⟨e⟩ := hn
      by_cases hd : F.degree = 1
      · exact Or.inl ⟨e.groupEquiv.trans
          ((ExtensionConsequences.degreeOneNaturalEquiv F hd 2).groupEquiv.trans
            ((BinaryLinear.OuterCyclic.slEquivLinear 2).trans
              BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree))⟩
      · have hl : 3 < Nat.card F.Carrier := by
          rw [F.card_eq]
          have hd' : 2 ≤ F.degree := by have := F.degree_pos; omega
          have hh := Nat.pow_le_pow_right (by decide : 0 < 2) hd'
          norm_num at hh
          omega
        let : Group.IsPerfect SL(2,F.Carrier) :=
          GorensteinWalter.sl2_isPerfect_of_card_gt_three F.Carrier hl
        exact False.elim (hp (Group.IsPerfect.ofSurjective
          (f := e.groupEquiv.symm.toMonoidHom) e.groupEquiv.symm.surjective))
    | symmetricFive hn => exact Or.inr ⟨hm,hn⟩
    | linearThree F _ hn => obtain ⟨e⟩ := hn; exact (three_perfect F e.groupEquiv).elim
  | doubleNatural F _ _ hn => obtain ⟨e⟩ := hn; exact (three_perfect F e.groupEquiv).elim
  | exceptional _ ex => exact (three_perfect BinaryField.two ex.natural.groupEquiv).elim
private theorem symmetricThree_product_dispatch
    (ρ : Representation (ZMod 2) D V) {K : GroupClass}
    (h : FFHypothesis K ρ.dual) (c : SourceTwoFactorCase ρ.dual)
    (ih : ∀ (A : Subgroup D) [Nontrivial A], Nat.card A < Nat.card D →
      FFHypothesis K (Representation.dual (ρ.comp A.subtype)) →
        quadraticRatio (ρ.comp A.subtype) ≤ 2)
    (e : c.first ≃* Equiv.Perm (Fin 3)) : quadraticRatio ρ ≤ 2 := by
  let : Nontrivial c.second := c.secondCase.nontrivial
  by_cases hp : Group.IsPerfect c.second
  · let := hp
    cases hc : c.secondCase with
    | natural hm hn => exact ordinary_perfect_product_bound ρ h c hm (ih c.second)
    | doubleNatural F ho hm hn => exact ordinary_perfect_product_bound ρ h c hm (ih c.second)
    | exceptional hm ex => exact quadraticRatio_le_two_of_symmetricThree_exceptional_product ρ h c e ex
  · rcases nonperfect_factor_models c.secondCase hp with he | ⟨hm,hn⟩
    · obtain ⟨f⟩ := he
      apply quadraticRatio_le_two_of_symmetricThree_small_product ρ h
        (c.product.equiv.symm.trans (MulEquiv.prodCongr e (MulEquiv.refl c.second)))
      rw [Theory.GroupTheory.primeRank_equiv 2 f]
      exact symmetricThree_twoRank_le
    · exact quadraticRatio_le_two_of_dual_symmetricFive_section ρ c.second c.secondSpace hm.ge hn
/-- Every nonperfect two-factor source branch reduces the original numerical
bound to the genuine smaller-group induction hypothesis. -/
theorem quadraticRatio_le_two_of_nonperfect_twoFactors_source
    (ρ : Representation (ZMod 2) D V) {K : GroupClass}
    (h : FFHypothesis K ρ.dual) (c : SourceTwoFactorCase ρ.dual)
    (ih : ∀ (A : Subgroup D) [Nontrivial A], Nat.card A < Nat.card D →
      FFHypothesis K (Representation.dual (ρ.comp A.subtype)) →
        quadraticRatio (ρ.comp A.subtype) ≤ 2)
    (hnp : ¬ Group.IsPerfect c.first ∨ ¬ Group.IsPerfect c.second) : quadraticRatio ρ ≤ 2 := by
  have first_case (d : SourceTwoFactorCase ρ.dual) (hp : ¬ Group.IsPerfect d.first) :
      quadraticRatio ρ ≤ 2 := by
    rcases nonperfect_factor_models d.firstCase hp with he | ⟨hm,hn⟩
    · obtain ⟨e⟩ := he
      exact symmetricThree_product_dispatch ρ h d ih e
    · exact quadraticRatio_le_two_of_dual_symmetricFive_section ρ d.first d.firstSpace hm.ge hn
  rcases hnp with hp | hp
  · exact first_case c hp
  · let d : SourceTwoFactorCase ρ.dual := {
      first := c.second
      second := c.first
      product := c.product.swap
      firstSpace := c.secondSpace
      secondSpace := c.firstSpace
      decomposition := c.decomposition.symm
      firstCase := c.secondCase
      secondCase := c.firstCase }
    exact first_case d hp
end CFSG.Quasithin.ChapterB.SourceB513
