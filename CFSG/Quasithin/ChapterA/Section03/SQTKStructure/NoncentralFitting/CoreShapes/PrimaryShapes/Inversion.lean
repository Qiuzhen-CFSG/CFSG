module

public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.CoreShapes.PrimaryShapes.Seeds
public import Theory.SpecificGroups.GL2.ProjectiveFourGroupObstruction
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Mathlib.GroupTheory.FixedPointFree

/-!
# Inversion of primary cores with an elementary supercritical seed

The elementary seed has trivial Frattini subgroup, so its actual action kernel
is F(L), and the seed is central in O_p(L). The given SL₂ Fitting quotient
makes L even; Cauchy's theorem supplies an involution outside the odd Fitting
subgroup. Perfectness forces determinant one on the seed's two-dimensional
prime-field vector space, so this nontrivial involution acts by inversion.

The fixed subgroup in O_p(L) commutes with the seed and meets it trivially.
Additivity of prime rank and the SQTK bound force that fixed subgroup to be
trivial. The fixed-point-free involution theorem then inverts the entire core,
which is therefore abelian. No equality between the core prime and quotient
prime, irreducibility, or bound on the core exponent is required.

The final theorem supplies precisely the `habelian` premise of
`primary_shapes_of_elementary_steps`. Its seed/kernel construction and the
remaining homocyclic recognition belong to the parent assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of A.3.6,
printed pp.44–45 (the elementary case and its repetition for SL₂(5)).
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterA.Section03.NoncentralFitting.CoreShapes.PrimaryShapes

private theorem plane_inversion {p : ℕ} [Fact p.Prime]
    {A E : Type*} [Group A] [Group.IsPerfect A] [Group E] [Finite E]
    [IsElementaryAbelian p E] (hp : Odd p) (hc : Nat.card E = p ^ 2)
    (a : A →* MulAut E) (t : A) (ht : t ^ 2 = 1) (hne : a t ≠ 1) :
    ∀ x : E, a t x = x⁻¹ := by
  classical
  have hdim : Module.finrank (ZMod p) (Additive E) = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive E)
    change Nat.card E = _ at h
    rw [Nat.card_zmod, hc] at h
    exact (Nat.pow_right_injective (Fact.out : p.Prime).one_lt h).symm
  let b := Module.finBasisOfFinrankEq (ZMod p) (Additive E) hdim
  let al : MulAut E →* (Additive E ≃ₗ[ZMod p] Additive E) :=
    { toFun := fun a => { a.toAdditive with map_smul' := ZMod.map_smul a.toAdditive }
      map_one' := by ext; rfl
      map_mul' := by intros; ext; rfl }
  let e := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Additive E)).symm.trans
    (Matrix.GeneralLinearGroup.toLin' b).symm
  let f := e.toMonoidHom.comp (al.comp a)
  have hsq : f t ^ 2 = 1 := by rw [← map_pow, ht, map_one]
  have hd : (f t).det = 1 :=
    Abelianization.commutator_subset_ker (Matrix.GeneralLinearGroup.det.comp f)
      Group.IsPerfect.mem_commutator
  have hp2 : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hh := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have : p = 2 := (Nat.dvd_prime Nat.prime_two).mp hh |>.resolve_left (Fact.out : p.Prime).ne_one
    exact hp.not_two_dvd_nat (by omega)
  have hn : f t = -1 := by
    rcases Matrix.GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one hp2 (f t) hsq hd with h | h
    · exfalso
      apply hne
      have hh : al (a t) = 1 := e.injective (h.trans e.map_one.symm)
      ext x
      exact congrArg (fun q : Additive E ≃ₗ[ZMod p] Additive E => q (Additive.ofMul x)) hh
    · exact h
  intro x
  have h := congrArg (fun M : Matrix.GeneralLinearGroup (Fin 2) (ZMod p) =>
    (Matrix.GeneralLinearGroup.toLin' b M).toLinearEquiv (Additive.ofMul x)) hn
  simp only [f, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    e, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at h
  rw [Matrix.GeneralLinearGroup.toLin'_apply] at h
  change Additive.ofMul (a t x) = _ at h
  simp only [Units.val_neg, Units.val_one, Matrix.neg_mulVec, Matrix.one_mulVec,
    map_neg, Fintype.linearCombination_apply, b.sum_repr] at h
  exact congrArg Additive.toMul h

variable {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]

omit [Finite A] in
private theorem elementary_seed (s : PrimarySeed p A)
    (e : s.X ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))) :
    IsElementaryAbelian p s.X := by
  let : IsMulCommutative s.X := IsMulCommutative.of_comm (fun x y =>
    e.injective (by simp only [map_mul, mul_comm]))
  refine { exponent_dvd_p := ?_ }
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr s.supercritical.pow_eq_one

/-- The elementary seed identifies the kernel of its actual action, before taking a quotient. -/
theorem elementary_action_eq_one_iff (s : PrimarySeed p A)
    (e : s.X ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))) (g : A) :
    coreAction s.X g = 1 ↔ g ∈ fittingSubgroup A := by
  let : IsElementaryAbelian p s.X := elementary_seed s e
  let : Fact (IsPGroup p s.X) := ⟨pCore_isPGroup.to_subgroup s.X⟩
  have hphi : frattini s.X = ⊥ := frattini_eq_bot_of_isElementaryAbelian (p := p)
  constructor
  · intro h
    rw [← s.kernel_eq]
    change quotientAut (frattini s.X) (coreAction s.X g) = 1
    rw [h, map_one]
  · intro h
    apply MulEquiv.ext
    intro x
    have hx := DFunLike.congr_fun (s.frattini_fixed g h) (QuotientGroup.mk' (frattini s.X) x)
    rw [quotientAut_apply_mk, MulAut.one_apply] at hx
    have hm := QuotientGroup.eq.mp hx
    rw [hphi, mem_bot] at hm
    exact inv_mul_eq_one.mp hm

/-- The full primary core centralizes its elementary supercritical seed. -/
theorem elementary_seed_le_center (s : PrimarySeed p A)
    (e : s.X ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))) :
    s.X ≤ center (pCore p A) := by
  intro x hx
  apply mem_center_iff.mpr
  intro g
  have he := (elementary_action_eq_one_iff s e (g : A)).mpr
    (pCore_le_fitting A p g.property)
  have hh := congrArg (fun a : MulAut s.X => ((a ⟨x, hx⟩ : pCore p A) : A)) he
  change (g : A) * (x : A) * (g : A)⁻¹ = (x : A) at hh
  apply Subtype.ext
  exact mul_inv_eq_iff_eq_mul.mp hh

/-- Every involution outside F(A) inverts the elementary seed under its literal conjugation action. -/
theorem elementary_seed_inverted [Group.IsPerfect A] (s : PrimarySeed p A)
    (hc : Nat.card s.X = p ^ 2)
    (e : s.X ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p)))
    (t : A) (ht : t ^ 2 = 1) (hnt : t ∉ fittingSubgroup A) :
    ∀ x : s.X, coreAction s.X t x = x⁻¹ := by
  let : IsElementaryAbelian p s.X := elementary_seed s e
  exact plane_inversion s.odd hc (coreAction s.X) t ht
    (fun h => hnt ((elementary_action_eq_one_iff s e t).mp h))

/-- The rank-two seed leaves no room for a nontrivial fixed subgroup in the primary core. -/
theorem elementary_core_fixedPointFree (s : PrimarySeed p A)
    (e : s.X ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p)))
    (hr : primeRank p A ≤ 2) (t : A)
    (hinv : ∀ x : s.X, coreAction s.X t x = x⁻¹) :
    MonoidHom.FixedPointFree (MulAut.conjNormal t : MulAut (pCore p A)) := by
  let S := pCore p A
  let a : MulAut S := MulAut.conjNormal t
  let C := a.fixedSubgroup
  have hd : Disjoint s.X C := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    have hi := congrArg (fun y : s.X => (y : S)) (hinv ⟨x, hx.1⟩)
    change a x = x⁻¹ at hi
    have hf : a x = x := (MulAut.mem_fixedSubgroup a x).mp hx.2
    have hx2 : x ^ 2 = 1 := by
      calc
        x ^ 2 = a x * x := by rw [pow_two, hf]
        _ = 1 := by rw [hi, inv_mul_cancel]
    have hxp : x ^ p = 1 := congrArg Subtype.val (s.supercritical.pow_eq_one ⟨x, hx.1⟩)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (Nat.coprime_two_right.mpr s.odd) (orderOf_dvd_of_pow_eq_one hxp)
      (orderOf_dvd_of_pow_eq_one hx2))
  have hc : s.X ≤ centralizer (C : Set S) := by
    intro x hx c _
    exact mem_center_iff.mp (elementary_seed_le_center s e hx) c
  have hb : primeRank p (s.X ⊔ C : Subgroup S) ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective p (s.X ⊔ C).subtype (s.X ⊔ C).subtype_injective).trans
      ((Theory.GroupTheory.primeRank_le_of_injective p S.subtype S.subtype_injective).trans hr)
  rw [s.X.primeRank_sup_eq_add_of_disjoint_commuting C hd hc p, s.rank_two] at hb
  have hz : primeRank p C = 0 := by
    exact Nat.eq_zero_of_le_zero (Nat.le_of_add_le_add_left hb)
  have hs : Subsingleton C := by
    by_contra hn
    let : Nontrivial C := not_subsingleton_iff_nontrivial.mp hn
    obtain ⟨k, hk, hkcard⟩ := (pCore_isPGroup.to_subgroup C).nontrivial_iff_card.mp
      (inferInstance : Nontrivial C)
    exact (PrimeRank.eq_zero_iff_not_dvd_card.mp hz)
      (hkcard ▸ dvd_pow_self p (Nat.ne_of_gt hk))
  intro x hx
  exact congrArg Subtype.val
    (hs.elim (⟨x, (MulAut.mem_fixedSubgroup a x).mpr hx⟩ : C) 1)

omit [Finite A] [Fact p.Prime] in
private theorem core_action_involutive (t : A) (ht : t ^ 2 = 1) :
    Function.Involutive (MulAut.conjNormal t : MulAut (pCore p A)) := by
  intro x
  have h : (MulAut.conjNormal t : MulAut (pCore p A)) ^ 2 = 1 := by
    rw [← map_pow, ht, map_one]
  exact congrArg (fun f : MulAut (pCore p A) => f x) h

/-- A nontrivial involution action on the elementary seed inverts the entire primary core. -/
theorem elementary_core_inverted [Group.IsPerfect A] (s : PrimarySeed p A)
    (hc : Nat.card s.X = p ^ 2)
    (e : s.X ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p)))
    (hr : primeRank p A ≤ 2) (t : A) (ht : t ^ 2 = 1) (hnt : t ∉ fittingSubgroup A) :
    ∀ x : pCore p A, (MulAut.conjNormal t : MulAut (pCore p A)) x = x⁻¹ := by
  have hf := elementary_core_fixedPointFree s e hr t
    (elementary_seed_inverted s hc e t ht hnt)
  exact congrFun (hf.coe_eq_inv_of_involutive (core_action_involutive t ht))

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}

/-- An actual involution of the component lies outside its odd Fitting subgroup. -/
theorem exists_involution_outside_fitting (hO : pCore 2 G = ⊥)
    (hL : L.IsCComponent) (hquot : PrimeSL2FittingQuotient L) :
    ∃ t : L, orderOf t = 2 ∧ t ∉ fittingSubgroup L := by
  obtain ⟨u, _, hu⟩ := exists_radical_quotient_involution hquot
  have hd : 2 ∣ Nat.card L :=
    (hu ▸ orderOf_dvd_natCard (QuotientGroup.mk' (fittingSubgroup L) u)).trans
      (card_quotient_dvd_card (fittingSubgroup L))
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 hd
  refine ⟨t, ht, ?_⟩
  intro hm
  have ho : orderOf (⟨t, hm⟩ : fittingSubgroup L) = 2 := (Subgroup.orderOf_mk t hm).trans ht
  exact (fitting_odd_card hL hO).not_two_dvd_nat
    (ho ▸ orderOf_dvd_natCard (⟨t, hm⟩ : fittingSubgroup L))

/-- The elementary branch supplies abelianness of the full primary core, with no restriction on its exponent. -/
theorem elementary_core_abelian
    {𝒦 : GroupClass} (hG : IsSQTK 𝒦 G) (hO : pCore 2 G = ⊥)
    (hL : L.IsCComponent) (hquot : PrimeSL2FittingQuotient L)
    (s : PrimarySeed p L) (hc : Nat.card s.X = p ^ 2)
    (he : Nonempty (s.X ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p)))) :
    IsMulCommutative (pCore p L) := by
  let : Group.IsPerfect L := hL.perfect
  obtain ⟨e⟩ := he
  obtain ⟨t, ht, hnt⟩ := exists_involution_outside_fitting hO hL hquot
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have hi := elementary_core_inverted s hc e
    ((hG.subgroup L).stronglyQuasithin p Fact.out s.odd) t ht2 hnt
  apply IsMulCommutative.of_comm
  intro x y
  have h := map_mul (MulAut.conjNormal t : MulAut (pCore p L)) x y
  rw [hi (x * y), hi x, hi y] at h
  simpa only [inv_inv, mul_inv_rev] using congrArg Inv.inv h

end CFSG.Quasithin.ChapterA.Section03.NoncentralFitting.CoreShapes.PrimaryShapes
