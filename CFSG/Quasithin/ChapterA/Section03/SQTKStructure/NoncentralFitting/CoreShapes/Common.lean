module

public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.QuotientConsequences
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.FittingActions
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Common clauses for the noncentral Fitting classification

For the actual prime-field quotient L/F(L) ≃ SL₂(r), the solvable radical
is the preimage of the center and F(L) has relative index two. Given the
natural or nilpotent core alternative, the source's central involution
inverts F(L)/Φ(F(L)). Its commutators generate this quotient; Frattini
nongeneration proves R′ = F(L). Cover rigidity then identifies this with
[F(L),L], supplying every common clause in A.3.6.

The same rigidity removes inactive central prime factors: every prime
in the order of F(L) has a noncentral prime core. A separate support lemma
identifies F(L) with Oₚ(L) when its only prime divisor is p.

`conclusion_of_alternatives` applies the existing omega-action strengthening
with every common clause discharged. The core alternatives remain explicit:
this is a conditional reduction, not the completed noncentral classification.
No center–Frattini equality or restriction on homocyclic exponents is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
A.3.6, printed pp.43–45, especially (*) and the common assertions.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterA.Section03.NoncentralFitting.CoreShapes

variable {A : Type*} [Group A] [Finite A]

private theorem radical_eq_comap_center (N : Subgroup A) [N.Normal]
    [Group.IsSolvable N] [IsQuasisimple (A ⧸ N)] :
    solvableRadical A = (center (A ⧸ N)).comap (QuotientGroup.mk' N) := by
  let : Group.IsSolvable (center (A ⧸ N)) :=
    Group.isSolvable_of_comm (fun a b => Subtype.ext (mem_center_iff.mp b.property a))
  have hc : solvableRadical (A ⧸ N) = center (A ⧸ N) :=
    le_antisymm IsQuasisimple.solvableRadical_le_center
      (le_solvableRadical _ inferInstance inferInstance)
  have hk : Group.IsSolvable (QuotientGroup.mk' N).ker := by
    rw [QuotientGroup.ker_mk']; infer_instance
  let := hk
  rw [← comap_solvableRadical_eq_of_solvable_ker (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N), hc]

private theorem fitting_le_radical : fittingSubgroup A ≤ solvableRadical A :=
  le_solvableRadical _ inferInstance inferInstance

private theorem radical_derived_le_fitting (h : PrimeSL2FittingQuotient A) :
    ⁅solvableRadical A, solvableRadical A⁆ ≤ fittingSubgroup A := by
  obtain ⟨r, hr, hr3, ⟨e⟩⟩ := h
  let : Fact r.Prime := ⟨hr⟩
  let : IsQuasisimple (A ⧸ fittingSubgroup A) :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv
      (by simpa using hr3) e
  apply commutator_le.mpr
  intro x hx y hy
  rw [radical_eq_comap_center (fittingSubgroup A)] at hx hy
  apply (QuotientGroup.eq_one_iff _).mp
  change (QuotientGroup.mk' (fittingSubgroup A)) ⁅x,y⁆ = 1
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact (mem_center_iff.mp hx _).symm

private theorem odd_frattini_inversion_generates
    (N R : Subgroup A) [N.Normal] (hNR : N ≤ R)
    (hodd : Odd (Nat.card N)) (t : A) (ht : t ∈ R)
    (hinv : ∀ x : N, QuotientGroup.mk' (frattini N) (MulAut.conjNormal t x) =
      (QuotientGroup.mk' (frattini N) x)⁻¹) : N ≤ ⁅R,R⁆ := by
  let D := (⁅R,R⁆).subgroupOf N
  let q := QuotientGroup.mk' (frattini N)
  have hmap : D.map q = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (frattini N) y
    obtain ⟨x, hx⟩ := hodd.coprime_two_right.pow_left_bijective.surjective a⁻¹
    change x ^ 2 = a⁻¹ at hx
    let c : N := MulAut.conjNormal t x * x⁻¹
    have hc : c ∈ D := by
      change t * (x : A) * t⁻¹ * (x : A)⁻¹ ∈ ⁅R,R⁆
      exact commutator_mem_commutator ht (hNR x.property)
    refine ⟨c, hc, ?_⟩
    change q (MulAut.conjNormal t x * x⁻¹) = q a
    rw [map_mul, map_inv, hinv]
    change (q x)⁻¹ * (q x)⁻¹ = q a
    rw [← pow_two, inv_pow, ← map_pow, hx, map_inv, inv_inv]
  have hsup : D ⊔ frattini N = ⊤ := by
    have he := congrArg (Subgroup.comap q) hmap
    simpa only [Subgroup.comap_map_eq, q, QuotientGroup.ker_mk', Subgroup.comap_top] using he
  have hD : D = ⊤ := frattini_nongenerating hsup
  intro x hx
  have hm : (⟨x,hx⟩ : N) ∈ D := hD ▸ mem_top _
  exact hm

private theorem center_neg_one {F : Type*} [Field F] :
    (-1 : Matrix.SpecialLinearGroup (Fin 2) F) ∈ center _ := by
  apply mem_center_iff.mpr
  intro g
  apply Subtype.ext
  simp

private theorem natural_radical_inverter (h : A36Natural A) :
    ∃ t : A, t ∈ solvableRadical A ∧
      ∀ x : fittingSubgroup A, MulAut.conjNormal t x = x⁻¹ := by
  obtain ⟨hF, p, hp, hp3, F, _, _, hcard, v, ρ, hact⟩ := h
  let : IsQuasisimple (A ⧸ generalizedFitting A) :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv
      (by omega) ρ
  have hsol : Group.IsSolvable (generalizedFitting A) := by rw [hF]; infer_instance
  let := hsol
  obtain ⟨t, ht⟩ := (ρ.surjective.comp
    (QuotientGroup.mk'_surjective (generalizedFitting A))) (-1)
  change ρ (QuotientGroup.mk' (generalizedFitting A) t) = -1 at ht
  have hr : t ∈ solvableRadical A := by
    rw [radical_eq_comap_center (generalizedFitting A)]
    apply mem_center_iff.mpr
    intro g
    apply ρ.injective
    simp only [map_mul, ht]
    exact mem_center_iff.mp center_neg_one (ρ g)
  have hinv (x : generalizedFitting A) : MulAut.conjNormal t x = x⁻¹ := by
    apply v.injective
    rw [map_inv]
    change v ⟨t * x * t⁻¹, _⟩ = (v x)⁻¹
    rw [hact, ht]
    apply Multiplicative.toAdd.injective
    change Matrix.mulVec (-1 : Matrix (Fin 2) (Fin 2) F) _ = Multiplicative.toAdd ((v x)⁻¹)
    change Matrix.mulVec (-1 : Matrix (Fin 2) (Fin 2) F) (v x).toAdd = -(v x).toAdd
    rw [Matrix.neg_mulVec, Matrix.one_mulVec]
  refine ⟨t, hr, ?_⟩
  intro x
  apply Subtype.ext
  exact congrArg (fun z : generalizedFitting A => (z : A))
    (hinv ((MulEquiv.subgroupCongr hF).symm x))

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}

/-- The actual Fitting subgroup has index two in the solvable radical. -/
theorem fitting_radical_index (h : PrimeSL2FittingQuotient L) :
    (fittingSubgroup L).relIndex (solvableRadical L) = 2 := by
  obtain ⟨r, hr, hr3, ⟨e⟩⟩ := h
  let : Fact r.Prime := ⟨hr⟩
  let : IsQuasisimple (L ⧸ fittingSubgroup L) :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv
      (by simpa using hr3) e
  rw [← QuotientGroup.ker_mk' (fittingSubgroup L), relIndex_ker]
  rw [radical_eq_comap_center (fittingSubgroup L),
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  rw [Nat.card_congr (centerCongr e).toEquiv,
    Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'
      (R := ZMod r) (n := Fin 2) 0).toEquiv]
  exact (IsPrimitiveRoot.neg_one (R := ZMod r) r (by omega)).card_rootsOfUnity

/-- Lift the central involution of the actual Fitting quotient into the radical. -/
theorem exists_radical_quotient_involution (h : PrimeSL2FittingQuotient L) :
    ∃ t : L, t ∈ solvableRadical L ∧
      orderOf (QuotientGroup.mk' (fittingSubgroup L) t) = 2 := by
  obtain ⟨r, hr, hr3, ⟨e⟩⟩ := h
  let : Fact r.Prime := ⟨hr⟩
  let : IsQuasisimple (L ⧸ fittingSubgroup L) :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv
      (by simpa using hr3) e
  obtain ⟨t, ht⟩ := (e.surjective.comp
    (QuotientGroup.mk'_surjective (fittingSubgroup L))) (-1)
  change e (QuotientGroup.mk' (fittingSubgroup L) t) = -1 at ht
  refine ⟨t, ?_, ?_⟩
  · rw [radical_eq_comap_center (fittingSubgroup L)]
    apply mem_center_iff.mpr
    intro g
    apply e.injective
    simp only [map_mul, ht]
    exact mem_center_iff.mp center_neg_one (e g)
  · rw [← e.orderOf_eq, ht]
    apply Matrix.SpecialLinearGroup.orderOf_neg_one_eq_two
    intro he
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < r)
      ((ZMod.natCast_eq_zero_iff 2 r).mp he)


universe u
variable {E : Type u} [Group E] [Finite E] {C : Subgroup E}

/-- A central primary factor cannot survive the source's central-supplement rigidity. -/
theorem core_not_central_of_dvd
    (hrigid : CFSG.Quasithin.ChapterA.RankActions.PrimeSL2CoverRigidity.{u})
    (hC : C.IsCComponent) (hquot : PrimeSL2FittingQuotient C)
    {p : ℕ} [Fact p.Prime] (hd : p ∣ Nat.card (fittingSubgroup C)) :
    ¬ pCore p C ≤ center C := by
  intro hcentral
  let F := fittingSubgroup C
  let N := F ⊓ pPrimeCore p C
  have hsplit : F ≤ pCore p C ⊔ N := by
    dsimp [F]
    rw [fitting_eq_sup_pCore]
    refine iSup_le fun r => ?_
    let : Fact r.val.val.Prime := ⟨Nat.prime_of_mem_primeFactors r.val.property⟩
    by_cases heq : r.val.val = p
    · rw [heq]
      exact le_sup_left
    · apply le_trans (show pCore r.val.val C ≤ N from ?_) le_sup_right
      apply le_inf (pCore_le_fitting C _)
      apply le_sSup
      refine ⟨inferInstance, ?_⟩
      obtain ⟨n, hn⟩ := (pCore_isPGroup (p := r.val.val) (G := C)).exists_card_eq
      rw [hn]
      exact ((Nat.coprime_primes (Fact.out : p.Prime)
        (Fact.out : r.val.val.Prime)).mpr (fun hh => heq hh.symm)).pow_right n
  have hF : F = center C ⊔ N := le_antisymm
    (hsplit.trans (sup_le_sup_right hcentral N))
    (sup_le (le_sSup ⟨inferInstance, inferInstance⟩) inf_le_left)
  have heq := fitting_central_supplement hrigid hC hquot N hF
  have hcop : Nat.Coprime p (Nat.card N) :=
    (pPrimeCore_coprime_card (p := p) (G := C)).of_dvd_right
      (card_dvd_of_le (show N ≤ pPrimeCore p C from inf_le_right))
  rw [heq] at hd
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp hcop hd

/-- Single-prime support identifies the Fitting subgroup with its actual prime core. -/
theorem fitting_eq_core_of_support {p : ℕ} [Fact p.Prime]
    (hs : ∀ q : ℕ, q.Prime → q ∣ Nat.card (fittingSubgroup C) → q = p) :
    fittingSubgroup C = pCore p C := by
  apply CFSG.Quasithin.Chapter1.RadicalStructure.fitting_eq_core
  apply (isPGroup_iff_primeFactors_card_subset (Fact.out : p.Prime).ne_zero).mpr
  intro q hq
  have he := hs q (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hq)
  subst q
  exact Nat.mem_primeFactors.mpr ⟨Fact.out, dvd_refl _, (Fact.out : p.Prime).ne_zero⟩

/-- The central involution on the actual Frattini quotient generates the radical derived subgroup. -/
theorem radical_derived_eq_fitting
    (hC : C.IsCComponent) (hO : pCore 2 E = ⊥)
    (hquot : PrimeSL2FittingQuotient C) (hs : A36Natural C ∨ A36Nilpotent C) :
    ⁅solvableRadical C, solvableRadical C⁆ = fittingSubgroup C := by
  refine le_antisymm (radical_derived_le_fitting hquot) ?_
  let : Group.IsPerfect C := hC.perfect
  rcases hs with ha | hn
  · obtain ⟨t, ht, hi⟩ := natural_radical_inverter ha
    apply odd_frattini_inversion_generates (fittingSubgroup C) (solvableRadical C)
      fitting_le_radical (fitting_odd_card hC hO) t ht
    intro x
    rw [hi, map_inv]
  · obtain ⟨t, ht, ho⟩ := exists_radical_quotient_involution hquot
    apply odd_frattini_inversion_generates (fittingSubgroup C) (solvableRadical C)
      fitting_le_radical (fitting_odd_card hC hO) t ht
    intro x
    have hi := FittingActions.nilpotent_fitting_inversion hn t ho
      (QuotientGroup.mk' (frattini (fittingSubgroup C)) x)
    rw [FittingActions.fittingFrattiniAction_apply_mk] at hi
    exact hi

/-- Every common clause, with the sole remaining structural premise being the core alternatives. -/
theorem common_of_alternatives
    (hrigid : CFSG.Quasithin.ChapterA.RankActions.PrimeSL2CoverRigidity.{u})
    (hC : C.IsCComponent) (hO : pCore 2 E = ⊥)
    (hn : ¬ fittingSubgroup C ≤ center C)
    (hquot : PrimeSL2FittingQuotient C) (hs : A36Natural C ∨ A36Nilpotent C) :
    A36Common C := by
  have hd := radical_derived_eq_fitting hC hO hquot hs
  refine ⟨fitting_eq_oddCore hC hO hquot, fitting_quotient_quasisimple hquot,
    Or.inl ⟨(generalizedFitting_eq_fitting hC hn).symm, fitting_le_radical,
      fitting_radical_index hquot⟩, ?_, ?_⟩
  · exact hd.trans (fitting_eq_commutator hrigid hC hquot)
  · let : IsQuasisimple (C ⧸ fittingSubgroup C) := fitting_quotient_quasisimple hquot
    exact IsQuasisimple.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hd).symm

/-- Source consumer with all common and omega-action premises discharged. -/
theorem conclusion_of_alternatives
    (hrigid : CFSG.Quasithin.ChapterA.RankActions.PrimeSL2CoverRigidity.{u})
    {𝒦 : GroupClass.{u}} (hE : IsSQTK 𝒦 E) (hO : pCore 2 E = ⊥)
    (hC : C.IsCComponent) (hn : ¬ fittingSubgroup C ≤ center C)
    (hquot : PrimeSL2FittingQuotient C) (hs : A36Natural C ∨ A36Nilpotent C) :
    A36Conclusion C ∧ CenterFrattiniSource.OmegaActionData C := by
  have hc := common_of_alternatives hrigid hC hO hn hquot hs
  have h : A36Conclusion C :=
    ⟨hs.elim A36Alternative.natural A36Alternative.nilpotent, hc⟩
  have hw := CenterFrattiniSource.strengthened_omega_actions hE hO hC h
  exact ⟨hw.1, hw.2 (not_quasisimple_of_noncentral_fitting hn)⟩

end CFSG.Quasithin.ChapterA.Section03.NoncentralFitting.CoreShapes
