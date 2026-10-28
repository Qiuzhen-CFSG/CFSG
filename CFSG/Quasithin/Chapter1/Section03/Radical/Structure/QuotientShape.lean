module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Quotient
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Structure
public import Theory.GroupTheory.PGroup.OmegaAction
public import Theory.GroupTheory.Fitting.Centralizer

/-!
# Radical quotient shapes and the single-prime centralizer

The actual quotient of Ξ_p(L) is Ω₁(O_p(L/O₂(L))). The natural-module
case is elementary abelian of order p². In the nilpotent case, the omega
subgroup of the homocyclic group still has order p², while the extraspecial
case has exponent p and its omega subgroup is the whole group.

The full common part of A.3.6 identifies the Fitting subgroup as the odd
core. If it has only one prime divisor, it equals that p-core and F*.
Its centralizer is proper by the final quasisimple-quotient clause of A.3.6;
C-component minimality then makes the centralizer solvable. The solvable
Fitting centralizer theorem proves C(F) ≤ F. Thus none of these steps
requires the additional center–Frattini equality printed in 1.2.1(4d).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.6,
printed pp.43–45, and the proofs of 1.3.3 and 1.3.8, pp.509 and 513.
The universal earlier A.3.6 implication remains an explicit parameter.
The action and maximal-component identification are separate obligations.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.Section02.LocalModels


namespace CFSG.Quasithin.Chapter1.RadicalStructure
variable {K : Type*} [Group K] {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem omega_top (h : ∀ x : K, x ^ p = 1) : omega K (p := p) 1 = ⊤ := by
  apply top_unique
  intro x _
  exact subset_closure (by simpa only [Set.mem_ofPred_eq, pow_one] using h x)

theorem extra_shape [Finite K] (h : OddExtraspecialThree p K) : XiOddQuotient p K := by
  let := h.1.1
  have hc : Nat.card K = p ^ 3 := by simpa using h.1.2
  let : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hc]; exact one_lt_pow₀ (Fact.out : p.Prime).one_lt (by decide))
  exact Or.inr ⟨h.1.1, hc, (Monoid.exponent_eq_prime_iff (Fact.out : p.Prime)).mpr (fun g hg => orderOf_eq_prime (h.2 g) hg)⟩

theorem extra_omega [Finite K] (h : OddExtraspecialThree p K) :
    XiOddQuotient p (omega K (p := p) 1) :=
  (extra_shape h).of_mulEquiv ((MulEquiv.subgroupCongr (omega_top h.2)).trans topEquiv).symm

private noncomputable def piTorsionEquiv (n k : ℕ) :
    (powMonoidHom k : Multiplicative (Fin 2 → ZMod n) →*
      Multiplicative (Fin 2 → ZMod n)).ker ≃
    (Fin 2 → (powMonoidHom k : Multiplicative (ZMod n) →* Multiplicative (ZMod n)).ker) where
  toFun x i := ⟨Multiplicative.ofAdd (x.val.toAdd i), by
    have h := congrArg (fun x : Multiplicative (Fin 2 → ZMod n) => x.toAdd i) x.property
    exact h⟩
  invFun x := ⟨Multiplicative.ofAdd (fun i => (x i).val.toAdd), by
    apply congrArg Multiplicative.ofAdd
    funext i
    exact (x i).property⟩
  left_inv x := rfl
  right_inv x := rfl

theorem homocyclic_omega (h : HomocyclicTwo p K) :
    XiOddQuotient p (omega K (p := p) 1) := by
  obtain ⟨a, ha, ⟨e⟩⟩ := h
  let C := Multiplicative (Fin 2 → ZMod (p ^ a))
  have hc : Nat.card (omega C (p := p) 1) = p ^ 2 := by
    rw [OmegaAction.omega_eq_pow_ker, pow_one,
      Nat.card_congr (piTorsionEquiv (p ^ a) p)]
    rw [Nat.card_fun, Nat.card_fin, IsCyclic.card_powMonoidHom_ker]
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    rw [Nat.gcd_eq_right (dvd_pow_self p (by omega : a ≠ 0))]
  have he : XiOddQuotient p (omega C (p := p) 1) :=
    Or.inl ⟨IsElementaryAbelian.omega₁_of_isMulCommutative C, hc⟩
  exact he.of_mulEquiv (e.omega p 1).symm


omit [Fact p.Prime] in
theorem natural_elementary [Finite K] {N : Subgroup K} [N.Normal]
    (h : NaturalSL2Action K N p) : IsElementaryAbelian p N ∧ Nat.card N = p ^ 2 := by
  obtain ⟨F, _, _, hF, v, _, _⟩ := h
  let : Fintype F := Fintype.ofFinite F
  have hpow : ∀ x : Multiplicative (Fin 2 → F), x ^ p = 1 := by
    intro x
    apply congrArg Multiplicative.ofAdd
    funext i
    change p • x.toAdd i = 0
    rw [← hF]
    exact card_nsmul_eq_zero'
  have hcomm : IsMulCommutative N := IsMulCommutative.of_comm (fun x y =>
    v.injective (by simp only [map_mul, mul_comm]))
  refine ⟨{ toIsMulCommutative := hcomm, exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }, ?_⟩
  · intro x
    apply v.injective
    simpa using hpow (v x)
  · rw [Nat.card_congr v.toEquiv]
    simpa only [Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      Fintype.card_fun, Fintype.card_fin] using congrArg (fun n => n ^ 2) hF

theorem fitting_eq_core [Finite K] (h : IsPGroup p (fittingSubgroup K)) :
    fittingSubgroup K = pCore p K := by
  apply le_antisymm _ (pCore_le_fitting K p)
  exact le_sSup ⟨inferInstance, h⟩

theorem natural_core [Finite K] (h : A36Natural K)
    (hp : p ∣ Nat.card (fittingSubgroup K)) :
    3 < p ∧ IsElementaryAbelian p (pCore p K) ∧ Nat.card (pCore p K) = p ^ 2 := by
  obtain ⟨hF, r, hr, hr3, ha⟩ := h
  let : Fact r.Prime := ⟨hr⟩
  obtain ⟨he, hc⟩ := natural_elementary ha
  have hd : p ∣ r ^ 2 := by simpa only [← hF, hc] using hp
  have hpr : p = r := (Nat.prime_dvd_prime_iff_eq Fact.out hr).mp
    ((Fact.out : p.Prime).dvd_of_dvd_pow hd)
  subst r
  have hfit : fittingSubgroup K = pCore p K := fitting_eq_core (by
    rw [← hF]
    exact IsPGroup.of_card hc)
  have hGF : generalizedFitting K = pCore p K := hF.trans hfit
  refine ⟨hr3, ?_, ?_⟩
  · exact hGF ▸ he
  · simpa only [hGF] using hc

theorem radical_core [Finite K] (h : A36Natural K ∨ A36Nilpotent K)
    (hp : p ∣ Nat.card (fittingSubgroup K)) :
    generalizedFitting K = fittingSubgroup K ∧ 3 < p ∧
      ((IsElementaryAbelian p (pCore p K) ∧ Nat.card (pCore p K) = p ^ 2) ∨
        OddExtraspecialThree p (pCore p K) ∨ HomocyclicTwo p (pCore p K)) := by
  rcases h with hn | hn
  · obtain ⟨hp3, he, hc⟩ := natural_core hn hp
    exact ⟨hn.1, hp3, Or.inl ⟨he, hc⟩⟩
  · obtain ⟨hm, hs⟩ := hn.2.2.2 p Fact.out (hn.1.symm ▸ hp)
    have hp3 : 3 < p := by
      have hp2 := (Fact.out : p.Prime).two_le
      rcases hm with (hm | hm) | hm <;> omega
    exact ⟨hn.1, hp3, Or.inr hs⟩

theorem nonsimple_radical {E : Type*} [Group E] [Finite E] {C : Subgroup E}
    (h : A36Conclusion C) (hn : ¬ IsQuasisimple C) : A36Natural C ∨ A36Nilpotent C := by
  cases h.1 with
  | simple hc _ _ => exact (hn hc.2).elim
  | cover hc _ _ => exact (hn hc.2).elim
  | natural hn => exact Or.inl hn
  | nilpotent hn => exact Or.inr hn


theorem core_omega [Finite K] (h : A36Natural K ∨ A36Nilpotent K)
    (hp : p ∣ Nat.card (fittingSubgroup K)) :
    3 < p ∧ XiOddQuotient p (omega (pCore p K) (p := p) 1) := by
  obtain ⟨_, hp3, he | he | he⟩ := radical_core h hp
  · let := he.1
    have ht : omega (pCore p K) (p := p) 1 = ⊤ := omega_top
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p (pCore p K)))
    exact ⟨hp3, (show XiOddQuotient p (pCore p K) from Or.inl he).of_mulEquiv
      ((MulEquiv.subgroupCongr ht).trans topEquiv).symm⟩
  · exact ⟨hp3, extra_omega he⟩
  · exact ⟨hp3, homocyclic_omega he⟩

theorem core_shape [Finite K] (h : A36Natural K ∨ A36Nilpotent K)
    (hp : p ∣ Nat.card (fittingSubgroup K)) :
    IsMulCommutative (pCore p K) ∨ ∀ x : pCore p K, x ^ p = 1 := by
  obtain ⟨_, _, he | he | he⟩ := radical_core h hp
  · exact Or.inl he.1.toIsMulCommutative
  · exact Or.inr he.2
  · obtain ⟨_, _, ⟨e⟩⟩ := he
    exact Or.inl (IsMulCommutative.of_comm (fun x y =>
      e.injective (by simp only [map_mul, mul_comm])))

private theorem fitting_map_le {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (fittingSubgroup A).map e.toMonoidHom ≤ fittingSubgroup B := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  rintro N ⟨hN, hnil⟩
  apply map_le_iff_le_comap.mp
  let := hnil
  exact le_sSup ⟨hN.map _ e.surjective, Group.nilpotent_of_mulEquiv (e.subgroupMap N)⟩

private theorem fitting_map {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (fittingSubgroup A).map e.toMonoidHom = fittingSubgroup B := by
  apply le_antisymm (fitting_map_le e)
  have h := map_mono (f := e.toMonoidHom) (fitting_map_le e.symm)
  simpa [map_map] using h

theorem core_eq_generalizedFitting [Finite K] (h : A36Natural K ∨ A36Nilpotent K)
    (hc : A36Common K)
    (hs : ∀ q : ℕ, q.Prime → Odd q → q ∣ Nat.card (fittingSubgroup K) → q = p) :
    pCore p K = generalizedFitting K := by
  have hfit : IsPGroup p (fittingSubgroup K) := by
    apply (isPGroup_iff_primeFactors_card_subset (Fact.out : p.Prime).ne_zero).mpr
    intro q hq
    obtain ⟨hq, hd, _⟩ := Nat.mem_primeFactors.mp hq
    have ho : Odd q := by
      rcases hq.eq_two_or_odd' with rfl | ho
      · have hcop := pPrimeCore_coprime_card (p := 2) (G := K)
        rw [← hc.1] at hcop
        have hdiv := Nat.dvd_gcd (dvd_refl 2) hd
        rw [hcop] at hdiv
        norm_num at hdiv
      · exact ho
    rw [hs q hq ho hd]
    exact (Fact.out : p.Prime).mem_primeFactors_self
  have hg : generalizedFitting K = fittingSubgroup K := h.elim And.left And.left
  exact (fitting_eq_core hfit).symm.trans hg.symm


theorem fitting_selfCentralizing {E : Type*} [Group E] [Finite E]
    {C : Subgroup E} (hC : C.IsCComponent) (h : A36Common C)
    (hn : ¬ IsQuasisimple C) :
    centralizer (fittingSubgroup C : Set C) ≤ fittingSubgroup C := by
  let D := centralizer (fittingSubgroup C : Set C)
  have hnD : D ≠ ⊤ := by
    intro hD
    have hcomm : ⁅fittingSubgroup C, (⊤ : Subgroup C)⁆ = ⊥ := by
      rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr hD.ge
    have hderived : ⁅solvableRadical C, solvableRadical C⁆ = ⊥ :=
      h.2.2.2.1.trans hcomm
    let := h.2.2.2.2
    exact hn (IsQuasisimple.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hderived).trans QuotientGroup.quotientBot))
  have hsolv := hC.isSolvable_of_subnormal_lt_top
    (inferInstance : D.Normal).isSubnormal hnD
  have hFD : fittingSubgroupOf D ≤ fittingSubgroup C :=
    le_sSup ⟨fittingSubgroupOf_normal D inferInstance, fittingSubgroupOf_isNilpotent D⟩
  intro x hx
  have hd : (⟨x, hx⟩ : D) ∈ fittingSubgroup D := by
    apply centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv
    apply mem_centralizer_iff.mpr
    intro y hy
    apply Subtype.ext
    exact mem_centralizer_iff.mp hx y (hFD (mem_map_of_mem D.subtype hy))
  exact hFD (mem_map_of_mem D.subtype hd)


private theorem layer_map_le {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (componentLayer A).map e.toMonoidHom ≤ componentLayer B := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro N hN
  exact map_le_iff_le_comap.mp (le_sSup (hN.map_equiv e))

private theorem layer_map {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (componentLayer A).map e.toMonoidHom = componentLayer B := by
  apply le_antisymm (layer_map_le e)
  have h := map_mono (f := e.toMonoidHom) (layer_map_le e.symm)
  simpa [map_map] using h

private theorem generalizedFitting_map {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (generalizedFitting A).map e.toMonoidHom = generalizedFitting B := by
  rw [generalizedFitting, generalizedFitting, Subgroup.map_sup, fitting_map, layer_map]

private noncomputable def fittingEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    fittingSubgroup A ≃* fittingSubgroup B :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (fitting_map e))

private noncomputable def coreEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (p : ℕ) :
    pCore p A ≃* pCore p B :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (pCore_map_iso p e))

theorem oddQuotient_of_a36 {G E : Type*} [Group G] [Finite G] [Group E] [Finite E]
    (L₀ : Subgroup G) {C : Subgroup E} (e : XiQuotient L₀ ≃* C)
    (h : A36Conclusion C) (hn : ¬ IsQuasisimple (XiQuotient L₀))
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L₀))) :
    3 < p ∧ XiOddQuotient p (XiQuotient (XiP p L₀)) := by
  have hnC : ¬ IsQuasisimple C := by
    intro hc
    let := hc
    exact hn (IsQuasisimple.of_mulEquiv e.symm)
  have hdC : p ∣ Nat.card (fittingSubgroup C) := by
    rwa [← Nat.card_congr (fittingEquiv e).toEquiv]
  obtain ⟨hp3, hq⟩ := core_omega (nonsimple_radical h hnC) hdC
  exact ⟨hp3, hq.of_mulEquiv
    ((xiPQuotientEquivOmega ho L₀).trans ((coreEquiv e p).omega p 1)).symm⟩

theorem singlePrime_structure_of_a36 {G E : Type*} [Group G] [Finite G] [Group E] [Finite E]
    (L₀ : Subgroup G) {C : Subgroup E} (e : XiQuotient L₀ ≃* C)
    (hC : C.IsCComponent) (h : A36Conclusion C)
    (hn : ¬ IsQuasisimple (XiQuotient L₀))
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L₀)))
    (hs : ∀ q : ℕ, q.Prime → Odd q →
      q ∣ Nat.card (fittingSubgroup (XiQuotient L₀)) → q = p) :
    pCore p (XiQuotient L₀) = generalizedFitting (XiQuotient L₀) ∧
    (IsMulCommutative (pCore p (XiQuotient L₀)) ∨
      ∀ x : pCore p (XiQuotient L₀), x ^ p = 1) ∧
    centralizer (pCore p (XiQuotient L₀) : Set (XiQuotient L₀)) ≤ pCore p (XiQuotient L₀) := by
  have hnC : ¬ IsQuasisimple C := by
    intro hc
    let := hc
    exact hn (IsQuasisimple.of_mulEquiv e.symm)
  have hdC : p ∣ Nat.card (fittingSubgroup C) := by
    rwa [← Nat.card_congr (fittingEquiv e).toEquiv]
  have hsC : ∀ q : ℕ, q.Prime → Odd q → q ∣ Nat.card (fittingSubgroup C) → q = p := by
    intro q hq ho hd
    apply hs q hq ho
    rwa [Nat.card_congr (fittingEquiv e).toEquiv]
  have ha := nonsimple_radical h hnC
  have hcore := core_eq_generalizedFitting ha h.2 hsC
  have hfit : pCore p C = fittingSubgroup C :=
    hcore.trans (ha.elim And.left And.left)
  refine ⟨?_, ?_, ?_⟩
  · apply map_injective (f := e.toMonoidHom) e.injective
    rw [pCore_map_iso, generalizedFitting_map]
    exact hcore
  · rcases core_shape ha hdC with hab | hexp
    · let := hab
      exact Or.inl (IsMulCommutative.of_comm (fun x y =>
        (coreEquiv e p).injective (by simp only [map_mul, mul_comm])))
    · exact Or.inr (fun x => (coreEquiv e p).injective (by
        simpa only [map_pow, map_one] using hexp (coreEquiv e p x)))
  · intro x hx
    have heC : e x ∈ centralizer (pCore p C : Set C) := by
      apply mem_centralizer_iff.mpr
      intro y hy
      obtain ⟨z, hz⟩ := (coreEquiv e p).surjective ⟨y, hy⟩
      have hez : e z = y := congrArg Subtype.val hz
      rw [← hez, ← map_mul, ← map_mul]
      exact congrArg e (mem_centralizer_iff.mp hx z z.property)
    have hecore : e x ∈ pCore p C := by
      rw [hfit] at heC ⊢
      exact fitting_selfCentralizing hC h.2 hnC heC
    rw [← pCore_map_iso p e] at hecore
    obtain ⟨y, hy, he⟩ := hecore
    exact e.injective he ▸ hy

end CFSG.Quasithin.Chapter1.RadicalStructure

namespace CFSG.Quasithin.Chapter1
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual image of the local C-component in the quotient of its join with T. -/
abbrev radicalLocalImage (T L₀ : Subgroup G) :=
  (L₀.subgroupOf (L₀ ⊔ T)).map (QuotientGroup.mk' (pCore 2 (L₀ ⊔ T : Subgroup G)))

noncomputable def radicalLocalQuotientEquiv {T L₀ : Subgroup G} (hL : L₀ ∈ L G T) :
    XiQuotient L₀ ≃* radicalLocalImage T L₀ := by
  let e : L₀ ≃* L₀.subgroupOf (L₀ ⊔ T) := (subgroupOfEquivOfLe le_sup_left).symm
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    (cComponentTwoCoreQuotientEquiv hL.1)

theorem XiP_oddQuotient_of_A36 {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → A36Conclusion C)
    {T L₀ : Subgroup G} (hL : L₀ ∈ L G T)
    (hQ : IsSQTK 𝒦 ((L₀ ⊔ T : Subgroup G) ⧸ pCore 2 (L₀ ⊔ T : Subgroup G)))
    (hn : ¬ IsQuasisimple (XiQuotient L₀)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L₀))) :
    3 < p ∧ XiOddQuotient p (XiQuotient (XiP p L₀)) := by
  apply RadicalStructure.oddQuotient_of_a36 L₀ (radicalLocalQuotientEquiv hL) _ hn ho hd
  exact proposition_1_2_1_four_earlier_conclusion hA36 hQ hL.1

theorem XiRad_oddQuotient_of_A36 {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → A36Conclusion C)
    {T : Subgroup G}
    (hQ : ∀ L₀ ∈ L G T, IsSQTK 𝒦 ((L₀ ⊔ T : Subgroup G) ⧸ pCore 2 (L₀ ⊔ T : Subgroup G)))
    {X : Subgroup G} (hX : X ∈ XiRad G T) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ 3 < p ∧ XiOddQuotient p (XiQuotient X) := by
  obtain ⟨L₀, hL, hn, p, hp, ho, hd, rfl⟩ := hX
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hp3, hodd⟩ := XiP_oddQuotient_of_A36 hA36 hL (hQ L₀ hL) hn ho hd
  exact ⟨p, hp, ho, hp3, hodd⟩

theorem XiP_singlePrime_structure_of_A36 {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → A36Conclusion C)
    {T L₀ : Subgroup G} (hL : L₀ ∈ L G T)
    (hQ : IsSQTK 𝒦 ((L₀ ⊔ T : Subgroup G) ⧸ pCore 2 (L₀ ⊔ T : Subgroup G)))
    (hn : ¬ IsQuasisimple (XiQuotient L₀)) {p : ℕ} [Fact p.Prime]
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L₀)))
    (hs : ∀ q : ℕ, q.Prime → Odd q →
      q ∣ Nat.card (fittingSubgroup (XiQuotient L₀)) → q = p) :
    pCore p (XiQuotient L₀) = generalizedFitting (XiQuotient L₀) ∧
    (IsMulCommutative (pCore p (XiQuotient L₀)) ∨
      ∀ x : pCore p (XiQuotient L₀), x ^ p = 1) ∧
    centralizer (pCore p (XiQuotient L₀) : Set (XiQuotient L₀)) ≤ pCore p (XiQuotient L₀) := by
  apply RadicalStructure.singlePrime_structure_of_a36 L₀ (radicalLocalQuotientEquiv hL) _ _ hn hd hs
  · let := pCore_isNilpotent (p := 2) (G := (L₀ ⊔ T : Subgroup G))
    exact hL.1.map_quotient _
  · exact proposition_1_2_1_four_earlier_conclusion hA36 hQ hL.1


end CFSG.Quasithin.Chapter1
