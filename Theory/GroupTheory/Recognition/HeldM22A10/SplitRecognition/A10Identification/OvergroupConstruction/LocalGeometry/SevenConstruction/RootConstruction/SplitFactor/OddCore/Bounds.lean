module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.RootQuotient
public import Theory.PPrimeCore
public import Theory.GroupAction.KleinFourCardinality

/-!
# The small odd core in Held's root centralizer

Write B = C_G(uv) and K = O(B). The marked element v cyclically permutes
pi*mu, tau*lambda and their product inside B. Thus their fixed subgroups
on K have the same order, which divides nine when |C_B(pi*mu)| = 72.
The central subgroup R = <uv> lies in all three fixed subgroups. The
Brauer--Wielandt formula gives that K is a three-group of order at most 81.

Any five-element of B fixes R. Orbit counting modulo five on K then makes
its whole action trivial: among the powers of three up to 81, a proper
fixed subgroup containing R cannot have the same residue modulo five.
This proves the action step directly, without introducing a quotient action.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 5.4, printed p.237. The final use of
Lemma 5.3 is isolated in the importing OddCore module. The proof uses no
unrestricted exclusion of subgroup orders divisible by fifteen.
-/

open Subgroup
noncomputable section

private theorem fixed_card_conjugate {H : Type*} [Group H]
    (a b c : MulAut H) (h : ∀ x, c (a x) = b (c x)) :
    Nat.card a.fixedSubgroup = Nat.card b.fixedSubgroup := by
  apply Nat.card_congr
  refine (Equiv.subtypeEquiv c.toEquiv ?_)
  intro x
  simp only [MulAut.mem_fixedSubgroup]
  change a x = x ↔ b (c x) = c x
  constructor
  · intro hx
    rw [← h, hx]
  · intro hx
    apply c.injective
    rw [h, hx]

namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (L : Source.SixLocalData D e)

public theorem rootKernel_le_oddCore :
    rootKernel D e L ≤ pPrimeCore 2 (rootCentralizer D e L) := by
  apply le_sSup
  exact ⟨inferInstance, by rw [rootKernel_card D e L]; decide⟩

namespace OddCore

private def first : rootCentralizer D e L :=
  ⟨pi D e * mu D e, A_le_rootCentralizer D e L L.pi_mu_mem⟩
private def second : rootCentralizer D e L :=
  ⟨tau D e * lam D e, A_le_rootCentralizer D e L L.tau_lam_mem⟩
private def cycler : rootCentralizer D e L :=
  ⟨L.v, A_le_rootCentralizer D e L L.v_mem⟩

private theorem first_square : first D e L ^ 2 = 1 := by
  apply Subtype.ext
  change (pi D e * mu D e) ^ 2 = 1
  have h : (modelElement 0 * modelElement 1) ^ 2 = 1 := by decide +kernel
  simpa only [element, map_mul, map_pow, map_one] using congrArg (D.a10ModelEmbedding e) h

private theorem second_square : second D e L ^ 2 = 1 := by
  apply Subtype.ext
  change (tau D e * lam D e) ^ 2 = 1
  have h : (modelElement 3 * modelElement 6) ^ 2 = 1 := by decide +kernel
  simpa only [element, map_mul, map_pow, map_one] using congrArg (D.a10ModelEmbedding e) h

private theorem first_commute_second : Commute (first D e L) (second D e L) := by
  apply Subtype.ext
  change (pi D e * mu D e) * (tau D e * lam D e) =
    (tau D e * lam D e) * (pi D e * mu D e)
  have h : (modelElement 0 * modelElement 1) * (modelElement 3 * modelElement 6) =
    (modelElement 3 * modelElement 6) * (modelElement 0 * modelElement 1) := by decide +kernel
  simpa only [element, map_mul] using congrArg (D.a10ModelEmbedding e) h

private theorem cycle_second :
    (cycler D e L)⁻¹ * second D e L * cycler D e L = first D e L := by
  apply Subtype.ext
  change L.v⁻¹ * (tau D e * lam D e) * L.v = pi D e * mu D e
  calc
    _ = (L.v⁻¹ * tau D e * L.v) * (L.v⁻¹ * lam D e * L.v) := by group
    _ = (pi D e * mu D e * lam D e) * lam D e := by
      rw [L.tau_v, L.v_lam_commute.inv_left.eq, inv_mul_cancel_right]
    _ = _ := by
      rw [mul_assoc, ← pow_two, element_square D e 6 (by decide), mul_one]

private theorem cycle_first :
    (cycler D e L)⁻¹ * first D e L * cycler D e L = first D e L * second D e L := by
  apply Subtype.ext
  change L.v⁻¹ * (pi D e * mu D e) * L.v =
    (pi D e * mu D e) * (tau D e * lam D e)
  calc
    _ = (L.v⁻¹ * pi D e * L.v) * (L.v⁻¹ * mu D e * L.v) := by group
    _ = (pi D e * tau D e * lam D e) * mu D e := by
      rw [L.pi_v, L.v_mu_commute.inv_left.eq, inv_mul_cancel_right]
    _ = _ := by
      have h : (modelElement 0 * modelElement 3 * modelElement 6) * modelElement 1 =
        (modelElement 0 * modelElement 1) * (modelElement 3 * modelElement 6) := by decide +kernel
      simpa only [element, map_mul] using congrArg (D.a10ModelEmbedding e) h

variable [Finite G]

/-- The literal odd core is a three-group of order at most 81. The three
fixed subgroups are conjugate by the marked element v; each divides 9. -/
public theorem three_group_bound
    (hY : Nat.card (centralizer ({pi D e * mu D e} : Set G) ⊓
      rootCentralizer D e L : Subgroup G) = 72) :
    IsPGroup 3 (pPrimeCore 2 (rootCentralizer D e L)) ∧
      Nat.card (pPrimeCore 2 (rootCentralizer D e L)) ≤ 81 := by
  let B := rootCentralizer D e L
  let K := pPrimeCore 2 B
  let f : B →* MulAut K := MulAut.conjNormal
  let a := f (first D e L)
  let b := f (second D e L)
  have ha : Function.Involutive a := by
    intro k
    change (a * a) k = k
    rw [← pow_two, show a ^ 2 = 1 from by
      dsimp only [a]; rw [← map_pow, first_square, map_one]]
    rfl
  have hb : Function.Involutive b := by
    intro k
    change (b * b) k = k
    rw [← pow_two, show b ^ 2 = 1 from by
      dsimp only [b]; rw [← map_pow, second_square, map_one]]
    rfl
  have hab : Commute a b := (first_commute_second D e L).map f
  have hba : Nat.card b.fixedSubgroup = Nat.card a.fixedSubgroup := by
    apply fixed_card_conjugate b a ((f (cycler D e L))⁻¹)
    intro x
    have he := congrArg f (cycle_second D e L)
    simp only [map_mul, map_inv] at he
    have he' : (f (cycler D e L))⁻¹ * b = a * (f (cycler D e L))⁻¹ := by
      apply (mul_right_cancel_iff (a := f (cycler D e L))).mp
      simpa only [mul_assoc, inv_mul_cancel, mul_one, a, b] using he
    exact congrArg (fun t : MulAut K => t x) he'
  have habcard : Nat.card (a*b).fixedSubgroup = Nat.card a.fixedSubgroup := by
    symm
    apply fixed_card_conjugate a (a*b) ((f (cycler D e L))⁻¹)
    intro x
    have he := congrArg f (cycle_first D e L)
    simp only [map_mul, map_inv] at he
    have he' : (f (cycler D e L))⁻¹ * a = (a*b) * (f (cycler D e L))⁻¹ := by
      apply (mul_right_cancel_iff (a := f (cycler D e L))).mp
      simpa only [mul_assoc, inv_mul_cancel, mul_one, a, b] using he
    exact congrArg (fun t : MulAut K => t x) he'
  have hd72 : Nat.card a.fixedSubgroup ∣ 72 := by
    let j : a.fixedSubgroup →* (centralizer ({pi D e * mu D e} : Set G) ⊓ B : Subgroup G) :=
      { toFun := fun x => ⟨x.val.val.val, by
          refine ⟨?_, x.val.val.property⟩
          apply mem_centralizer_singleton_iff.mpr
          have hx := congrArg (fun k : K => ((k : B) : G))
            ((MulAut.mem_fixedSubgroup a x.val).mp x.property)
          change (pi D e * mu D e) * x.val.val.val * (pi D e * mu D e)⁻¹ = x.val.val.val at hx
          exact (mul_inv_eq_iff_eq_mul.mp hx).symm⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    rw [← hY]
    apply card_dvd_of_injective j
    intro x y h
    have hh := congrArg (fun z :
      (centralizer ({pi D e * mu D e} : Set G) ⊓ B : Subgroup G) => (z : G)) h
    exact Subtype.ext (Subtype.ext (Subtype.ext hh))
  have hd9 : Nat.card a.fixedSubgroup ∣ 9 := by
    have hc : Nat.Coprime (Nat.card a.fixedSubgroup) 8 :=
      ((pPrimeCore_coprime_card (p := 2) (G := B)).of_dvd_right
        a.fixedSubgroup.card_subgroup_dvd_card).symm.pow_right 3
    exact hc.dvd_of_dvd_mul_left (show Nat.card a.fixedSubgroup ∣ 8 * 9 from hd72)
  have hcommon : 3 ≤ Nat.card (a.fixedSubgroup ⊓ b.fixedSubgroup : Subgroup K) := by
    let R := (rootKernel D e L).subgroupOf K
    have hRcard : Nat.card R = 3 :=
      (Nat.card_congr (subgroupOfEquivOfLe (rootKernel_le_oddCore D e L)).toEquiv).trans
        (rootKernel_card D e L)
    have hle : R ≤ a.fixedSubgroup ⊓ b.fixedSubgroup := by
      intro x hx
      have hfix (z : B) : f z x = x := by
        apply Subtype.ext
        change z * (x : B) * z⁻¹ = x
        have hc : z * (x : B) = (x : B) * z :=
          mem_center_iff.mp (rootKernel_le_center D e L hx) z
        rw [hc, mul_inv_cancel_right]
      exact ⟨(MulAut.mem_fixedSubgroup _ _).mpr (hfix _),
        (MulAut.mem_fixedSubgroup _ _).mpr (hfix _)⟩
    rw [← hRcard]
    exact card_le_of_le hle
  have hodd : Odd (Nat.card K) := Nat.coprime_two_left.mp
    (pPrimeCore_coprime_card (p := 2) (G := B))
  have hformula := Theory.GroupAction.brauerWielandt_fixedSubgroup_card hodd a b ha hb hab
  rw [hba, habcard] at hformula
  have hd729 : Nat.card K ∣ 3 ^ 6 := by
    apply dvd_trans (show Nat.card K ∣ Nat.card a.fixedSubgroup ^ 3 from ?_)
      (show Nat.card a.fixedSubgroup ^ 3 ∣ 3 ^ 6 from by
        simpa only [pow_succ, pow_zero, one_mul, Nat.reduceMul] using
          Nat.mul_dvd_mul (Nat.mul_dvd_mul hd9 hd9) hd9)
    exact ⟨Nat.card (a.fixedSubgroup ⊓ b.fixedSubgroup : Subgroup K)^2, by
      simpa only [pow_succ, pow_zero, one_mul] using hformula.symm⟩
  refine ⟨IsPGroup.of_card_dvd_pow hd729, ?_⟩
  have hdle : Nat.card a.fixedSubgroup ≤ 9 := Nat.le_of_dvd (by decide) hd9
  have hpowle := Nat.pow_le_pow_left hdle 3
  have hcommon2 : 9 ≤ Nat.card (a.fixedSubgroup ⊓ b.fixedSubgroup : Subgroup K)^2 := by nlinarith
  have hmul := Nat.mul_le_mul_left (Nat.card K) hcommon2
  nlinarith


private theorem five_action_trivial {H A : Type*} [Group H] [Finite H]
    [Group A] [MulDistribMulAction A H]
    (hH : IsPGroup 3 H) (hbound : Nat.card H ≤ 81) (hA : Nat.card A = 5)
    (hfixed : 3 ≤ Nat.card (FixedPoints.subgroup A H)) :
    ∀ a : A, ∀ x : H, a • x = x := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hp : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  let F := FixedPoints.subgroup A H
  obtain ⟨n, hn⟩ := hH.exists_card_eq
  have hnle : n ≤ 4 := by
    by_contra! hh
    have hp := Nat.pow_le_pow_right (by decide : 0 < 3) hh
    rw [← hn] at hp
    norm_num at hp
    omega
  obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (hn ▸ F.card_subgroup_dvd_card)
  have hmod := hp.card_modEq_card_fixedPoints H
  change Nat.card H % 5 = Nat.card F % 5 at hmod
  have hcardeq : Nat.card F = Nat.card H := by
    change 3 ≤ Nat.card F at hfixed
    rw [hn, hcard] at hmod ⊢
    rw [hcard] at hfixed
    interval_cases n <;> interval_cases k <;> norm_num at *
  have htop := F.eq_top_of_card_eq hcardeq
  intro a x
  exact (show x ∈ F from htop ▸ mem_top x) a

/-- The central root rules out a nontrivial five-action on the small odd core.
This applies to every order-five element of the full root centralizer. -/
public theorem five_centralizes
    (hY : Nat.card (centralizer ({pi D e * mu D e} : Set G) ⊓
      rootCentralizer D e L : Subgroup G) = 72)
    (w : rootCentralizer D e L) (hw : orderOf w = 5) :
    ∀ x ∈ pPrimeCore 2 (rootCentralizer D e L), Commute w x := by
  let B := rootCentralizer D e L
  let K := pPrimeCore 2 B
  let A := zpowers w
  let f : A →* MulAut K := (MulAut.conjNormal : B →* MulAut K).comp A.subtype
  let : MulDistribMulAction A K := MulDistribMulAction.compHom K f
  have hA : Nat.card A = 5 := by rw [Nat.card_zpowers, hw]
  have hfixed : 3 ≤ Nat.card (FixedPoints.subgroup A K) := by
    let R := (rootKernel D e L).subgroupOf K
    have hRcard : Nat.card R = 3 :=
      (Nat.card_congr (subgroupOfEquivOfLe (rootKernel_le_oddCore D e L)).toEquiv).trans
        (rootKernel_card D e L)
    have hle : R ≤ FixedPoints.subgroup A K := by
      intro x hx a
      apply Subtype.ext
      change (a : B) * (x : B) * (a : B)⁻¹ = x
      have hc : (a : B) * (x : B) = (x : B) * a :=
        mem_center_iff.mp (rootKernel_le_center D e L hx) a
      rw [hc, mul_inv_cancel_right]
    rw [← hRcard]
    exact card_le_of_le hle
  obtain ⟨hK, hbound⟩ := three_group_bound D e L hY
  have htriv := five_action_trivial hK hbound hA hfixed
  intro x hx
  have hf := congrArg Subtype.val (htriv ⟨w, mem_zpowers w⟩ ⟨x, hx⟩)
  change w * x * w⁻¹ = x at hf
  exact mul_inv_eq_iff_eq_mul.mp hf

end OddCore

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor
