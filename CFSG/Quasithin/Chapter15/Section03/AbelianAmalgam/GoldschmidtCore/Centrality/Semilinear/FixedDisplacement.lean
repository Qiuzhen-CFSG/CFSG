module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.ActualAction

/-!
# Fixed vectors are the actual inverter commutators

The dimension-independent identity Fix(τ)=im(τ+1) is transported through
the literal binary conjugation action. Every fixed element is one actual
commutator with q. All powers of q act as either the identity or the same
inverter, so this also identifies the subgroup commutator [U,⟨q⟩] with
C_U(Q). Injectivity of the explicit cubic pair map proves that the two
actual summands W and Wᵇ have trivial intersection.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
the semilinear module argument after 15.3.68, printed pp.1154–1155.
-/

@[expose] public section
open Subgroup Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
variable {G : Type*} [Group G] [Finite G]

/-- Every Q-fixed element of U is one actual commutator with the bad core
inverter, and every such commutator is Q-fixed. -/
theorem coreFixed_mem_iff_commutator (H B U : Subgroup G) [IsElementaryAbelian 2 U]
    (hHB : H ≤ normalizer (B : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hBU : B ≤ normalizer (U : Set G))
    (h0U : ambientTwoCore B ≤ centralizer (U : Set G))
    (hN : ambientTwoCore H ⊓ characterKernel H B hHB = H ⊓ centralizer (U : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3) (hgen : U = ⁅U,B⁆)
    (q : H) (hq : q ∈ localTwoCore H) (hqχ : quotientAction H B hHB q ≠ 1)
    (b : B) (hb : b ∉ localTwoCore B) (x : U) :
    (x : G) ∈ coreFixed H U ↔ ∃ u : U, ⁅(q : G),(u : G)⁆ = (x : G) := by
  let β := externalCubicAction B U hBU h0U (QuotientGroup.mk' _ b)
  let τ := spanAction H U hHU q
  have he := fixed_eq_displacement_range β τ
    (externalCubicAction_polynomial B U hBU h0U hc hgen b hb)
    (coreAction_square H B U hHB hHU hN hc q hq)
    (coreAction_inverts_cubic H B U hHB hHU hBU h0U hc q hqχ b)
  have hi (u : U) : ((τ + 1) (Additive.ofMul u)).toMul.val = ⁅(q : G),(u : G)⁆ := by
    have hpow : (u : G) ^ 2 = 1 := congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 U) u)
    have hinv : (u : G)⁻¹ = u := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hpow)
    change (q : G) * (u : G) * (q : G)⁻¹ * u = ⁅(q : G),(u : G)⁆
    rw [commutatorElement_def,hinv]
  have hiff : (x : G) ∈ coreFixed H U ↔ τ (Additive.ofMul x) = Additive.ofMul x :=
    coreFixed_iff_fixed H B U hHB hHU hN hc q hq hqχ (Additive.ofMul x)
  rw [hiff]
  change τ (Additive.ofMul x) = Additive.ofMul x ↔ _
  rw [← sub_eq_zero]
  change Additive.ofMul x ∈ LinearMap.ker (τ - 1) ↔ _
  rw [he]
  constructor
  · rintro ⟨u,hu⟩
    exact ⟨u.toMul,(hi u.toMul).symm.trans (congrArg (fun v : Additive U => (v.toMul : G)) hu)⟩
  · rintro ⟨u,hu⟩
    refine ⟨Additive.ofMul u,?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (hi u).trans hu

/-- The source W=[U,q] identity, as the actual subgroup commutator. -/
theorem coreFixed_eq_commutator (H B U : Subgroup G) [IsElementaryAbelian 2 U]
    (hHB : H ≤ normalizer (B : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hBU : B ≤ normalizer (U : Set G))
    (h0U : ambientTwoCore B ≤ centralizer (U : Set G))
    (hN : ambientTwoCore H ⊓ characterKernel H B hHB = H ⊓ centralizer (U : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3) (hgen : U = ⁅U,B⁆)
    (q : H) (hq : q ∈ localTwoCore H) (hqχ : quotientAction H B hHB q ≠ 1)
    (b : B) (hb : b ∉ localTwoCore B) :
    coreFixed H U = ⁅U,zpowers (q : G)⁆ := by
  rw [commutator_comm]
  have hqW (u : U) : ⁅(q : G),(u : G)⁆ ∈ coreFixed H U := by
    have hmem : ⁅(q : G),(u : G)⁆ ∈ U := by
      rw [commutatorElement_def]
      exact U.mul_mem ((mem_normalizer_iff.mp (hHU q.property) u).mp u.property) (U.inv_mem u.property)
    exact (coreFixed_mem_iff_commutator H B U hHB hHU hBU h0U hN hc hgen q hq hqχ b hb
      ⟨_,hmem⟩).mpr ⟨u,rfl⟩
  apply le_antisymm
  · intro x hx
    obtain ⟨u,hu⟩ := (coreFixed_mem_iff_commutator H B U hHB hHU hBU h0U hN hc hgen
      q hq hqχ b hb ⟨x,hx.1⟩).mp hx
    change ⁅(q : G),(u : G)⁆ = x at hu
    rw [← hu]
    exact commutator_mem_commutator (mem_zpowers (q : G)) u.property
  · apply commutator_le.mpr
    intro r hr u hu
    have hrQ : r ∈ ambientTwoCore H := (zpowers_le.mpr (show (q : G) ∈ ambientTwoCore H from hq)) hr
    let rH : H := ⟨r,pCoreIn_le 2 H hrQ⟩
    let v : Additive U := Additive.ofMul ⟨u,hu⟩
    by_cases hrχ : quotientAction H B hHB rH = 1
    · have ha := LinearMap.congr_fun (coreAction_eq_one H B U hHB hHU hN rH hrQ hrχ) v
      have ha' := congrArg (fun w : Additive U => (w.toMul : G)) ha
      change r*u*r⁻¹ = u at ha'
      rw [commutatorElement_def,ha',mul_inv_cancel]
      exact (coreFixed H U).one_mem
    · have hχ := ((Nat.card_eq_two_iff' (1 : MulAut (B ⧸ localTwoCore B))).mp
        (ExternalQuotient.aut_card B hc)).unique hrχ hqχ
      have ha := LinearMap.congr_fun
        (coreAction_eq_of_character H B U hHB hHU hN rH q hrQ hq hχ) v
      have ha' := congrArg (fun w : Additive U => (w.toMul : G)) ha
      change r*u*r⁻¹ = (q : G)*u*(q : G)⁻¹ at ha'
      rw [commutatorElement_def,ha']
      exact hqW ⟨u,hu⟩

/-- The actual two cubic summands have trivial intersection. -/
theorem coreFixed_disjoint_cubic (H B U : Subgroup G) [IsElementaryAbelian 2 U]
    (hHB : H ≤ normalizer (B : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hBU : B ≤ normalizer (U : Set G))
    (h0U : ambientTwoCore B ≤ centralizer (U : Set G))
    (hN : ambientTwoCore H ⊓ characterKernel H B hHB = H ⊓ centralizer (U : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3) (hgen : U = ⁅U,B⁆)
    (q : H) (hq : q ∈ localTwoCore H) (hqχ : quotientAction H B hHB q ≠ 1)
    (b : B) (hb : b ∉ localTwoCore B) :
    Disjoint (coreFixed H U) ((coreFixed H U).map (MulAut.conj (b : G)).toMonoidHom) := by
  let W := coreFixed H U
  let P := coreFixedPairEquiv H B U hHB hHU hBU h0U hN hc hgen q hq hqχ b hb
  apply Subgroup.disjoint_def.mpr
  intro x hx hx'
  obtain ⟨v,hv,hvx⟩ := hx'
  change (b : G)*v*(b : G)⁻¹ = x at hvx
  let xx : Additive W := Additive.ofMul ⟨x,hx⟩
  let vv : Additive W := Additive.ofMul ⟨v,hv⟩
  have hp : P (xx,0) = P (0,vv) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change x * ((b : G)*1*(b : G)⁻¹) = 1*((b : G)*v*(b : G)⁻¹)
    simpa only [mul_one,mul_inv_cancel,one_mul] using hvx.symm
  have hz : xx = 0 := congrArg Prod.fst (P.injective hp)
  exact congrArg (fun w : Additive W => (w.toMul : G)) hz

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
