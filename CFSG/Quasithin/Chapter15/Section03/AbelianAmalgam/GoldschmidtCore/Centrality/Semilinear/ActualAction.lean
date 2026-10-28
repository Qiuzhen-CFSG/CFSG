module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.SourceKernel
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.OperatorSplitting
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.ExternalQuotient.LocalStructure
public import Theory.Representation.BinaryInternalFixedSpaceCodimension.Action
public import Theory.Representation.BinaryOffender.ConjugationGeneration

/-!
# The actual semilinear operators and faithful fixed-space action

Keep B external to H. Its normalization of V extends to U = ⟨Vᴴ⟩.
The source core and commutator identities make U elementary abelian and
U = [U,B]. Conjugation by B descends through its literal cubic quotient;
commutator generation proves β²+β+1=0 on U. The source kernel equality
N = C_H(U) then gives τ²=1 and τβ=β²τ for an actual bad core element.

The Q-fixed subgroup W = C_U(Q) is exactly Fix(τ), and the explicit
map (w,v) ↦ w · bvb⁻¹ identifies W × W with U. Restriction determines
an operator commuting with β, proving C_H(W)=Q. Thus actual conjugation
on W gives a faithful representation of the literal quotient H/Q.

This supplies the action construction in the repaired bad-character branch
of Aschbacher–Smith 15.3.68, printed pp.1154–1155 (combined manuscript,
1 March 2004). The preceding source kernel identities are explicit inputs
proved in SourceKernel; neither B≤H nor core centrality is used. The
identification W=⟨Zᴴ⟩, offender transfer, recognition, and ambient transport
are further source-assembly obligations, not conclusions of this file.
-/

@[expose] public section
open Subgroup Stellmacher Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
variable {G : Type*} [Group G]

theorem external_normalizes_span (H B V : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G))
    (hBV : B ≤ normalizer (V : Set G)) :
    B ≤ normalizer (conjugateSpanBy V H : Set G) := by
  apply le_normalizer_closure_iff.mpr
  rintro b hb x ⟨h,hh,v,hv,rfl⟩
  have hk : h⁻¹ * b * h ∈ B := by
    simpa using (mem_normalizer_iff.mp (hHB (H.inv_mem hh)) b).mp hb
  have hv' := (mem_normalizer_iff.mp (hBV hk) v).mp hv
  exact subset_closure ⟨h,hh,(h⁻¹*b*h)*v*(h⁻¹*b*h)⁻¹,hv',by group⟩

theorem span_le_external_core (H B V : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G)) (hV : V ≤ ambientTwoCore B) :
    conjugateSpanBy V H ≤ ambientTwoCore B :=
  conjugateSpanBy_le hV
    (hHB.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B)))

theorem external_span_elementary (H B V : Subgroup G) [IsElementaryAbelian 2 V]
    (hHB : H ≤ normalizer (B : Set G)) (hV : V ≤ ambientTwoCore B)
    (h0V : ambientTwoCore B ≤ centralizer (V : Set G)) :
    IsElementaryAbelian 2 (conjugateSpanBy V H) := by
  let : IsMulCommutative (conjugateSpanBy V H) :=
    le_centralizer_iff_isMulCommutative.mp
      ((span_le_external_core H B V hHB hV).trans
        (external_twoCore_centralizes_span H B V hHB h0V))
  let : IsMulCommutative (closure {x | ∃ h ∈ H, ∃ z ∈ V, h*z*h⁻¹ = x}) := inferInstanceAs (IsMulCommutative (conjugateSpanBy V H))
  apply IsElementaryAbelian.closure_of_isMulCommutative
  rintro x ⟨g,_,v,hv,rfl⟩
  rw [conj_pow,elemPow_eq_one_of_isElementaryAbelian v hv,mul_one,mul_inv_cancel]

theorem external_span_eq_commutator (H B V : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G))
    (hBV : B ≤ normalizer (V : Set G)) (hV : V = ⁅V,B⁆) :
    conjugateSpanBy V H = ⁅conjugateSpanBy V H,B⁆ := by
  have hn : H ≤ normalizer (⁅conjugateSpanBy V H,B⁆ : Subgroup G) := by
    intro h hh
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy V H hh),
      mem_normalizer_iff_map_conj_eq.mp (hHB hh)]
  apply le_antisymm
  · apply conjugateSpanBy_le _ hn
    exact hV.le.trans (commutator_mono (le_conjugateSpanBy V H) le_rfl)
  · exact le_normalizer_iff_commutator_le_left.mp (external_normalizes_span H B V hHB hBV)


private theorem cubic_elements {C : Type*} [Group C] [Finite C]
    (hc : Nat.card C = 3) (b : C) (hb : b ≠ 1) (c : C) :
    c = 1 ∨ c = b ∨ c = b ^ 2 := by
  classical
  have hord : orderOf b = 3 :=
    (orderOf_eq_card_of_zpowers_eq_top (zpowers_eq_top_of_prime_card hc hb)).trans hc
  have hm := (isOfFinOrder_of_finite b).mem_zpowers_iff_mem_range_orderOf.mp
    (mem_zpowers_of_prime_card hc hb (g' := c))
  rw [hord] at hm
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hm
  have hn' := Finset.mem_range.mp hn
  interval_cases n <;> simp_all

private theorem cubic_aut_nontrivial {C : Type*} [Group C] [Finite C]
    (hc : Nat.card C = 3) (a : MulAut C) (ha : a ≠ 1) :
    ∀ c : C, a c = c⁻¹ := by
  let := isCyclic_of_prime_card hc
  let : CommGroup C := IsMulCommutative.instCommGroup
  have hinv : (MulEquiv.inv C : MulAut C) ≠ 1 := by
    intro he
    have hp (c : C) : c ^ 2 = 1 := by
      have hh := congrArg (fun f : MulAut C => f c) he
      change c⁻¹ = c at hh
      calc
        c ^ 2 = c⁻¹ * c := by rw [pow_two,hh]
        _ = 1 := inv_mul_cancel c
    have hall (c : C) : c = 1 := by
      have h3 : c ^ 3 = 1 := by simpa only [hc] using (pow_card_eq_one' (x := c))
      have h := h3
      rw [show (3 : ℕ) = 2+1 from rfl,pow_succ,hp,one_mul] at h
      exact h
    have : Subsingleton C := ⟨fun c d => (hall c).trans (hall d).symm⟩
    have := Nat.card_unique (α := C)
    omega
  have hac : Nat.card (MulAut C) = 2 := by rw [IsCyclic.card_mulAut,hc]; decide
  have he := ((Nat.card_eq_two_iff' (1 : MulAut C)).mp hac).unique ha hinv
  intro c
  rw [he]
  rfl

private theorem cubic_polynomial {C X : Type*} [Group C] [Finite C]
    [AddCommGroup X] [Module (ZMod 2) X]
    (hc : Nat.card C = 3) (ρ : Representation (ZMod 2) C X)
    (hgen : BinaryOffender.subspaceCommutator ρ ⊤ ⊤ = ⊤)
    (b : C) (hb : b ≠ 1) : ρ b ^ 2 + ρ b + 1 = 0 := by
  let t := ρ b ^ 2 + ρ b + 1
  have h3 : ρ b ^ 3 = 1 := by
    rw [← map_pow,show b ^ 3 = 1 from by simpa only [hc] using (pow_card_eq_one' (x := b)),map_one]
  have ht : t * ρ b = t := by
    dsimp [t]
    calc
      (ρ b ^ 2 + ρ b + 1) * ρ b = ρ b ^ 3 + ρ b ^ 2 + ρ b := by noncomm_ring
      _ = ρ b ^ 2 + ρ b + 1 := by rw [h3]; abel
  have hall (c : C) : t * ρ c = t := by
    rcases cubic_elements hc b hb c with rfl | rfl | rfl
    · rw [map_one,mul_one]
    · exact ht
    · rw [map_pow,pow_two,← mul_assoc,ht,ht]
  have hk : BinaryOffender.subspaceCommutator ρ ⊤ ⊤ ≤ LinearMap.ker t := by
    apply Submodule.span_le.mpr
    rintro _ ⟨c,_,x,_,rfl⟩
    change t (ρ c x - x) = 0
    rw [map_sub,show t (ρ c x) = t x from LinearMap.congr_fun (hall c) x,sub_self]
  rw [hgen] at hk
  ext x
  exact hk Submodule.mem_top

/-- The actual external cubic action on U, descended only through B₀. -/
noncomputable def externalCubicAction (B U : Subgroup G) [IsElementaryAbelian 2 U]
    (hBU : B ≤ normalizer (U : Set G))
    (h0U : ambientTwoCore B ≤ centralizer (U : Set G)) :
    Representation (ZMod 2) (B ⧸ localTwoCore B) (Additive U) :=
  QuotientGroup.lift (localTwoCore B)
    (BinaryInternalFixedSpaceCodimension.representation U B hBU) (by
      intro b hb
      apply LinearMap.ext
      intro u
      apply Additive.toMul.injective
      apply Subtype.ext
      change (b : G) * (u.toMul : G) * (b : G)⁻¹ = u.toMul
      have hh := h0U hb u.toMul u.toMul.property
      change (u.toMul : G) * (b : G) = (b : G) * (u.toMul : G) at hh
      rw [← hh,mul_inv_cancel_right])

theorem externalCubicAction_apply (B U : Subgroup G) [IsElementaryAbelian 2 U]
    (hBU : B ≤ normalizer (U : Set G))
    (h0U : ambientTwoCore B ≤ centralizer (U : Set G)) (b : B) (u : Additive U) :
    ((externalCubicAction B U hBU h0U (QuotientGroup.mk' _ b) u).toMul : G) =
      (b : G) * (u.toMul : G) * (b : G)⁻¹ := rfl

/-- Commutator generation proves the cubic polynomial on the literal U. -/
theorem externalCubicAction_polynomial [Finite G]
    (B U : Subgroup G) [IsElementaryAbelian 2 U]
    (hBU : B ≤ normalizer (U : Set G))
    (h0U : ambientTwoCore B ≤ centralizer (U : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3) (hgen : U = ⁅U,B⁆)
    (b : B) (hb : b ∉ localTwoCore B) :
    externalCubicAction B U hBU h0U (QuotientGroup.mk' _ b) ^ 2 +
      externalCubicAction B U hBU h0U (QuotientGroup.mk' _ b) + 1 = 0 := by
  let ρ := externalCubicAction B U hBU h0U
  have hg := BinaryOffender.commutator_eq_top_of_conjugation ρ U B hBU
    (QuotientGroup.mk' (localTwoCore B)) (MonoidHom.id U) Function.surjective_id
    (fun b u => rfl) (by rw [commutator_comm]; exact hgen.symm)
  rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)] at hg
  exact cubic_polynomial hc ρ hg _ (fun he => hb ((QuotientGroup.eq_one_iff b).mp he))


/-- The ambient H-action on the actual elementary span. -/
noncomputable abbrev spanAction (H U : Subgroup G) [IsElementaryAbelian 2 U]
    (hHU : H ≤ normalizer (U : Set G)) : Representation (ZMod 2) H (Additive U) :=
  BinaryInternalFixedSpaceCodimension.representation U H hHU

theorem spanAction_eq_one_iff (H U : Subgroup G) [IsElementaryAbelian 2 U]
    (hHU : H ≤ normalizer (U : Set G)) (h : H) :
    spanAction H U hHU h = 1 ↔ (h : G) ∈ centralizer (U : Set G) := by
  constructor
  · intro he u hu
    have hh := congrArg (fun f : Module.End (ZMod 2) (Additive U) =>
      ((f (Additive.ofMul ⟨u,hu⟩)).toMul : G)) he
    change (h : G) * u * (h : G)⁻¹ = u at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro he
    apply LinearMap.ext
    intro u
    apply Additive.toMul.injective
    apply Subtype.ext
    change (h : G) * (u.toMul : G) * (h : G)⁻¹ = u.toMul
    rw [← he u.toMul u.toMul.property,mul_inv_cancel_right]

/-- The cubic and H-actions satisfy the literal character intertwining identity. -/
theorem externalCubicAction_intertwining (H B U : Subgroup G) [IsElementaryAbelian 2 U]
    (hHB : H ≤ normalizer (B : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hBU : B ≤ normalizer (U : Set G))
    (h0U : ambientTwoCore B ≤ centralizer (U : Set G))
    (h : H) (z : B ⧸ localTwoCore B) :
    spanAction H U hHU h * externalCubicAction B U hBU h0U z =
      externalCubicAction B U hBU h0U (quotientAction H B hHB h z) * spanAction H U hHU h := by
  obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective _ z
  rw [quotientAction_apply]
  apply LinearMap.ext
  intro u
  apply Additive.toMul.injective
  apply Subtype.ext
  change (h : G) * ((b : G) * (u.toMul : G) * (b : G)⁻¹) * (h : G)⁻¹ =
    ((h : G)*(b : G)*(h : G)⁻¹) * ((h : G)*(u.toMul : G)*(h : G)⁻¹) *
      ((h : G)*(b : G)*(h : G)⁻¹)⁻¹
  group

/-- The source kernel identity kills exactly the trivial-character core actors. -/
theorem coreAction_eq_one (H B U : Subgroup G) [IsElementaryAbelian 2 U]
    (hHB : H ≤ normalizer (B : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hN : ambientTwoCore H ⊓ characterKernel H B hHB = H ⊓ centralizer (U : Set G))
    (q : H) (hq : q ∈ localTwoCore H) (hχ : quotientAction H B hHB q = 1) :
    spanAction H U hHU q = 1 := by
  apply (spanAction_eq_one_iff H U hHU q).mpr
  exact (hN.le ⟨hq,mem_map.mpr ⟨q,hχ,rfl⟩⟩).2

/-- Core actors with the same character have the same action on U. -/
theorem coreAction_eq_of_character (H B U : Subgroup G) [IsElementaryAbelian 2 U]
    (hHB : H ≤ normalizer (B : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hN : ambientTwoCore H ⊓ characterKernel H B hHB = H ⊓ centralizer (U : Set G))
    (q r : H) (hq : q ∈ localTwoCore H) (hr : r ∈ localTwoCore H)
    (hχ : quotientAction H B hHB q = quotientAction H B hHB r) :
    spanAction H U hHU q = spanAction H U hHU r := by
  have he := coreAction_eq_one H B U hHB hHU hN (q⁻¹*r)
    ((localTwoCore H).mul_mem ((localTwoCore H).inv_mem hq) hr)
    (by rw [map_mul,map_inv,hχ,inv_mul_cancel])
  calc
    spanAction H U hHU q = spanAction H U hHU q * 1 := (mul_one _).symm
    _ = spanAction H U hHU q * spanAction H U hHU (q⁻¹*r) := by rw [he]
    _ = spanAction H U hHU r := by rw [← map_mul,mul_inv_cancel_left]

/-- The actual bad core element acts as an involution. -/
theorem coreAction_square [Finite G] (H B U : Subgroup G) [IsElementaryAbelian 2 U]
    (hHB : H ≤ normalizer (B : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hN : ambientTwoCore H ⊓ characterKernel H B hHB = H ⊓ centralizer (U : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3)
    (q : H) (hq : q ∈ localTwoCore H) :
    spanAction H U hHU q * spanAction H U hHU q = 1 := by
  rw [← map_mul]
  apply coreAction_eq_one H B U hHB hHU hN _ ((localTwoCore H).mul_mem hq hq)
  rw [map_mul,← pow_two]
  simpa only [ExternalQuotient.aut_card B hc] using
    (pow_card_eq_one' (x := quotientAction H B hHB q))

/-- A nontrivial core character inverts the actual cubic operator. -/
theorem coreAction_inverts_cubic [Finite G]
    (H B U : Subgroup G) [IsElementaryAbelian 2 U]
    (hHB : H ≤ normalizer (B : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hBU : B ≤ normalizer (U : Set G))
    (h0U : ambientTwoCore B ≤ centralizer (U : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3)
    (q : H) (hq : quotientAction H B hHB q ≠ 1) (b : B) :
    spanAction H U hHU q * externalCubicAction B U hBU h0U (QuotientGroup.mk' _ b) =
      externalCubicAction B U hBU h0U (QuotientGroup.mk' _ b) ^ 2 * spanAction H U hHU q := by
  rw [externalCubicAction_intertwining H B U hHB hHU hBU h0U,
    cubic_aut_nontrivial hc _ hq]
  have he (z : B ⧸ localTwoCore B) : z⁻¹ = z ^ 2 := by
    have h3 : z ^ 3 = 1 := by simpa only [hc] using (pow_card_eq_one' (x := z))
    apply (mul_left_cancel (a := z))
    rw [mul_inv_cancel,← pow_succ',h3]
  rw [he,map_pow]

/-- All H-operators commute with the core involution, since its character quotient is C₂. -/
theorem coreAction_commutes [Finite G]
    (H B U : Subgroup G) [IsElementaryAbelian 2 U]
    (hHB : H ≤ normalizer (B : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hN : ambientTwoCore H ⊓ characterKernel H B hHB = H ⊓ centralizer (U : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3)
    (q : H) (hq : q ∈ localTwoCore H) (h : H) :
    spanAction H U hHU h * spanAction H U hHU q =
      spanAction H U hHU q * spanAction H U hHU h := by
  let : IsCyclic (MulAut (B ⧸ localTwoCore B)) := isCyclic_of_prime_card (ExternalQuotient.aut_card B hc)
  let : CommGroup (MulAut (B ⧸ localTwoCore B)) := IsMulCommutative.instCommGroup
  have he := coreAction_eq_of_character H B U hHB hHU hN (h*q*h⁻¹) q
    ((inferInstance : (localTwoCore H).Normal).conj_mem q hq h) hq
    (by simp [mul_comm])
  calc
    spanAction H U hHU h * spanAction H U hHU q =
        spanAction H U hHU (h*q*h⁻¹) * spanAction H U hHU h := by
      rw [← map_mul,← map_mul]; congr 1; group
    _ = spanAction H U hHU q * spanAction H U hHU h := by rw [he]


/-- The literal Q-fixed subgroup of the ambient span. -/
abbrev coreFixed (H U : Subgroup G) : Subgroup G :=
  U ⊓ centralizer (ambientTwoCore H : Set G)

instance coreFixed_elementary (H U : Subgroup G) [IsElementaryAbelian 2 U] :
    IsElementaryAbelian 2 (coreFixed H U) := IsElementaryAbelian.of_le inf_le_left

/-- The H-action preserves the actual fixed subgroup. -/
theorem coreFixed_normalized (H U : Subgroup G)
    (hHU : H ≤ normalizer (U : Set G)) : H ≤ normalizer (coreFixed H U : Set G) := by
  have hQ : H ≤ normalizer (ambientTwoCore H : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hCQ : H ≤ normalizer (centralizer (ambientTwoCore H : Set G) : Set G) :=
    hQ.trans ((normal_subgroupOf_iff_le_normalizer
      (centralizer_le_normalizer (ambientTwoCore H : Set G))).mp inferInstance)
  exact (le_inf hHU hCQ).trans inf_normalizer_le_normalizer_inf

/-- The fixed space of the chosen bad actor is the fixed space of the whole core. -/
theorem coreFixed_iff_fixed [Finite G]
    (H B U : Subgroup G) [IsElementaryAbelian 2 U]
    (hHB : H ≤ normalizer (B : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hN : ambientTwoCore H ⊓ characterKernel H B hHB = H ⊓ centralizer (U : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3)
    (q : H) (hq : q ∈ localTwoCore H) (hqχ : quotientAction H B hHB q ≠ 1)
    (u : Additive U) : (u.toMul : G) ∈ coreFixed H U ↔ spanAction H U hHU q u = u := by
  constructor
  · intro hu
    apply Additive.toMul.injective
    apply Subtype.ext
    change (q : G) * (u.toMul : G) * (q : G)⁻¹ = u.toMul
    rw [hu.2 q hq,mul_inv_cancel_right]
  · intro hu
    refine ⟨u.toMul.property,?_⟩
    intro r hr
    let rH : H := ⟨r,pCoreIn_le 2 H hr⟩
    have he : spanAction H U hHU rH u = u := by
      by_cases hrχ : quotientAction H B hHB rH = 1
      · rw [coreAction_eq_one H B U hHB hHU hN rH hr hrχ]; rfl
      · have hχ := ((Nat.card_eq_two_iff' (1 : MulAut (B ⧸ localTwoCore B))).mp
          (ExternalQuotient.aut_card B hc)).unique hrχ hqχ
        rw [coreAction_eq_of_character H B U hHB hHU hN rH q hr hq hχ]
        exact hu
    have he' := congrArg (fun w : Additive U => (w.toMul : G)) he
    change r * (u.toMul : G) * r⁻¹ = u.toMul at he'
    exact mul_inv_eq_iff_eq_mul.mp he'

/-- In the character kernel, fixation of W forces fixation of both cubic summands. -/
theorem character_fixed_centralizes_span [Finite G]
    (H B U : Subgroup G) [IsElementaryAbelian 2 U]
    (hHB : H ≤ normalizer (B : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hBU : B ≤ normalizer (U : Set G))
    (h0U : ambientTwoCore B ≤ centralizer (U : Set G))
    (hN : ambientTwoCore H ⊓ characterKernel H B hHB = H ⊓ centralizer (U : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3) (hgen : U = ⁅U,B⁆)
    (q : H) (hq : q ∈ localTwoCore H) (hqχ : quotientAction H B hHB q ≠ 1)
    (b : B) (hb : b ∉ localTwoCore B)
    (h : H) (hχ : quotientAction H B hHB h = 1)
    (hw : (h : G) ∈ centralizer (coreFixed H U : Set G)) :
    (h : G) ∈ centralizer (U : Set G) := by
  let β := externalCubicAction B U hBU h0U (QuotientGroup.mk' _ b)
  let τ := spanAction H U hHU q
  have hβ := externalCubicAction_polynomial B U hBU h0U hc hgen b hb
  have hτ := coreAction_square H B U hHB hHU hN hc q hq
  have hi := coreAction_inverts_cubic H B U hHB hHU hBU h0U hc q hqχ b
  apply (spanAction_eq_one_iff H U hHU h).mp
  apply commuting_operator_ext β τ _ 1 hβ hτ hi
  · simpa only [hχ,MulAut.one_apply] using
      externalCubicAction_intertwining H B U hHB hHU hBU h0U h (QuotientGroup.mk' _ b)
  · simp
  · intro u hu
    have huf := (coreFixed_iff_fixed H B U hHB hHU hN hc q hq hqχ u).mpr hu
    apply Additive.toMul.injective
    apply Subtype.ext
    change (h : G) * (u.toMul : G) * (h : G)⁻¹ = u.toMul
    rw [← hw u.toMul huf,mul_inv_cancel_right]

/-- The faithful quotient is exactly H/Q, established on the constructed W. -/
theorem coreFixed_centralizer [Finite G]
    (H B U : Subgroup G) [IsElementaryAbelian 2 U]
    (hHB : H ≤ normalizer (B : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hBU : B ≤ normalizer (U : Set G))
    (h0U : ambientTwoCore B ≤ centralizer (U : Set G))
    (hN : ambientTwoCore H ⊓ characterKernel H B hHB = H ⊓ centralizer (U : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3) (hgen : U = ⁅U,B⁆)
    (q : H) (hq : q ∈ localTwoCore H) (hqχ : quotientAction H B hHB q ≠ 1)
    (b : B) (hb : b ∉ localTwoCore B) :
    H ⊓ centralizer (coreFixed H U : Set G) = ambientTwoCore H := by
  have hQW : ambientTwoCore H ≤ centralizer (coreFixed H U : Set G) :=
    le_centralizer_iff.mp inf_le_right
  apply le_antisymm
  · rintro h ⟨hh,hw⟩
    let hH : H := ⟨h,hh⟩
    have hle (r : H) (hrχ : quotientAction H B hHB r = 1)
        (hrw : (r : G) ∈ centralizer (coreFixed H U : Set G)) : (r : G) ∈ ambientTwoCore H := by
      have hr := character_fixed_centralizes_span H B U hHB hHU hBU h0U hN hc hgen
        q hq hqχ b hb r hrχ hrw
      exact (hN.ge ⟨r.property,hr⟩).1
    by_cases hχ : quotientAction H B hHB hH = 1
    · exact hle hH hχ hw
    · have hχq := ((Nat.card_eq_two_iff' (1 : MulAut (B ⧸ localTwoCore B))).mp
        (ExternalQuotient.aut_card B hc)).unique hχ hqχ
      have hk : ((q⁻¹*hH : H) : G) ∈ ambientTwoCore H := hle (q⁻¹*hH)
        (by rw [map_mul,map_inv,hχq,inv_mul_cancel])
        ((centralizer (coreFixed H U : Set G)).mul_mem
          ((centralizer (coreFixed H U : Set G)).inv_mem (hQW hq)) hw)
      have hm := (ambientTwoCore H).mul_mem hq hk
      change (q : G) * ((q : G)⁻¹ * h) ∈ ambientTwoCore H at hm
      simpa only [mul_inv_cancel_left] using hm
  · exact le_inf (pCoreIn_le 2 H) hQW


/-- The fixed-subgroup coordinates identify the actual W with the operator fixed space. -/
noncomputable def coreFixedEquiv [Finite G]
    (H B U : Subgroup G) [IsElementaryAbelian 2 U]
    (hHB : H ≤ normalizer (B : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hN : ambientTwoCore H ⊓ characterKernel H B hHB = H ⊓ centralizer (U : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3)
    (q : H) (hq : q ∈ localTwoCore H) (hqχ : quotientAction H B hHB q ≠ 1) :
    Additive (coreFixed H U) ≃ₗ[ZMod 2] LinearMap.ker (spanAction H U hHU q - 1) := by
  let e : Additive (coreFixed H U) ≃+ LinearMap.ker (spanAction H U hHU q - 1) := {
    toFun w := ⟨Additive.ofMul ⟨w.toMul,w.toMul.property.1⟩,by
      change spanAction H U hHU q (Additive.ofMul ⟨w.toMul,w.toMul.property.1⟩) -
        Additive.ofMul ⟨w.toMul,w.toMul.property.1⟩ = 0
      exact sub_eq_zero.mpr ((coreFixed_iff_fixed H B U hHB hHU hN hc q hq hqχ _).mp w.toMul.property)⟩
    invFun w := Additive.ofMul ⟨w.val.toMul,
      (coreFixed_iff_fixed H B U hHB hHU hN hc q hq hqχ w.val).mpr (sub_eq_zero.mp w.property)⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl }
  exact e.toLinearEquiv (fun c x => ZMod.map_smul e.toAddMonoidHom c x)

/-- The two actual conjugate summands give coordinates on U in arbitrary dimension. -/
noncomputable def coreFixedPairEquiv [Finite G]
    (H B U : Subgroup G) [IsElementaryAbelian 2 U]
    (hHB : H ≤ normalizer (B : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hBU : B ≤ normalizer (U : Set G))
    (h0U : ambientTwoCore B ≤ centralizer (U : Set G))
    (hN : ambientTwoCore H ⊓ characterKernel H B hHB = H ⊓ centralizer (U : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3) (hgen : U = ⁅U,B⁆)
    (q : H) (hq : q ∈ localTwoCore H) (hqχ : quotientAction H B hHB q ≠ 1)
    (b : B) (hb : b ∉ localTwoCore B) :
    (Additive (coreFixed H U) × Additive (coreFixed H U)) ≃ₗ[ZMod 2] Additive U :=
  ((coreFixedEquiv H B U hHB hHU hN hc q hq hqχ).prodCongr
    (coreFixedEquiv H B U hHB hHU hN hc q hq hqχ)).trans
    (fixedPairEquiv (externalCubicAction B U hBU h0U (QuotientGroup.mk' _ b))
      (spanAction H U hHU q) (externalCubicAction_polynomial B U hBU h0U hc hgen b hb)
      (coreAction_square H B U hHB hHU hN hc q hq)
      (coreAction_inverts_cubic H B U hHB hHU hBU h0U hc q hqχ b))

/-- The splitting uses the literal conjugation by the chosen cubic lift. -/
theorem coreFixedPairEquiv_apply [Finite G]
    (H B U : Subgroup G) [IsElementaryAbelian 2 U]
    (hHB : H ≤ normalizer (B : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hBU : B ≤ normalizer (U : Set G))
    (h0U : ambientTwoCore B ≤ centralizer (U : Set G))
    (hN : ambientTwoCore H ⊓ characterKernel H B hHB = H ⊓ centralizer (U : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3) (hgen : U = ⁅U,B⁆)
    (q : H) (hq : q ∈ localTwoCore H) (hqχ : quotientAction H B hHB q ≠ 1)
    (b : B) (hb : b ∉ localTwoCore B) (w v : Additive (coreFixed H U)) :
    ((coreFixedPairEquiv H B U hHB hHU hBU h0U hN hc hgen q hq hqχ b hb (w,v)).toMul : G) =
      (w.toMul : G) * ((b : G) * (v.toMul : G) * (b : G)⁻¹) := rfl

/-- Descend actual conjugation through precisely the two-core quotient. -/
noncomputable def coreQuotientAction (H W : Subgroup G) [IsElementaryAbelian 2 W]
    (hHW : H ≤ normalizer (W : Set G))
    (hC : H ⊓ centralizer (W : Set G) = ambientTwoCore H) :
    Representation (ZMod 2) (H ⧸ pCore 2 H) (Additive W) :=
  QuotientGroup.lift (pCore 2 H) (spanAction H W hHW) (by
    intro h hh
    exact (spanAction_eq_one_iff H W hHW h).mpr
      (hC.ge (mem_map.mpr ⟨h,hh,rfl⟩)).2)

/-- The quotient action retains its representative formula. -/
theorem coreQuotientAction_apply (H W : Subgroup G) [IsElementaryAbelian 2 W]
    (hHW : H ≤ normalizer (W : Set G))
    (hC : H ⊓ centralizer (W : Set G) = ambientTwoCore H) (h : H) (w : Additive W) :
    ((coreQuotientAction H W hHW hC (QuotientGroup.mk' _ h) w).toMul : G) =
      (h : G) * (w.toMul : G) * (h : G)⁻¹ := rfl

/-- The constructed representation of the literal quotient H/Q is faithful. -/
theorem coreQuotientAction_injective (H W : Subgroup G) [IsElementaryAbelian 2 W]
    (hHW : H ≤ normalizer (W : Set G))
    (hC : H ⊓ centralizer (W : Set G) = ambientTwoCore H) :
    Function.Injective (coreQuotientAction H W hHW hC) := by
  apply (coreQuotientAction H W hHW hC).ker_eq_bot_iff.mp
  apply le_bot_iff.mp
  intro x hx
  obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective _ x
  apply (QuotientGroup.eq_one_iff h).mpr
  have hcen := (spanAction_eq_one_iff H W hHW h).mp hx
  have hm := hC.le ⟨h.property,hcen⟩
  obtain ⟨k,hk,he⟩ := hm
  exact (Subtype.ext he : k = h) ▸ hk

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
