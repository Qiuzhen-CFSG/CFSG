module
public import Theory.GroupTheory.PGroup.Supercritical
public import Theory.GroupTheory.TwoFixedLinesIrreducible
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.PResidual.NormalizedImageLift
public import Theory.GroupTheory.PCoreActionSplitting
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms

/-!
# Cubic centralizers and prime roots of supercritical subgroups

An order-three subgroup outside a supercritical subgroup has a nontrivial
proper centralizer there. For supercritical subgroups of order nine or
27 this centralizer is elementary abelian, of order three or nine, and
its full normalizer is controlled by the normalizer of the acting cubic.
The normalized lift theorem retains the whole two-group kernel and the
intrinsic two-core of the lifted subgroup.

For an extraspecial supercritical subgroup, every ambient prime-order
root already lies inside it. The ambient conjugation action has central
displacement, so extraspecial commutator duality realizes it by an inner
automorphism. Removing this inner action gives a commuting prime-order
root, which belongs to the supercritical subgroup by definition.

Source: Aschbacher–Smith, A.1.20–23, printed pp.24–25, and the final
centralizer step in 14.7.27, printed pp.1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace IsSupercriticalPSubgroup
variable {D : Type*} [Group D] [Finite D]
  (P : Subgroup D) [P.Normal] (hP : IsPGroup 3 P)
  (X : Subgroup P) (hX : IsSupercriticalPSubgroup 3 X)
  (B : Subgroup D) (hBP : B ≤ P) (hB : Nat.card B = 3)

include hP hX hBP hB

/-- An outside cubic has a nontrivial proper centralizer in the supercritical subgroup. -/
theorem cubic_centralizer_proper
    (hXne : X ≠ ⊥) (hout : ¬ B ≤ X.map P.subtype) :
    X.map P.subtype ⊓ centralizer (B : Set D) ≠ ⊥ ∧
    X.map P.subtype ⊓ centralizer (B : Set D) < X.map P.subtype ∧
    normalizer (B : Set D) ≤
      normalizer (X.map P.subtype ⊓ centralizer (B : Set D) : Set D) := by
  let : X.Characteristic := hX.characteristic
  let Z := X.map P.subtype
  let : Z.Normal := inferInstance
  have hZne : Z ≠ ⊥ := by
    intro hz
    exact hXne ((map_injective P.subtype_injective) (by simpa using hz))
  have hn : B ≤ normalizer (Z : Set D) := le_normalizer_of_normal
  have hc := inf_centralizer_ne_bot_of_pGroups B Z
    (IsPGroup.of_card (n := 1) (by simpa using hB)) ((hP.to_subgroup X).map P.subtype) hn hZne
  refine ⟨hc,lt_of_le_of_ne inf_le_left ?_,?_⟩
  · intro he
    have hZC : Z ≤ centralizer (B : Set D) := he.ge.trans inf_le_right
    have hBZ : B ≤ centralizer (Z : Set D) := le_centralizer_iff.mp hZC
    apply hout
    intro b hb
    by_cases hb1 : b = 1
    · simpa only [hb1] using Z.one_mem
    have ho : orderOf b = 3 := by
      have hd : orderOf b ∣ 3 := by
        rw [←hB,orderOf_coe (⟨b,hb⟩ : B)]
        exact orderOf_dvd_natCard _
      exact (Nat.dvd_prime Nat.prime_three).mp hd |>.resolve_left
        (fun h1 => hb1 (orderOf_eq_one_iff.mp h1))
    have hbX : (⟨b,hBP hb⟩ : P) ∈ X := hX.order_p_mem _ (by
      intro x hx
      apply Subtype.ext
      exact hBZ hb x (mem_map_of_mem P.subtype hx)) (by
        exact (Subgroup.orderOf_coe _).symm.trans ho)
    exact mem_map_of_mem P.subtype hbX
  · exact (le_inf le_normalizer_of_normal (normalizer_le_normalizer_centralizer B)).trans
      inf_normalizer_le_normalizer_inf

/-- In orders nine and 27 the proper fixed subgroup is elementary of order three or nine. -/
theorem cubic_centralizer_elementary
    (hcard : Nat.card X = 9 ∨ Nat.card X = 27)
    (hout : ¬ B ≤ X.map P.subtype) :
    IsElementaryAbelian 3 (X.map P.subtype ⊓ centralizer (B : Set D) : Subgroup D) ∧
      (Nat.card (X.map P.subtype ⊓ centralizer (B : Set D) : Subgroup D) = 3 ∨
        Nat.card (X.map P.subtype ⊓ centralizer (B : Set D) : Subgroup D) = 9) := by
  let C := X.map P.subtype ⊓ centralizer (B : Set D)
  have hXne : X ≠ ⊥ := by
    intro he
    simp only [he,card_bot] at hcard
    omega
  obtain ⟨hne,hlt,_⟩ := hX.cubic_centralizer_proper P hP X B hBP hB hXne hout
  have hbound : Nat.card C < 27 := by
    have hh : Nat.card C < Nat.card (X.map P.subtype) :=
      lt_of_not_ge (fun hh => hlt.ne (eq_of_le_of_card_ge hlt.le hh))
    rw [card_map_of_injective P.subtype_injective] at hh
    rcases hcard with hcard | hcard <;> omega
  have hp : IsPGroup 3 C := ((hP.to_subgroup X).map P.subtype).to_le inf_le_left
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hnlt : n < 3 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 3)).mp
    (show 3 ^ n < 3 ^ 3 by simpa only [hn] using hbound)
  have hn0 : n ≠ 0 := by
    intro hz
    exact hne (Subgroup.card_eq_one.mp (by simpa only [hz,pow_zero] using hn))
  have hc : Nat.card C = 3 ∨ Nat.card C = 9 := by
    rcases (show n = 1 ∨ n = 2 by omega) with hn1 | hn2
    · exact Or.inl (by simpa only [hn1,pow_one] using hn)
    · exact Or.inr (by simpa only [hn2, Nat.reducePow] using hn)
  have hcomm : IsMulCommutative C := by
    rcases hc with h3 | h9
    · let : IsCyclic C := isCyclic_of_card_dvd_prime (p := 3) (by rw [h3])
      infer_instance
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) h9
  refine ⟨{ toIsMulCommutative := hcomm, exponent_dvd_p := ?_ },hc⟩
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro c
  obtain ⟨x,hx,he⟩ := c.property.1
  apply Subtype.ext
  change (c : D) ^ 3 = 1
  rw [←he]
  exact congrArg (fun a : X => ((a : P) : D)) (hX.pow_eq_one ⟨x,hx⟩)

end IsSupercriticalPSubgroup

namespace Subgroup
variable {D E : Type*} [Group D] [Finite D] [Group E] [Finite E]

/-- Lift a normalized three-subgroup inside a prescribed normal subgroup, with the full two-core kernel. -/
theorem exists_three_lift_within_normal
    (q : D →* E) (hk : IsPGroup 2 q.ker)
    (Y : Subgroup D) [Y.Normal] (C A : Subgroup E)
    (hCY : C ≤ Y.map q) (hAC : A ≤ normalizer (C : Set E))
    (hC : IsPGroup 3 C) :
    ∃ W : Subgroup D, W ≤ Y ∧ IsPPerfect 2 W ∧ W.map q = C ∧
      A.comap q ≤ normalizer (W : Set D) ∧
      q.ker ≤ normalizer (W : Set D) ∧
      (q.comp W.subtype).ker = pCore 2 W ∧
      Nonempty ((W ⧸ pCore 2 W) ≃* C) := by
  have hp : IsPPerfect 2 C := by
    apply (pResidual_eq_top_iff 2 C).mp
    apply top_unique
    intro x _
    obtain ⟨n,hn⟩ := hC.exists_card_eq
    exact mem_pResidual_of_orderOf_coprime
      (((by decide : Nat.Coprime 2 3).pow_right n).of_dvd_right
        (hn ▸ _root_.orderOf_dvd_natCard x))
  obtain ⟨W,hWY,hWp,hWm,hWA⟩ :=
    exists_pPerfect_lift_within_normal q Y C A hCY hAC hp
  let f := q.comp W.subtype
  have hr : f.range = C := by rw [MonoidHom.range_comp,range_subtype,hWm]
  have hfp : IsPGroup 2 f.ker := hk.comap_of_injective _ W.subtype_injective
  have hfr : IsPGroup 3 f.range := hr.symm ▸ hC
  have hz : pCore 2 f.range = ⊥ :=
    bot_unique ((le_inf le_rfl le_top).trans
      (pCore_isPGroup.disjoint_of_coprime (hfr.to_subgroup ⊤)
        (by decide : Nat.Coprime 2 3)).le_bot)
  have hf := f.ker_eq_pCore_of_range_core_eq_bot 2 hfp hz
  refine ⟨W,hWY,hWp,hWm,hWA,?_,hf,?_⟩
  · apply le_trans ?_ hWA
    intro x hx
    change q x ∈ A
    rw [show q x = 1 from hx]
    exact A.one_mem
  · exact ⟨(QuotientGroup.quotientMulEquivOfEq hf.symm).trans
      ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hr))⟩
end Subgroup

namespace IsSupercriticalPSubgroup
open scoped commutatorElement
variable {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
  {X : Subgroup P}

/-- An extraspecial supercritical subgroup contains every ambient prime-order root. -/
theorem prime_root_mem_of_extraspecial (hX : IsSupercriticalPSubgroup p X)
    [IsExtraspecial p X] (b : P) (hb : b ^ p = 1) : b ∈ X := by
  let : X.Characteristic := hX.characteristic
  let α : MulAut X := MulAut.conjNormal b
  have hα : ∀ x : X, α x * x⁻¹ ∈ center X := by
    intro x
    have hcomm : ⁅(⊤ : Subgroup P),X⁆ ≤ (center X).map X.subtype := by
      rw [commutator_comm]
      exact hX.commutator_le
    obtain ⟨z,hz,he⟩ := hcomm (commutator_mem_commutator (mem_top b) x.property)
    have he' : z = α x * x⁻¹ := Subtype.ext he
    exact he' ▸ hz
  obtain ⟨r,hr⟩ := IsExtraspecial.exists_conj_of_central_displacement (p := p) α hα
  have hbr : Commute b (r : P) := by
    have hh := congrArg Subtype.val (DFunLike.congr_fun hr r)
    change (r : P) * r * (r : P)⁻¹ = b * r * b⁻¹ at hh
    have he : b * (r : P) * b⁻¹ = r := by simpa using hh.symm
    exact mul_inv_eq_iff_eq_mul.mp he
  have hcent : (r : P)⁻¹ * b ∈ centralizer (X : Set P) := by
    intro x hx
    have hh := congrArg Subtype.val (DFunLike.congr_fun hr (⟨x,hx⟩ : X))
    change (r : P) * x * (r : P)⁻¹ = b * x * b⁻¹ at hh
    calc
      x * ((r : P)⁻¹ * b) = (r : P)⁻¹ * ((r : P) * x * (r : P)⁻¹) * b := by group
      _ = (r : P)⁻¹ * (b * x * b⁻¹) * b := by rw [hh]
      _ = ((r : P)⁻¹ * b) * x := by group
  have hroot : ((r : P)⁻¹ * b) ^ p = 1 := by
    rw [hbr.symm.inv_left.mul_pow,inv_pow,hb]
    have hrp : (r : P) ^ p = 1 := congrArg Subtype.val (hX.pow_eq_one r)
    rw [hrp,inv_one,one_mul]
  have hmem : (r : P)⁻¹ * b ∈ X := by
    by_cases he : (r : P)⁻¹ * b = 1
    · exact he ▸ X.one_mem
    · exact hX.order_p_mem _ hcent (orderOf_eq_prime_iff.mpr ⟨hroot,he⟩)
  have hh := X.mul_mem r.property hmem
  simpa only [mul_inv_cancel_left] using hh

/-- An extraspecial supercritical subgroup is exactly the ambient first omega subgroup. -/
theorem omega_one_eq_of_extraspecial (hX : IsSupercriticalPSubgroup p X)
    [IsExtraspecial p X] : omega₁ P (p := p) = X := by
  apply le_antisymm
  · apply (closure_le X).mpr
    intro x hx
    change x ^ (p ^ 1) = 1 at hx
    exact hX.prime_root_mem_of_extraspecial x (by simpa only [pow_one] using hx)
  · intro x hx
    apply subset_closure
    change x ^ (p ^ 1) = 1
    simpa only [pow_one,coe_pow,coe_one] using congrArg Subtype.val (hX.pow_eq_one ⟨x,hx⟩)

end IsSupercriticalPSubgroup
