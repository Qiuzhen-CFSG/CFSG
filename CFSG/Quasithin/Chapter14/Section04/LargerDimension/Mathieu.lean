module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension
public import Theory.Representation.BinaryOffender.CubicInversionContainment
public import Theory.ElementaryAbelian.ExtraspecialNormalCommutator

/-!
# Quotient and moved-space steps for the Mathieu branch

The carrier in case 14.4.2(6) is the nonsplit triple cover of M₂₂ extended by
an outer involution. The legacy name `TwoM22Output` is preserved, but is not a
description of a double central cover or a proof of Lemma 14.4.12.

This module defines the literal first residual actor and proves three steps of
the source argument: lifting an order-four moved image through its central line,
excluding the Borel residual when it centralizes the quotient point, and placing
the second moved space in E using an inverting actor on the quotient module.
It also assembles the literal Y-family once the three-actor catalogue and the
remaining model calculations have been established. Those calculations, actor
distinctness, and the line-stabilizer quotient are still separate obligations;
this module does not yet prove the full source lemma.

Source: Aschbacher--Smith, Lemma 14.4.12, printed pp.1011--1012, with case
14.4.2(6) on p.1006 and H.12.1 on pp.393--394 (1 March 2004 manuscript).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu

open Subgroup Representation.BinaryOffender

universe u v
variable {G : Type u} [Group G]

/-- The actual `O₂,₃(H)`: pull back the three-core after quotienting by the
intrinsic two-core, then embed in the original ambient group. -/
def twoThreeCore (H : Subgroup G) : Subgroup G :=
  ((pCore 3 (H ⧸ pCore 2 H)).comap (QuotientGroup.mk' (pCore 2 H))).map H.subtype

/-- The actor called `X₁` in 14.4.12, with both residual and core conventions
retained. Membership in the source family still requires proof. -/
def firstActor (H : Subgroup G) : Subgroup G := twoResidual (twoThreeCore H)

/-- The Borel actor is the two-residual of its actual preimage in H. -/
def borelActor (B : Subgroup G) : Subgroup G := twoResidual B

/-- The central kernel contributes the additional factor two in the source's
passage from a binary plane in U/Z(U) to a moved subgroup of order eight. -/
theorem movedSpace_card_eight_of_quotient
    {Q : Type v} [Group Q] (U V₂ X : Subgroup G) (q : U →* Q)
    (hVU : movedSpace V₂ X ≤ U)
    (hker : q.ker ≤ (movedSpace V₂ X).subgroupOf U)
    (hker_card : Nat.card q.ker = 2)
    (himage : Nat.card (((movedSpace V₂ X).subgroupOf U).map q) = 4) :
    Nat.card (movedSpace V₂ X) = 8 := by
  have h := relIndex_mul_relIndex (⊥ : Subgroup U) q.ker
    ((movedSpace V₂ X).subgroupOf U) bot_le hker
  rw [relIndex_bot_left, relIndex_bot_left, relIndex_ker, hker_card, himage] at h
  have hcard : Nat.card ((movedSpace V₂ X).subgroupOf U) =
      Nat.card (movedSpace V₂ X) := by
    rw [← card_map_of_injective (K := (movedSpace V₂ X).subgroupOf U) U.subtype_injective,
      map_subgroupOf_eq_of_le hVU]
  rw [hcard] at h
  exact h.symm

/-- For a source X-actor the central-kernel premise in the preceding lift is
automatic. The T-invariance of X gives U-invariance, and a nonzero moved image
then forces Z(U) into the actual commutator. Thus a quotient plane really lifts
to order eight, rather than merely specifying a plane in U/Z(U). -/
theorem movedSpace_card_eight_of_extraspecial_image [Finite G]
    {Q : Type v} [Group Q] (H T U V₂ X : Subgroup G) [IsExtraspecial 2 U]
    (hX : X ∈ XFamily H T) (hUT : U ≤ T)
    (hHU : H ≤ normalizer (U : Set G)) (hVU : V₂ ≤ U)
    (hZV : center U ≤ V₂.subgroupOf U)
    (q : U →* Q) (hker : q.ker = center U)
    (himage : Nat.card (((movedSpace V₂ X).subgroupOf U).map q) = 4) :
    Nat.card (movedSpace V₂ X) = 8 := by
  have hXU := hX.le_H.trans hHU
  have hMU : movedSpace V₂ X ≤ U :=
    (commutator_mono hVU le_rfl).trans (le_normalizer_iff_commutator_le_left.mp hXU)
  have hne : ((movedSpace V₂ X).subgroupOf U).map q ≠ ⊥ := by
    intro hb
    rw [hb, card_bot] at himage
    omega
  apply movedSpace_card_eight_of_quotient U V₂ X q hMU
  · rw [hker]
    exact extraspecial_center_le_commutator_of_image_ne_bot U V₂ X hVU hZV
      (hUT.trans hX.T_normalizes) q hne
  · rw [hker, IsExtraspecial.center_order_p 2 U]
  · exact himage

/-- Centralizing the image of V₂ in a quotient of H with a small kernel
excludes the actual ambient actor from Y. The quotient is relative to H;
neither its kernel nor H is required to be normal in G. -/
theorem not_mem_YFamily_of_quotient_centralizes [Finite G]
    {Q : Type v} [Group Q] (H T V₂ E X : Subgroup G) (q : H →* Q)
    (hVH : V₂ ≤ H) (hXH : X ≤ H) (hsmall : Nat.card q.ker < 8)
    (hfix : (X.subgroupOf H).map q ≤
      centralizer ((V₂.subgroupOf H).map q : Set Q)) :
    X ∉ YFamily H T V₂ E := by
  have hmap : (⁅V₂.subgroupOf H, X.subgroupOf H⁆).map q = ⊥ := by
    rw [map_commutator, commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hfix
  have hcard := Subgroup.card_le_of_le ((Subgroup.map_eq_bot_iff _).mp hmap)
  have hlift : (⁅V₂.subgroupOf H, X.subgroupOf H⁆).map H.subtype =
      movedSpace V₂ X := by
    rw [map_commutator, map_subgroupOf_eq_of_le hVH, map_subgroupOf_eq_of_le hXH]
    rfl
  rw [← card_map_of_injective
    (K := ⁅V₂.subgroupOf H, X.subgroupOf H⁆) H.subtype_injective, hlift] at hcard
  intro hY
  have heq := hY.2.1
  omega

open scoped IsMulCommutative

/-- The Borel residual is excluded using the actual action on U/Z(U). This
requires only centralization of the quotient point; centralization of V₂ in
the original extraspecial group is not asserted. -/
theorem not_mem_YFamily_of_fixed_quotient_point [Finite G]
    {D Q : Type*} [Group D] [Group Q] [IsMulCommutative Q]
    [Module (ZMod 2) (Additive Q)]
    (ρ : Representation (ZMod 2) D (Additive Q))
    (H T U V₂ E X₃ : Subgroup G)
    (hn : X₃ ≤ normalizer (U : Set G)) (hVU : V₂ ≤ U)
    (f : X₃ →* D) (q : U →* Q)
    (hact : ∀ (a : X₃) (u : U), ρ (f a) (Additive.ofMul (q u)) =
      Additive.ofMul (q ⟨(a : G) * u * (a : G)⁻¹,
        le_normalizer_iff.mp hn a a.property u u.property⟩))
    (Pbar : Submodule (ZMod 2) (Additive Q))
    (hP : ∀ u : U, (u : G) ∈ V₂ → Additive.ofMul (q u) ∈ Pbar)
    (hsmall : Nat.card q.ker < 8)
    (hfix : Pbar ≤ fixedSpace ρ f.range) : X₃ ∉ YFamily H T V₂ E := by
  let K := q.ker.map U.subtype
  have hKU : K.subgroupOf U = q.ker :=
    Subgroup.comap_map_eq_self_of_injective U.subtype_injective _
  have hE : Subgroup.toAddSubgroup.symm
      (⊥ : Submodule (ZMod 2) (Additive Q)).toAddSubgroup = (K.subgroupOf U).map q := by
    rw [hKU, (Subgroup.map_eq_bot_iff _).mpr le_rfl]
    rfl
  have hcomm := (subspaceCommutator_eq_bot_iff ρ Pbar f.range).mpr hfix
  have hle : movedSpace V₂ X₃ ≤ K :=
    commutator_le_of_conjugation_image ρ U V₂ X₃ K hn hVU f q hact
      Pbar ⊥ hP hE (by rw [hKU]) (by rw [hcomm])
  have hcard := Subgroup.card_le_of_le hle
  change Nat.card (movedSpace V₂ X₃) ≤ Nat.card (q.ker.map U.subtype) at hcard
  rw [card_map_of_injective U.subtype_injective] at hcard
  intro hY
  have heq := hY.2.1
  omega

/-- The last paragraph's second-actor argument on a literal conjugation
quotient. `hWE` is the earlier 12.8.11(1) bound after total singularity has
placed the D-module in W. In particular, commuting is asserted on the action
image, as in the source's `x⁺` centralizing `X₂⁺`. -/
theorem second_movedSpace_le_of_cubic_inversion
    {D Q : Type*} [Group D] [Group Q] [IsMulCommutative Q]
    [Module (ZMod 2) (Additive Q)]
    (ρ : Representation (ZMod 2) D (Additive Q)) (U V₂ X₂ E : Subgroup G)
    (hn : X₂ ≤ normalizer (U : Set G)) (hVU : V₂ ≤ U)
    (f : X₂ →* D) (q : U →* Q)
    (hact : ∀ (a : X₂) (u : U), ρ (f a) (Additive.ofMul (q u)) =
      Additive.ofMul (q ⟨(a : G) * u * (a : G)⁻¹,
        le_normalizer_iff.mp hn a a.property u u.property⟩))
    (Pbar Ebar : Submodule (ZMod 2) (Additive Q))
    (hP : ∀ u : U, (u : G) ∈ V₂ → Additive.ofMul (q u) ∈ Pbar)
    (hE : Subgroup.toAddSubgroup.symm Ebar.toAddSubgroup = (E.subgroupOf U).map q)
    (hker : q.ker ≤ E.subgroupOf U)
    (W : Subgroup D) (c x : D)
    (hc : (ρ c) ^ 3 = 1) (hfree : ∀ v, ρ c v = v → v = 0)
    (hx : ρ x * ρ x = 1) (hxc : ρ x * ρ c = (ρ c) ^ 2 * ρ x)
    (hPx : ∀ v ∈ Pbar, ρ x v = v)
    (hX : ∀ a ∈ f.range, Commute (ρ x) (ρ a)) (hxW : x ∈ W)
    (hWE : subspaceCommutator ρ ⊤ W ≤ Ebar) : movedSpace V₂ X₂ ≤ E := by
  exact commutator_le_of_conjugation_image ρ U V₂ X₂ E hn hVU f q hact
    Pbar Ebar hP hE hker
    ((subspaceCommutator_le_of_cubic_inversion ρ Pbar f.range W c x
      hc hfree hx hxc hPx hX hxW).trans hWE)

/-- Once all three residual actors have been classified, the two calculated
moved spaces and exclusion of the Borel actor give the literal family equality.
This is an assembly lemma, not a substitute for the model catalogue. -/
theorem yFamily_eq_pair_of_three_actor_calculation
    (H T V₂ E X₁ X₂ X₃ : Subgroup G)
    (hcatalogue : XFamily H T = {X₁, X₂, X₃})
    (h₁ : Nat.card (movedSpace V₂ X₁) = 8) (h₂ : Nat.card (movedSpace V₂ X₂) = 8)
    (h₁E : movedSpace V₂ X₁ ≤ E) (h₂E : movedSpace V₂ X₂ ≤ E)
    (h₃ : X₃ ∉ YFamily H T V₂ E) : YFamily H T V₂ E = {X₁, X₂} := by
  ext X
  constructor
  · intro hX
    have hx : X ∈ XFamily H T := hX.1
    rw [hcatalogue] at hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact (h₃ hX).elim
  · intro hX
    have hX₁ : X₁ ∈ XFamily H T := by rw [hcatalogue]; simp
    have hX₂ : X₂ ∈ XFamily H T := by rw [hcatalogue]; simp
    rcases hX with rfl | hX
    · exact ⟨hX₁, h₁, h₁E⟩
    · have heq : X = X₂ := hX
      subst X
      exact ⟨hX₂, h₂, h₂E⟩

/-- Adapter to the preserved public output, retaining the additional complete
family equality required by the book. Distinctness and the actual quotient
isomorphism remain obligations of the native line-stabilizer calculation. -/
theorem twoM22Output_of_three_actor_calculation
    (H T V₂ E X₁ X₂ X₃ : Subgroup G)
    (hcatalogue : XFamily H T = {X₁, X₂, X₃})
    (h₁ : Nat.card (movedSpace V₂ X₁) = 8) (h₂ : Nat.card (movedSpace V₂ X₂) = 8)
    (h₁E : movedSpace V₂ X₁ ≤ E) (h₂E : movedSpace V₂ X₂ ≤ E)
    (h₃ : X₃ ∉ YFamily H T V₂ E) (hdistinct : X₁ ≠ X₂)
    (hquotient : Nonempty (coreQuotient (X₁ ⊔ X₂ ⊔ T) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    YFamily H T V₂ E = {X₁, X₂} ∧ TwoM22Output H T V₂ E X₁ X₂ := by
  have hY := yFamily_eq_pair_of_three_actor_calculation H T V₂ E X₁ X₂ X₃
    hcatalogue h₁ h₂ h₁E h₂E h₃
  refine ⟨hY, ?_⟩
  exact ⟨by rw [hY]; simp, by rw [hY]; simp, hdistinct, hquotient⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu
