module

public import Stellmacher.Recognition.NormalEightNonnormalCoreReduction
public import Theory.GroupTheory.PGroup.ExtraspecialFrattiniLargeFactor
public import Theory.GroupTheory.PGroup.NormalEightGeneratorBound

/-!
# The Frattini input for arbitrary large-factor reduction

The four-generator bound on normal subgroups of the original Sylow transfers
to the literal quotient two-core through its Sylow embedding. An upper bound
of sixteen for this core's Frattini quotient then absorbs every commuting
normal supplement to an extraspecial factor of order at least thirty-two.
The resulting whole core is extraspecial of order thirty-two.

The MacWilliams–Sah input remains an explicit premise in these reduction
lemmas. It is a bound on Frattini quotients, not on elementary subgroups:
the latter does not supply this generator bound. The unconditional assembly
must discharge this premise from the absence of normal elementary eights.

Source: Janko–Thompson (1970), result 1.1 on printed p.385 and the first
width paragraph in §4, printed p.389.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- Only normal subgroups of the original Sylow are needed to bound the
Frattini quotient of the quotient two-core. -/
public theorem omegaQuotient_pCore_frattini_card_le_sixteen_of_normal_subgroup_bound
    (S : Sylow 2 G)
    (hbound : ∀ U : Subgroup S, U.Normal → Nat.card (U ⧸ frattini U) ≤ 16) :
    Nat.card (pCore 2 (OmegaQuotient S) ⧸ frattini (pCore 2 (OmegaQuotient S))) ≤ 16 := by
  let H := pCore 2 (OmegaQuotient S)
  let f := omegaQuotientHom S
  have hrange : H ≤ f.range := by
    rw [omegaQuotientHom_range]
    exact pCore_isPGroup.le_sylow_of_normal (omegaQuotientSylow S)
  let U := H.comap f
  let e : U ≃* H := MulEquiv.ofBijective (f.subgroupComap H) ⟨by
    intro x y h
    exact Subtype.ext (omegaQuotientHom_injective S (congrArg Subtype.val h)), by
    intro u
    obtain ⟨x, hx⟩ := hrange u.property
    exact ⟨⟨x, by change f x ∈ H; rw [hx]; exact u.property⟩, Subtype.ext hx⟩⟩
  have he : Nat.card (U ⧸ frattini U) = Nat.card (H ⧸ frattini H) :=
    Nat.card_congr (QuotientGroup.congr (frattini U) (frattini H)
      e e.mapSubgroup.map_radical).toEquiv
  exact he ▸ hbound U inferInstance

/-- The generator bound reduces an arbitrarily large extraspecial factor
to the whole core of order thirty-two. No Hall hypothesis on the tail is needed. -/
public theorem omegaQuotient_pCore_large_factor_reduction_of_frattini_bound
    (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (hbound : Nat.card
      (pCore 2 (OmegaQuotient S) ⧸ frattini (pCore 2 (OmegaQuotient S))) ≤ 16)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B]
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hg : B ⊔ D = ⊤) (hlarge : 32 ≤ Nat.card B) :
    IsExtraspecial 2 (pCore 2 (OmegaQuotient S)) ∧
      Nat.card (pCore 2 (OmegaQuotient S)) = 32 := by
  let : IsCyclic (center (pCore 2 (OmegaQuotient S))) :=
    omegaQuotient_pCore_center_isCyclic S hno W hunique hnormal
  exact extraspecial_card_thirty_two_of_large_factor_of_frattini_quotient_le_sixteen
    pCore_isPGroup hbound B D hlarge hc hg

/- The ambient normal-elementary exclusion gives the Frattini bound needed by
the preceding intrinsic reduction.  The quotient core is pulled back along
the canonical Sylow embedding so that the MacWilliams--Sah theorem applies in
the original Sylow, where its normal-elementary hypothesis is available. -/
public theorem omegaQuotient_pCore_large_factor_reduction
    [IsSimpleGroup G]
    (_hns : ¬ Group.IsSolvable G)
    (_hN : Stellmacher.IsNTwoGroup G)
    (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (_hA : 8 ≤ Nat.card A)
    (_hnonab : ¬ IsMulCommutative S)
    (_hZ : Nat.card (omega₁ (Subgroup.center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧
      8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (_hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] (_hD : IsBinaryHallFactor D)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hg : B ⊔ D = ⊤) (hlarge : 32 ≤ Nat.card B) :
    IsExtraspecial 2 (pCore 2 (OmegaQuotient S)) ∧
      Nat.card (pCore 2 (OmegaQuotient S)) = 32 := by
  let H := pCore 2 (OmegaQuotient S)
  let f := omegaQuotientHom S
  let U := H.comap f
  have hrange : H ≤ f.range := by
    rw [omegaQuotientHom_range]
    exact pCore_isPGroup.le_sylow_of_normal (omegaQuotientSylow S)
  have e : U ≃* H := MulEquiv.ofBijective (f.subgroupComap H) ⟨by
    intro x y h
    exact Subtype.ext (omegaQuotientHom_injective S (congrArg Subtype.val h)), by
    intro u
    obtain ⟨x, hx⟩ := hrange u.property
    exact ⟨⟨x, by change f x ∈ H; rw [hx]; exact u.property⟩, Subtype.ext hx⟩⟩
  have hsympH : IsBinarySymplecticType H :=
    omegaQuotient_pCore_symplectic S hno W hunique hnormal
  have hcycH : IsCyclic (center H) :=
    omegaQuotient_pCore_center_isCyclic S hno W hunique hnormal
  let : IsCyclic (center U) :=
    (MulEquiv.isCyclic (Subgroup.centerCongr e)).mpr hcycH
  have hboundU : Nat.card (U ⧸ frattini U) ≤ 16 :=
    IsPGroup.normal_subgroup_frattini_card_le_sixteen_of_symplectic_type
      S.isPGroup' hno U (hsympH.of_mulEquiv e.symm)
  have he : Nat.card (U ⧸ frattini U) = Nat.card (H ⧸ frattini H) :=
    Nat.card_congr (QuotientGroup.congr (frattini U) (frattini H)
      e e.mapSubgroup.map_radical).toEquiv
  have hbound : Nat.card (H ⧸ frattini H) ≤ 16 := he ▸ hboundU
  exact omegaQuotient_pCore_large_factor_reduction_of_frattini_bound S hno W
    hunique hnormal hbound B D hc hg hlarge

end Stellmacher.Recognition.NormalEightNonnormalImage
