module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.SporadicModels.QuotientTransfer
public import CFSG.Quasithin.ClassificationModels.Families

/-!
# Intrinsic inputs for the sporadic rank-one inspection

This module constructs the model-local configuration from the actual quotient
I/C_I(L). In particular it retains relative normality, the O^{3′} residual,
the specified S₃ quotient by its two-core, and the faithful normal four-group.
The concrete-carrier list is exactly that in 1.1.5(3)(f). Comparisons with
L/Z(L) and L/O₂(L) use the actual component projection.

The configuration is a conditional input for independent model proofs. Neither
its definition nor its construction asserts their classification conclusion.
Source: Aschbacher--Smith, combined manuscript (1 March 2004), 1.1.5(3)(f),
printed p.502, and the sporadic paragraph of 15.3.43, printed p.1140.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels
variable {G : Type*} [Group G] {I L : Subgroup G}

/-- The intrinsic inputs of the sporadic inspection in 15.3.43(e).
The component is normal and acts faithfully, S is Sylow, M is a proper
normalizer maximal subject to local characteristic two, and V is a normal
four-group with its full Y-action. No model reduction or centralizer of Y
is assumed. -/
structure LocalConfiguration (K S M Y V : Subgroup G) : Prop where
  normal : K.Normal
  simple : IsSimpleGroup K
  perfect : Group.IsPerfect K
  fitting : Theory.GroupTheory.generalizedFitting G = K
  faithful : centralizer (K : Set G) = ⊥
  sylow : ∃ P : Sylow 2 G, (P : Subgroup G) = S
  generated : K ⊔ S = ⊤
  sylow_le_local : S ≤ M
  y_le_component : Y ≤ K
  normalizer_eq : normalizer (Y : Set G) = M
  proper : M < ⊤
  twoLocal : IsTwoLocal M
  residual : Y = threeResidualIn M
  shadow : SymmetricThreeShadow Y S
  maximal : Maximal (fun X : Subgroup G =>
    Theory.GroupTheory.generalizedFitting X = pCore 2 X) M
  plane_le_sylow : V ≤ S
  plane_le_local : V ≤ M
  plane_elementary : IsElementaryAbelian 2 V
  plane_card : Nat.card V = 4
  plane_normal : (V.subgroupOf M).Normal
  plane_commutator : ⁅V, Y⁆ = V

/-- Construct all intrinsic model inputs from the shared reduced configuration and its faithfully transported four-group. -/
theorem localConfiguration_of_reduced [Finite G] {Y S M I L V₁ V₂ : Subgroup G}
    (c : ReducedConfiguration Y S M I L V₁ V₂) :
    LocalConfiguration (c.toComponentAction.image L) (c.toComponentAction.image S)
      (c.toComponentAction.image M) (c.toComponentAction.image Y)
      (c.toComponentAction.image V₂) := by
  let d := c.toComponentAction
  let : Group.IsPerfect L := reduced_component_perfect c
  have hSI : S ≤ I := le_sup_right.trans c.minimal.1.1.2
  have hVI := c.plane_two_le.trans hSI
  obtain ⟨⟨e⟩, hVM, hnV, hcomm⟩ := c.four_group_image
  obtain ⟨P, hP⟩ := c.sylow
  have hN := d.image_normalizer_and_proper c.minimal.1
    c.y_le_component c.normalizer_eq c.theta_eq
  have hgen : L.subgroupOf I ⊔ S.subgroupOf I = ⊤ := by
    apply Subgroup.map_injective I.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le c.component_le,
      map_subgroupOf_eq_of_le hSI, ← c.generated, ← MonoidHom.range_eq_map, I.range_subtype]
  let : IsElementaryAbelian 2 V₂ := c.plane_two_elementary
  let : IsElementaryAbelian 2 (V₂.subgroupOf I) := IsElementaryAbelian.subgroupOf hVI
  exact {
    normal := d.image_component_normal
    simple := c.quotient.simple
    perfect := Group.IsPerfect.ofSurjective d.componentMap_surjective
    fitting := c.quotient.fitting
    faithful := component_image_centralizer_eq_bot d
    sylow := d.image_sylow P hP
    generated := by
      change (L.subgroupOf I).map d.quotientMap ⊔
        (S.subgroupOf I).map d.quotientMap = ⊤
      rw [← Subgroup.map_sup, hgen, map_top_of_surjective _ d.quotientMap_surjective]
    sylow_le_local := map_mono (fun _ hx => c.sylow_le_M hx)
    y_le_component := map_mono (fun _ hx => c.y_le_component hx)
    normalizer_eq := hN.1
    proper := hN.2
    twoLocal := c.quotient.twoLocal
    residual := c.quotient.residual
    shadow := c.quotient.shadow
    maximal := c.quotient.maximal
    plane_le_sylow := map_mono (fun _ hx => c.plane_two_le hx)
    plane_le_local := hVM
    plane_elementary := IsElementaryAbelian.map d.quotientMap
    plane_card := (Nat.card_congr e.toEquiv).symm.trans c.plane_two_card
    plane_normal := hnV
    plane_commutator := hcomm }

/-- Exactly the ten sporadic carriers of 1.1.5(3)(f): M₁₁, M₁₂, M₂₂,
M₂₃, M₂₄, J₂, J₄, HS, He and Ru. Membership requires an actual group
isomorphism. J₃, the extra name in the larger classification list, is excluded. -/
def IsListedModel (K : Type*) [Group K] : Prop :=
  ∃ name : ClassificationModels.SporadicName, name ≠ .j3 ∧
    Nonempty (K ≃* name.Carrier)

/-- Transport an actual central-quotient model equivalence to the component image. -/
theorem listed_image_of_center_quotient (d : ComponentAction I L)
    (h : IsListedModel (L ⧸ center L)) : IsListedModel (d.image L) := by
  obtain ⟨name, hn, ⟨e⟩⟩ := h
  exact ⟨name, hn, ⟨d.centerQuotientEquiv.symm.trans e⟩⟩

/-- The source equality of ambient images identifies Z(L) with the intrinsic O₂(L). -/
theorem reduced_center_eq_two_core {Y S M I L V₁ V₂ : Subgroup G}
    (c : ReducedConfiguration Y S M I L V₁ V₂) : center L = pCore 2 L :=
  Subgroup.map_injective L.subtype_injective c.component_center

/-- The source quotient L/O₂(L) is canonically the component image in
I/C_I(L); the map preserves the possible central two-cover. -/
noncomputable def reducedTwoCoreQuotientEquiv {Y S M I L V₁ V₂ : Subgroup G}
    (c : ReducedConfiguration Y S M I L V₁ V₂) :
    (L ⧸ pCore 2 L) ≃* c.toComponentAction.image L :=
  (QuotientGroup.quotientMulEquivOfEq (reduced_center_eq_two_core c).symm).trans
    c.toComponentAction.centerQuotientEquiv

/-- Transport the quotient convention in 1.1.5(3)(f) to the actual component image. -/
theorem listed_image_of_two_core_quotient {Y S M I L V₁ V₂ : Subgroup G}
    (c : ReducedConfiguration Y S M I L V₁ V₂)
    (h : IsListedModel (L ⧸ pCore 2 L)) : IsListedModel (c.toComponentAction.image L) := by
  obtain ⟨name, hn, ⟨e⟩⟩ := h
  exact ⟨name, hn, ⟨(reducedTwoCoreQuotientEquiv c).symm.trans e⟩⟩

end CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels
