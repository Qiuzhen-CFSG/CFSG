module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.HexadQuotient
public import Theory.ElementaryAbelian.ExtraspecialCentralFunctionals
public import Theory.GroupTheory.BinaryPairingCard

/-!
# Commutator duality for the original hexad fixed subgroup

The exact E₁ is a maximal elementary subgroup of the extraspecial Q.
Its central commutator pairing therefore has right kernel E₁. Restrict
that pairing to any actual subgroup A of Q and double-count its two
kernels. This proves |A| |C_E₁(A)| = 128 |A ∩ E₁|.

In the literal full quotient G₁,₃/E, the image A* has kernel A ∩ E₁.
Consequently |A*| |C_E₁(A)| = 128, the duality equality used in the final
paragraph of the proof of AS91 (4.6)(1). No Mathieu cocode marking is
assumed. The constructed E is also self-centralizing in O₂(G₁,₃).
The remaining strict bounds for actors outside E and the full normalizer
recognition are separate obligations.

Source: Aschbacher–Segev, The uniqueness of groups of type J4,
Invent. Math. 105 (1991), (4.6), printed p.598, DOI 10.1007/BF01232280.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Sporadic.Mathieu LocalGeometry
variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z) (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
  (X : Sylow 3 (CubicLift.subgroup e))

/-- The original maximal elementary subgroup satisfies the full central-functional configuration. -/
theorem originalHexadFixedCore_configuration {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    ExtraspecialCentralFunctionals.Configuration (core z)
      (originalHexadFixedCore h e X B) (center (centralizer z)) := by
  obtain ⟨hU,hUc⟩ := originalHexadFixedCore_data h e X hB
  let := hU
  refine ⟨originalHexadFixedCore_le h e X B,
    center_le_originalHexadFixedCore h e X B,center_le_centralizer _,?_,
    originalHexadFixedCore_selfcentralizing h e X hUc,
    centralizer_center_card h,?_⟩
  · rw [←core_center_eq_centralizer_center h,←map_subtype_commutator]
    apply map_mono
    let := h.extraspecial
    exact (IsExtraspecial.quotient_elementary_abelian 2 (core z)).commutator_le_center_of_central_quotient
  · rw [hUc,h.core_card]
    norm_num

private theorem central_pairing_card {H : Type*} [Group H] [Finite H]
    {Q U Z : Subgroup H}
    [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 Z]
    (c : ExtraspecialCentralFunctionals.Configuration Q U Z)
    (A : Subgroup H) (hA : A ≤ Q) :
    Nat.card A * Nat.card (U ⊓ Subgroup.centralizer (A : Set H) : Subgroup H) =
      Nat.card U * Nat.card (A ⊓ U : Subgroup H) := by
  let p := (ExtraspecialCentralFunctionals.pairing c).comp (inclusion hA)
  let f : A →* (U →* Z) := {
    toFun a := (p a).comp (QuotientGroup.mk' (Z.subgroupOf U))
    map_one' := by apply MonoidHom.ext; intro u; change p 1 _ = 1; rw [map_one]; rfl
    map_mul' a b := by apply MonoidHom.ext; intro u; change p (a*b) _ = p a _ * p b _; rw [map_mul]; rfl }
  have heval (a : A) (u : U) : (f a u : H) = ⁅(a : H),(u : H)⁆ :=
    ExtraspecialCentralFunctionals.pairing_apply c (inclusion hA a) u
  have hleft : f.ker = (A ⊓ U).subgroupOf A := by
    ext a
    change f a = 1 ↔ a.val ∈ A ⊓ U
    constructor
    · intro ha
      refine ⟨a.property,?_⟩
      apply c.self_centralizing.le
      refine ⟨hA a.property,?_⟩
      intro u hu
      have hh := congrArg (fun t : U →* Z => (t ⟨u,hu⟩ : H)) ha
      rw [heval] at hh
      exact (commutatorElement_eq_one_iff_mul_comm.mp hh).symm
    · intro ha
      apply MonoidHom.ext
      intro u
      apply Subtype.ext
      rw [heval]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (congrArg Subtype.val (mul_comm (⟨a.val,ha.2⟩ : U) u))
  have hright : f.flip.ker = (U ⊓ Subgroup.centralizer (A : Set H)).subgroupOf U := by
    ext u
    change f.flip u = 1 ↔ u.val ∈ U ⊓ Subgroup.centralizer (A : Set H)
    constructor
    · intro hu
      refine ⟨u.property,?_⟩
      intro a ha
      have hh := congrArg (fun t : A →* Z => (t ⟨a,ha⟩ : H)) hu
      change (f ⟨a,ha⟩ u : H) = 1 at hh
      rw [heval] at hh
      exact commutatorElement_eq_one_iff_mul_comm.mp hh
    · intro hu
      apply MonoidHom.ext
      intro a
      apply Subtype.ext
      change (f a u : H) = 1
      rw [heval]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hu.2 a a.property)
  have hc := MonoidHom.binary_pairing_kernel_card c.center_card f
  rw [hleft,hright,
    Nat.card_congr (subgroupOfEquivOfLe (show A ⊓ U ≤ A from inf_le_left)).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (show U ⊓ Subgroup.centralizer (A : Set H) ≤ U from inf_le_left)).toEquiv] at hc
  exact hc

/-- The two literal centralizers in the original extraspecial pairing have complementary orders. -/
theorem originalHexadFixedCore_centralizer_card {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (A : Subgroup (centralizer z)) (hA : A ≤ core z) :
    Nat.card A * Nat.card (originalHexadFixedCore h e X B ⊓
      Subgroup.centralizer (A : Set (centralizer z)) : Subgroup (centralizer z)) =
      128 * Nat.card (A ⊓ originalHexadFixedCore h e X B : Subgroup (centralizer z)) := by
  obtain ⟨hU,hUc⟩ := originalHexadFixedCore_data h e X hB
  let := hU
  let : IsElementaryAbelian 2 (center (centralizer z)) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun a => by
      simpa only [centralizer_center_card h] using pow_card_eq_one' (x := a) }
  simpa only [hUc] using central_pairing_card
    (originalHexadFixedCore_configuration h e X hB) A hA
/-- The source Q-image measures exactly the fixed-space index on E1. -/
theorem originalHexadQuotient_core_centralizer_card
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (A : Subgroup (centralizer z)) (hA : A ≤ core z) :
    letI := originalHexadElementary_normal h e X hB
    let L := originalPlaneHexad e B
    let f := QuotientGroup.mk' ((originalHexadElementary h e X B).subgroupOf L)
    Nat.card ((A.subgroupOf L).map f) *
      Nat.card (originalHexadFixedCore h e X B ⊓
        Subgroup.centralizer (A : Set (centralizer z)) : Subgroup (centralizer z)) = 128 := by
  let := originalHexadElementary_normal h e X hB
  let L := originalPlaneHexad e B
  let U := originalHexadFixedCore h e X B
  let E := originalHexadElementary h e X B
  let f := QuotientGroup.mk' (E.subgroupOf L)
  have hAL : A ≤ L := hA.trans ((CubicLift.core_le e).trans (originalPlaneHexad_cubic_le e B))
  have hi : A ⊓ E = A ⊓ U := by
    have hu : E ⊓ core z = U := (originalHexadElementary_data h e X hB).2.2.2.2.2
    rw [←hu,←inf_assoc,inf_right_comm,inf_eq_left.mpr hA]
  have hker : A.subgroupOf L ⊓ f.ker = (A ⊓ U).subgroupOf L := by
    rw [QuotientGroup.ker_mk']
    change (A ⊓ E).subgroupOf L = (A ⊓ U).subgroupOf L
    rw [hi]
  have hc := IsElementaryAbelian.card_inf_ker_mul_card_map (A.subgroupOf L) f
  rw [hker,Nat.card_congr (subgroupOfEquivOfLe hAL).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (show A ⊓ U ≤ L from inf_le_left.trans hAL)).toEquiv] at hc
  have hd := originalHexadFixedCore_centralizer_card h e X hB A hA
  change Nat.card A * Nat.card (U ⊓ Subgroup.centralizer (A : Set (centralizer z)) : Subgroup (centralizer z)) =
    128 * Nat.card (A ⊓ U : Subgroup (centralizer z)) at hd
  have hp : 0 < Nat.card (A ⊓ U : Subgroup (centralizer z)) := Nat.card_pos
  rw [←hc] at hd
  nlinarith

/-- The two-core acts faithfully modulo E on E; this is relative to the original overlap. -/
theorem originalHexadElementary_twoCore_centralizer
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (originalPlaneHexad e B).pCoreIn 2 ⊓
      Subgroup.centralizer (originalHexadElementary h e X B : Set (centralizer z)) =
        originalHexadElementary h e X B := by
  obtain ⟨hU,hUc,hE,_⟩ := originalHexadElementary_data h e X hB
  let := hU
  let := hE
  apply le_antisymm
  · exact (inf_le_inf_left _ (Subgroup.centralizer_le (fun x hx => (show originalHexadFixedCore h e X B ≤ originalHexadElementary h e X B from le_sup_left) hx))).trans
      (originalHexadElementary_eq_centralizer h e X hUc).ge
  · refine le_inf ?_ (originalHexadElementary h e X B).le_centralizer
    rw [originalPlaneHexad_twoCore h e X B]
    exact sup_le_sup (originalHexadFixedCore_le h e X B) le_rfl

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
