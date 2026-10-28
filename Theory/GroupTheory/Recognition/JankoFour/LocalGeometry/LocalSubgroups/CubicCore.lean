module

public import Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.Intrinsic
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.Mathieu.M22.Properties.FixedHexads
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection

/-!
# The canonical cubic lift in a type-J₄ centralizer

The cubic kernel in C_G(z)/Q is precisely its three-core. The proof uses
simplicity and centerlessness of the native M₂₂ and the general prime-core
lemma for automorphism overgroups. Hence its inverse image is the literal
iterated core O_{2,3}(C_G(z)), independently of the chosen quotient map.
Its two-core is Q, so its ambient normalizer is C_G(z).

Source: Aschbacher–Segev, Invent. Math. 105 (1991), §4; exposition (3.1)(5–6),
p.16. These results identify the denominator from the plane group. They do
not replace it with an iterated core of an intersection group.
-/

@[expose] public section

open Subgroup Theory.GroupTheory Sporadic.Mathieu
namespace Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.LocalSubgroups

private theorem m22_threeCore : pCore 3 M22 = ⊥ := by
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  rcases (inferInstance : (pCore 3 M22).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hp : IsPGroup 3 (⊤ : Subgroup M22) := h ▸ pCore_isPGroup
    have hG : IsPGroup 3 M22 := hp.of_equiv Subgroup.topEquiv
    have hd := hG.dvd_orderOf (g := m22Standard11) (by
      intro he
      have hh := m22Standard11_order
      rw [he, orderOf_one] at hh
      omega)
    rw [m22Standard11_order] at hd
    norm_num at hd

theorem cubic_kernel_eq_threeCore {H : Type*} [Group H] [Finite H]
    (e : CubicAutomorphismQuotient H) : e.projection.ker = pCore 3 H := by
  apply (core_eq_kernel_of_action 3
    (conj_injective_of_center_eq_bot m22_center_eq_bot) m22_threeCore
    e.projection (fun x => e.surjective (MulAut.conj x)) ?_).symm
  exact IsPGroup.of_card (n := 1) (by simpa using e.kernel_card)

def twoThreeCore (H : Type*) [Group H] : Subgroup H :=
  (pCore 3 (H ⧸ pCore 2 H)).comap (QuotientGroup.mk' (pCore 2 H))

instance {H : Type*} [Group H] : (twoThreeCore H).Normal :=
  inferInstanceAs ((pCore 3 (H ⧸ pCore 2 H)).comap _).Normal

variable {G : Type*} [Group G] [Finite G] {z : G}

private theorem threeCore_preimage_congr {H : Type*} [Group H]
    (A B : Subgroup H) [A.Normal] [B.Normal] (h : A = B) :
    (pCore 3 (H ⧸ A)).comap (QuotientGroup.mk' A) =
      (pCore 3 (H ⧸ B)).comap (QuotientGroup.mk' B) := by
  subst B
  rfl

theorem cubicLift_eq_twoThreeCore (h : IsTypeJ4 z)
    (e : CubicAutomorphismQuotient ((centralizer z) ⧸ core z)) :
    CubicLift.subgroup e = twoThreeCore (centralizer z) := by
  change e.projection.ker.comap (QuotientGroup.mk' (core z)) = _
  rw [cubic_kernel_eq_threeCore e]
  exact threeCore_preimage_congr _ _ h.core_eq_twoCore

theorem twoThreeCore_card (h : IsTypeJ4 z) :
    Nat.card (twoThreeCore (centralizer z)) = 3 * 2 ^ 13 := by
  obtain ⟨e⟩ := h.cubic_quotient
  rw [← cubicLift_eq_twoThreeCore h e]
  exact CubicLift.subgroup_card e h

theorem core_le_twoThreeCore (h : IsTypeJ4 z) :
    core z ≤ twoThreeCore (centralizer z) := by
  obtain ⟨e⟩ := h.cubic_quotient
  rw [← cubicLift_eq_twoThreeCore h e]
  exact CubicLift.core_le e

noncomputable def automorphismQuotientEquiv (h : IsTypeJ4 z)
    (e : CubicAutomorphismQuotient ((centralizer z) ⧸ core z)) :
    (centralizer z ⧸ twoThreeCore (centralizer z)) ≃* MulAut M22 :=
  (QuotientGroup.quotientMulEquivOfEq (cubicLift_eq_twoThreeCore h e).symm).trans
    (CubicLift.automorphismQuotientEquiv e)

@[simp] theorem automorphismQuotientEquiv_mk (h : IsTypeJ4 z)
    (e : CubicAutomorphismQuotient ((centralizer z) ⧸ core z)) (g : centralizer z) :
    automorphismQuotientEquiv h e (QuotientGroup.mk' _ g) = CubicLift.projection e g := rfl

theorem twoCore_twoThreeCore (h : IsTypeJ4 z) :
    pCore 2 (twoThreeCore (centralizer z)) =
      (core z).subgroupOf (twoThreeCore (centralizer z)) := by
  rw [h.core_eq_twoCore]
  exact ((inferInstance : (twoThreeCore (centralizer z)).Normal).isSubnormal.pCore_subgroupOf 2).symm

def ambientTwoThreeCore (z : G) : Subgroup G :=
  (twoThreeCore (centralizer z)).map (centralizer z).subtype

omit [Finite G] in
theorem ambientTwoThreeCore_le (z : G) : ambientTwoThreeCore z ≤ centralizer z :=
  map_subtype_le _

omit [Finite G] in
theorem ambientTwoThreeCore_subgroupOf (z : G) :
    (ambientTwoThreeCore z).subgroupOf (centralizer z) = twoThreeCore (centralizer z) :=
  comap_map_eq_self (by simp)

theorem ambientTwoThreeCore_twoCore (h : IsTypeJ4 z) :
    (pCore 2 (ambientTwoThreeCore z)).map (ambientTwoThreeCore z).subtype = ambientCore z := by
  let e := (twoThreeCore (centralizer z)).equivMapOfInjective
    (centralizer z).subtype (centralizer z).subtype_injective
  unfold ambientTwoThreeCore
  rw [← pCore_map_iso 2 e, twoCore_twoThreeCore h, map_map]
  change ((core z).subgroupOf (twoThreeCore (centralizer z))).map
    ((centralizer z).subtype.comp (twoThreeCore (centralizer z)).subtype) = _
  rw [← map_map, map_subgroupOf_eq_of_le (core_le_twoThreeCore h)]
  rfl

theorem normalizer_ambientTwoThreeCore (h : IsTypeJ4 z) :
    normalizer (ambientTwoThreeCore z : Set G) = centralizer z := by
  apply le_antisymm
  · have hh := normalizer_le_normalizer_characteristic_image (ambientTwoThreeCore z)
      (pCore 2 (ambientTwoThreeCore z))
    rwa [ambientTwoThreeCore_twoCore h, normalizer_ambientCore h] at hh
  · apply (normal_subgroupOf_iff_le_normalizer (ambientTwoThreeCore_le z)).mp
    rw [ambientTwoThreeCore_subgroupOf]
    infer_instance

end Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.LocalSubgroups
