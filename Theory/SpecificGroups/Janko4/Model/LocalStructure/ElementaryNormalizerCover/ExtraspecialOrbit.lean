module
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Theory.GroupTheory.PGroup.ClassTwoCyclicCenter
public import Theory.ElementaryAbelian.Injective

/-!
# Pure subgroups from an extraspecial center orbit

Let X be elementary abelian inside an extraspecial two-group Q and contain
its central involution z. The class-two commutator identity makes Q normalize
X. Every x outside the central line is Q-conjugate to zx. Consequently the
N(X)-orbit of z, together with identity, is closed under multiplication.
It is a nontrivial N(X)-invariant subgroup consisting of ambient conjugates
of z. If X contains an involution not conjugate to z, this subgroup is proper.

This proves the reducibility step needed in Kleidman--Wilson, *The Maximal
Subgroups of J4* (1988), Proposition 2.2.3, p.491, directly from the actual
extraspecial containment. No classification of transvection groups is needed
for this specialization. `ExtraspecialReduction` applies it to the literal
J4 first-centralizer core and its conjugates. Native placement into that core
is a separate part of the source proof.
-/

open Subgroup
open scoped IsMulCommutative commutatorElement

namespace Janko4.LocalStructure.ElementaryNormalizerCover

private theorem elementary_square {V : Type*} [Group V] [IsElementaryAbelian 2 V]
    (x : V) : x * x = 1 := by
  simpa only [pow_two] using
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) x

private theorem orbit_subgroup_of_shears {H V : Type*} [Group H] [Group V]
    [IsElementaryAbelian 2 V] (ρ : H →* MulAut V) (z : V)
    (hshear : ∀ x : V, x ≠ 1 → x ≠ z → ∃ h : H, ρ h x = z * x) :
    ∃ W : Subgroup V,
      (∀ x, x ∈ W ↔ x = 1 ∨ ∃ h : H, ρ h z = x) ∧
      ∀ h : H, ∀ x ∈ W, ρ h x ∈ W := by
  let S : Set V := {x | x = 1 ∨ ∃ h : H, ρ h z = x}
  have hmul {x y : V} (hx : x ∈ S) (hy : y ∈ S) : x * y ∈ S := by
    rcases hx with rfl | ⟨g, rfl⟩
    · simpa only [one_mul] using hy
    rcases hy with rfl | ⟨h, rfl⟩
    · exact Or.inr ⟨g, by simp⟩
    by_cases he : ρ g z = ρ h z
    · exact Or.inl (by rw [he, elementary_square])
    let x := ρ g⁻¹ (ρ h z)
    have hxz : x ≠ z := by
      intro hh
      apply he
      have hh' := congrArg (ρ g) hh
      simpa only [x, map_inv, MulAut.apply_inv_self] using hh'.symm
    by_cases hx1 : x = 1
    · have hh := congrArg (ρ g) hx1
      have hy1 : ρ h z = 1 := by
        simpa only [x, map_inv, MulAut.apply_inv_self, map_one] using hh
      exact Or.inr ⟨g, by rw [hy1, mul_one]⟩
    obtain ⟨k, hk⟩ := hshear x hx1 hxz
    refine Or.inr ⟨g * k * (g⁻¹ * h), ?_⟩
    calc
      ρ (g * k * (g⁻¹ * h)) z = ρ g (ρ k x) := by
        simp only [x, map_mul, MulAut.mul_apply]
      _ = ρ g (z * x) := congrArg (ρ g) hk
      _ = ρ g z * ρ h z := by
        simp only [map_mul, x, map_inv, MulAut.apply_inv_self]
  let W : Subgroup V :=
    { carrier := S
      one_mem' := Or.inl rfl
      mul_mem' := hmul
      inv_mem' := fun {x} hx => by
        have hi : x⁻¹ = x := inv_eq_of_mul_eq_one_left (elementary_square x)
        rwa [hi] }
  refine ⟨W, fun _ => Iff.rfl, ?_⟩
  intro h x hx
  rcases hx with rfl | ⟨g, rfl⟩
  · exact Or.inl (map_one _)
  · exact Or.inr ⟨h * g, by simp only [map_mul, MulAut.mul_apply]⟩

private theorem center_eq_one_or_marked {Q : Type*} [Group Q] [IsExtraspecial 2 Q]
    (z : Q) (hz : z ∈ center Q) (hz1 : z ≠ 1) {x : Q} (hx : x ∈ center Q) :
    x = 1 ∨ x = z := by
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  · exact Or.inr (congrArg Subtype.val
      (((Nat.card_eq_two_iff' (1 : center Q)).mp (IsExtraspecial.center_order_p 2 Q)).unique
        (show (⟨x, hx⟩ : center Q) ≠ 1 from fun h => hx1 (congrArg Subtype.val h))
        (show (⟨z, hz⟩ : center Q) ≠ 1 from fun h => hz1 (congrArg Subtype.val h))))

private theorem extraspecial_shear {Q : Type*} [Group Q] [IsExtraspecial 2 Q]
    (z : Q) (hz : z ∈ center Q) (hz1 : z ≠ 1)
    (x : Q) (hx1 : x ≠ 1) (hxz : x ≠ z) :
    ∃ q : Q, q * x * q⁻¹ = z * x := by
  have hx : x ∉ center Q := fun h =>
    (center_eq_one_or_marked z hz hz1 h).elim hx1 hxz
  obtain ⟨q, hq⟩ : ∃ q : Q, q * x ≠ x * q := by
    by_contra! hh
    exact hx (mem_center_iff.mpr hh)
  have hc : ⁅q, x⁆ ∈ center Q :=
    (IsExtraspecial.quotient_elementary_abelian 2 Q).commutator_le_center_of_central_quotient
      (commutator_mem_commutator (mem_top _) (mem_top _))
  have hc1 : ⁅q, x⁆ ≠ 1 := fun h => hq (commutatorElement_eq_one_iff_mul_comm.mp h)
  have he : ⁅q, x⁆ = z := (center_eq_one_or_marked z hz hz1 hc).resolve_left hc1
  exact ⟨q, eq_mul_of_mul_inv_eq he⟩

/-- The class-two core supplies the elementary shears without a transvection-group
classification. The invariant subgroup is the normalizer orbit of the marked
central involution together with identity. -/
public theorem extraspecial_pure_reduction {G : Type*} [Group G]
    (Q X : Subgroup G) [IsExtraspecial 2 Q] [IsElementaryAbelian 2 X]
    (hXQ : X ≤ Q) (z : Q) (hz : z ∈ center Q) (hz1 : z ≠ 1)
    (hzX : (z : G) ∈ X) (w : X) (hw1 : w ≠ 1) (hw : ¬ IsConj (z : G) (w : G)) :
    ∃ Y : Subgroup G, Y ≠ ⊥ ∧ Y < X ∧ IsElementaryAbelian 2 Y ∧
      normalizer (X : Set G) ≤ normalizer (Y : Set G) ∧
      ∀ y ∈ Y, y ≠ 1 → IsConj (z : G) y := by
  have hZX : (center Q).map Q.subtype ≤ X := by
    rintro x ⟨q, hq, rfl⟩
    rcases center_eq_one_or_marked z hz hz1 hq with rfl | rfl
    · exact X.one_mem
    · exact hzX
  have hn : Q ≤ normalizer (X : Set G) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    apply (commutator_mono le_rfl hXQ).trans
    rw [← map_subtype_commutator]
    exact (map_mono (IsExtraspecial.quotient_elementary_abelian 2 Q).commutator_le_center_of_central_quotient).trans hZX
  let zX : X := ⟨z, hzX⟩
  have hs : ∀ x : X, x ≠ 1 → x ≠ zX →
      ∃ h : normalizer (X : Set G), X.normalizerMonoidHom h x = zX * x := by
    intro x hx1 hxz
    obtain ⟨q, hq⟩ := extraspecial_shear z hz hz1 (⟨x, hXQ x.property⟩ : Q)
      (fun h => hx1 (Subtype.ext (congrArg (fun t : Q => (t : G)) h)))
      (fun h => hxz (Subtype.ext (congrArg (fun t : Q => (t : G)) h)))
    refine ⟨⟨q, hn q.property⟩, Subtype.ext ?_⟩
    exact congrArg (fun t : Q => (t : G)) hq
  obtain ⟨W, hW, hWi⟩ := orbit_subgroup_of_shears X.normalizerMonoidHom zX hs
  let Y := W.map X.subtype
  have hYX : Y ≤ X := map_subtype_le _
  have hzY : (z : G) ∈ Y := by
    exact mem_map_of_mem X.subtype ((hW zX).mpr (Or.inr ⟨1, by simp⟩))
  have hpure : ∀ y ∈ Y, y ≠ 1 → IsConj (z : G) y := by
    rintro y ⟨x, hx, rfl⟩ hx1
    rcases (hW x).mp hx with rfl | ⟨h, hh⟩
    · exact (hx1 rfl).elim
    · exact isConj_iff.mpr ⟨h, congrArg Subtype.val hh⟩
  have hwY : (w : G) ∉ Y := fun h =>
    hw (hpure _ h (fun he => hw1 (Subtype.ext he)))
  have hnY : normalizer (X : Set G) ≤ normalizer (Y : Set G) := by
    have forward (g : normalizer (X : Set G)) {x : G} (hx : x ∈ Y) :
        (g : G) * x * (g : G)⁻¹ ∈ Y := by
      obtain ⟨y, hy, rfl⟩ := hx
      exact mem_map_of_mem X.subtype (hWi g y hy)
    intro g hg x
    constructor
    · exact forward ⟨g, hg⟩
    · intro hx
      change x ∈ Y
      have hh := forward (⟨g, hg⟩⁻¹) hx
      simp only [Subgroup.coe_inv, inv_inv, mul_assoc, inv_mul_cancel_left,
        inv_mul_cancel, mul_one] at hh
      exact hh
  have : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective W.subtype W.subtype_injective
  have : IsElementaryAbelian 2 Y := IsElementaryAbelian.map X.subtype
  refine ⟨Y, ?_, lt_of_le_of_ne hYX ?_, inferInstance, hnY, hpure⟩
  · intro he
    have he1 : (z : G) = 1 := mem_bot.mp (he ▸ hzY)
    exact hz1 (Subtype.ext he1)
  · intro he
    exact hwY (he.symm ▸ w.property)

end Janko4.LocalStructure.ElementaryNormalizerCover
