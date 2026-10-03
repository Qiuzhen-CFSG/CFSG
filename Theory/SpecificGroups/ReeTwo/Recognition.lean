module

public import Theory.SpecificGroups.ReeTwo.Centralizer
public import Theory.SpecificGroups.ReeTwo.CoreFaithfulness
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Faithful recognition maps for the Ree two centralizer

The complement acts faithfully on the first five binary core coordinates,
where inner automorphisms act trivially. Hence the embedded core contains
its centralizer. A kernel avoiding the last root meets the core trivially
by `Core.hom_injective_of_last_root`; normality makes that kernel centralize
the core, so it is trivial.

This gives an injectivity criterion for the actual root-and-Weyl map, without
assuming independent core coordinates or injectivity of the complement.
Only after this relation-based argument do equal orders give surjectivity.
The root action is Shinoda (1975), pp.81–83, (2.3) and (3.2).
-/

namespace ReeTwo.Core

private def head (g : Core) : Fin 5 → ZMod 2 := ![g.b0, g.b1, g.b2, g.b3, g.b4]

private theorem head_mul (g h : Core) : head (g * h) = head g + head h := by
  funext i
  fin_cases i <;> rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem head_stabilizer : ∀ (i : Fin 5) (j : Fin 4),
    (head ((c ^ i.val * a ^ j.val) (root 0)) = head (root 0) ∧
      head ((c ^ i.val * a ^ j.val) (root 4)) = head (root 4)) →
    i = 0 ∧ j = 0 := by decide +kernel

private theorem complement_head_faithful (p : complement)
    (hp : ∀ i, head ((p : MulAut Core) (root i)) = head (root i)) : p = 1 := by
  obtain ⟨i, j, h⟩ := complement_normal_form p
  have he : (p : MulAut Core) = c ^ i.val * a ^ j.val := by
    rw [h]
    rfl
  obtain ⟨hi, hj⟩ := head_stabilizer i j (by simpa only [he] using And.intro (hp 0) (hp 4))
  subst i j
  simp [h]

end ReeTwo.Core

namespace ReeTwo.Centralizer

/-- The specified core contains its full centralizer in the model. -/
public theorem centralizer_core_le : Subgroup.centralizer (core : Set Centralizer) ≤ core := by
  intro g hg
  have hc (i : CoreRoot) : g * root i = root i * g :=
    (Subgroup.mem_centralizer_iff.mp hg (root i) ⟨Core.root i, rfl⟩).symm
  have hr : g.right = 1 := by
    apply Core.complement_head_faithful
    intro i
    have he := congrArg SemidirectProduct.left (hc i)
    change g.left * (g.right : MulAut Core) (Core.root i) = Core.root i * g.left at he
    have hh := congrArg Core.head he
    rw [Core.head_mul, Core.head_mul] at hh
    exact add_left_cancel (hh.trans (add_comm _ _))
  exact ⟨g.left, SemidirectProduct.ext rfl hr.symm⟩

/-- Preserving the central involution forces a map of the entire model to be
injective, including its complement action. -/
public theorem hom_injective_of_last_root {H : Type*} [Group H]
    (f : Centralizer →* H) (hz : f (root 9) ≠ 1) : Function.Injective f := by
  have hi : Function.Injective (f.comp SemidirectProduct.inl) :=
    Core.hom_injective_of_last_root _ hz
  have hdisjoint : f.ker ⊓ core = ⊥ := by
    apply le_antisymm _ bot_le
    rintro g ⟨hg, q, rfl⟩
    have hq : q = 1 := hi (by simpa using hg)
    simp [hq]
  have hc : ⁅f.ker, core⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_le_inf _ _).trans hdisjoint.le)
  have hk : f.ker ≤ core :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc).trans centralizer_core_le
  exact (MonoidHom.ker_eq_bot_iff f).mp (by simpa only [inf_eq_left.mpr hk] using hdisjoint)

/-- The root map carries the specified core into any subgroup containing all
ten chosen roots. -/
public theorem lift_core_le {G : Type*} [Group G] {x : CoreRoot → G}
    (hx : CoreRelations x) {s w : G} (hs : RootOneRelations s x)
    (hw : ∀ i, w * x i * w⁻¹ = x (weylRoot i))
    (hc : ((s⁻¹) ^ 2 * w) ^ 5 = 1) (ha : (s⁻¹) ^ 4 = 1)
    (h : s⁻¹ * ((s⁻¹) ^ 2 * w) * (s⁻¹)⁻¹ = ((s⁻¹) ^ 2 * w) ^ 2)
    (Q : Subgroup G) (hQ : ∀ i, x i ∈ Q) :
    core.map (lift hx hs hw hc ha h) ≤ Q := by
  rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
  simp only [lift, Core.semidirectLift, SemidirectProduct.lift_inl,
    Core.lift_apply, Core.normalWord]
  repeat' first | apply Q.mul_mem | apply Q.pow_mem
  all_goals exact hQ _

/-- The universal root map is faithful whenever its last root is nontrivial. -/
public theorem lift_injective {G : Type*} [Group G] {x : CoreRoot → G}
    (hx : CoreRelations x) {s w : G} (hs : RootOneRelations s x)
    (hw : ∀ i, w * x i * w⁻¹ = x (weylRoot i))
    (hc : ((s⁻¹) ^ 2 * w) ^ 5 = 1) (ha : (s⁻¹) ^ 4 = 1)
    (h : s⁻¹ * ((s⁻¹) ^ 2 * w) * (s⁻¹)⁻¹ = ((s⁻¹) ^ 2 * w) ^ 2)
    (hz : x 9 ≠ 1) : Function.Injective (lift hx hs hw hc ha h) :=
  hom_injective_of_last_root _ (by simpa using hz)

/-- Root recognition: relations and a surviving last root identify a target
of order 20480 with the specified model. -/
public theorem lift_bijective {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 20480) {x : CoreRoot → G}
    (hx : CoreRelations x) {s w : G} (hs : RootOneRelations s x)
    (hw : ∀ i, w * x i * w⁻¹ = x (weylRoot i))
    (hc : ((s⁻¹) ^ 2 * w) ^ 5 = 1) (ha : (s⁻¹) ^ 4 = 1)
    (h : s⁻¹ * ((s⁻¹) ^ 2 * w) * (s⁻¹)⁻¹ = ((s⁻¹) ^ 2 * w) ^ 2)
    (hz : x 9 ≠ 1) : Function.Bijective (lift hx hs hw hc ha h) :=
  (lift_injective hx hs hw hc ha h hz).bijective_of_nat_card_le (by rw [hcard, card])

end ReeTwo.Centralizer
