module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Marked.PairingData

public import Theory.Representation.InvertedThreeFixed

/-!
# Literal marked fixed images from cubic operator identities

`MarkedOperatorRelations` records three identities on the actual conjugation
representation on U. It is an intermediate contract, not a source hypothesis:
the original orthogonal action and inherited span must supply its witness.

These identities give complementary raw fixed spaces and, through an explicit
correction inside E, fixed representatives for the quotient action. The resulting
complementary quotient subspaces are exactly `MarkedSection.fixedImage`, not
arbitrarily chosen copies or unproved full quotient fixed spaces. Right
conjugation is retained in the raw and quotient identities.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed pp.1153–1154, PDF pp.1170–1171.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
open Representation.NormalElementaryQuotient
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement
variable {G D : Type*} [Group G] [Group D]

/-- Operator identities on the original module, before taking its line quotient.
The source construction must prove these from the original action and span. -/
structure MarkedOperatorRelations (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (f : G →* D) (hf : Function.Surjective f)
    (hker : f.ker = centralizer (U : Set G)) (τ y : G) : Prop where
  cubic : representation U f hf hker (f y⁻¹) ^ 2 +
    representation U f hf hker (f y⁻¹) + 1 = 0
  involutory : representation U f hf hker (f τ) *
    representation U f hf hker (f τ) = 1
  inverts : representation U f hf hker (f τ) * representation U f hf hker (f y⁻¹) =
    representation U f hf hker (f y⁻¹) ^ 2 * representation U f hf hker (f τ)
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement.MarkedSection
variable {G D : Type*} [Group G] [Group D]
  (U E : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] [E.Normal]
  (f : G →* D) (hf : Function.Surjective f)
  (hker : f.ker = centralizer (U : Set G))

omit [E.Normal] in
/-- The literal element centralizer is the fixed subspace of conjugation. -/
theorem rawFixed_eq_ker (τ : G) :
    subspace U ((centralizer ({τ} : Set G)).subgroupOf U) =
      (representation U f hf hker (f τ) - 1).ker := by
  ext v
  change (v.toMul : G) ∈ centralizer ({τ} : Set G) ↔
    representation U f hf hker (f τ) v - v = 0
  rw [sub_eq_zero]
  constructor
  · intro hv
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [representation_apply, ← mem_centralizer_singleton_iff.mp hv, mul_inv_cancel_right]
  · intro hv
    apply mem_centralizer_singleton_iff.mpr
    have h := congrArg (fun v : Additive U => (v.toMul : G)) hv
    rw [representation_apply] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm

private theorem ker_conjugate {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) G X) (τ y : G) :
    (ρ (y⁻¹ * τ * y) - 1).ker = ((ρ τ - 1).ker).map (ρ y⁻¹) := by
  have hinv (v : X) : ρ y (ρ y⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hginv (v : X) : ρ y⁻¹ (ρ y v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  ext v
  constructor
  · intro hv
    have hv' : ρ (y⁻¹ * τ * y) v = v := sub_eq_zero.mp hv
    refine ⟨ρ y v, ?_, hginv v⟩
    apply sub_eq_zero.mpr
    have h := congrArg (ρ y) hv'
    simpa only [map_mul, Module.End.mul_apply, Module.End.one_apply, hinv] using h
  · rintro ⟨w, hw, rfl⟩
    apply sub_eq_zero.mpr
    have hw' : ρ τ w = w := sub_eq_zero.mp hw
    simp only [map_mul, Module.End.mul_apply, Module.End.one_apply, hinv, hw']

omit [E.Normal] in
/-- Right conjugation sends the first actual fixed subspace to the second. -/
theorem rawFixed_conjugate (τ y : G) :
    subspace U ((centralizer ({y⁻¹ * τ * y} : Set G)).subgroupOf U) =
      (subspace U ((centralizer ({τ} : Set G)).subgroupOf U)).map
        (representation U f hf hker (f y⁻¹)) := by
  rw [rawFixed_eq_ker U f hf hker, rawFixed_eq_ker U f hf hker]
  exact ker_conjugate ((representation U f hf hker).comp f) τ y

/-- Right conjugation descends to the images of the actual fixed subgroups. -/
theorem fixedImage_conjugate (τ y : G) :
    fixedImage U E (y⁻¹ * τ * y) =
      (fixedImage U E τ).map (action U E f hf hker y⁻¹) := by
  unfold fixedImage
  rw [rawFixed_conjugate U f hf hker τ y, ← Submodule.map_comp, ← Submodule.map_comp]
  rfl

omit [U.Normal] [IsElementaryAbelian 2 U] [E.Normal] in
/-- The denominator intersection is the original fixed subgroup inside E. -/
theorem markedFixed_inf_line (hEU : E ≤ U) (τ : G) :
    markedFixed U τ ⊓ E = markedFixed E τ := by
  ext v
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hEU h.1, h.2⟩, h.1⟩⟩


/-- Every fixed quotient vector has a fixed representative, corrected inside E. -/
theorem fixedImage_eq_ker (τ y : G) (h : MarkedOperatorRelations U f hf hker τ y) :
    fixedImage U E τ = (action U E f hf hker τ - 1).ker := by
  let N := subspace U (E.subgroupOf U)
  let b := representation U f hf hker (f τ)
  let t := representation U f hf hker (f y⁻¹)
  apply Submodule.ext
  intro w
  constructor
  · intro hw
    exact sub_eq_zero.mpr (fixedImage_fixed U E f hf hker τ w hw)
  · intro hw
    have hw' : action U E f hf hker τ w = w := sub_eq_zero.mp hw
    have hδ : ∀ e ∈ N.mkQ.ker, b e = e → ∃ d ∈ N.mkQ.ker, b d - d = e := by
      intro e he hefix
      refine ⟨t e, ?_, Representation.InvertedThreeFixed.fixed_displacement
        t b h.cubic h.inverts e hefix⟩
      change N.mkQ (t e) = 0
      change action U E f hf hker y⁻¹ (N.mkQ e) = 0
      rw [show N.mkQ e = 0 from he, map_zero]
    obtain ⟨v, hv, hqv⟩ := Representation.InvertedThreeFixed.exists_fixed_lift
      b (action U E f hf hker τ) N.mkQ N.mkQ_surjective (fun _ => rfl) h.involutory
      hδ w hw'
    apply (mem_fixedImage_iff U E τ w).mpr
    refine ⟨v, ?_, hqv⟩
    have hv' : v ∈ (b - 1).ker := sub_eq_zero.mpr hv
    rw [← rawFixed_eq_ker U f hf hker τ] at hv'
    exact hv'

/-- The three operator identities descend to the literal quotient action. -/
theorem quotient_operator_relations (τ y : G)
    (h : MarkedOperatorRelations U f hf hker τ y) :
    (action U E f hf hker y⁻¹) ^ 2 + action U E f hf hker y⁻¹ + 1 = 0 ∧
    action U E f hf hker τ * action U E f hf hker τ = 1 ∧
    action U E f hf hker τ * action U E f hf hker y⁻¹ =
      (action U E f hf hker y⁻¹) ^ 2 * action U E f hf hker τ := by
  let N := subspace U (E.subgroupOf U)
  refine ⟨?_, ?_, ?_⟩
  · apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := N.mkQ_surjective w
    have hv := congrArg N.mkQ (LinearMap.congr_fun h.cubic v)
    simpa only [N, map_add, map_zero, LinearMap.add_apply, pow_two,
      Module.End.mul_apply, Module.End.one_apply, LinearMap.zero_apply, action_mk] using hv
  · apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := N.mkQ_surjective w
    have hv := congrArg N.mkQ (LinearMap.congr_fun h.involutory v)
    simpa only [N, Module.End.mul_apply, Module.End.one_apply, action_mk] using hv
  · apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := N.mkQ_surjective w
    have hv := congrArg N.mkQ (LinearMap.congr_fun h.inverts v)
    simpa only [N, pow_two, Module.End.mul_apply, action_mk] using hv

/-- The images of the two actual fixed subgroups are complementary. -/
theorem fixedImage_isCompl (τ y : G) (h : MarkedOperatorRelations U f hf hker τ y) :
    IsCompl (fixedImage U E τ) (fixedImage U E (y⁻¹ * τ * y)) := by
  rw [fixedImage_conjugate U E f hf hker, fixedImage_eq_ker U E f hf hker τ y h]
  obtain ⟨ht, hb, hbt⟩ := quotient_operator_relations U E f hf hker τ y h
  exact Representation.InvertedThreeFixed.isCompl_fixed_map _ _ ht hb hbt

omit [E.Normal] in
/-- The two raw fixed subspaces are complementary before taking the quotient. -/
theorem rawFixed_isCompl (τ y : G) (h : MarkedOperatorRelations U f hf hker τ y) :
    IsCompl (subspace U ((centralizer ({τ} : Set G)).subgroupOf U))
      (subspace U ((centralizer ({y⁻¹ * τ * y} : Set G)).subgroupOf U)) := by
  rw [rawFixed_conjugate U f hf hker, rawFixed_eq_ker U f hf hker]
  exact Representation.InvertedThreeFixed.isCompl_fixed_map _ _ h.cubic h.involutory h.inverts


omit [E.Normal] in
/-- The two literal fixed subgroups generate U. -/
theorem markedFixed_sup_eq (τ y : G) (h : MarkedOperatorRelations U f hf hker τ y) :
    markedFixed U τ ⊔ markedFixed U (y⁻¹ * τ * y) = U := by
  apply le_antisymm (sup_le inf_le_left inf_le_left)
  intro v hv
  have hspan := (rawFixed_isCompl U f hf hker τ y h).sup_eq_top
  have hv' : Additive.ofMul (⟨v, hv⟩ : U) ∈
      subspace U ((centralizer ({τ} : Set G)).subgroupOf U) ⊔
        subspace U ((centralizer ({y⁻¹ * τ * y} : Set G)).subgroupOf U) := by
    rw [hspan]
    trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hv'
  have he : (a.toMul : G) * (b.toMul : G) = v :=
    congrArg (fun x : Additive U => (x.toMul : G)) hab
  rw [← he]
  exact (markedFixed U τ ⊔ markedFixed U (y⁻¹ * τ * y)).mul_mem
    (mem_sup_left ⟨a.toMul.property, ha⟩) (mem_sup_right ⟨b.toMul.property, hb⟩)

omit [E.Normal] in
/-- The two literal fixed subgroups have trivial intersection. -/
theorem markedFixed_inf_eq_bot (τ y : G) (h : MarkedOperatorRelations U f hf hker τ y) :
    markedFixed U τ ⊓ markedFixed U (y⁻¹ * τ * y) = ⊥ := by
  apply le_bot_iff.mp
  intro v hv
  have hz : Additive.ofMul (⟨v, hv.1.1⟩ : U) = 0 :=
    (Submodule.disjoint_def.mp (rawFixed_isCompl U f hf hker τ y h).disjoint)
      _ hv.1.2 hv.2.2
  exact congrArg (fun x : Additive U => (x.toMul : G)) hz

omit [U.Normal] [E.Normal] in
/-- The binary denominator intersection retains the actual centralizer in E. -/
theorem rawFixed_denominator_intersection (τ : G) :
    subspace U (E.subgroupOf U) ⊓
      subspace U ((centralizer ({τ} : Set G)).subgroupOf U) =
        subspace U ((markedFixed E τ).subgroupOf U) := rfl

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement.MarkedSection
