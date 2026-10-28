module

public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# The kernel on an involution's fixed space

For a faithful binary action, the elements of C_G(t) fixing C_V(t) pointwise
form an elementary abelian subgroup normal in C_G(t). Commuting with t
forces their displacements into C_V(t), and all products of two such
displacements vanish. This supplies the actual relative normal subgroup
used in the Tits equality case of GM04 Lemma 8.8 (internal p.57), refining
the fixed-space argument of Lemma 2.3 (internal p.6).
-/

public section
open Subgroup Representation Representation.BinaryOffender

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem binary_neg (v : V) : -v = v := by
  apply neg_eq_iff_add_eq_zero.mpr
  have h := @two_smul (ZMod 2) V _ _ _ v
  rw [show (2 : ZMod 2) = 0 by decide, zero_smul] at h
  exact h.symm

/-- The pointwise kernel inside the actual involution centralizer. -/
@[expose] noncomputable def involutionFixedKernel (t : G) :=
  subspaceKernel ρ (fixedSpace ρ (zpowers t)) (centralizer {t})

private theorem displacement_mem_fixed (t : G) (ht : t ^ 2 = 1) (v : V) :
    ρ t v - v ∈ fixedSpace ρ (zpowers t) := by
  rw [mem_fixedSpace_zpowers_iff, map_sub]
  have hh : ρ t (ρ t v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, ← pow_two, ht, map_one]
    rfl
  rw [hh]
  simp only [sub_eq_add_neg, binary_neg]
  exact add_comm _ _

private theorem kernel_displacement (t : G) (ht : t ^ 2 = 1) {g : G}
    (hg : g ∈ involutionFixedKernel ρ t) (v : V) :
    ρ g v - v ∈ fixedSpace ρ (zpowers t) := by
  have hc := (mem_centralizer_singleton_iff.mp hg.1)
  have he : ρ t (ρ g v) = ρ g (ρ t v) := by
    simp only [← Module.End.mul_apply, ← map_mul, hc]
  have hf := hg.2 _ (displacement_mem_fixed ρ t ht v)
  rw [mem_fixedSpace_zpowers_iff, map_sub, he]
  rw [map_sub] at hf
  apply sub_eq_sub_iff_add_eq_add.mpr
  simpa only [add_comm] using sub_eq_sub_iff_add_eq_add.mp hf

/-- The actual pointwise kernel is elementary abelian. -/
theorem involutionFixedKernel_elementary (hf : Function.Injective ρ) (t : G) (ht : t ^ 2 = 1) :
    IsElementaryAbelian 2 (involutionFixedKernel ρ t) := by
  have he (g h : involutionFixedKernel ρ t) (v : V) :
      ρ g (ρ h v) = ρ g v + ρ h v - v := by
    have hh := g.property.2 _ (kernel_displacement ρ t ht h.property v)
    rw [map_sub] at hh
    calc
      _ = (ρ g (ρ h v) - ρ g v) + ρ g v := by abel
      _ = (ρ h v - v) + ρ g v := by rw [hh]
      _ = _ := by abel
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
  · intro g h
    apply Subtype.ext
    apply hf
    ext v
    change ρ ((g : G) * (h : G)) v = ρ ((h : G) * (g : G)) v
    simp only [map_mul, Module.End.mul_apply, he]
    rw [add_comm]
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro g
    apply Subtype.ext
    apply hf
    ext v
    change ρ ((g : G) ^ 2) v = ρ 1 v
    rw [pow_two, map_mul, Module.End.mul_apply, he, map_one, Module.End.one_apply]
    have h := binary_neg (ρ g v)
    have hh : ρ g v + ρ g v = 0 := neg_eq_iff_add_eq_zero.mp h
    rw [hh, zero_sub, binary_neg]

private theorem centralizer_stabilizes (t : G) :
    centralizer {t} ≤ subspaceStabilizer ρ (fixedSpace ρ (zpowers t)) := by
  apply le_subspaceStabilizer
  intro g hg v hv
  rw [mem_fixedSpace_zpowers_iff] at hv ⊢
  rw [← Module.End.mul_apply, ← map_mul,
    ← mem_centralizer_singleton_iff.mp hg, map_mul, Module.End.mul_apply, hv]

/-- Normality is relative to C_G(t), with its literal inclusion. -/
theorem involutionFixedKernel_normal (t : G) :
    ((involutionFixedKernel ρ t).subgroupOf (centralizer {t})).Normal :=
  subspaceKernel_normal ρ _ _ (centralizer_stabilizes ρ t)

end Representation.BinaryOffender
