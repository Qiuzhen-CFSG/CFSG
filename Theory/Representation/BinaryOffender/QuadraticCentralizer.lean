module
public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.Representation.BinaryOffender.IrreducibleSection
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Quadratic actors and the centralizer of a moved factor

If [K,A]=K and A is quadratic, every displacement by an element of
A intersect C(K) is fixed by A. That displacement space is invariant
under K, so the commutator identity makes K fix it too. If K has zero
fixed space, faithfulness forces the intersection to be trivial.
For a normal quasisimple K it suffices that A does not centralize K.

The nonbinary linear-three MS application uses this on the entire central
omega, retaining its even covering kernel and the literal initial projection.
Source: the elementary quadratic-action argument in the setting of
Aschbacher--Smith B.1.5 and C.1.34, printed pp.69--70,136--137.
-/

public section
open Subgroup Theory.GroupTheory
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- A quadratic subgroup generating a fixed-free factor by commutators
has trivial intersection with its centralizer. -/
theorem quadratic_inf_centralizer_eq_bot
    (ρ : Representation (ZMod 2) G V) (K A : Subgroup G)
    (hf : Function.Injective ρ) (hfix : fixedSpace ρ K = ⊥)
    (hgen : ⁅K,A⁆ = K) (hq : IsQuadratic ρ A) :
    A ⊓ centralizer (K : Set G) = ⊥ := by
  apply bot_unique
  rintro a ⟨ha,hac⟩
  let W := LinearMap.range (ρ a - 1)
  have hK : K ≤ subspaceStabilizer ρ W := by
    apply le_subspaceStabilizer
    rintro k hk v ⟨w,rfl⟩
    refine ⟨ρ k w,?_⟩
    change ρ a (ρ k w) - ρ k w = ρ k (ρ a w - w)
    rw [map_sub,←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul,
      mem_centralizer_iff.mp hac k hk]
  have hA : A ≤ subspaceStabilizer ρ W := by
    apply le_subspaceStabilizer
    rintro b hb v ⟨w,rfl⟩
    change ρ b (ρ a w-w) ∈ W
    rw [hq b hb a ha w]
    exact ⟨w,rfl⟩
  let H := K ⊔ A
  let I := invariantSubspace ρ H W (sup_le hK hA)
  let σ := I.toRepresentation
  have hAk : A.subgroupOf H ≤ σ.ker := by
    intro b hb
    apply LinearMap.ext
    rintro ⟨v,w,rfl⟩
    exact Subtype.ext (hq b.val hb a ha w)
  have hg : ⁅K.subgroupOf H,A.subgroupOf H⁆ = K.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_commutator,
      map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),
      map_subgroupOf_eq_of_le (show A ≤ H from le_sup_right),hgen]
  have hKk : K.subgroupOf H ≤ σ.ker := by
    rw [←hg]
    exact (commutator_mono le_rfl hAk).trans (commutator_le_right _ _)
  have haρ : ρ a = ρ 1 := by
    rw [map_one]
    apply LinearMap.ext
    intro v
    have hz : ρ a v-v ∈ fixedSpace ρ K := by
      intro k
      exact congrArg Subtype.val (LinearMap.congr_fun
        (hKk (show (⟨k,mem_sup_left k.property⟩ : H) ∈ K.subgroupOf H from k.property))
        (⟨ρ a v-v,⟨v,rfl⟩⟩ : W))
    rw [hfix,Submodule.mem_bot] at hz
    exact sub_eq_zero.mp hz
  exact hf haρ

/-- For a normal quasisimple factor, noncentral action supplies the required
commutator generation without assuming a trivial center. -/
theorem quadratic_inf_centralizer_eq_bot_of_component
    (ρ : Representation (ZMod 2) G V) (K A : Subgroup G)
    [K.Normal] [IsQuasisimple K]
    (hf : Function.Injective ρ) (hfix : fixedSpace ρ K = ⊥)
    (hnot : ¬ A ≤ centralizer (K : Set G)) (hq : IsQuadratic ρ A) :
    A ⊓ centralizer (K : Set G) = ⊥ := by
  have hgen : ⁅K,A⁆ = K := by
    rcases (show IsComponent G K from
      ⟨(inferInstance : K.Normal).isSubnormal,inferInstance⟩).commutator_dichotomy A with hb | he
    · exact (hnot (le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp hb))).elim
    · exact le_antisymm (commutator_le_left K A)
        ((le_iSup_conjugates K A).trans_eq he.symm)
  exact quadratic_inf_centralizer_eq_bot ρ K A hf hfix hgen hq

end Representation.BinaryOffender
