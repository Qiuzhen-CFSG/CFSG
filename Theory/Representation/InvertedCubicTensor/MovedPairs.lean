module
public import Theory.Representation.InvertedCubicTensor
public import Theory.Representation.BinaryOffender.IrreducibleTransport
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.Representation.BinaryOffender.Homogeneous.Basic

/-!
# Component commutators in the cubic tensor decomposition

The explicit cubic pair coordinates carry component differences to the two
copies of the multiplicity differences. Thus the whole component moved space
is the sum of a multiplicity subspace and its marked cubic translate. These
summands are disjoint. Equivariant equivalences also restrict to the specified
inverter-fixed spaces, including quotients with equal central kernels.
Source: Aschbacher–Smith, 13.8.20(a), printed p.954; the final source application
is HigherFieldReduction.OriginalSource.LinearTwoComplete.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace InvertedCubicTensor
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  (σ : Representation (ZMod 2) S₃ V) (ρ : Representation (ZMod 2) D V)
  (hc : ∀ g t v, ρ g (σ t v) = σ t (ρ g v))
  (hfree : ∀ v, σ cubic v = v → v = 0)

include hfree in
/-- Component commutators are exactly the sum of their two multiplicity
copies, with the second copy obtained by the specified cubic element. -/
theorem moved_pair (K : Subgroup D) :
    let I := (subspaceCommutator (multiplicity σ ρ hc) ⊤ K).map (multiplicitySpace σ).subtype
    subspaceCommutator ρ ⊤ K = I ⊔ I.map (σ cubic) := by
  let μ := multiplicity σ ρ hc
  let I := (subspaceCommutator μ ⊤ K).map (multiplicitySpace σ).subtype
  have hI : I ≤ subspaceCommutator ρ ⊤ K := by
    have he := subspaceCommutator_map_embedding ρ μ (MonoidHom.id D)
      (multiplicitySpace σ).subtype (fun _ _ => rfl) K ⊤
    rw [Subgroup.map_id] at he
    exact he.ge.trans (subspaceCommutator_mono_left ρ le_top K)
  have hsecond : I.map (σ cubic) ≤ subspaceCommutator ρ ⊤ K := by
    apply Submodule.map_le_iff_le_comap.mpr
    change (subspaceCommutator μ ⊤ K).map (multiplicitySpace σ).subtype ≤ _
    apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨k,hk,v,_,rfl⟩
    change σ cubic (ρ k v.val - v.val) ∈ subspaceCommutator ρ ⊤ K
    rw [map_sub,←hc]
    exact Submodule.subset_span ⟨k,hk,σ cubic v.val,Submodule.mem_top,rfl⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨k,hk,v,_,rfl⟩
    obtain ⟨⟨a,b⟩,rfl⟩ := (pairEquiv σ hfree).surjective v
    have ha : ρ k a.val - a.val ∈ I :=
      ⟨μ k a - a,Submodule.subset_span ⟨k,hk,a,Submodule.mem_top,rfl⟩,rfl⟩
    have hb : ρ k b.val - b.val ∈ I :=
      ⟨μ k b - b,Submodule.subset_span ⟨k,hk,b,Submodule.mem_top,rfl⟩,rfl⟩
    have he : ρ k (pairEquiv σ hfree (a,b)) - pairEquiv σ hfree (a,b) =
        (ρ k a.val - a.val) + σ cubic (ρ k b.val - b.val) := by
      rw [pairEquiv_apply,map_add,hc,map_sub]
      abel
    rw [he]
    exact Submodule.add_mem_sup ha ⟨_,hb,rfl⟩
  · exact sup_le hI hsecond

include hfree in
/-- Any subspace of the inverter-fixed multiplicity is disjoint from its
cubic translate. This retains the actual ambient inclusion. -/
theorem multiplicity_subspace_disjoint
    (I : Submodule (ZMod 2) (multiplicitySpace σ)) :
    Disjoint (I.map (multiplicitySpace σ).subtype)
      ((I.map (multiplicitySpace σ).subtype).map (σ cubic)) := by
  apply Submodule.disjoint_def.mpr
  intro v hv hw
  obtain ⟨a,ha,rfl⟩ := hv
  obtain ⟨_,⟨b,hb,rfl⟩,he⟩ := hw
  have hp : pairEquiv σ hfree (a,0) = pairEquiv σ hfree (0,b) := by
    simpa only [pairEquiv_apply,Submodule.subtype_apply,Submodule.coe_zero,map_zero,add_zero,zero_add] using he.symm
  have ha0 := congrArg Prod.fst ((pairEquiv σ hfree).injective hp)
  exact congrArg Subtype.val ha0
end InvertedCubicTensor

public noncomputable section
open Representation
namespace InvertedCubicTensor
variable {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  (σ : Representation (ZMod 2) S₃ V) (τ : Representation (ZMod 2) S₃ W)
  (e : V ≃ₗ[ZMod 2] W) (he : ∀ g v, e (σ g v) = τ g (e v))

include he in
/-- An equivariant equivalence restricts to the marked inverter-fixed spaces. -/
def multiplicityCongr : multiplicitySpace σ ≃ₗ[ZMod 2] multiplicitySpace τ :=
  e.ofSubmodules _ _ (by
    ext w
    constructor
    · rintro ⟨v,hv,rfl⟩
      have hv' := (mem_multiplicitySpace σ v).mp hv
      apply (mem_multiplicitySpace τ _).mpr
      exact (he inverter v).symm.trans (congrArg e hv')
    · intro hw
      obtain ⟨v,rfl⟩ := e.surjective w
      refine ⟨v,?_,rfl⟩
      apply (mem_multiplicitySpace σ v).mpr
      apply e.injective
      rw [he]
      exact (mem_multiplicitySpace τ _).mp hw)

theorem multiplicityCongr_apply (v : multiplicitySpace σ) :
    (multiplicityCongr σ τ e he v).val = e v := by rfl
end InvertedCubicTensor

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace InvertedCubicTensor
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]

/-- If a constituent and its translate fill the moved space of a normal
component, their sum is exactly the full ambient orbit of the constituent. -/
theorem orbit_pair_of_moved (ρ : Representation (ZMod 2) D V)
    (K : Subgroup D) [K.Normal] (x : D) (I : Submodule (ZMod 2) V)
    (hpair : subspaceCommutator ρ ⊤ K = I ⊔ I.map (ρ x)) :
    orbitSpan ρ ⊤ I = I ⊔ I.map (ρ x) := by
  have hI : I ≤ subspaceCommutator ρ ⊤ K := le_sup_left.trans hpair.ge
  have hs : (⊤ : Subgroup D) ≤ subspaceStabilizer ρ (subspaceCommutator ρ ⊤ K) :=
    subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer _ ⊤ (by intros; trivial)) le_normalizer_of_normal
  apply le_antisymm ((orbitSpan_le ρ hI hs).trans hpair.le)
  exact sup_le (le_orbitSpan _ _ _)
    (le_iSup (fun g : (⊤ : Subgroup D) => I.map (ρ g)) ⟨x,mem_top _⟩)
end InvertedCubicTensor
