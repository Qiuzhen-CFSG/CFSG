module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorInnerWeakClosure.Subspaces
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorConjugateSingularCommutator
public import Theory.Representation.OrthogonalFourPlusMatrix.InnerPlanes
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Calculus

/-!
# The inner-actor branch of tensor weak closure

Let A be a subgroup of corank at most one in an original conjugate of V.
If A lies in T and its action on V is inner, the two singular planes
constructed from a containing tensor Sylow subgroup have action kernels
of index at most four in A. Thus r(G,V)>3 makes both planes normalize
the conjugate module. Their commutators with A lie in a singular subgroup
of order four, so the singular-displacement theorem makes both plane
actions trivial. The two planes detect every inner tensor operator.

This proves the inner branch of Aschbacher–Smith 9.4.4–5, printed
pp.736–737. The same argument covers all inner actor ranks.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- A subgroup of corank at most one in a conjugate tensor module centralizes
the original module whenever its induced action lies in the inner tensor group. -/
theorem tensor_inner_actor_centralizes (hr : 3 < globalR D.fullModule)
    (g : G) {A : Subgroup G}
    (hAW : A ≤ D.fullModule.map (MulAut.conj g).toMonoidHom)
    (hcor : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom) A ≤ 1)
    (hAT : A ≤ (T : Subgroup G))
    (hinner : (A.subgroupOf D.maximalLocal).map m.maximalAction ≤ Binary.linearAction.range) :
    A ≤ centralizer (D.fullModule : Set G) := by
  let W := D.fullModule.map (MulAut.conj g).toMonoidHom
  let := m.fullModule_elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 A := offender_elementary_of_le hAW
  have hAM : A ≤ D.maximalLocal := hAT.trans (le_normalizer_componentOrbit L T)
  have hinj : Function.Injective Binary.linearAction := by
    intro a b h
    exact Binary.action_injective (congrArg LinearEquiv.toLinearMap h)
  let E : Binary.G ≃* Binary.linearAction.range := MonoidHom.ofInjective hinj
  let f₀ : A →* (Binary.V ≃ₗ[ZMod 2] Binary.V) := m.maximalAction.comp (inclusion hAM)
  have hf₀ (a : A) : f₀ a ∈ Binary.linearAction.range :=
    hinner (mem_map.mpr ⟨⟨a,hAM a.property⟩,a.property,rfl⟩)
  let f : A →* Binary.G := E.symm.toMonoidHom.comp (f₀.codRestrict _ hf₀)
  have hf (a : A) : m.maximalAction ⟨a,hAM a.property⟩ = Binary.linearAction (f a) := by
    have hh := congrArg Subtype.val (E.apply_symm_apply ⟨f₀ a,hf₀ a⟩)
    exact hh.symm
  let d := Binary.innerPlaneData f (T.isPGroup'.to_le hAT)
  have hnormalize (U : Submodule (ZMod 2) Binary.V) (K : Subgroup A)
      (hKi : K.index ≤ 4)
      (hfix : ∀ a ∈ K, ∀ u ∈ U, Binary.action (f a) u = u) :
      m.tensorCoordinateSubgroup U ≤ normalizer (W : Set G) := by
    let K₀ := K.map A.subtype
    have hKA : K₀ ≤ A := map_subtype_le _
    have hi : K₀.relIndex A ≤ 4 := by
      change (K₀.subgroupOf A).index ≤ 4
      rw [show K₀.subgroupOf A = K from comap_map_eq_self_of_injective A.subtype_injective K]
      exact hKi
    have hcA : subgroupCorank A K₀ ≤ 2 := by
      change Nat.log 2 (K₀.relIndex A) ≤ 2
      exact (Nat.log_mono_right hi).trans (by decide)
    have hcW : subgroupCorank W K₀ ≤ 3 := by
      rw [offender_corank_add hKA hAW]
      omega
    have hrW : 3 < globalR W := by
      rw [globalR_map_equiv]
      exact hr
    have hCN : centralizer (K₀ : Set G) ≤ normalizer (W : Set G) :=
      centralizer_le_normalizer_of_corank_lt_globalR (hKA.trans hAW)
        ((show (subgroupCorank W K₀ : ℕ∞) ≤ 3 by exact_mod_cast hcW).trans_lt hrW)
    apply le_trans (le_centralizer_iff.mp ?_) hCN
    rintro a ⟨b,hb,rfl⟩
    apply m.tensorCoordinateSubgroup_fixed U ⟨b,hAM b.property⟩
    intro u hu
    rw [hf]
    exact hfix b hb u hu
  have hN₁ := hnormalize d.firstPlane d.firstKernel d.first_index d.first_fixed
  have hN₂ := hnormalize d.secondPlane d.secondKernel d.second_index d.second_fixed
  have hS := m.tensorCoordinateSubgroup_le d.line
  have hScard : Nat.card (m.tensorCoordinateSubgroup d.line) ≤ 4 := by
    rw [m.card_tensorCoordinateSubgroup,d.line_card]
  have hSsing (s : m.tensorCoordinateSubgroup d.line) :
      ((m.sectionData.coordinates ⟨s,hS s.property⟩).toAdd).det = 0 :=
    d.line_singular _ ((m.mem_tensorCoordinateSubgroup d.line _).mp s.property)
  have hcomm₁ : ⁅m.tensorCoordinateSubgroup d.firstPlane,A⁆ ≤ m.tensorCoordinateSubgroup d.line := by
    rw [commutator_comm]
    apply m.tensorCoordinateSubgroup_commutator hAM
    intro a u hu
    rw [hf]
    exact d.first_moved a u hu
  have hcomm₂ : ⁅m.tensorCoordinateSubgroup d.secondPlane,A⁆ ≤ m.tensorCoordinateSubgroup d.line := by
    rw [commutator_comm]
    apply m.tensorCoordinateSubgroup_commutator hAM
    intro a u hu
    rw [hf]
    exact d.second_moved a u hu
  have hc₁ := m.tensor_commutator_eq_bot_of_singular_image g hAW hcor
    (m.tensorCoordinateSubgroup_le d.firstPlane) hN₁ hS hScard hSsing hcomm₁
  have hc₂ := m.tensor_commutator_eq_bot_of_singular_image g hAW hcor
    (m.tensorCoordinateSubgroup_le d.secondPlane) hN₂ hS hScard hSsing hcomm₂
  have hfix (U : Submodule (ZMod 2) Binary.V)
      (hc : ⁅m.tensorCoordinateSubgroup U,A⁆ = ⊥) (a : A) :
      ∀ u ∈ U, Binary.action (f a) u = u := by
    intro u hu
    obtain ⟨v,hv⟩ := m.sectionData.onto (Multiplicative.ofAdd u)
    have hv' : (m.sectionData.coordinates v).toAdd = u := congrArg Multiplicative.toAdd hv
    have hvU : (v : G) ∈ m.tensorCoordinateSubgroup U :=
      (m.mem_tensorCoordinateSubgroup U v).mpr (hv' ▸ hu)
    have hh := (commutator_eq_bot_iff_le_centralizer.mp hc) hvU a a.property
    have he := m.maximalAction_coordinates ⟨a,hAM a.property⟩ v
    have hve : D.fullModule.normalizerMonoidHom
        ⟨(a : G),D.maximalLocal_normalizes_fullModule (hAM a.property)⟩ v = v := by
      apply Subtype.ext
      change (a : G) * (v : G) * (a : G)⁻¹ = v
      rw [hh,mul_inv_cancel_right]
    rw [hve,hf,hv'] at he
    exact he
  intro a ha v hv
  have hfa := d.separate ⟨a,ha⟩ (hfix d.firstPlane hc₁ ⟨a,ha⟩)
    (hfix d.secondPlane hc₂ ⟨a,ha⟩)
  have haid : m.maximalAction ⟨a,hAM ha⟩ = 1 := by rw [hf ⟨a,ha⟩,hfa,map_one]
  have he := m.maximalAction_coordinates ⟨a,hAM ha⟩ ⟨v,hv⟩
  rw [haid] at he
  have hh := congrArg (fun x : D.fullModule => (x : G))
    (m.coordinates_injective (Multiplicative.toAdd.injective he.symm))
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
