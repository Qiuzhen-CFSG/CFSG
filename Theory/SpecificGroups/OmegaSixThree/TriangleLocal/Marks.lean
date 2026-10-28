module
public import Theory.SpecificGroups.OmegaSixThree.TriangleLocal.Vertex
public import Theory.SpecificGroups.OmegaSixThree.VertexCoordinates
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation
public import Theory.GroupTheory.PCoreProduct

/-!
# Core, complement and graph marks in the F.5 local group

The original local two-core maps to the product of the two literal Klein-four
kernels of S₄ → S₃. Thus it is E₁₆ and lies in the vertex intersection. The
independent second S₄ factor has its own exact equivalence. Finally the source
graph involution and the first D₈ central involution are retained as different
explicit double transpositions. These are the markings needed to compare the
local and vertex maps in F.5.7.
Source: Aschbacher--Smith F.5.3 and F.5.7, printed pp.300--303.
-/

@[expose] public section

namespace OmegaSixThree.TriangleLocal
open SixTernaryCoordinates OrthogonalityGraph Subgroup
open Theory.SpecificGroups.SymmetricSix.DuadCalculation

/-- The marked E₁₆ is O₂ of the full local group, not O₂ of its vertex subgroup. -/
abbrev localCore := pCore 2 H

theorem core_map : localCore.map productEquiv.toMonoidHom = core.prod core := by
  rw [pCore_map_iso,pCore_prod,←core_eq]

theorem core_preimage : localCore = (core.prod core).comap toProduct := by
  rw [←core_map]
  exact (Subgroup.comap_map_eq_self_of_injective toProduct_injective _).symm

noncomputable def coreEquiv : localCore ≃* core × core :=
  ((productEquiv.subgroupMap localCore).trans (MulEquiv.subgroupCongr core_map)).trans
    (Subgroup.prodEquiv core core)

theorem core_card : Nat.card localCore = 16 := by
  rw [Nat.card_congr coreEquiv.toEquiv,Nat.card_prod,
    Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_card]

theorem core_elementary : IsElementaryAbelian 2 localCore := by
  refine { is_comm := ⟨?_⟩, exponent_dvd_p := ?_ }
  · intro a b
    apply coreEquiv.injective
    rw [map_mul,map_mul]
    apply Prod.ext <;> exact IsMulCommutative.is_comm.comm _ _
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro a
    apply coreEquiv.injective
    rw [map_pow,map_one]
    apply Prod.ext <;>
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 core) _

theorem core_le_vertexLocal : localCore ≤ vertexLocal := by
  rw [core_preimage,vertexLocal_eq]
  apply Subgroup.comap_mono
  apply Subgroup.prod_mono _ le_top
  intro p hp
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  exact (show ∀ p : Four, p ∈ core → p * delta = delta * p by
    decide +kernel) p hp

/-- The independent S₄ complement has its original second-factor embedding. -/
noncomputable def complementEquiv : complementFactor ≃* Four where
  toFun g := (productEquiv g.val).2
  invFun p := ⟨productEquiv.symm (1,p),by
    change productEquiv (productEquiv.symm (1,p)) ∈ (⊥ : Subgroup Four).prod ⊤
    rw [productEquiv.apply_symm_apply]
    exact ⟨rfl,mem_top _⟩⟩
  left_inv g := by
    apply Subtype.ext
    apply productEquiv.injective
    rw [productEquiv.apply_symm_apply]
    apply Prod.ext
    · exact g.property.1.symm
    · rfl
  right_inv p := by simp
  map_mul' g h := congrArg Prod.snd (map_mul productEquiv g.val h.val)

theorem graph_mem : vertexGraphInvolution ∈ H := by
  apply (mem_triangleStabilizer_iff _).mpr
  apply Set.EqOn.image_eq_self
  intro p hp
  obtain ⟨i,rfl⟩ := (mem_standardTriangle_iff p).mp hp
  apply (point_eq_iff _ _ _ _).mpr
  exact (show ∀ i : Fin 3, signed (graphInvolution (negativeBasis i)) (negativeBasis i) by
    unfold signed; decide +kernel) i

def graphElement : H := ⟨vertexGraphInvolution,graph_mem⟩

/-- The source graph involution is the other nontrivial Klein-four element;
it is distinct from the central involution of the displayed vertex D₈. -/
theorem graphElement_image : productEquiv graphElement = (Equiv.swap 0 3 * Equiv.swap 1 2,1) := by
  apply Prod.ext <;> apply Equiv.ext <;> intro i
  · apply imageIndex_eq
    exact (show ∀ i : Fin 4, signed (graphInvolution (tetra false i))
        (tetra false ((Equiv.swap 0 3 * Equiv.swap 1 2 : Four) i)) by
      unfold signed; decide +kernel) i
  · apply imageIndex_eq
    exact (show ∀ i : Fin 4, signed (graphInvolution (tetra true i)) (tetra true i) by
      unfold signed; decide +kernel) i

theorem graphElement_mem_core : graphElement ∈ localCore := by
  rw [core_preimage]
  change productEquiv graphElement ∈ core.prod core
  rw [graphElement_image]
  constructor
  · change (Equiv.swap 0 3 * Equiv.swap 1 2 : Four) ∈ core
    decide +kernel
  · exact core.one_mem

theorem pairElement_mem_core : pairElement ∈ localCore := by
  rw [core_preimage]
  change productEquiv pairElement ∈ core.prod core
  rw [show productEquiv pairElement = (delta,1) from pairElement_image]
  constructor
  · change delta ∈ core
    decide +kernel
  · exact core.one_mem

end OmegaSixThree.TriangleLocal
