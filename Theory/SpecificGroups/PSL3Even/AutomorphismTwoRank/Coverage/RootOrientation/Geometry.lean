module

public import Theory.SpecificGroups.PSL3.RootPlaneGeometry
public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage.RootOrientation.Signs

/-!
# Recovering A₂ roots from the opposite root planes

The two upper elementary abelian planes intersect in the highest root. The
upper unipotent subgroup intersects the normalizer of each lower plane in
one simple root. The existing root-plane normalizer theorem identifies these
normalizers with actual projective parabolics; their exact SL₃ preimages and
inverse transpose reduce membership to two vanishing matrix coordinates.
Inverse transpose gives the corresponding negative-root identities.

These calculations use the literal SL₃/Z(SL₃) model and are valid also over
the four-element field. No automorphism lift or simplicity assumption is used.
Source: the normalization step toward GLS3 Theorem 2.5.12(a) and the matrix
conventions in §2.7, `refs/KGroup/GLS3/chapter2.tex`, lines 1111–1115.
-/

@[expose] public section

open scoped MatrixGroups
open Matrix Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3Even.UnipotentGeometry
open Matrix.PSL3.OuterSolvable Matrix.PSL3.OuterSolvable.OddPrimeCoverage
open Matrix.PSL3.RootPlaneGeometry
namespace Matrix.PSL3Even.AutomorphismCoverage.RootOrientation
variable (F : Type*) [Field F]

def lowerPlane (b : Bool) : Subgroup PSL(3,F) :=
  (rootPlane F b).map (graph F).toMonoidHom

def simpleIndex (b : Bool) : Fin 3 := if b then 0 else 2

theorem rootPlane_eq_map (b : Bool) :
    rootPlane F b = (if b then V₁ F else V₂ F).map (projective F) := by
  rw [rootPlane, rootPlaneSL, Subgroup.map_map]
  rfl

theorem graph_twice (x : PSL(3,F)) : graph F (graph F x) = x :=
  congrArg (fun a : MulAut PSL(3,F) => a x) (graph_sq F)

theorem map_graph_twice (H : Subgroup PSL(3,F)) :
    (H.map (graph F).toMonoidHom).map (graph F).toMonoidHom = H := by
  rw [Subgroup.map_map]
  have he : (graph F).toMonoidHom.comp (graph F).toMonoidHom = MonoidHom.id _ := by
    ext x
    exact graph_twice F x
  rw [he, Subgroup.map_id]

theorem mem_map_graph (H : Subgroup PSL(3,F)) (x : PSL(3,F)) :
    x ∈ H.map (graph F).toMonoidHom ↔ graph F x ∈ H := by
  constructor
  · rintro ⟨y,hy,rfl⟩
    change graph F (graph F y) ∈ H
    rw [graph_twice]
    exact hy
  · intro hx
    exact ⟨graph F x,hx,graph_twice F x⟩

private def rootU (k : Fin 3) (a : F) : U F :=
  ⟨if k = 2 then a else 0, if k = 0 then a else 0, if k = 1 then a else 0⟩

private theorem projective_rootU (k : Fin 3) (a : F) :
    projective F (rootU F k a) = rootElement (rootFirst_ne_second k) a := by
  apply congrArg (QuotientGroup.mk : SL(3,F) → PSL(3,F))
  apply Subtype.ext
  change matrix F (rootU F k a) = 1 + Matrix.single (rootFirst k) (rootSecond k) a
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [rootU, matrix, rootFirst, rootSecond]

private theorem mem_positiveRoot (u : U F) (k : Fin 3) :
    projective F u ∈ positiveRoot k ↔ ∃ a, u = rootU F k a := by
  constructor
  · rintro ⟨a,ha⟩
    change rootElement (rootFirst_ne_second k) a.toAdd = projective F u at ha
    rw [← projective_rootU] at ha
    exact ⟨a.toAdd, (projective_injective F ha).symm⟩
  · rintro ⟨a,rfl⟩
    rw [projective_rootU]
    exact rootElement_mem _ _

theorem positiveRoot_le_upper (k : Fin 3) : positiveRoot (F:=F) k ≤ upperUnipotent F := by
  rintro _ ⟨a,rfl⟩
  change rootElement (rootFirst_ne_second k) a.toAdd ∈ _
  rw [← projective_rootU, upperUnipotent, ← projective_range]
  exact ⟨_,rfl⟩

private theorem mem_simpleRoot (u : U F) (b : Bool) :
    projective F u ∈ positiveRoot (simpleIndex b) ↔
      if b then u.x = 0 ∧ u.c = 0 else u.c = 0 ∧ u.y = 0 := by
  rw [mem_positiveRoot]
  cases b <;> simp only [simpleIndex, Bool.false_eq_true, ↓reduceIte]
  · constructor
    · rintro ⟨a,rfl⟩; exact ⟨rfl,rfl⟩
    · rintro ⟨hc,hy⟩; exact ⟨u.x, U.ext rfl hy hc⟩
  · constructor
    · rintro ⟨a,rfl⟩; exact ⟨rfl,rfl⟩
    · rintro ⟨hx,hc⟩; exact ⟨u.y, U.ext hx rfl hc⟩

theorem graph_positiveRoot (k : Fin 3) :
    (positiveRoot (F:=F) k).map (graph F).toMonoidHom = negativeRoot k := by
  ext x
  constructor
  · rintro ⟨_,⟨a,rfl⟩,rfl⟩
    exact ⟨Multiplicative.ofAdd (-a.toAdd), (graph_rootElement _ _).symm⟩
  · rintro ⟨a,rfl⟩
    refine ⟨rootElement (rootFirst_ne_second k) (-a.toAdd), rootElement_mem _ _, ?_⟩
    change graph F (rootElement _ _) = rootElement _ _
    rw [graph_rootElement, neg_neg]

theorem planes_inter : rootPlane F true ⊓ rootPlane F false = positiveRoot 1 := by
  rw [rootPlane_eq_map, rootPlane_eq_map]
  change (V₁ F).map (projective F) ⊓ (V₂ F).map (projective F) = _
  rw [← Subgroup.map_inf _ _ _ (projective_injective F), root_planes_inter]
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩
    obtain ⟨hx,hy⟩ := (mem_Z F u).mp hu
    apply (mem_positiveRoot F u 1).mpr
    exact ⟨u.c, U.ext hx hy rfl⟩
  · rintro ⟨a,rfl⟩
    change rootElement (rootFirst_ne_second 1) a.toAdd ∈ _
    rw [← projective_rootU]
    exact ⟨rootU F 1 a.toAdd, (mem_Z F _).mpr ⟨rfl,rfl⟩, rfl⟩

theorem lowerPlanes_inter : lowerPlane F true ⊓ lowerPlane F false = negativeRoot 1 := by
  rw [lowerPlane, lowerPlane, ← Subgroup.map_inf _ _ (graph F).toMonoidHom (graph F).injective,
    planes_inter, graph_positiveRoot]

theorem simpleRoot_le_plane (b : Bool) :
    positiveRoot (F:=F) (simpleIndex b) ≤ rootPlane F (!b) := by
  rintro _ ⟨a,rfl⟩
  change rootElement (rootFirst_ne_second (simpleIndex b)) a.toAdd ∈ _
  rw [← projective_rootU, rootPlane_eq_map]
  refine ⟨rootU F (simpleIndex b) a.toAdd, ?_, rfl⟩
  cases b <;> simp [simpleIndex, rootU]

theorem simpleRoot_plane_iff (a b : Bool) :
    positiveRoot (F:=F) (simpleIndex a) ≤ rootPlane F (!b) ↔ a = b := by
  constructor
  · intro h
    have hm := h (rootElement_mem (F:=F) (rootFirst_ne_second (simpleIndex a)) 1)
    rw [← projective_rootU, rootPlane_eq_map] at hm
    obtain ⟨u,hu,he⟩ := hm
    have hh := projective_injective F he
    subst u
    cases a <;> cases b <;> simp_all [simpleIndex, rootU]
  · rintro rfl; exact simpleRoot_le_plane F a

variable [Finite F]
private theorem graph_projective_mem_parabolic (b : Bool) (u : U F) :
    graph F (projective F u) ∈ parabolic F b ↔
      if b then u.x = 0 ∧ u.c = 0 else u.c = 0 ∧ u.y = 0 := by
  change projection F ((SpecialLinearGroup.transpose (specialLinear F u))⁻¹) ∈ _ ↔ _
  rw [map_inv, Subgroup.inv_mem_iff]
  cases b
  · change SpecialLinearGroup.transpose (specialLinear F u) ∈
      (lineParabolic F).comap (projection F) ↔ _
    rw [lineParabolic_comap, mem_lineParabolicSL_iff]
    rfl
  · change SpecialLinearGroup.transpose (specialLinear F u) ∈
      (pointParabolic F).comap (projection F) ↔ _
    rw [pointParabolic_comap, mem_pointParabolicSL_iff]
    rfl

variable [CharP F 2]
theorem upper_inf_normalizer_lowerPlane (b : Bool) :
    upperUnipotent F ⊓ Subgroup.normalizer (lowerPlane F b) =
      positiveRoot (simpleIndex b) := by
  rw [lowerPlane, ← Subgroup.map_equiv_normalizer_eq, normalizer_rootPlane]
  apply le_antisymm
  · rintro x ⟨hx,hN⟩
    change x ∈ unipotent F at hx
    rw [← projective_range] at hx
    obtain ⟨u,rfl⟩ := hx
    exact (mem_simpleRoot F u b).mpr ((graph_projective_mem_parabolic F b u).mp
      ((mem_map_graph F _ _).mp hN))
  · intro x hx
    have hU := positiveRoot_le_upper F (simpleIndex b) hx
    refine ⟨hU,?_⟩
    change x ∈ unipotent F at hU
    rw [← projective_range] at hU
    obtain ⟨u,rfl⟩ := hU
    exact (mem_map_graph F _ _).mpr ((graph_projective_mem_parabolic F b u).mpr
      ((mem_simpleRoot F u b).mp hx))

theorem lower_inf_normalizer_rootPlane (b : Bool) :
    lowerUnipotent F ⊓ Subgroup.normalizer (rootPlane F b) =
      negativeRoot (simpleIndex b) := by
  have h := congrArg (fun H : Subgroup PSL(3,F) => H.map (graph F).toMonoidHom)
    (upper_inf_normalizer_lowerPlane F b)
  rw [Subgroup.map_inf _ _ (graph F).toMonoidHom (graph F).injective, Subgroup.map_equiv_normalizer_eq,
    lowerPlane, map_graph_twice, graph_positiveRoot] at h
  exact h
end Matrix.PSL3Even.AutomorphismCoverage.RootOrientation
