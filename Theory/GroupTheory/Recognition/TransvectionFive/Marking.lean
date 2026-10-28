module

public import Theory.SpecificGroups.BinaryLinear.AffineFourMarking
public import Theory.GroupTheory.Recognition.TransvectionFive.LocalData

/-!
# Marking the original affine translations as a root subgroup

Compose the original affine point marking with its homogeneous-coordinate
centralizer equivalence. The same map sends z to I+E₀₄ and sends every
original translation to the column root group. Surjectivity on those
translations proves literal subgroup equality in the original ambient group.

This is the marked comparison needed to exclude the Held normalizer pattern
in Aschbacher–Smith 12.2.27(1), using Aschbacher, *Sporadic Groups* (1994),
39.1(2) and 40.5(3), pp.213,219.
-/

@[expose] public noncomputable section
open Subgroup

namespace Theory.GroupTheory.TransvectionFive
open BinaryLinear.Affine BinaryLinear.Affine.FourMarking
variable {G : Type*} [Group G] {z : G} {V : Subgroup G}

noncomputable def markingOfAffine (M : PointMarking 4 z V) (hz : z ≠ 1) :
    MarkedCentralizer z where
  equiv := M.centralizerEquiv.trans
    (pointEquiv (M.vectorEquiv ⟨z,M.point_mem⟩) (M.vector_ne_one hz))
  on_point := by
    have he : M.centralizerEquiv ⟨z,mem_centralizer_singleton_iff.mpr rfl⟩ =
        TranslationCentralizer.inclusion (action 4) (M.vectorEquiv ⟨z,M.point_mem⟩)
          (M.vectorEquiv ⟨z,M.point_mem⟩) := Subtype.ext M.on_point
    change (pointEquiv _ _ (M.centralizerEquiv _) : BinaryLinear.TransvectionFiveLocal.SL) = _
    rw [he,pointEquiv_point]

theorem markingOfAffine_on_seed (M : PointMarking 4 z V) (hz : z ≠ 1) (u : V) :
    ((markingOfAffine M hz).equiv ⟨u,M.seed_le u.property⟩ :
      BinaryLinear.TransvectionFiveLocal.SL) =
    embed (SemidirectProduct.inl (action 4
      (rotation (M.vectorEquiv ⟨z,M.point_mem⟩) (M.vector_ne_one hz)) (M.vectorEquiv u))) := by
  have he : M.centralizerEquiv ⟨u,M.seed_le u.property⟩ =
      TranslationCentralizer.inclusion (action 4) (M.vectorEquiv ⟨z,M.point_mem⟩)
        (M.vectorEquiv u) := Subtype.ext (M.on_seed u)
  change (pointEquiv _ _ (M.centralizerEquiv _) : BinaryLinear.TransvectionFiveLocal.SL) = _
  rw [he,pointEquiv_inclusion]

theorem markingOfAffine_column (M : PointMarking 4 z V) (hz : z ≠ 1) :
    V = (markingOfAffine M hz).column := by
  let F := markingOfAffine M hz
  apply le_antisymm
  · intro x hx
    apply (F.mem_pullback_iff Model.column ⟨x,M.seed_le hx⟩).mpr
    rw [markingOfAffine_on_seed M hz ⟨x,hx⟩]
    exact embed_inl_mem_column _
  · intro x hx
    let xC : Subgroup.centralizer ({z} : Set G) := ⟨x,F.pullback_le _ hx⟩
    have hm := (F.mem_pullback_iff Model.column xC).mp hx
    change (F.equiv xC : BinaryLinear.TransvectionFiveLocal.SL) ∈
      BinaryLinear.TransvectionFiveLocal.naturalFactor at hm
    rw [column_eq_translation_range] at hm
    obtain ⟨v,hv⟩ := hm
    let a := action 4 (rotation (M.vectorEquiv ⟨z,M.point_mem⟩) (M.vector_ne_one hz))
    let u := M.vectorEquiv.symm (a.symm v)
    have hu : (F.equiv ⟨u,M.seed_le u.property⟩ : BinaryLinear.TransvectionFiveLocal.SL) =
        F.equiv xC := by
      rw [markingOfAffine_on_seed M hz u]
      change embed (SemidirectProduct.inl (a (M.vectorEquiv (M.vectorEquiv.symm (a.symm v))))) = _
      rw [M.vectorEquiv.apply_symm_apply, a.apply_symm_apply]
      exact hv
    have hux : (u : G) = x := congrArg Subtype.val (F.equiv.injective (Subtype.ext hu))
    exact hux ▸ u.property

theorem exists_marking_of_affine (z : G) (hz : z ≠ 1) (M : PointMarking 4 z V) :
    ∃ F : MarkedCentralizer z, V = F.row ∨ V = F.column :=
  ⟨markingOfAffine M hz, Or.inr (markingOfAffine_column M hz)⟩

end Theory.GroupTheory.TransvectionFive
