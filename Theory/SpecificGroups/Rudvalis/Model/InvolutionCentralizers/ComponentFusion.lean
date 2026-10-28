module

public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Shapes
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.SylowCenters
public import Theory.SpecificGroups.Suzuki.InvolutionFusion
public import Theory.SpecificGroups.Suzuki.SchurCoverReduction
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Components and marked Suzuki involution fusion in Rudvalis

For an actual centralizer isomorphism with E₄ × Sz(8), the kernel of projection
to E₄ is normal and isomorphic to the genuine Suzuki matrix group. It is a
component, and every component equals it: a perfect subgroup has trivial
image in the solvable factor, and containment between components is equality.

One involution of this marked kernel in the b² class suffices for all of its
involutions. Suzuki's proved single involution class transports through the
actual subgroup maps; the Rudvalis Sylow-center theorem then gives equality
with the whole center, not merely containment in a Sylow subgroup.

Both the centralizer isomorphism and the single marked fusion witness remain
explicit inputs, to be supplied by the concrete C(a) calculation. No arbitrary
Suzuki embedding is asserted to satisfy that fusion mark.
Source: Aschbacher–Smith, 16.1.7(3)(i) and 16.3.4, printed pp.1172,1178;
GLS3 Table 5.3r and the component calculus of GLS2 Theorem 3.5.
-/

@[expose] public section

open Subgroup
namespace Rudvalis.InvolutionCentralizers

/-- One marked involution and the actual Suzuki isomorphism lift every subgroup involution to a whole Sylow center. -/
theorem suzuki_subgroup_involutions_generate_sylow_centers
    (D : Subgroup Model) (e : D ≃* SzEight)
    (u : D) (hu : orderOf u = 2) (hclass : IsConj (u : Model) (b ^ 2))
    (v : D) (hv : orderOf v = 2) :
    ∃ P : Sylow 2 Model,
      (center P).map (P : Subgroup Model).subtype = zpowers (v : Model) := by
  have h := BenderSuzuki.MatrixGroups.suzuki_involutions_isConj 1 (by decide)
    (e v) (e u) ((e.orderOf_eq v).trans hv) ((e.orderOf_eq u).trans hu)
  have hdu : IsConj v u := by
    have hh : IsConj (e.symm (e v)) (e.symm (e u)) := e.symm.toMonoidHom.map_isConj h
    simpa only [e.symm_apply_apply] using hh
  exact exists_sylow_center_eq_of_isConj_square v
    ((orderOf_injective D.subtype D.subtype_injective v).trans hv)
    ((D.subtype.map_isConj hdu).trans hclass)

variable {C : Type*} [Group C]

/-- The actual normal subgroup selected by projection away from the elementary factor. -/
noncomputable def suzukiKernel (e : C ≃* Elementary 2 × SzEight) : Subgroup C :=
  ((MonoidHom.fst (Elementary 2) SzEight).comp e.toMonoidHom).ker

/-- Normality is intrinsic to the centralizer carrier, not to the ambient Rudvalis group. -/
instance suzukiKernel_normal (e : C ≃* Elementary 2 × SzEight) :
    (suzukiKernel e).Normal := inferInstanceAs (MonoidHom.ker _).Normal

/-- Projection onto the Suzuki factor identifies the marked kernel with the genuine Sz(8) carrier. -/
noncomputable def suzukiKernelEquiv (e : C ≃* Elementary 2 × SzEight) :
    suzukiKernel e ≃* SzEight := by
  let f : suzukiKernel e →* SzEight :=
    ((MonoidHom.snd (Elementary 2) SzEight).comp e.toMonoidHom).comp
      (suzukiKernel e).subtype
  apply MulEquiv.ofBijective f
  constructor
  · intro x y h
    apply Subtype.ext
    apply e.injective
    exact Prod.ext (x.property.trans y.property.symm) h
  · intro s
    refine ⟨⟨e.symm (1, s), ?_⟩, ?_⟩
    · change (e (e.symm (1, s))).1 = 1
      rw [e.apply_symm_apply]
    · change (e (e.symm (1, s))).2 = s
      rw [e.apply_symm_apply]

/-- The marked projection kernel is an actual quasisimple component. -/
theorem suzukiKernel_isComponent (e : C ≃* Elementary 2 × SzEight) :
    Theory.GroupTheory.IsComponent C (suzukiKernel e) := by
  let : Fact (0 < (1 : ℕ)) := ⟨by decide⟩
  let : Theory.GroupTheory.IsQuasisimple SzEight :=
    BenderSuzuki.MatrixGroups.SchurCover.base_isQuasisimple 1
  exact ⟨(suzukiKernel_normal e).isSubnormal,
    Theory.GroupTheory.IsQuasisimple.of_mulEquiv (suzukiKernelEquiv e).symm⟩

/-- Every component is exactly the marked projection kernel. -/
theorem component_eq_suzukiKernel (e : C ≃* Elementary 2 × SzEight)
    (K : Subgroup C) (hK : Theory.GroupTheory.IsComponent C K) :
    K = suzukiKernel e := by
  let := hK.2
  let f : C →* Elementary 2 := (MonoidHom.fst (Elementary 2) SzEight).comp e.toMonoidHom
  have himage : K.map f = ⊥ := by
    let : Group.IsPerfect (K.map f) := Group.IsPerfect.map _
    by_contra hn
    let : Nontrivial (K.map f) := (nontrivial_iff_ne_bot _).mpr hn
    exact Group.IsPerfect.not_isSolvable (K.map f) inferInstance
  apply hK.eq_of_le (suzukiKernel_isComponent e)
  intro x hx
  exact mem_bot.mp (himage ▸ mem_map_of_mem f hx)

/-- Identify each actual component with Sz(8), using its equality with the projection kernel. -/
noncomputable def componentEquivSuzuki (e : C ≃* Elementary 2 × SzEight)
    (K : Subgroup C) (hK : Theory.GroupTheory.IsComponent C K) : K ≃* SzEight :=
  (MulEquiv.subgroupCongr (component_eq_suzukiKernel e K hK)).trans
    (suzukiKernelEquiv e)

/-- For the literal centralizer and any actual component, one marked kernel involution gives the full Sylow-center fusion conclusion. -/
theorem centralizer_component_fusion (t : Model)
    (e : Centralizer t ≃* Elementary 2 × SzEight)
    (u : suzukiKernel e) (hu : orderOf u = 2)
    (hclass : IsConj ((u : Centralizer t) : Model) (b ^ 2))
    (D : Subgroup (Centralizer t))
    (hD : Theory.GroupTheory.IsComponent (Centralizer t) D)
    (v : D) (hv : orderOf v = 2) :
    ∃ P : Sylow 2 Model,
      (center P).map (P : Subgroup Model).subtype =
        zpowers ((v : Centralizer t) : Model) := by
  obtain rfl := component_eq_suzukiKernel e D hD
  let s := suzukiKernelEquiv e
  have h := BenderSuzuki.MatrixGroups.suzuki_involutions_isConj 1 (by decide)
    (s v) (s u) ((s.orderOf_eq v).trans hv) ((s.orderOf_eq u).trans hu)
  have hdu : IsConj v u := by
    have hh : IsConj (s.symm (s v)) (s.symm (s u)) := s.symm.toMonoidHom.map_isConj h
    simpa only [s.symm_apply_apply] using hh
  let f : suzukiKernel e →* Model :=
    (Centralizer t).subtype.comp (suzukiKernel e).subtype
  have hfi : Function.Injective f :=
    (Centralizer t).subtype_injective.comp (suzukiKernel e).subtype_injective
  exact exists_sylow_center_eq_of_isConj_square (f v)
    ((orderOf_injective f hfi v).trans hv) ((f.map_isConj hdu).trans hclass)

end Rudvalis.InvolutionCentralizers
