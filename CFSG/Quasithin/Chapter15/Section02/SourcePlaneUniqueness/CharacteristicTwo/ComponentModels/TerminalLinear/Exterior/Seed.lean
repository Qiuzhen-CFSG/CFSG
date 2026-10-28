module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.SeedCentralizer
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Rows
public import Theory.Representation.SL5ExteriorSquare.SeedCoreGeometry
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Duality.Core

/-!
# The original exterior-five centralizer

A generating Sylow-fixed seed in the exterior square has the 2+3 parabolic
as pointwise stabilizer. Complementary wedges transport the cube to the
square with the specified inverse-transpose twist. Applying this to the
literal U∩ZS and the proved equality C_X(U∩ZS)=M₁ marks the actual image
of M₁ through X → X/O₂(X), retaining both twist and conjugating element.

Source: Aschbacher--Smith 15.2.23(d), printed p.1117, and B.5.1.
-/

set_option backward.isDefEq.respectTransparency false
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open ChapterB.QuasisimpleSource Section01
open Representation.SL5TenDimensional

/-- Exterior cube coordinates become square coordinates after the specified graph twist. -/
theorem exterior_square_coordinates
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) {r : ℕ} (hr : r = 2 ∨ r = 3)
    (e : ActionEquiv ρ (exteriorAction r)) :
    ∃ f : ActionEquiv ρ (exteriorAction 2),
      f.groupEquiv = e.groupEquiv ∨
        f.groupEquiv = e.groupEquiv.trans SL5ExteriorSquare.Duality.graph := by
  rcases hr with rfl | rfl
  · exact ⟨e,Or.inl rfl⟩
  · refine ⟨⟨e.groupEquiv.trans SL5ExteriorSquare.Duality.graph,
      e.linearEquiv.trans SL5ExteriorSquare.Duality.hodge, ?_⟩,Or.inr rfl⟩
    intro g v
    change SL5ExteriorSquare.Duality.hodge (e.linearEquiv (ρ g v)) = _
    rw [e.intertwines,SL5ExteriorSquare.Duality.hodge_action]
    rfl

/-- A generating Sylow-fixed seed in the exterior square marks the 2+3 parabolic. -/
theorem exterior_seedKernel
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (e : ActionEquiv ρ (exteriorAction 2))
    (P : Sylow 2 D) (Z : Submodule (ZMod 2) W)
    (hZ : Z ≤ fixedSpace ρ P) (hgen : (⨆ g : D, Z.map (ρ g)) = ⊤) :
    ∃ g : SL5TenDimensional.Group,
      ((subspaceKernel ρ Z ⊤).map e.groupEquiv.toMonoidHom).map
        (MulAut.conj g).toMonoidHom = SL5ExteriorSquare.parabolic 2 := by
  let Q := P.mapSurjective (f := e.groupEquiv.toMonoidHom) e.groupEquiv.surjective
  let Z' := Z.map e.linearEquiv.toLinearMap
  have hdim : 0 < Module.finrank (ZMod 2) (ExteriorModule 2) := by
    rw [finrank_exteriorModule_two]
    decide
  let : Nontrivial (ExteriorModule 2) := Module.nontrivial_of_finrank_pos hdim
  let : Nontrivial W := e.linearEquiv.symm.injective.nontrivial
  have hZn : Z ≠ ⊥ := by
    intro he
    have hb : (⊥ : Submodule (ZMod 2) W) = ⊤ := by
      simpa only [he,Submodule.map_bot,iSup_bot] using hgen
    exact bot_ne_top hb
  have hZ'n : Z' ≠ ⊥ := by
    intro he
    apply hZn
    apply le_bot_iff.mp
    intro v hv
    apply e.linearEquiv.injective
    have hm := Submodule.mem_map_of_mem (f := e.linearEquiv.toLinearMap) hv
    rw [show Z.map e.linearEquiv.toLinearMap = ⊥ from he,Submodule.mem_bot] at hm
    exact hm.trans (map_zero e.linearEquiv).symm
  have hfix : Z' ≤ fixedSpace (exteriorAction 2) Q := by
    rintro _ ⟨v,hv,rfl⟩ ⟨g,hg⟩
    obtain ⟨a,ha,rfl⟩ := hg
    exact (e.intertwines a v).symm.trans (congrArg e.linearEquiv (hZ hv ⟨a,ha⟩))
  obtain ⟨g,hg⟩ := SL5ExteriorSquare.seedKernel_conjugate_parabolic_two Q Z' hZ'n hfix
  refine ⟨g,?_⟩
  have he : (subspaceKernel ρ Z ⊤).map e.groupEquiv.toMonoidHom =
      subspaceKernel (exteriorAction 2) Z' ⊤ := by
    ext a
    constructor
    · rintro ⟨b,hb,rfl⟩
      refine ⟨mem_top _,?_⟩
      rintro _ ⟨v,hv,rfl⟩
      exact (e.intertwines b v).symm.trans (congrArg e.linearEquiv (hb.2 v hv))
    · intro ha
      obtain ⟨b,rfl⟩ := e.groupEquiv.surjective a
      refine ⟨b,⟨mem_top _,?_⟩,rfl⟩
      intro v hv
      apply e.linearEquiv.injective
      rw [e.intertwines]
      exact ha.2 _ (Submodule.mem_map_of_mem hv)
  rw [he]
  exact hg

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The image of the original M₁ is the actual 2+3 exterior parabolic. -/
theorem M1_image_parabolic_of_exterior
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G))
    {r : ℕ} (hr : r = 2 ∨ r = 3) :
    letI := U_elementary d hI hfit hXI
    ∀ e : ActionEquiv (U_representation d hI hfit hXI hn) (exteriorAction r),
    ∃ (f : ActionEquiv (U_representation d hI hfit hXI hn) (exteriorAction 2))
      (g : SL5TenDimensional.Group),
      (f.groupEquiv = e.groupEquiv ∨
        f.groupEquiv = e.groupEquiv.trans SL5ExteriorSquare.Duality.graph) ∧
      ((((M1 X ZS).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
        f.groupEquiv.toMonoidHom).map (MulAut.conj g).toMonoidHom =
          SL5ExteriorSquare.parabolic 2 := by
  let := U_elementary d hI hfit hXI
  intro e
  let σ := U_representation d hI hfit hXI hn
  obtain ⟨f,hf⟩ := exterior_square_coordinates σ hr e
  let q := QuotientGroup.mk' (pCore 2 X)
  let : (X.subgroupOf I).Normal := normal_subgroupOf_of_le_normalizer hn
  obtain ⟨S,hS⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    (d.sylow_in_escape hI) hXI (inferInstance : (X.subgroupOf I).Normal).isSubnormal
  let P := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let Z := AddSubgroup.toZModSubmodule 2 (ZS.subgroupOf (U X ZS)).toAddSubgroup
  have hZ : Z ≤ fixedSpace σ P := by
    intro u hu p
    obtain ⟨x,hx,he⟩ := p.property
    change σ (p : X ⧸ pCore 2 X) u = u
    rw [← he]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [U_representation_apply]
    have hxc : (x : G) ∈ centralizer (ZS : Set G) :=
      ((hS.le.trans inf_le_left) (mem_map_of_mem X.subtype hx)).2
    have hh : (u.toMul : G) * (x : G) = (x : G) * (u.toMul : G) := hxc _ hu
    rw [← hh,mul_inv_cancel_right]
  obtain ⟨g,hg⟩ := exterior_seedKernel σ f P Z hZ
    (U_seed_module_generates d hI hfit hXI hn σ (U_representation_apply d hI hfit hXI hn))
  refine ⟨f,g,hf,?_⟩
  rw [M1_image_eq_seedKernel d hI hfit hXI hn]
  exact hg

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear
