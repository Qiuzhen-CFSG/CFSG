module
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.G2
public import Theory.GroupTheory.Amalgam.RankTwoCompletion

/-!
# The ternary G₂ amalgam and the remaining completion theorem

The endpoints are the actual short and long parabolics of the split-octonion
model over ZMod 3. Their common group is their whole intersection, proved to
be the Borel. The native completion is given by the literal inclusions.
Coordinate evaluation proves that its two Weyl involutions lie outside the
Borel and have product of order six. Thus the source hypotheses have a
concrete model instance with the correct field, maps, and hexagon parameter.

`Recognition` names precisely the still-unproved finite G₂(3) specialization
of Aschbacher–Smith F.4.26, printed p.288; F.4.1, printed p.273, explicitly
allows odd characteristic. Its proof is independent completion mathematics.
The I.4.5 owner must still construct such a completion and its involutions
from the original G₂(3)-type configuration, and exclude the strongly
three-embedded branch. Nothing here proves recognition or assumes an
isomorphism for the original ambient group.

The source route is the one cited in I.4.5, printed p.417, via Aschbacher,
*Finite groups of G₂(3)-type*, J. Algebra 257 (2002), 197–214, and F.4.26.
Imported octonion coordinates retain the ATLAS attribution and license in
Theory/AtlasPort (LICENSES/ATLAS.txt).
-/

@[expose] public section
universe u
open Subgroup Theory.GroupTheory
open Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.SplitOctonion
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.TernaryCompletion

/-- Faithful completion of the actual ternary parabolic amalgam. -/
abbrev Completion (G : Type*) [Group G] :=
  RankTwoAmalgam.FaithfulCompletion
    (ChapterF.GreenBook.LieModels.G2.amalgam (F := ZMod 3)) (G := G)

/-- The native model with its literal parabolic inclusion maps. -/
noncomputable def modelCompletion : Completion (Model (ZMod 3)) :=
  RankTwoAmalgam.FaithfulCompletion.ofSubgroups
    parabolic₁ (parabolic₁ ⊓ parabolic₂) parabolic₂ inf_le_left inf_le_right
    parabolics_generate

@[simp] theorem model_left_range : modelCompletion.left.range = parabolic₁ :=
  range_subtype _
@[simp] theorem model_right_range : modelCompletion.right.range = parabolic₂ :=
  range_subtype _
@[simp] theorem model_middle_range : modelCompletion.middle.range = borel := by
  change (parabolic₁ (F := ZMod 3) ⊓ parabolic₂).subtype.range = _
  rw [range_subtype,parabolics_intersection]

theorem weylS_not_mem_borel : (weylS : Model (ZMod 3)) ∉ borel := by
  intro h
  have hp := parabolic_le_pointStabilizer (borel_le_parabolic₂ h)
  obtain ⟨a,ha⟩ := (mem_pointStabilizer_iff _).mp hp
  have hh := congrFun ha 1
  norm_num [weylS,weylSEquiv,weylSLinear,weylSApply,basisVector,Units.smul_def] at hh

theorem weylR_not_mem_borel : (weylR : Model (ZMod 3)) ∉ borel := by
  intro h
  have hh := (borel_le_shortPlaneStabilizer h).1 (basisVector 1)
    (basis_mem_shortPlane 1 (by decide)) 2 (by decide)
  change (-1 : ZMod 3) = 0 at hh
  norm_num at hh

theorem weylS_order : orderOf (weylS : Model (ZMod 3)) = 2 :=
  orderOf_eq_prime weylS_sq (fun h => weylS_not_mem_borel (h ▸ one_mem _))
theorem weylR_order : orderOf (weylR : Model (ZMod 3)) = 2 :=
  orderOf_eq_prime weylR_sq (fun h => weylR_not_mem_borel (h ▸ one_mem _))

theorem weyl_product_order : orderOf ((weylS : Model (ZMod 3)) * weylR) = 6 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide)
  · apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    funext i
    fin_cases i <;> simp [pow_succ,weylS,weylR,weylSEquiv,weylREquiv,
      weylSLinear,weylRLinear,weylSApply,weylRApply]
  · intro p hp hd he
    have hp' : p=2 ∨ p=3 := by
      have hle := Nat.le_of_dvd (by decide : 0<6) hd
      interval_cases p <;> norm_num at *
    rcases hp' with rfl | rfl
    · have hh := congrArg (fun g : Model (ZMod 3) => g.val (basisVector 0) 0) he
      change (0 : ZMod 3) = 1 at hh
      norm_num at hh
    · have hh := congrArg (fun g : Model (ZMod 3) => g.val (basisVector 0) 0) he
      change (0 : ZMod 3) = 1 at hh
      norm_num at hh

/-- The actual standard parabolics overlap in the whole ternary Borel. -/
theorem model_overlap : modelCompletion.left.range ⊓ modelCompletion.right.range =
    modelCompletion.middle.range := by
  rw [model_left_range,model_right_range,model_middle_range,parabolics_intersection]

/-- The native model supplies endpoint involutions outside the whole Borel,
whose product has the required hexagon order. -/
theorem model_endpoint_involutions :
    ∃ s t : Model (ZMod 3),
      s∈modelCompletion.left.range ∧ t∈modelCompletion.right.range ∧
      s∉modelCompletion.middle.range ∧ t∉modelCompletion.middle.range ∧
      orderOf s=2 ∧ orderOf t=2 ∧ orderOf (s*t)=6 := by
  refine ⟨weylS,weylR,?_,?_,?_,?_,weylS_order,weylR_order,weyl_product_order⟩
  · rw [model_left_range]
    exact mem_sup_right (subset_closure (by simp))
  · rw [model_right_range]
    exact weylR_mem_parabolic
  · rw [model_middle_range]
    exact weylS_not_mem_borel
  · rw [model_middle_range]
    exact weylR_not_mem_borel

/-- The exact finite G₂(3) specialization of F.4.26 still to be proved.
This is a proposition naming the independent recognition obligation, not an
instance or a theorem asserting it. The ambient source owner must construct
the completion and its endpoint involutions before applying it. -/
def Recognition : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (c : Completion G) (s t : G),
    s∈c.left.range → t∈c.right.range → s∉c.middle.range → t∉c.middle.range →
    orderOf s=2 → orderOf t=2 → orderOf (s*t)=6 →
    Nonempty (G ≃* Model (ZMod 3))

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.TernaryCompletion
