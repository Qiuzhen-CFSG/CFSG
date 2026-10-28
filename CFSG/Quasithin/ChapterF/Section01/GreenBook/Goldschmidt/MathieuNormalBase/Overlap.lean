module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.Goldschmidt.MathieuExtensions
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.ModelResidualAction

/-!
# The original overlap inside the actual outer Mathieu Borel

A marked residual identification transports the faithful original-overlap
action into the compatible automorphism group of the M₁₂ pair.  The proved
outer-Borel equivalence realizes this as a homomorphism into the actual
Aut(M₁₂) Borel.  On the residual overlap it is the literal inner conjugation
embedding.  These identities supply the normal-product reconstruction of
both original endpoints in Goldschmidt (1980), §3.8.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.Goldschmidt.MathieuNormalBase
open Subgroup Theory.GroupTheory RankTwoAmalgam Sporadic.Mathieu
open SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

abbrev baseAmalgam (F : Bool → Subgroup G) :=
  inclusionAmalgam (residualFamily F false) (residualFamily F true)

/-- The residual overlap retains its original ambient element in the original overlap. -/
def baseOverlapEmbedding (F : Bool → Subgroup G) :
    ↥(residualFamily F false ⊓ residualFamily F true) →* ↥(F false ⊓ F true) where
  toFun s := ⟨s.val.val, s.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The original overlap, represented in the source's actual Aut(M₁₂) Borel. -/
def overlapHom (e : Iso (baseAmalgam F) MathieuTwelve.amalgam) :
    ↥(F false ⊓ F true) →* AutMathieuTwelve.autB :=
  MathieuExtensions.outerBorelActionEquiv.symm.toMonoidHom.comp
    (modelResidualAction F e)

theorem overlapHom_injective (h : CubicTreeAction F)
    (e : Iso (baseAmalgam F) MathieuTwelve.amalgam) :
    Function.Injective (overlapHom e) :=
  MathieuExtensions.outerBorelActionEquiv.symm.injective.comp
    (h.modelResidualAction_injective e)

private theorem action_overlapHom (e : Iso (baseAmalgam F) MathieuTwelve.amalgam)
    (t : ↥(F false ⊓ F true)) :
    MathieuExtensions.outerBorelAction (overlapHom e t) = modelResidualAction F e t :=
  MathieuExtensions.outerBorelActionEquiv.apply_symm_apply _

theorem overlapHom_left (e : Iso (baseAmalgam F) MathieuTwelve.amalgam)
    (t : ↥(F false ⊓ F true)) (n : residualFamily F false) :
    ((overlapHom e t : AutMathieuTwelve.autB) : MulAut M12) (e.left n : M12) =
      (e.left ((residualAmalgamAction F t).left n) : M12) := by
  have he := congrArg (fun a : Iso MathieuTwelve.amalgam MathieuTwelve.amalgam =>
    (a.left (e.left n) : M12)) (action_overlapHom e t)
  rw [MathieuExtensions.outerBorelAction_left_apply] at he
  change _ = (e.left ((residualAmalgamAction F t).left (e.left.symm (e.left n))) : M12) at he
  simpa only [e.left.symm_apply_apply] using he

theorem overlapHom_middle (e : Iso (baseAmalgam F) MathieuTwelve.amalgam)
    (t : ↥(F false ⊓ F true)) (n : ↥(residualFamily F false ⊓ residualFamily F true)) :
    ((overlapHom e t : AutMathieuTwelve.autB) : MulAut M12) (e.middle n : M12) =
      (e.middle ((residualAmalgamAction F t).middle n) : M12) := by
  have he := congrArg (fun a : Iso MathieuTwelve.amalgam MathieuTwelve.amalgam =>
    (a.middle (e.middle n) : M12)) (action_overlapHom e t)
  rw [MathieuExtensions.outerBorelAction_middle_apply] at he
  change _ = (e.middle ((residualAmalgamAction F t).middle
    (e.middle.symm (e.middle n))) : M12) at he
  simpa only [e.middle.symm_apply_apply] using he

theorem overlapHom_right (e : Iso (baseAmalgam F) MathieuTwelve.amalgam)
    (t : ↥(F false ⊓ F true)) (n : residualFamily F true) :
    ((overlapHom e t : AutMathieuTwelve.autB) : MulAut M12) (e.right n : M12) =
      (e.right ((residualAmalgamAction F t).right n) : M12) := by
  have he := congrArg (fun a : Iso MathieuTwelve.amalgam MathieuTwelve.amalgam =>
    (a.right (e.right n) : M12)) (action_overlapHom e t)
  rw [MathieuExtensions.outerBorelAction_right_apply] at he
  change _ = (e.right ((residualAmalgamAction F t).right (e.right.symm (e.right n))) : M12) at he
  simpa only [e.right.symm_apply_apply] using he

/-- The residual overlap maps to its exact inner-conjugation copy in the outer Borel. -/
theorem overlapHom_base (e : Iso (baseAmalgam F) MathieuTwelve.amalgam)
    (s : ↥(residualFamily F false ⊓ residualFamily F true)) :
    overlapHom e (baseOverlapEmbedding F s) =
      MathieuExtensions.sourceInnerBorelEmbedding (e.middle s) := by
  apply MathieuExtensions.outerBorelAction_injective
  apply Iso.ext
  · apply MulEquiv.ext
    intro x
    obtain ⟨n, rfl⟩ := e.left.surjective x
    apply Subtype.ext
    rw [MathieuExtensions.outerBorelAction_left_apply, overlapHom_left,
      MathieuExtensions.source_inner_action_left]
    have hc : (residualAmalgamAction F (baseOverlapEmbedding F s)).left n =
        (baseAmalgam F).left s * n * ((baseAmalgam F).left s)⁻¹ := rfl
    rw [hc, map_mul, map_mul, map_inv, e.left_commutes]
    rfl
  · apply MulEquiv.ext
    intro x
    obtain ⟨n, rfl⟩ := e.middle.surjective x
    apply Subtype.ext
    rw [MathieuExtensions.outerBorelAction_middle_apply, overlapHom_middle,
      MathieuExtensions.source_inner_action_middle]
    have hc : (residualAmalgamAction F (baseOverlapEmbedding F s)).middle n =
        s * n * s⁻¹ := rfl
    rw [hc, map_mul, map_mul, map_inv]
    rfl
  · apply MulEquiv.ext
    intro x
    obtain ⟨n, rfl⟩ := e.right.surjective x
    apply Subtype.ext
    rw [MathieuExtensions.outerBorelAction_right_apply, overlapHom_right,
      MathieuExtensions.source_inner_action_right]
    have hc : (residualAmalgamAction F (baseOverlapEmbedding F s)).right n =
        (baseAmalgam F).right s * n * ((baseAmalgam F).right s)⁻¹ := rfl
    rw [hc, map_mul, map_mul, map_inv, e.right_commutes]
    rfl

theorem inner_range_le_overlap_range (e : Iso (baseAmalgam F) MathieuTwelve.amalgam) :
    MathieuExtensions.sourceInnerBorelEmbedding.range ≤ (overlapHom e).range := by
  rintro _ ⟨b, rfl⟩
  obtain ⟨s, rfl⟩ := e.middle.surjective b
  exact ⟨baseOverlapEmbedding F s, overlapHom_base e s⟩

/-- The actual normal extension has either the inner or the full outer Borel image. -/
theorem overlap_range_cases (e : Iso (baseAmalgam F) MathieuTwelve.amalgam) :
    (overlapHom e).range = MathieuExtensions.sourceInnerBorelEmbedding.range ∨
      (overlapHom e).range = ⊤ :=
  MathieuExtensions.source_intermediate_borel_eq _ (inner_range_le_overlap_range e)

/-- Exact preimage of the source inner overlap, used to make endpoint gluing injective. -/
theorem overlapHom_mem_inner_iff (h : CubicTreeAction F)
    (e : Iso (baseAmalgam F) MathieuTwelve.amalgam) (t : ↥(F false ⊓ F true)) :
    overlapHom e t ∈ MathieuExtensions.sourceInnerBorelEmbedding.range ↔
      (t : G) ∈ pResidual 2 G := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨s, rfl⟩ := e.middle.surjective b
    have he : baseOverlapEmbedding F s = t :=
      overlapHom_injective h e ((overlapHom_base e s).trans hb)
    exact he ▸ s.val.property
  · intro ht
    let s : ↥(residualFamily F false ⊓ residualFamily F true) := ⟨⟨t, ht⟩, t.property⟩
    exact ⟨e.middle s, (overlapHom_base e s).symm⟩

end CFSG.Quasithin.ChapterF.GreenBook.Goldschmidt.MathieuNormalBase
