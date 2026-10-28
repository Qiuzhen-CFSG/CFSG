module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Modules
public import Theory.Representation.PSL3Two.ParabolicCyclic.PointRecognition
public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual

/-!
# Preserving the given marking in cyclic-seed recognition

Twist the actual quotient representation by inverse transpose followed by
the inverse of the supplied natural marking. The checked point-seed theorem
then gives coordinates in which the original action is exactly the dual of
that marking. This yields SpanQuotient with its literal kernel and ambient
conjugation equation. The point-fixer, cyclic-generation and plane-dimension
premises are intermediate obligations; this module does not derive them
from the geometric seed of MS93 (4.6.12)(3), pp.910--911.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed
open Representation

/-- The precise change of actor needed to recognize the dual of a given marking. -/
def dualTwist (marking : SL ≃* SL) : SL ≃* SL :=
  BinaryLinearThree.AutomorphismAction.graph.trans marking.symm

/-- The change of actor cancels the marked inverse-transpose action. -/
theorem dualTwist_cancel (marking : SL ≃* SL) (g : SL) :
    dualTwist marking (BinaryLinearThree.AutomorphismAction.graph (marking g)) = g := by
  simp only [dualTwist, MulEquiv.trans_apply, BinaryLinearThree.AutomorphismAction.graph_graph,
    MulEquiv.symm_apply_apply]

/-- Cyclic point recognition with the original marking retained explicitly. -/
theorem marked_dual_of_cyclic_seed {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) SL W) (marking : SL ≃* SL) (v : W)
    (hv : v ≠ 0)
    (hfixed : ∀ g ∈ Matrix.PSL3Two.pointParabolicSL,
      ρ (dualTwist marking g) v = v)
    (hgen : BinaryLinearThree.ParabolicCyclic.orbitSpan
      (ρ.comp (dualTwist marking).toMonoidHom) ⊤ v = ⊤)
    (hdim : Module.finrank (ZMod 2) (BinaryLinearThree.ParabolicCyclic.orbitSpan
      (ρ.comp (dualTwist marking).toMonoidHom) Matrix.PSL3Two.lineParabolicSL v) = 2) :
    ∃ e : W ≃ₗ[ZMod 2] Linear.W,
      ∀ g w, e (ρ g w) = Linear.dual (marking g) (e w) := by
  obtain ⟨e⟩ := BinaryLinearThree.ParabolicCyclic.point_seed_equiv_natural
    (ρ.comp (dualTwist marking).toMonoidHom) v hv hfixed hgen hdim
  refine ⟨e.toLinearEquiv, ?_⟩
  intro g w
  have h := LinearMap.congr_fun
    (e.isIntertwining' (BinaryLinearThree.AutomorphismAction.graph (marking g))) w
  change e (ρ (dualTwist marking (BinaryLinearThree.AutomorphismAction.graph (marking g))) w) =
    Linear.dual (marking g) (e w) at h
  rwa [dualTwist_cancel] at h

variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  (common : CommonFacts R source geometry)

/-- The recognized coordinates produce the exact requested ambient quotient. -/
theorem spanQuotient_of_cyclic_seed {c : Vertex R}
    (d : LayerModule source (orbitSpan c)) (v : d.Space) (hv : v ≠ 0)
    (hfixed : ∀ g ∈ Matrix.PSL3Two.pointParabolicSL,
      d.representation (dualTwist common.natural.marking g) v = v)
    (hgen : BinaryLinearThree.ParabolicCyclic.orbitSpan
      (d.representation.comp (dualTwist common.natural.marking).toMonoidHom) ⊤ v = ⊤)
    (hdim : Module.finrank (ZMod 2) (BinaryLinearThree.ParabolicCyclic.orbitSpan
      (d.representation.comp (dualTwist common.natural.marking).toMonoidHom)
        Matrix.PSL3Two.lineParabolicSL v) = 2) :
    Nonempty (SpanQuotient source common c) := by
  obtain ⟨e, he⟩ := marked_dual_of_cyclic_seed d.representation
    common.natural.marking v hv hfixed hgen hdim
  exact ⟨d.spanQuotient common e he⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed
