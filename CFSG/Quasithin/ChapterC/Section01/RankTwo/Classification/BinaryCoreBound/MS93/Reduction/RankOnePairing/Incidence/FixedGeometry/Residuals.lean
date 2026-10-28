module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.Pencils
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.FiniteParabolicTransfer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Parabolics.Model

/-!
# Normal generation by the untilded local residual

The two-core Q lies in O^{2′}(M_i), since it is a two-group. The normal
closure of that residual covers the simple marked quotient SL₃(2), as its
image contains a full parabolic. Clause (A) then forces the extension
kernel into that normal closure. Thus the closure is all of M, which in
particular gives the component containment used in MS93 (1.7)(i), p.847.
No two-group assumption on the entire extension kernel is made.
-/

public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry
open Subgroup
universe u
variable {M : Type u} [Group M]

/-- The untilded residual of either actual local normalizer normally generates M. -/
theorem residual_normalClosure_eq_top (e : Extension (M := M)) {Z : Subgroup M}
    (f : LocalFacts e Z) (i : Bool) :
    normalClosure (localResidual (localParabolic e i) : Set M) = ⊤ := by
  let P := localParabolic e i
  let N := normalClosure (localResidual P : Set M)
  have hQN : extensionCore e.projection ≤ N := by
    have hQP := f.core_le i
    have h := le_primeToResidual_of_isPGroup
      ((extensionCore_isPGroup e.projection).comap_subtype (K := P))
    intro q hq
    exact le_normalClosure (show q ∈ localResidual P from
      ⟨⟨q, hQP hq⟩, h hq, rfl⟩)
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank
    (F := ZMod 2) 3 (by decide)
  let : IsSimpleGroup SL := Matrix.PSL3Two.equiv.isSimpleGroup
  have hn : (N.map e.projection).Normal :=
    Normal.map inferInstance e.projection e.base.surjective
  have hm : N.map e.projection = ⊤ := by
    rcases hn.eq_bot_or_eq_top with hbot | htop
    · have hp : modelParabolic e.flag i ≤ (⊥ : Subgroup SL) := by
        rw [← f.residual_image i, ← hbot]
        exact map_mono le_normalClosure
      have hc := card_modelParabolic e.flag i
      rw [bot_unique hp, card_bot] at hc
      contradiction
    · exact htop
  have hs : N ⊔ e.projection.ker = ⊤ := by
    have he := congrArg (fun K : Subgroup SL => K.comap e.projection) hm
    simpa only [comap_map_eq, comap_top] using he
  have hEN : e.projection.ker ≤ N := by
    have he := e.base.no_supplement N (by rw [hs]; exact le_top)
    rwa [sup_eq_left.mpr hQN] at he
  exact (sup_eq_left.mpr hEN).symm.trans hs

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry
