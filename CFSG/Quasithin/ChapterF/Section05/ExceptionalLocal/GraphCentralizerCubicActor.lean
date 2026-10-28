module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerElementaryTI
public import Theory.SpecificGroups.AlternatingSix.CentralizingCubicActor
/-!
# The centralizing cubic actor in the elementary R₀ branch

The normalizer of the residual centralizer V normalizes the actual A₆ residual K:
conjugating the graph involution inside V identifies the two point-centralizer
residuals. The cubic action already supplied by fusion can therefore be adjusted
by K to centralize K, while retaining its order-three action on V.

This is the independent actor used on each actual V × V₄ subgroup in the
F.5.5 elementary-family contradiction (Aschbacher–Smith, printed p.302).
-/
@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
include h

theorem source_residualCentralizer_normalizes_residual
    (R : Sylow 2 (C c i)) (hR : Tf c i ≤ R) :
    normalizer (sourceResidualCentralizer c i : Set G) ≤
      normalizer (((pResidual 2 (C c i)).map (C c i).subtype) : Set G) := by
  intro g hg
  let f := Source.graphElement c i
  have hf : f ∈ sourceResidualCentralizer c i := source_graph_mem_residual_centralizer c i
  have hgf : g*f*g⁻¹∈sourceResidualCentralizer c i :=
    (mem_normalizer_iff.mp hg f).mp hf
  have heV := sourceResidualCentralizer_eq_point c i z h R hR
  have hres := pointCentralizerResidual_eq_of_conjugate_mem 2 f (g*f*g⁻¹)
    (heV ▸ hgf) (isConj_iff.mpr ⟨g,rfl⟩)
  have hmap := pointCentralizerResidual_map 2 f (MulAut.conj g)
  change (pointCentralizerResidual 2 f).map (MulAut.conj g).toMonoidHom =
    pointCentralizerResidual 2 (g*f*g⁻¹) at hmap
  rw [hres] at hmap
  change g∈normalizer (pointCentralizerResidual 2 f : Set G)
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hmap ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom hx
  · intro hx
    rw [←hmap] at hx
    obtain ⟨y,hy,he⟩ := hx
    exact (MulAut.conj g).injective he ▸ hy

variable [IsElementaryAbelian 2 (sourceResidualCentralizer c i)]
theorem source_residualCentralizer_centralizing_cubic
    (R : Sylow 2 (C c i)) (hR : Tf c i ≤ R) :
    ∃ g : normalizer (sourceResidualCentralizer c i : Set G),
      (g:G) ∈ centralizer (((pResidual 2 (C c i)).map (C c i).subtype) : Set G) ∧
      orderOf ((sourceResidualCentralizer c i).normalizerMonoidHom g) = 3 := by
  let V := sourceResidualCentralizer c i
  let K := (pResidual 2 (C c i)).map (C c i).subtype
  obtain ⟨g,hg,_⟩ := source_residualCentralizer_cubic_action c i z h R hR
  have hKV : K ≤ centralizer (V : Set G) := by
    intro k hk v hv
    change v ∈ sourceResidualCentralizer c i at hv
    rw [sourceResidualCentralizer_eq_point c i z h R hR] at hv
    exact (hv.2 k hk).symm
  obtain ⟨eA⟩ := source_centralizer_residual_alternating c i z h R hR
  let eK : K ≃* alternatingGroup (Fin 6) :=
    ((pResidual 2 (C c i)).equivMapOfInjective (C c i).subtype
      (C c i).subtype_injective).symm.trans eA
  exact AlternatingSix.centralizing_cubic_actor V K eK hKV g
    (source_residualCentralizer_normalizes_residual c i z h R hR g.property) hg
end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
