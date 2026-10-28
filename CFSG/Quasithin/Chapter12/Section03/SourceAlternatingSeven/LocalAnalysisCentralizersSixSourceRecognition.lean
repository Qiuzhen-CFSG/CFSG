module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowModelsRecognition
public import Theory.GroupTheory.PCoreCentralPreimageRestriction
public import Theory.Alternating.OddCentralCovers

/-!
# The weight-six residual with its central cover retained

Restrict the original projection L → A₇ to C_L(v)∞. Its image is the
literal A₆ word stabilizer. Centrality modulo O₂(L) restricts to centrality
modulo O₂(C_L(v)∞); conversely the centerless A₆ image kills the whole
central preimage. Thus the restricted projection has exactly that kernel.

This constructs the marked central quotient and proves that the two-core
quotient is quasisimple, with actual A₆ or triple-cover isomorphisms. No
simple A₇ two-core quotient or contrary Sylow-normalizer premise is used.
The component-normality and point-centralizer applications are in
LocalAnalysisCentralizersSixSource. Source: Aschbacher--Smith 12.3.6,
printed p.809, including the A₆ and triple-cover alternatives.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}
namespace Setup.NaturalCoordinates
variable (E : S.NaturalCoordinates)

/-- The original residual projection, marked by its six-letter stabilizer. -/
def sixResidualSimpleProjection (v : V)
    (hv : weight (E.coordinates v).toAdd.val = 6) :
    SylowNormalizer.pointResidual L (v : G) →* alternatingGroup (Fin 6) :=
  (WeightSixGeometry.sixEquiv (E.coordinates v).toAdd hv).toMonoidHom.comp
    (E.sixResidualProjection v hv)

/-- The perfect residual covers the full six-letter stabilizer. -/
theorem sixResidualSimpleProjection_surjective (v : V)
    (hv : weight (E.coordinates v).toAdd.val = 6) :
    Function.Surjective (E.sixResidualSimpleProjection v hv) :=
  (WeightSixGeometry.sixEquiv (E.coordinates v).toAdd hv).surjective.comp
    (E.sixResidualProjection_surjective v hv)

/-- The original map retains exactly the two-core and central-cover kernel. -/
theorem sixResidualSimpleProjection_ker (v : V)
    (hv : weight (E.coordinates v).toAdd.val = 6) :
    (E.sixResidualSimpleProjection v hv).ker =
      centralPreimage (pCore 2 (SylowNormalizer.pointResidual L (v : G))) := by
  apply (centralPreimage_pCore_eq_ker_of_centerless 2 _
    (E.sixResidualSimpleProjection_surjective v hv)
    alternatingGroup.SevenComponent.alternating_six_twoCore
    (alternatingGroup.center_eq_bot (by simp)) ?_).symm
  let K := SylowNormalizer.pointResidual L (v : G)
  let i : K →* L := inclusion ((SylowNormalizer.pointResidual_le L (v : G)).trans inf_le_left)
  apply le_trans ?_ (centralPreimage_pCore_comap_le 2 i (inclusion_injective _))
  intro x hx
  have he : E.sixResidualProjection v hv x = 1 :=
    (WeightSixGeometry.sixEquiv (E.coordinates v).toAdd hv).map_eq_one_iff.mp hx
  have hf : S.projection (i x) = 1 := congrArg Subtype.val he
  change i x ∈ centralPreimage (pCore 2 L)
  exact (QuotientGroup.eq_one_iff (i x)).mp (S.quotient.map_eq_one_iff.mp hf)

/-- The literal O₂,Z quotient of the weight-six residual is A₆. -/
def sixResidualCentralEquiv (v : V)
    (hv : weight (E.coordinates v).toAdd.val = 6) :
    CentralQuotient (SylowNormalizer.pointResidual L (v : G)) ≃*
      alternatingGroup (Fin 6) :=
  (QuotientGroup.quotientMulEquivOfEq (E.sixResidualSimpleProjection_ker v hv).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (E.sixResidualSimpleProjection_surjective v hv))

/-- The recognition isomorphism agrees with the original restricted projection. -/
theorem sixResidualCentralEquiv_mk (v : V)
    (hv : weight (E.coordinates v).toAdd.val = 6)
    (x : SylowNormalizer.pointResidual L (v : G)) :
    E.sixResidualCentralEquiv v hv (QuotientGroup.mk' _ x) =
      E.sixResidualSimpleProjection v hv x := by
  rfl

/-- The two-core quotient is quasisimple even when its center is nontrivial. -/
theorem sixResidualCore_quasisimple (v : V)
    (hv : weight (E.coordinates v).toAdd.val = 6) :
    IsQuasisimple (SylowNormalizer.pointResidual L (v : G) ⧸
      pCore 2 (SylowNormalizer.pointResidual L (v : G))) where
  toIsPerfect := inferInstance
  simple := by
    let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact ((centralPreimageQuotientEquiv _).symm.trans
      (E.sixResidualCentralEquiv v hv)).isSimpleGroup

/-- Both genuine source models, including the concrete triple cover. -/
theorem sixResidualCore_models (v : V)
    (hv : weight (E.coordinates v).toAdd.val = 6) :
    Nonempty ((SylowNormalizer.pointResidual L (v : G) ⧸
      pCore 2 (SylowNormalizer.pointResidual L (v : G))) ≃* alternatingGroup (Fin 6)) ∨
    Nonempty ((SylowNormalizer.pointResidual L (v : G) ⧸
      pCore 2 (SylowNormalizer.pointResidual L (v : G))) ≃* Atlas.Codes.HexEvenAutomorphisms) := by
  let K := SylowNormalizer.pointResidual L (v : G)
  let Q := K ⧸ pCore 2 K
  let : IsQuasisimple Q := E.sixResidualCore_quasisimple v hv
  let e := (centralPreimageQuotientEquiv (pCore 2 K)).symm.trans
    (E.sixResidualCentralEquiv v hv)
  have ho : Odd (Nat.card (center Q)) := by
    apply Nat.not_even_iff_odd.mp
    rw [even_iff_two_dvd]
    exact PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot (G := K) 2) _ le_rfl
  rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 6 (by decide) e ho with h | ⟨_,h⟩
  · exact Or.inl ⟨GLS3.Chapter5.OddCentralCovers.alternatingEquivOfCenterCardOne 6 e h⟩
  · exact Or.inr (GLS3.Chapter5.OddCentralCovers.triple_six_equiv_hexacode e h)

end Setup.NaturalCoordinates
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
