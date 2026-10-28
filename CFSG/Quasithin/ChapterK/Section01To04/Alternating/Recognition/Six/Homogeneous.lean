module
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.FourSpace
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.SmallParameter.FlagModule
public import Theory.Representation.BinaryAlternatingSixModels.CatalogueSource
public import Theory.Representation.BinaryAlternatingSixNaturalNormalizer
public import Theory.Representation.BinaryOffender.Homogeneous.DoubleCoordinates

/-!
# A proper homogeneous A₆ module of degree at most eight

The full binary catalogue and faithfulness force the repeated constituent
into degree four. Properness and homogeneity then construct exactly two
copies, and four-space recognition supplies one common A₆ marking on them.
The resulting coordinates intertwine the original representation.

Source: Aschbacher--Smith G.11.7, printed p.366. The original rank-two
application is SmallRows.AlternatingSixActionSourceMultiplicity.
-/

public noncomputable section
open Representation
namespace CFSG.Quasithin.ChapterK.Alternating.RecognitionInputs.Six
/-- The homogeneous degree bound constructs a marked natural double, including
its original action, rather than only determining the dimension. -/
theorem naturalCoordinates_of_homogeneous_degree_le_eight
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) D V)
    (e6 : D ≃* alternatingGroup (Fin 6))
    (R : Subrepresentation ρ) [IsIrreducible R.toRepresentation]
    (hf : Function.Injective R.toRepresentation)
    (hh : BinaryOffender.Homogeneous.homogeneousPart R ⊤ = ⊤)
    (hp : R.toSubmodule ≠ ⊤) (hd : Module.finrank (ZMod 2) V ≤ 8) :
    BinaryAlternatingSixNaturalNormalizer.HasNaturalCoordinates ρ := by
  let σ := R.toRepresentation.comp e6.symm.toMonoidHom
  let : IsIrreducible σ := (irreducible_comp_surjective_iff
    e6.symm.toMonoidHom e6.symm.surjective _).mpr inferInstance
  have hfσ : Function.Injective σ := hf.comp e6.symm.injective
  have hlo := ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.SmallParameter.degree_ge_four σ hfσ
  have hdeg := BinaryAlternatingSix.alternating_degrees σ
  have hle := R.toSubmodule.finrank_le.trans hd
  have hfour : Module.finrank (ZMod 2) R.toSubmodule = 4 := by omega
  obtain ⟨c⟩ := BinaryOffender.Homogeneous.double_coordinates_of_degree_le
    R inferInstance hh hp (by omega)
  obtain ⟨a⟩ := ChapterK.Alternating.RecognitionInputs.Six.actionEquiv_of_faithful_fourSpace σ hfσ hfour
  have ha (k : D) (w : R.toSubmodule) :
      a.linearEquiv (R.toRepresentation k w) =
      BinaryAlternatingSixNaturalNormalizer.action (a.groupEquiv (e6 k)) (a.linearEquiv w) := by
    simpa only [σ, ChapterB.QuasisimpleSource.alternatingNatural, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using a.intertwines (e6 k) w
  refine ⟨e6.trans a.groupEquiv, Or.inr
    ⟨c.toLinearEquiv.trans (a.linearEquiv.prodCongr a.linearEquiv), ?_⟩⟩
  intro k w
  have hc := LinearMap.congr_fun (c.isIntertwining' k) w
  change c (ρ k w) = (R.toRepresentation.prod R.toRepresentation) k (c w) at hc
  change (a.linearEquiv (c (ρ k w)).1, a.linearEquiv (c (ρ k w)).2) = _
  rw [hc]
  exact Prod.ext (ha k (c w).1) (ha k (c w).2)

end CFSG.Quasithin.ChapterK.Alternating.RecognitionInputs.Six
