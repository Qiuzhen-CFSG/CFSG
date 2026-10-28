module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.ConstructionInputs
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Inputs
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.LocalCoverage

/-!
# Extending the long cubic through the source root J₂

In the concrete permutation J₂, the literal D₁₀ centralizer K is already
proved isomorphic to A₅. Restrict an actual marked J₂ map to K. Its inverter
moves coordinate zero to coordinate five, so this restriction is nontrivial;
simplicity makes it injective. The image is therefore A₅. Transporting
commutation with the marked dihedral group gives ambient centralization,
and X ≤ K puts the literal long cubic in this same image.

The final application uses the icosian embedding conjugated inside C(I).
Its two remaining premises are a comparison of the concrete J₂ carriers
and an alignment of the three marks for the supplied arbitrary LongFrame.
No unconditional `exists_a5Placement` is claimed until those are proved.
No assumption about L.swap, a faithful whole-centralizer action, or a
completed G₂ embedding enters this transport.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284,
using 47.2 (p.261), 49.1, and 48.8 (p.273). The consumer is the construction
of `Geometry` in the parent module, after independent scalar fusion.
-/

open Atlas.Conway
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
open OctonionLocals

variable {L : LongFrame}
    {f : Sporadic.LeechRelated.J2.Carrier →* LeechCentralQuotient}

open Sporadic.LeechRelated.J2.RecognitionGeometry in
/-- Restrict the actual root J₂ map to its literal dihedral centralizer. -/
def rootCentralizerHom
    (f : Sporadic.LeechRelated.J2.Carrier →* LeechCentralQuotient) :
    K →* LeechCentralQuotient := f.comp K.subtype

open Sporadic.LeechRelated.J2.RecognitionGeometry in
theorem RootJ2Marks.inverter_ne_one (M : RootJ2Marks L f) :
    f LocalA5.inverter ≠ 1 := by
  intro h
  have he := M.reflection_on_single 0 1
  rw [h, map_one] at he
  have hv := L.coordinates_injective he
  rw [← graph_action] at hv
  have hz := congrFun hv 0
  simp [pairRepresentation, pairLinear, pairAction, flip] at hz

open Sporadic.LeechRelated.J2.RecognitionGeometry in
theorem RootJ2Marks.local_injective (M : RootJ2Marks L f) :
    Function.Injective (rootCentralizerHom f) := by
  let : IsSimpleGroup K := LocalA5.localEquiv.isSimpleGroup
  rcases (rootCentralizerHom f).normal_ker.eq_bot_or_eq_top with h | h
  · exact (rootCentralizerHom f).ker_eq_bot_iff.mp h
  · have hi : (⟨LocalA5.inverter, LocalA5.inverter_mem_K⟩ : K) ∈
        (rootCentralizerHom f).ker := h ▸ Subgroup.mem_top _
    exact False.elim (M.inverter_ne_one (MonoidHom.mem_ker.mp hi))

open Sporadic.LeechRelated.J2.RecognitionGeometry in
theorem RootJ2Marks.range_le_localCentralizer (M : RootJ2Marks L f)
    (hf : ∀ a, f a ∈ centralizerI) :
    (rootCentralizerHom f).range ≤ localCentralizer L := by
  rintro a ⟨k, rfl⟩
  refine ⟨hf k, ?_⟩
  intro d hd
  obtain ⟨b, hb, rfl⟩ := M.dihedral_le hd
  have h := congrArg f (k.property b hb)
  simpa only [rootCentralizerHom, MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul] using h

open Sporadic.LeechRelated.J2.RecognitionGeometry in
theorem RootJ2Marks.cubic_le_range (M : RootJ2Marks L f) :
    (longCubic L).range ≤ (rootCentralizerHom f).range := by
  intro c hc
  obtain ⟨x, hx, hxc⟩ := M.cubic_le hc
  exact ⟨⟨x, X_sup_Y_le_K (Subgroup.mem_sup_left hx)⟩, hxc⟩

open Sporadic.LeechRelated.J2.RecognitionGeometry in
/-- Transport the proved J₂ centralizer, discharging injectivity internally. -/
def a5PlacementOfRootJ2 (f : Sporadic.LeechRelated.J2.Carrier →* LeechCentralQuotient)
    (hf : ∀ a, f a ∈ centralizerI) (M : RootJ2Marks L f) : A5Placement L where
  subgroup := (rootCentralizerHom f).range
  alternating := (MonoidHom.ofInjective M.local_injective).symm.trans LocalA5.localEquiv
  le_centralizer := M.range_le_localCentralizer hf
  cubic_le := M.cubic_le_range
  reflection := ⟨f LocalA5.inverter,
    ⟨⟨LocalA5.inverter, LocalA5.inverter_mem_K⟩, rfl⟩⟩
  reflection_on_single := M.reflection_on_single

/-- The actual Leech consumer of the carrier-comparison and mark-alignment branches. -/
theorem exists_a5Placement_of_rootJ2_alignment (L : LongFrame)
    (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel)
    (g : LeechCentralQuotient) (hg : g ∈ centralizerI)
    (M : RootJ2Marks L (conjugatedRootJ2 e g)) : Nonempty (A5Placement L) :=
  ⟨a5PlacementOfRootJ2 _ (conjugatedRootJ2_mem e hg) M⟩

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
