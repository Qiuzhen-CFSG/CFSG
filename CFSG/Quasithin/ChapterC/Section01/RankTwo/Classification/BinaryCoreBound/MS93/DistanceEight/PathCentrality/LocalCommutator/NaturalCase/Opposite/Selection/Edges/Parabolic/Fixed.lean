module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Edges.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Selection.Model

/-!
# Selecting the opposite parabolic on the actual moving quotient

A nonzero vector fixed by the parabolic in the contragredient coordinates
forces zero fixed space on the actual natural U_c. Selecting a flag fixing
the moving element's coordinate fixes that element modulo the literal B_c.
The flag and side use the frame's original projection throughout.

This is the flag-selection part of MS93 (4.4.1)(1), pp.890–891. The
full-parabolic normalization of the ambient displacement is a separate step.
The finite flag selection is reused from FirstPairing/Orientation; no
Escape.Counterexample or favorable orientation is required.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection
open RankOnePairing RankOnePairing.Incidence
open RankOnePairing.Incidence.FixedGeometry.ValueConstruction
variable {M : Type*} [Group M] {L R : Subgroup M}

private theorem original_fixed_bot (σ : MulAut SL) (flag : SL) (side : Bool)
    (hf : fixedSpace (markedParabolic (DualGeometry.dualMark σ) flag side) ≠ ⊥) :
    fixedSpace (markedParabolic σ flag side) = ⊥ := by
  obtain ⟨k, ⟨hp, _⟩ | ⟨hp, _⟩⟩ := ModelProof.marked_pair σ flag side
  · exact False.elim (hf (by
      rw [DualGeometry.ModelProof.dual_marked, hp,
        DualGeometry.ModelProof.map_graph_conj,
        Matrix.PSL3Two.MarkedAutomorphisms.pointParabolic_map_diagram,
        ModelProof.fixedSpace_conj, ModelProof.line_fixed_bot, Subgroup.map_bot]))
  · rw [hp, ModelProof.fixedSpace_conj, ModelProof.line_fixed_bot, Subgroup.map_bot]

private theorem actual_fixed_bot {G : Type*} [Group G] {π : G →* SL} {U : Subgroup G}
    (n : NaturalFactor π ⊤ U ⊥) (hπ : Function.Surjective π) (flag : SL) (side : Bool)
    (hf : fixedSpace (markedParabolic n.marking flag side) = ⊥) :
    U ⊓ centralizer (parabolic π flag side : Set G) = ⊥ := by
  apply le_bot_iff.mp
  rintro x ⟨hx, hfix⟩
  let u : U := ⟨x, hx⟩
  have hu : n.coordinates u ∈ fixedSpace (markedParabolic n.marking flag side) := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨l, rfl⟩ := hπ v
    have hc : (u : G) = l * (u : G) * l⁻¹ := by
      rw [hfix l hv, mul_inv_cancel_right]
    exact (n.action l (mem_top _) u u hc).symm
  have h : n.coordinates u = 1 := mem_bot.mp (hf.le hu)
  exact congrArg Subtype.val (n.equivOfBot.injective (h.trans (map_one _).symm))

private theorem fixed_class_of_coordinates {G : Type*} [Group G] {π : G →* SL}
    {W B : Subgroup G} [B.Normal] (n : NaturalFactor π ⊤ W B)
    (x : W) (flag : SL) (side : Bool)
    (hf : ∀ a ∈ modelParabolic flag side,
      (n.marking a).val.mulVec (n.coordinates x).toAdd = (n.coordinates x).toAdd) :
    ⁅zpowers (x : G), parabolic π flag side⁆ ≤ B := by
  let C := centralizerModulo (⊤ : Subgroup G) (parabolic π flag side) B
  have hx : (x : G) ∈ C := by
    apply mem_centralizerModulo_iff.mpr
    refine ⟨mem_top _, ?_⟩
    intro a ha
    let y : W := ⟨a * (x : G) * a⁻¹,
      (mem_normalizer_iff.mp (n.normalized (mem_top _)) _).mp x.property⟩
    have he : n.coordinates y = n.coordinates x := by
      apply Multiplicative.toAdd.injective
      exact (n.action a (mem_top _) x y rfl).trans (hf (π a) ha)
    have hk : y * x⁻¹ ∈ n.coordinates.ker := by
      change n.coordinates (y * x⁻¹) = 1
      rw [map_mul, map_inv, he, mul_inv_cancel]
    rw [n.kernel] at hk
    exact hk
  rw [commutator_comm]
  apply commutator_le.mpr
  intro a ha z hz
  exact (mem_centralizerModulo_iff.mp (zpowers_le.mpr hx hz)).2 a ha

/-- A common flag selected from the actual opposite action, before lifting
normalization from the two-residual to the whole parabolic. -/
structure FixedSeed (geometry : Geometry R) {a c : Vertex R} (f : FrameAt a c)
    extends MovingSeed a c where
  flag : SL
  weakBN : BinaryWeakBN flag
  side : Bool
  natural_fixed_eq_bot : (U R c).subgroupOf (stabilizer R c) ⊓
    centralizer (parabolic f.sectionData.projection flag side : Set (stabilizer R c)) = ⊥
  class_fixed : ⁅zpowers element,
    (parabolic f.sectionData.projection flag side).map (stabilizer R c).subtype⁆ ≤
      B R c (geometry.Z_normal c)

variable [Finite M] {source : LocalSource L R} {geometry : Geometry R}

/-- The moving class chooses a parabolic with zero fixed space on the actual U_c. -/
theorem fixedSeed_nonempty (source : LocalSource L R)
    {a c : Vertex R} (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2)
    (hb : 2 < geometry.b R) (hn : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c)
    (f : FrameAt a c) (hop : ¬ f.SameOrientation) : Nonempty (FixedSeed geometry f) := by
  obtain ⟨s⟩ := movingSeed_nonempty hd hn
  let S := stabilizer R c
  let W := (localZSpan R a c).subgroupOf S
  let x : W := ⟨⟨s.element, f.sectionData.local_group
    (Z_le_localZSpan R a c s.element_mem)⟩, Z_le_localZSpan R a c s.element_mem⟩
  let n := (spanDual source hc hd hb f hop).graphNatural
  obtain ⟨flag, side, w, hw, hx, hfix⟩ :=
    Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Selection.exists_fixed_flag
      n.marking (n.coordinates x).toAdd
  have hf : fixedSpace (markedParabolic n.marking flag side) ≠ ⊥ := by
    intro hz
    have hm : Multiplicative.ofAdd w ∈ fixedSpace (markedParabolic n.marking flag side) := by
      rintro _ ⟨v, hv, rfl⟩
      exact hfix v hv
    exact hw (congrArg Multiplicative.toAdd (mem_bot.mp (hz.le hm)))
  let := fixed_normal (geometry := geometry) c
  have hclass := map_mono (f := S.subtype) (fixed_class_of_coordinates n x flag side hx)
  rw [map_commutator, MonoidHom.map_zpowers] at hclass
  refine ⟨{ s with
    flag := flag
    weakBN := binaryWeakBN flag
    side := side
    natural_fixed_eq_bot := actual_fixed_bot f.naturalU
      f.sectionData.module_section.projection_surjective flag side
      (original_fixed_bot f.naturalU.marking flag side hf)
    class_fixed := hclass.trans (map_le_iff_le_comap.mpr le_rfl) }⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection
