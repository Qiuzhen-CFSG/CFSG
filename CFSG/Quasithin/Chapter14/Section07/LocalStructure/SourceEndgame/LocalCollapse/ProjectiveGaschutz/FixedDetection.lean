module

public import Theory.Representation.SL2FourNaturalBorelFixedLifting.MarkedCentralizer
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.FixedDetection
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.Setup
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.HAccounting.DualSection

/-!
# Fixed detection on the original section in the first Gaschütz step

The prescribed Borel marking and its trivial S₅ centralizer place QC in
QH through the original map qH = model ∘ starMap, with domain H.
SourceDuality and Earlier.sectionCentralizer identify the original QH/C
coordinates; the previously constructed inclusion of QK/C is equivariant
and has trivial quotient action by the definition QK = [QH,K]C.

The actual parabolic L₁ maps onto the Borel and contains a Sylow subgroup
of K, supplied by the two-core identity and Prior.parabolic_sylow. Its
fixed QC coordinates are therefore detected by the natural dual section.
The final theorem below retains only the independent general fixed-lift
implication; the genuine Gaschütz semidirect-product producer remains to
be supplied. This conditional source application is not a completed
14.7.74. The earlier SourceDuality, QKDualCoordinates and parabolic marking
retain their existing 14.5.21, H-accounting and left-parabolic producers.

Source: Aschbacher--Smith, 14.7.71--74, especially the first paragraph of
14.7.74, printed p.1077 (PDF p.1094), manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.ProjectiveFixedDetection
open Chapter12.Section08 CriticalFusion.Source ChiefFactors
open CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors
open Matrix.SpecialLinearGroup
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
  {X Y : Type u} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

/-- The original left parabolic, viewed inside the original K. -/
abbrev parabolic : Subgroup (K F) := (F.Li L 1).subgroupOf (K F)

/-- The 14.7.73 two-core equality gives the actual Sylow witness in L₁. -/
theorem parabolic_contains_sylow (a : Prior d) :
    ∃ P : Sylow 2 (K F), (P : Subgroup (K F)) ≤ parabolic (L := L) (F := F) := by
  obtain ⟨P, hP⟩ := a.parabolic_sylow
  refine ⟨P, ?_⟩
  intro k hk
  have hm : (k : G) ∈ S L F ⊔ (K F).pCoreIn 2 :=
    hP ▸ mem_map_of_mem (K F).subtype hk
  rw [← a.parabolic_core] at hm
  exact pCoreIn_le 2 (F.Li L 1) hm

/-- Transport the earlier marking through qK without choosing new coordinates. -/
theorem parabolic_marking
    (hm : ((F.Li L 1).subgroupOf F.H).map d.qH =
      (rankOneBorel SL2FourNatural.F).map (alternatingActor d.naturalQuotient)) :
    (parabolic (L := L) (F := F)).map (RootRecognition.qK d) =
      rankOneBorel SL2FourNatural.F := by
  apply map_injective (f := alternatingActor d.naturalQuotient)
    (Subtype.val_injective.comp d.naturalQuotient.marking.injective)
  rw [map_map, ← hm]
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨inclusion (K_le_H F) k, hk, RootRecognition.qK_marking d k⟩
  · rintro ⟨h, hh, rfl⟩
    refine ⟨⟨h, L₁_le_K hh⟩, hh, ?_⟩
    exact (RootRecognition.qK_marking d ⟨h, L₁_le_K hh⟩).symm

/-- Centralizing the marked Borel modulo QH places QC in QH. -/
theorem QC_le_QH_of_marked_centralizer
    (hm : ((F.Li L 1).subgroupOf F.H).map d.qH =
      (rankOneBorel SL2FourNatural.F).map (alternatingActor d.naturalQuotient))
    (hcentral : centralizer (((rankOneBorel SL2FourNatural.F).map
      (alternatingActor d.naturalQuotient)) : Set ChapterJ.S5) = ⊥) :
    QC T L V ≤ F.H.pCoreIn 2 := by
  intro x hx
  let xH : F.H := ⟨x, Q_le_H F (commutatorPreimage_le _ _ _ hx)⟩
  have hc : d.qH xH ∈ centralizer (((rankOneBorel SL2FourNatural.F).map
      (alternatingActor d.naturalQuotient)) : Set ChapterJ.S5) := by
    rw [← hm]
    rintro z ⟨l, hl, rfl⟩
    have hcomm : ⁅xH, l⁆ ∈ d.qH.ker := by
      rw [d.qH_ker]
      exact U_le_QH d (Data.V_le_U F
        (QC_commutator_le (F := F) (commutator_mem_commutator hx
          ((F.Li_le L 1 hl).1))))
    have he := MonoidHom.mem_ker.mp hcomm
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at he
    exact he.symm
  have hz : d.qH xH = 1 := by simpa only [hcentral, mem_bot] using hc
  have hh : xH ∈ d.qH.ker := hz
  rw [d.qH_ker] at hh
  exact hh

/-- The precise model centralizer discharges the quotient obstruction. -/
theorem QC_le_QH
    (hm : ((F.Li L 1).subgroupOf F.H).map d.qH =
      (rankOneBorel SL2FourNatural.F).map (alternatingActor d.naturalQuotient)) :
    QC T L V ≤ F.H.pCoreIn 2 :=
  QC_le_QH_of_marked_centralizer d hm
    (SL2FourNaturalBorelFixedLifting.marked_borel_centralizer d.naturalQuotient.marking)

/-- The kernel is C = H ∩ C_G(U), not an unrelated module kernel. -/
theorem section_coordinate_kernel (hc : d.SectionCentralizer)
    (s : CriticalIntersections.SourceDuality F X Y) :
    s.qSection.coordinates.ker = (C F).subgroupOf (F.H.pCoreIn 2) := by
  rw [s.qSection.kernel_eq, q_centralizer_eq_h_centralizer d hc]
  rfl

/-- The section QH/C, with the original action and coordinate map. -/
def qHCSection (hc : d.SectionCentralizer)
    (s : CriticalIntersections.SourceDuality F X Y) :
    BinaryConjugationSection F.H (F.H.pCoreIn 2) (C F) s.qAction where
  section_le := s.qSection.section_le
  kernel_le := C_le_QH d hc
  normalized := s.qSection.normalized
  coordinates := s.qSection.coordinates
  onto := s.qSection.onto
  kernel_eq := section_coordinate_kernel d hc s
  equivariant := s.qSection.equivariant

/-- The actual inclusion, after the quotient-centralizer argument. -/
def qcToQH (hQC : QC T L V ≤ F.H.pCoreIn 2) : QC T L V →* F.H.pCoreIn 2 :=
  inclusion hQC

/-- The source bound [QC,L₁] ≤ V ≤ U gives fixed section coordinates. -/
theorem QC_coordinates_fixed
    (hc : d.SectionCentralizer) (s : CriticalIntersections.SourceDuality F X Y)
    (hQC : QC T L V ≤ F.H.pCoreIn 2) (q : QC T L V) :
    (s.qSection.coordinates (qcToQH hQC q)).toAdd ∈
      fixedSpace (FixedDetection.sectionAction s) (parabolic (L := L) (F := F)) := by
  intro l
  let lH : F.H := inclusion (K_le_H F) l.val
  let qH := qcToQH hQC q
  let q' : F.H.pCoreIn 2 := ⟨lH * qH * (lH : G)⁻¹,
    (mem_normalizer_iff.mp (s.qSection.normalized lH.property) qH).mp qH.property⟩
  have he : s.qSection.coordinates (q' * qH⁻¹) = 1 := by
    rw [s.qSection.coordinates_eq_one_iff, q_centralizer_eq_h_centralizer d hc]
    apply U_le_C d
    apply Data.V_le_U F
    have hb := QC_commutator_le (T := T) (L := L) (V := V) (F := F)
    rw [commutator_comm] at hb
    exact hb (commutator_mem_commutator ((F.Li_le L 1 l.property).1) q.property)
  have heq : s.qSection.coordinates q' = s.qSection.coordinates qH := by
    apply mul_inv_eq_one.mp
    simpa only [map_mul, map_inv] using he
  change s.qAction lH (s.qSection.coordinates qH).toAdd = _
  rw [← s.qSection.equivariant lH qH]
  exact congrArg Multiplicative.toAdd heq

/-- Global fixation in the literal coordinates gives the original commutator bound. -/
theorem QC_commutator_le_C_of_fixed_coordinates
    (hc : d.SectionCentralizer) (s : CriticalIntersections.SourceDuality F X Y)
    (hQC : QC T L V ≤ F.H.pCoreIn 2)
    (hfix : ∀ (q : QC T L V) (k : K F),
      FixedDetection.sectionAction s k (s.qSection.coordinates (qcToQH hQC q)).toAdd =
        (s.qSection.coordinates (qcToQH hQC q)).toAdd) :
    ⁅QC T L V, K F⁆ ≤ C F := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro k hk q hq
  let kH : F.H := ⟨k, K_le_H F hk⟩
  let qH := qcToQH hQC ⟨q, hq⟩
  let q' : F.H.pCoreIn 2 := ⟨kH * qH * (kH : G)⁻¹,
    (mem_normalizer_iff.mp (s.qSection.normalized kH.property) qH).mp qH.property⟩
  have heq : s.qSection.coordinates q' = s.qSection.coordinates qH := by
    apply Multiplicative.toAdd.injective
    exact (s.qSection.equivariant kH qH).trans (hfix ⟨q, hq⟩ ⟨k, hk⟩)
  have he : s.qSection.coordinates (q' * qH⁻¹) = 1 := by
    rw [map_mul, map_inv, heq, mul_inv_cancel]
  have hh := (s.qSection.coordinates_eq_one_iff _).mp he
  rw [q_centralizer_eq_h_centralizer d hc] at hh
  exact hh

/-- The earlier coordinates are finite because they are a quotient of QH. -/
theorem section_finite (s : CriticalIntersections.SourceDuality F X Y) : Finite Y := by
  apply Finite.of_surjective (fun q : F.H.pCoreIn 2 => (s.qSection.coordinates q).toAdd)
  intro y
  obtain ⟨q, hq⟩ := s.qSection.onto (Multiplicative.ofAdd y)
  exact ⟨q, congrArg Multiplicative.toAdd hq⟩

/-- The original-section application of fixed lifting. The only new premise
is the general fixed-lift implication, whose Gaschütz producer is independent
of the source groups, the natural marking, and the desired commutator bound. -/
theorem QC_K_le_C_of_fixed_lift
    (a : Prior d) (c : CriticalPath (L := L) F) (e : Earlier d c)
    (s : CriticalIntersections.SourceDuality F X Y) (b : QKDualCoordinates d)
    (hm : ((F.Li L 1).subgroupOf F.H).map d.qH =
      (rankOneBorel SL2FourNatural.F).map (alternatingActor d.naturalQuotient))
    (hlift : ∀ (N : Submodule (ZMod 2) Y),
      (∀ k y, FixedDetection.sectionAction s k y - y ∈ N) →
      ∀ P : Sylow 2 (K F), ∀ y ∈ fixedSpace (FixedDetection.sectionAction s) (P : Subgroup (K F)),
        ∃ w, (∀ k, FixedDetection.sectionAction s k w = w) ∧ y - w ∈ N) :
    ⁅QC T L V, K F⁆ ≤ C F := by
  have hQC := QC_le_QH d hm
  obtain ⟨P, hP⟩ := parabolic_contains_sylow d a
  let i := FixedDetection.dualInclusion d e.sectionCentralizer s b
  have hdisp : ∀ k y, FixedDetection.sectionAction s k y - y ∈ i.toLinearMap.range :=
    FixedDetection.displacement_mem_range d e.sectionCentralizer s b
  have hfix := SL2FourNaturalBorelFixedLifting.dual_fixed_of_borel_of_fixed_lift
    (FixedDetection.sectionAction s) (RootRecognition.qK d) i
    (FixedDetection.coordinateInclusion_injective d e.sectionCentralizer s b)
    (parabolic (L := L) (F := F)) P hP (parabolic_marking d hm)
    (hlift i.toLinearMap.range hdisp P)
  apply QC_commutator_le_C_of_fixed_coordinates d e.sectionCentralizer s hQC
  intro q k
  exact hfix _ (QC_coordinates_fixed d e.sectionCentralizer s hQC q) k

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.ProjectiveFixedDetection
