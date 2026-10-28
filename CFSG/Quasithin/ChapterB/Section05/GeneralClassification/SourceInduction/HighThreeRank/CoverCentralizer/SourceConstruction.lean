module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.LowerSources
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.CenterBounds
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.UniqueComponent

/-!
# The source cover structure in the high-three-rank branch

The complete existential B.5.2 implication selects the actual prepared cover
and lifted component. The complete B.5.5 implication gives positive three-rank
for every component downstairs; a component upstairs cannot vanish in the
nilpotent kernel. The center bound and cyclic-Sylow transfer then prove
uniqueness of the lifted component, and lifting every component gives the
layer equality downstairs. A.2.1 supplies SQTK inheritance for the component,
and B.5.5(2) gives the required generalized-Fitting equality.

The four explicit universal inputs are B.5.2 (`CoverInput`), B.5.5
(`ComponentsInput`), full A.2.1 (`SemisimpleInput`), and the numerical
order-divides-48 consequence of I.1.3 (`MultiplierInput`). Their producers
are `qt-b05-quotient-components`, `qt-a-02`, and `qt-i-01`. The parent owns
discharging these inputs. No B.5.6, B.5.7 or A.3.18 conclusion is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.2–5 and the opening reduction of B.5.7, printed pp.103–106.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction
open ChapterA.Section02
universe u v
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

omit [Finite G] in
/-- A component survives the nilpotent kernel of the prepared cover. This
applies to both source presentations of the component facts. -/
theorem component_image (c : PreparedCover K G)
    {D : Subgroup c.Cover} (hD : IsComponent c.Cover D) :
    IsComponent G (D.map c.projection) := by
  rcases hD.map_surjective c.projection c.surjective with hz | hi
  · have hle : D ≤ c.projection.ker := by
      rw [← MonoidHom.comap_bot]
      exact map_le_iff_le_comap.mp hz.le
    let := hD.2
    let : Group.IsNilpotent c.projection.ker := c.kernel_nilpotent
    let : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective
      (inclusion_injective hle)
    let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
    let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
    exact (Group.IsPerfect.not_isSolvable D inferInstance).elim
  · exact hi

/-- Construct all structural fields of the lifted cover from the permitted
universal earlier inputs, retaining the original component and projection. -/
theorem exists_liftedCover (h52 : CoverInput K) (h55 : ComponentsInput.{u,v} K)
    (hA : SemisimpleInput K) (hI : MultiplierInput K)
    (hyp : FFHypothesis K ρ) {L : Subgroup G} (hL : IsComponent G L)
    (hrL : 1 < primeRank 3 L) : Nonempty (LiftedCover K G L) := by
  obtain ⟨c⟩ := h52 G hyp.quotient
  obtain ⟨M, hM, hmap⟩ := c.component_lifts L hL
  have hz := lift_center_order hA hI c.prepared hyp.twoCore hM
  have hrM := lift_rank c.prepared.projection M hmap hrL
  have hpos (D : Subgroup c.prepared.Cover) (hD : IsComponent c.prepared.Cover D) :
      0 < primeRank 3 D := by
    have hi := component_rank_pos ρ h55 hyp (component_image c.prepared hD)
    apply Nat.pos_of_ne_zero
    intro hd
    exact (Nat.ne_of_gt hi) (PrimeRank.eq_zero_of_surjective
      (c.prepared.projection.subgroupMap D)
      (c.prepared.projection.subgroupMap_surjective D) hd)
  have hEc : componentLayer c.prepared.Cover = M :=
    layer_eq_of_components_positive hM hrM
      (c.prepared.sqtk.stronglyQuasithin 3 Nat.prime_three (by decide))
      (by rcases hz with h | h <;> omega) hpos
  have hE : componentLayer G = L := by
    apply le_antisymm
    · apply sSup_le
      intro D hD
      obtain ⟨N, hN, hn⟩ := c.component_lifts D hD
      have hNM : N ≤ M := hEc ▸ (show N ≤ componentLayer c.prepared.Cover from le_sSup hN)
      rw [← hn, ← hmap]
      exact map_mono hNM
    · exact le_sSup hL
  let := hL.2
  have hsq : IsSQTK K L := by
    apply quasisimple_section_sqtk hA c.prepared.sqtk
    exact ⟨M, (MulEquiv.subgroupCongr hmap).toMonoidHom.comp
        (c.prepared.projection.subgroupMap M),
      (MulEquiv.subgroupCongr hmap).surjective.comp
        (c.prepared.projection.subgroupMap_surjective M)⟩
  exact ⟨{
    cover := c.prepared
    lift := M
    component := hM
    component_image := hmap
    lift_layer := hEc
    layer := hE
    component_sqtk := hsq
    fitting := hE ▸ (h55 G V ρ hyp).fitting
    center_order := hz }⟩

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction
