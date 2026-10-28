module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSMarking
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreLayer
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryQuotient

/-!
# Secondary component selection from the original line marking

The original MS witness and line marking now suffice to construct the
simultaneous Sylow marking internally. Applying the checked root and
component construction in these coordinates gives the actual normal component
in N_G(Z_S), its quasisimple full quotient, and the strict orbit U<E inside
its two-core. All subgroups are the original ambient subgroups and both
component embeddings are retained. No Sylow placement premise remains.

This does not infer K₂<O₂(K_Z)K₂ from U<E. That strict secondary-core
inequality, construction of MSData and its line marking, and final assembly
remain with qt-d-1222-rankone-uniqueness-nonblock. The independent whole-core
nonbinary classification retains its existing producer and final discharge.
Source: Aschbacher--Smith, original 4.3.10--14, pp.617--618.
-/

public section
open Subgroup Theory.GroupTheory Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

/-- From the original line marking, select an actual component with the
quadratic orbit in its two-core. The Sylow marking is constructed internally. -/
theorem MSData.exists_sourceComponent_of_line_marking (d : MSData c n) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier) :
    ∃ B : Subgroup (rootNormalizer c),
      B.IsCComponent ∧ B.Normal ∧ IsQuasisimple (B ⧸ pCore 2 B) ∧
      secondary c < B.map (rootNormalizer c).subtype ∧
      B.map (rootNormalizer c).subtype ≤ Subgroup.centralizer (root c : Set G) ∧
      U c < rootCoreLayer c ∧
      rootCoreLayer c ≤ (B.map (rootNormalizer c).subtype).pCoreIn 2 ∧
      (B.map (rootNormalizer c).subtype ⊔ (T : Subgroup G)).pCoreIn 2 ≤ R₂ c ∧
      (frattini (rootCoreLayer c)).map (rootCoreLayer c).subtype ≤ root c ∧
      ⁅rootCoreLayer c,rootCoreLayer c⁆ ≤ root c := by
  obtain ⟨g,hL',hSL'⟩ := d.exists_simultaneous_marking D hL
  let d' := d.conjugateModel g.val
  let B := d'.sourceComponent hn D h hL' hSL'
  obtain ⟨hB,hBn,hsec,hcent⟩ := d'.sourceComponent_spec hn D h hL' hSL'
  obtain ⟨hU,hE,hPhi,hcomm,_⟩ := d'.sourceComponent_core_layer hn D h hL' hSL'
  obtain ⟨m⟩ := d'.rootCoordinates_of_marked_parabolic hL' hSL'
  refine ⟨B,hB,hBn,d'.sourceComponent_quasisimple hn D h hL' hSL',hsec,hcent,
    hU,hE,?_,hPhi,hcomm⟩
  exact m.enlarged_core_le_radical_source hn D _
    (sup_le (hsec.le.trans le_sup_left) (inf_le_left.trans le_sup_right))

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
