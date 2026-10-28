module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianFixedLine
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianConstituentAction
public import Theory.Representation.BinaryPermutation.SixDoubleNormalizer

/-!
# Original fixed-line constituents and the faithful A₆ exclusion

The original fixed-line action selects a moved component orbit and an actual
constituent. In the marked branch the constituent is proper, homogeneous,
faithful for the orbit and self-dual, with the literal actor kernel and action
quotient retained. The whole irreducible branch is excluded by the original
point-component argument. The exchanged branch remains an explicit alternative.

If the actor is faithful on a proper A₆ constituent, its whole normal action
is a doubled natural module. The normalizer embeds the entire original
faithful acting group in S₆ × S₃. This contradicts the factor of seven supplied
by the original point group, without identifying the proper constituent orbit
with that point group. Other faithful rows and the nonfaithful branch remain
for the fixed-line contradiction and final point-span abelianity.

Source: Aschbacher--Smith G.11.6--9 and 12.9.3--4,
printed pp.365--369,858--860.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
open ChapterG.Section11
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- The original seven-section excludes any whole doubled natural A₆ action
of a normal subgroup. No point-component identification is required. -/
theorem nonabelian_doubled_six_impossible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (F : InvariantFlag T V n)
    (hne : ¬ IsMulCommutative F.U) [IsElementaryAbelian 2 F.Uhat]
    (J : Subgroup F.TerminalHdot) [J.Normal]
    (hmodel : ChapterG.Section09.Quasiequivalent (F.terminalRepresentation.comp J.subtype)
      ((BinaryPermutation.alternatingNaturalRepresentation (Fin 6)).prod
        (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)))) : False := by
  obtain ⟨e,c,hc⟩ := hmodel
  obtain ⟨j,_,hj,_,_⟩ := BinaryPermutation.SixDoubleNormalizer.exists_tensor_embedding_of_double
    F.terminalRepresentation F.terminalRepresentation_injective J e c hc
  have hseven := (point_hat_seven_dvd h hn F hne).trans
    (card_subgroup_dvd_card (F.terminalDot (F.Li L 1)))
  have hd := hseven.trans (card_dvd_of_injective j hj)
  norm_num [BinaryPermutation.SixDoubleNormalizer.TensorGroup,
    Nat.card_prod,Nat.card_perm,Nat.card_fin,Fintype.card_perm,Nat.factorial] at hd


/-- Exclude the proper faithful natural A₆ constituent on the original flag.
Faithful conjugation bounds the original actor rank by three; homogeneity
then constructs the double coordinates needed for the ambient seven obstruction. -/
theorem nonabelian_faithful_six_constituent_impossible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (F : InvariantFlag T V n)
    (hne : ¬ IsMulCommutative F.U) [IsElementaryAbelian 2 F.Uhat]
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hg10 : ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
      (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hS : NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)))
    {J : Subgroup F.TerminalHdot} (hJ : IsComponent F.TerminalHdot J)
    (hm : ⁅J,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : IsIrrPlus F.terminalRepresentation (componentOrbit J ⊤) I)
    (hv : v ∈ I) (hp : I ≠ ⊤)
    (hfX : Function.Injective (fun x : F.terminalDot (F.X g) =>
      (F.terminalRepresentation (x : F.TerminalHdot)).comp I.subtype))
    (e : componentOrbit J ⊤ ≃* alternatingGroup (Fin 6)) : False := by
  obtain ⟨S,hSv,hXS,hnS⟩ := hS
  have hnX := (normal_subgroupOf_iff_le_normalizer hXS).mp hnS
  let := componentOrbit_top_normal J
  exact nonabelian_doubled_six_impossible h hn F hne (componentOrbit J ⊤)
    (FixedLineConstituent.double_six_of_proper_faithful hg10
      (nonabelian_hat_not_solvable h hn F hne) (nonabelian_sqtkCover h F)
      S hnX hJ hm hI hv hp hfX e)

/-- Select the actual moved component and constituent in the fixed-line branch.
The marked constituent is proper, homogeneous, faithful and self-dual; a
faithful actor excludes A₆. The exchanged alternative is retained literally. -/
theorem nonabelian_fixed_line_constituents
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (preferred : PreferredDimension KnownSimple.IsKnownSimple T n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ hX : IsElementaryAbelian 2 (F.terminalDot (F.X g)),
      let := hX
      ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
        ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
          (F.terminalDot (F.X g))
          ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
        hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v} ∧
        NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
        ∃ J : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot J ∧
          ⁅J,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
          ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B J ∧
          ∃ I : Submodule (ZMod 2) (Additive F.Uhat),
          ∃ hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit J ⊤)
            (F.terminalDot (F.X g)) I,
          (FixedLineConstituent.MarkedData F.terminalRepresentation B v
              (F.terminalDot (F.X g)) J I hI ∧
            (Function.Injective (fun x : F.terminalDot (F.X g) =>
              (F.terminalRepresentation (x : F.TerminalHdot)).comp I.subtype) →
              ¬ Nonempty (componentOrbit J ⊤ ≃* alternatingGroup (Fin 6)))) ∨
          (v ∉ I ∧ ChapterG.Section10.ExchangedConstituentGeometry
            F.terminalRepresentation B v (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I) := by
  obtain ⟨hX,B,v,hg10,hline,hS⟩ := nonabelian_g10_hypothesis h earlier F hne g hgP hgH
  let := hX
  have hns := nonabelian_hat_not_solvable h hn F hne
  have cover := nonabelian_sqtkCover h F
  have hF := hg10.fitting_centralizer_ne_bot_of_not_solvable ⟨cover⟩ hns
  obtain ⟨J,hJ,hm,hsel,horth⟩ := hg10.exists_moved_component_orthogonal_selection hns hF
  obtain ⟨_,_,I,hI,_⟩ := hsel
  refine ⟨hX,B,v,hg10,hline,hS,J,hJ,hm,horth,I,hI,?_⟩
  obtain ⟨S,hSv,hXS,hnS⟩ := hS
  have hnX := (normal_subgroupOf_iff_le_normalizer hXS).mp hnS
  have hind := cover.component_normalizer_index_le_two hJ
  by_cases hv : v ∈ I
  · have hfix := (nonabelian_fixed_line_and_moved_rank modules h hn preferred earlier four
      F hne g hgP hgH).1.trans hline
    rcases FixedLineConstituent.marked_or_whole_of_point_mem hg10 hns cover S hnX hJ hm hI hv hfix
      with hdata | hi
    · refine Or.inl ⟨hdata,?_⟩
      intro hfX ⟨e⟩
      exact nonabelian_faithful_six_constituent_impossible h hn F hne g hg10
        ⟨S,hSv,hXS,hnS⟩ hJ hm hI.isIrrPlus hv hdata.choose_spec.1 hfX e
    · have h9 := hg10.componentHypothesis_of_orbit_irreducible ⟨cover⟩ hJ hm hind hi
      obtain ⟨C⟩ := componentGeometry earlier h hn F
      obtain ⟨he,hOrbit⟩ := nonabelian_whole_eq_point h hn F hne C h9
      rw [hOrbit,he] at h9
      exact (nonabelian_point_whole_impossible modules h hn preferred earlier four
        F hne g hgP hgH hg10 C h9).elim
  · exact Or.inr ⟨hv,hg10.exchanged_constituent_geometry hns hJ hm S hnX hind hI hv⟩

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
