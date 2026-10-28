module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.CenterAbovePoint.Seed

/-!
# The center is the marked point for a solvable terminal actor

In the original nonabelian rank-two source, a larger center forces an
irreducible degree-four full orthogonal action. Its marked residual is
an elementary nine-group and its inverter moves the actual W-hyperplane.
Coprime splitting then puts the entire seed orbit in the moving summand,
contradicting the larger center. The selected-source wrapper constructs
the earlier geometry, terminal hypothesis and SQTK cover internally.

Source: Aschbacher--Smith 14.3.15, printed pp.994--995.
-/

public section
open Subgroup Theory.GroupTheory Module
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G]

open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- In the selected nonabelian rank-two source, a solvable terminal actor
forces the center of the original span to be exactly its marked point. -/
theorem center_eq_point_of_solvable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hne : ¬ IsMulCommutative F.U)
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (cover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple F.TerminalHdot))
    (hs : Group.IsSolvable F.TerminalHdot) : F.ZU = F.Vi 1 := by
  classical
  by_contra hZ
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let : Representation.IsIrreducible F.terminalRepresentation :=
    irreducible_of_center_ne_point hG T hempty hM hu hmany hcard e hnot
      F d hne g hgP hgH hyp hZ
  have hr := full_orthogonal_of_center_ne_point hG T hempty hM hu hmany hcard e hnot
    F d hne g hgP hgH hyp hZ cover hs
  have hc := rankTwo_centers_commute h F d hne g hgP hgH
  have hg := F.conjugate_center_le_H g
    (F.P_le_seed_normalizer _ h.L_normalizes_seed hgP)
  obtain ⟨_,h9,_⟩ := rankTwo_full_orthogonal_center_residual h F d hne g hgP hgH hyp hZ hr
  obtain ⟨hsplit,hdis⟩ := terminal_tilde_center_residual_direct_sum F d g hg hc h9
  have hd := (orthogonal_case_of_center_ne_point hG T hempty hM hu hmany hcard e hnot
    F d hne g hgP hgH hyp hZ cover hs).2.1
  have he := rankTwo_full_orthogonal_center_commutator h F d hne g hgP hgH hyp hZ hr hd
  exact terminal_tilde_seed_splitting_contradiction F _ h.L_normalizes_seed
    g hgP hgH hc he hsplit hdis hZ

/-- Actual 14.3.15 larger-center exclusion: earlier-source geometry, the
terminal action and its SQTK cover are constructed from the selected flag.
Only solvability of the actual terminal actor remains with final assembly. -/
theorem source_center_eq_point_of_solvable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot) : F.ZU = F.Vi 1 := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨d,he,hx,B,v,hyp,cover⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  let := hx
  exact center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot
    F d hne g hgP hgH hyp cover hs

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
