module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.CubicIntersection
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.RankSolvable

/-!
# Original unitary reduction (b)

The original chosen module supplies one compatible flag marking. Its plane
residual has an odd cubic lift whose joined three-spaces have centralizer
in M, using precisely original 13.3.12(2). The literal residual intersection
is therefore a two-group, giving solvability and all odd-rank bounds.

The universal earlier 12.2 statements and the plane-centralizer source
remain explicit. No conjugator, intersection, solvability or rank premise
is added to the original configuration. Source: Aschbacher--Smith
13.3.14(b), printed p.891.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Original unitary reduction (b), retaining exactly the earlier nondegenerate
plane-centralizer source input. The actual cubic lift and the vanishing
intersection are constructed internally. -/
theorem unitary_original_residual_solvable_and_odd_rank
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (h : Hypothesis1331 D.T D.L) (chosen : ChosenModule D.T D.L D.V)
    (hmax : D.L ∈ Chapter1.LStar G (D.T : Subgroup G))
    (eL : (D.L ⧸ pCore 2 D.L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (e : inducedAutomizer D.V D.L ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0 : Additive D.V ≃ₗ[F] Atlas.G2.Natural.Space F)
    (he0 : ∀ (l : inducedAutomizer D.V D.L) v,
      E0 (automizerRepresentation D.V l v) =
        Atlas.G2.Natural.derivedAction F (e l) (E0 v))
    (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
    (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
    (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
    (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
    (B : Subgroup G) (hBV : B ≤ D.V)
    (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
    (hHfull : D.H = normalizer (D.V₁ : Set G))
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hplanes : UnitaryPlaneCentralizers D.V (normalizer (D.L : Set G))) :
    Group.IsSolvable (Noncentrality.centralizingResidual D.UH) ∧
      ∀ p : ℕ, p.Prime → Odd p → primeRank p (Noncentrality.centralizingResidual D.UH) ≤ 1 := by
  have h12 := unitary_original_hypothesis1223 h hmax eL
  obtain ⟨hTN,hNL⟩ := unitary_original_module_normalizers h hmax eL chosen structural
  obtain ⟨rho,E,he,_,hd,hz,hp,hs⟩ := exists_unitary_flag_marking D.T D.L D.V₁ B D.Vplus
    chosen.normalizes hNL e E0 he0 hTN hZV hBV hUV hTZ hTB hTU hZ hB hU
  have hZB := marked_point_le_plane D.V₁ B E hz hp hZV
  have hBU : B ≤ D.Vplus := by
    intro b hb
    let v : Additive D.V := Additive.ofMul ⟨b,hBV hb⟩
    have hv : E v ∈ plane := hp ▸ (mem_pointCoordinateSubspace E B v).mpr hb
    exact (mem_pointCoordinateSubspace E D.Vplus v).mp (hs.symm ▸ plane_le_seed hv)
  have hZn : D.V₁ ≠ ⊥ := D.V₁.one_lt_card_iff_ne_bot.mp (by omega)
  let : IsSimpleGroup Atlas.G2.Natural.BinaryNormalizer.Derived := Atlas.G2.isSimple_commutator_binary
  have hfaith : D.L ⊓ centralizer (D.V : Set G) ≤ D.L.pCoreIn 2 := by
    have hc := congrArg (map D.L.subtype) (chosen.centralizer_eq_core_of_simple eL.isSimpleGroup)
    exact (show D.L ⊓ centralizer (D.V : Set G) = D.L.pCoreIn 2 by
      simpa only [pCoreIn,subgroupOf_map_subtype,inf_comm] using hc).le
  have hout : ¬ D.H ≤ normalizer (D.L : Set G) := by
    rw [hHfull]
    exact unitary_original_line_escape h h12 earlier chosen e E0 he0 hZV hZ
  obtain ⟨g,hg,hodd,hgB,hjoin⟩ := unitary_odd_cubic_join_centralizer D.L B D.Vplus
    (normalizer (D.L : Set G)) rho E he hp hs hBV chosen.normalizes hd hplanes
  have hgL : g ∈ D.L := ((map_subtype_le _).trans inf_le_left) hg
  have hi := unitary_residual_intersection_isTwoGroup D.T D.L D.V₁ B D.Vplus D.H
    h.qtke rho E he hs hUV hZB hBU (hZV.trans chosen.le_sylow) hZn hTZ
    chosen.sylow_normalizes_component chosen.normalizes hfaith
    (h12.source_chosen_TI structural chosen)
    (h12.source_normalizer_maximal_unique structural
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))).2
    hHfull hout ⟨g,hgL⟩ hgB hjoin
  exact ⟨unitary_residual_solvable_of_intersection h.qtke D.V₁ B D.Vplus D.H hZB hBU
      hHfull hB g hgB hodd hi,
    unitary_residual_odd_rank_of_intersection h.qtke D.V₁ B D.Vplus D.H hZB hBU
      hHfull hB g hgB hi⟩
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
