module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianSeven
public import CFSG.Quasithin.Chapter12.Section08.Terminal.OrthogonalModels.Assembly
public import CFSG.Quasithin.ChapterG.Section11.NontrivialActorCatalogue

/-!
# The surviving orthogonal action in 12.9.4

The literal point residual and its full Sylow exclude the S₈ extension,
so the split-six actor is A₈. Its normal A₈ marking is therefore the whole
acting group, with actual equivariant quadratic coordinates. The original
normal point component surjects onto this group.

The marked plane is fixed by the original quotient Sylow. The concrete
four-block stabilizer gives three-rank at least two, so the source center
is larger than V₁ and its conjugate has nontrivial dotted image. These
are proved inputs to the remaining minimal-parabolic argument, not an
exclusion of the orthogonal row itself.

Source: Aschbacher--Smith 12.8.13(5) and 12.9.4, printed pp.855--856,859--860.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- The surviving split-six action has acting group A₈. The possible full S₈
extension is excluded using the literal point residual and its Sylow action. -/
theorem nonabelian_caseFive_alternating_eight
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B) :
    Nonempty (F.TerminalHdot ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨_,_,_,_,_,H,hH,e,_⟩ := h5
  let a := ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv.symm
  let J := H.map a.toMonoidHom
  let eJ : F.TerminalHdot ≃* J := e.trans (a.subgroupMap H)
  have hj : J.index ≤ 2 := by
    rw [show J.index = H.index from Subgroup.index_map_equiv H a]
    exact hH
  have hnot : J ≠ ⊤ := by
    intro ht
    exact point_hat_not_symmetric_eight h hn earlier F hne
      ⟨eJ.trans ((MulEquiv.subgroupCongr ht).trans topEquiv)⟩
  have hindex : J.index = 2 := by
    have hpos : J.index ≠ 0 := index_ne_zero_of_finite
    have hne : J.index ≠ 1 := fun he => hnot (index_eq_one.mp he)
    omega
  exact ⟨eJ.trans (MulEquiv.subgroupCongr
    (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex))⟩

/-- The original orthogonal action is the actual natural A₈ action, with
quadratic coordinates. This identifies the whole faithful quotient, not just
a family label or an abstract component. -/
theorem nonabelian_caseFive_marking
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B) :
    ∃ q : QuadraticForm (ZMod 2) (Additive F.Uhat),
      ∃ c : q.IsometryEquiv BinaryPermutation.TerminalOrthogonal.Eight.form,
      ∃ e : F.TerminalHdot ≃* alternatingGroup (Fin 8),
        ∀ a v, c (F.terminalRepresentation a v) =
          BinaryPermutation.naturalRepresentation (Fin 8) (e a).val (c v) := by
  obtain ⟨q,c,K,_,_,e,he⟩ := ChapterG.Section11.SplitSix.caseFive_selfcentralizing_marking h5
  obtain ⟨a⟩ := nonabelian_caseFive_alternating_eight h hn earlier F hne B h5
  have hc : Nat.card K = Nat.card F.TerminalHdot :=
    (Nat.card_congr e.toEquiv).trans (Nat.card_congr a.toEquiv).symm
  have ht : K = ⊤ := Subgroup.eq_top_of_card_eq K hc
  let k : F.TerminalHdot ≃* K := topEquiv.symm.trans (MulEquiv.subgroupCongr ht.symm)
  refine ⟨q,c,k.trans e,?_⟩
  intro x v
  exact he (k x) v



/-- In the split-six branch the original normal point component surjects
onto the whole faithful actor. -/
theorem nonabelian_caseFive_point_component_image
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) : F.terminalDot C.K1 = ⊤ := by
  obtain ⟨e⟩ := nonabelian_caseFive_alternating_eight h hn earlier F hne B h5
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup F.TerminalHdot := e.isSimpleGroup
  have hnormal : (F.terminalDot C.K1).Normal :=
    C.normal.map (QuotientGroup.mk' F.terminalHatAction.ker) (QuotientGroup.mk'_surjective _)
  apply hnormal.eq_bot_or_eq_top.resolve_left
  intro he
  exact point_hat_ne_bot h hn F hne
    (le_bot_iff.mp (he ▸ map_mono (comap_mono C.contains)))

/-- The marked plane in the surviving orthogonal action has a point
centralizer of three-rank at least two, using its actual full Sylow. -/
theorem nonabelian_caseFive_point_rank
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (v : Additive F.Uhat) (hv : v ≠ 0)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v}) :
    2 ≤ primeRank 3 (F.terminalPointCentralizer v) := by
  obtain ⟨q,c,e,he⟩ := nonabelian_caseFive_marking h hn earlier F hne B h5
  let Q := (T.subtype (F.invariant 1)).mapSurjective
    (f := QuotientGroup.mk' F.terminalHatAction.ker) (QuotientGroup.mk'_surjective _)
  have hfix : ∀ x ∈ (Q : Subgroup F.TerminalHdot),
      F.terminalFaithfulHatAction x v.toMul = v.toMul := by
    intro x hx
    exact sylow_fixes_plane_hat_point F v hv hline x hx
  let a : (⊤ : Subgroup F.TerminalHdot) ≃* alternatingGroup (Fin 8) := topEquiv.trans e
  have ha : ∀ (x : (⊤ : Subgroup F.TerminalHdot)) (u : F.Uhat),
      c (Additive.ofMul (F.terminalFaithfulHatAction x u)) =
        BinaryPermutation.naturalRepresentation (Fin 8) (a x).val (c (Additive.ofMul u)) := by
    intro x u
    exact he x (Additive.ofMul u)
  obtain ⟨_,_,_,_,_,_,_,hr⟩ := F.terminal_alternating_eight_residual_structure
    q c ⊤ a ha Q v.toMul hv hfix
  exact hr

/-- In the orthogonal branch the center strictly contains V₁, and the
literal conjugate center acts nontrivially on U/Z(U). These are the source
center inputs to the remaining minimal-parabolic argument. -/
theorem nonabelian_caseFive_center
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B) :
    F.Vi 1 < F.ZU ∧ F.terminalDot (conjugate F.ZU g) ≠ ⊥ := by
  obtain ⟨_,_,v,_,_,_,hv,hline,_⟩ :=
    nonabelian_transvection_geometry h earlier F hne g hgP hgH
  have hr := nonabelian_caseFive_point_rank h hn earlier F hne B h5 v hv hline
  refine ⟨?_, nonabelian_conjugate_center_detected h hn earlier F hne g hgP hgH v hline hr⟩
  let := h.chosen.elementary
  refine lt_of_le_of_ne (F.point_le_ZU (by omega)) ?_
  intro he
  have hr' := nonabelian_point_three_rank_of_center_eq h earlier F hne g hgP hgH v hline he.symm
  omega

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
