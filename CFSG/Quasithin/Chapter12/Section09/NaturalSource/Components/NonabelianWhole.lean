module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianRecognition
public import CFSG.Quasithin.ChapterG.Section10.NumericalGeometry
public import CFSG.Quasithin.ChapterG.Section11.LargeActorExchangedExclusion
public import CFSG.Quasithin.ChapterG.Section11.LargeWholeModels
public import CFSG.Quasithin.ChapterG.Section11.LargeWholePair
public import CFSG.Quasithin.ChapterG.Section11.LargeWholeSeven
public import CFSG.Quasithin.ChapterG.Section11.LargeWholeBinaryG2

/-!
# The larger-center branch has a whole A8 component

A nontrivial returning-center image removes one rank from the actual
quotient actor. The resulting half-degree bound excludes every exchanged
natural constituent and the two-component tensor branch. The checked
whole-component carrier theorem leaves A7, A8 and binary G2 derived;
the original marked smaller actor excludes A7, and the original perfect
point residual excludes G2. Thus the same whole component is A8.

The ambient module comparison then constructs the actual split quadratic
six-space, so the original CaseFive contradiction excludes this branch in
both degrees. Every remaining nonabelian span has center exactly V₁ and
trivial returning-center image. The final same-flag consumer retains only
the extraspecial-center recognition; full catalogue exhaustion remains open.
Source: Aschbacher--Smith 12.9.4 and G.11.6--7, printed pp.859,365--367.
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

/-- The original larger-center branch supplies the half-degree bound on
its full actor, with the literal smaller-actor quotient retained. -/
theorem nonabelian_dimension_le_twice_actor
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hZ : F.Vi 1 < F.ZU) [IsElementaryAbelian 2 (F.terminalDot (F.X g))] :
    finrank (ZMod 2) (Additive F.Uhat) ≤
      2 * finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by
  obtain ⟨hX,B,v,hg10,_⟩ := nonabelian_g10_hypothesis h earlier F hne g hgP hgH
  apply hg10.dimension_le_twice_actor_of_smaller_ne_bot
  intro hb
  have hh := congrArg (fun A : Subgroup (F.terminalDot (F.X g)) =>
    A.map (F.terminalDot (F.X g)).subtype) hb
  have hle : F.terminalDot (conjugate F.ZU g) ≤ F.terminalDot (F.X g) :=
    map_mono (comap_mono (F.conjugate_ZU_le_X g))
  exact nonabelian_conjugate_center_ne_bot h hn earlier F hne g hgP hgH hZ
    (by simpa only [map_subgroupOf_eq_of_le hle, Subgroup.map_bot] using hh)

/-- Every larger-center source configuration has an actual whole A8
component on the original terminal representation. The quotient maps,
marked actor and form have not been replaced by abstract family tags. -/
theorem nonabelian_larger_center_whole_eight
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (preferred : PreferredDimension KnownSimple.IsKnownSimple T n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hZ : F.Vi 1 < F.ZU) :
    ∃ hX : IsElementaryAbelian 2 (F.terminalDot (F.X g)),
      let := hX
      ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
        ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
          (F.terminalDot (F.X g))
          ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
        hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v} ∧
        ∃ J : Subgroup F.TerminalHdot,
          ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
            F.terminalRepresentation (F.terminalDot (F.X g)) J J
            (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∧
          Nonempty (J ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨hX,B,v,hg10,hline,hS,hns,hi,hd,hm⟩ :=
    nonabelian_remaining_recognition modules h hn preferred earlier four F hne g hgP hgH
  let := hX
  have hlarge := nonabelian_dimension_le_twice_actor h hn earlier F hne g hgP hgH hZ
  have hsix : 6 ≤ finrank (ZMod 2) (Additive F.Uhat) := by omega
  have hZdot := nonabelian_conjugate_center_ne_bot h hn earlier F hne g hgP hgH hZ
  obtain ⟨hw,hm⟩ := hm.resolve_left (fun he => hZ.ne he.1.symm)
  obtain ⟨J,hJ,hmJ,horth,h9⟩ := ExchangedRecognition.whole_of_remaining_of_large
    hg10 ⟨nonabelian_sqtkCover h F⟩ hw hS hns hlarge hm
  have heq : componentOrbit J ⊤ = J := by
    by_contra heq
    exact LargeWhole.not_component_pair hg10 hw hlarge h9 heq
  rw [heq] at h9
  obtain ⟨_,hmodel⟩ := LargeWhole.single_small_carrier hg10 h9 hw hS hsix hlarge
  cases hmodel with
  | seven e =>
    exact (LargeWhole.not_seven_of_smaller_ne_bot hg10 h9 hsix
      (map_mono (comap_mono (F.conjugate_ZU_le_X g))) hZdot e.some).elim
  | eight e => exact ⟨hX,B,v,hg10,hline,J,h9,e⟩
  | binary_g2 e =>
    exact (nonabelian_not_caseSix h hn earlier F hne
      (LargeWhole.caseSix_of_binary_g2 hg10 h9 hsix hlarge e.some)).elim

/-- Whole A8 recognition constructs a genuine CaseFive for some transported
polar form. No choice of the G.10 form is needed by the original CaseFive
contradiction, so the supplied action and split quadratic form suffice. -/
theorem whole_eight_caseFive
    {D A : Type*} [Group D] [Finite D] [AddCommGroup A]
    [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]
    {ρ : Representation (ZMod 2) D A} {X J : Subgroup D}
    [IsElementaryAbelian 2 X]
    (h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      ρ X J J (finrank (ZMod 2) (Additive X)))
    (hd : 6 ≤ finrank (ZMod 2) A) (e : J ≃* alternatingGroup (Fin 8)) :
    ∃ B : LinearMap.BilinForm (ZMod 2) A, CaseFive ρ B := by
  let := h9.normal_H
  obtain hsmall | ⟨hnat,hd6,_⟩ :=
    ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.four_alternatives
      h9 (e.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two)
  · have := hsmall.2.1
    omega
  obtain ⟨e,f,hf⟩ := hnat
  let E := f.trans RankTwo.Symmetric.splitNaturalEquiv
  have hE (l : J) (u : A) : E (ρ l u) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 8) (e l) (E u) := by
    change RankTwo.Symmetric.splitNaturalEquiv (f (ρ l u)) = _
    have hfl := hf l u
    change f (ρ l u) = Representation.BinaryLinearRecognition.orthogonalEightAction (e l) (f u) at hfl
    rw [hfl]
    exact RankTwo.Symmetric.symmetricOrthogonalEquiv_action (e l).val (f u)
  obtain ⟨q,hq,hact,hker⟩ := BinaryPermutation.EightNormalizer.exists_ambient_hom
    ρ J e.toMonoidHom e.surjective E hE
  have hqi : Function.Injective q := (MonoidHom.ker_eq_bot_iff q).mp
    (hker.trans ((MonoidHom.ker_eq_bot_iff ρ).mpr h9.faithful))
  have hA : alternatingGroup (Fin 8) ≤ q.range := by
    intro b hb
    obtain ⟨l,hl⟩ := e.surjective ⟨b,hb⟩
    exact ⟨l,(hq l).trans (congrArg Subtype.val hl)⟩
  have hind : q.range.index ≤ 2 := by
    have hi := Subgroup.index_antitone hA
    simpa only [alternatingGroup.index_eq_two] using hi
  let c := RankTwo.Symmetric.symmetricOrthogonalEquiv
  let H := q.range.map c.toMonoidHom
  let eG := (MonoidHom.ofInjective hqi).trans
    (q.range.equivMapOfInjective c.toMonoidHom c.injective)
  let Q := (ClassicalOrthogonal.formD 3 (ZMod 2)).comp f.toLinearMap
  refine ⟨Q.polarBilin,hd6,Q,rfl,f,(fun _ => rfl),H,?_,eG,?_⟩
  · exact (Subgroup.index_map_equiv q.range c).le.trans hind
  · intro a u
    apply RankTwo.Symmetric.splitNaturalEquiv.injective
    change E (ρ a u) = RankTwo.Symmetric.splitNaturalEquiv
      (RankTwo.Symmetric.splitOrthogonalAction (c (q a)) (f u))
    rw [RankTwo.Symmetric.symmetricOrthogonalEquiv_action]
    exact hact a u

/-- The larger-center branch is impossible on the original flag in both
degrees. Recognition gives the actual split six-space; the original CaseFive
argument discharges its ambient contradiction with the retained earlier inputs. -/
theorem nonabelian_larger_center_impossible
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (preferred : PreferredDimension KnownSimple.IsKnownSimple T n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hZ : F.Vi 1 < F.ZU) : False := by
  obtain ⟨hX,_,_,_,_,J,h9,⟨e⟩⟩ :=
    nonabelian_larger_center_whole_eight modules h hn preferred earlier four F hne g hgP hgH hZ
  let := hX
  have hd := nonabelian_hat_rank h earlier F hne
  obtain ⟨B,h5⟩ := whole_eight_caseFive h9 (by omega) e
  have hn4 := nonabelian_degree_four_of_hat_rank_le_six h hn earlier F hne h5.1.le
  subst n
  exact nonabelian_caseFive_impossible modules h preferred earlier four F hne g hgP hgH B h5
/-- Every remaining nonabelian point span has center exactly the original
point. The larger-center branch is discharged, using the same escaping g
and the actual whole-component action. -/
theorem nonabelian_center_eq_point
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (preferred : PreferredDimension KnownSimple.IsKnownSimple T n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    F.ZU = F.Vi 1 := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  by_contra hZ
  have hlt : F.Vi 1 < F.ZU := by
    apply lt_of_le_of_ne ?_ (Ne.symm hZ)
    rw [← F.seed_inf_center_eq_point_of_ambient_natural h.naturalMarking h.rank.1 hne]
    exact inf_le_right
  exact nonabelian_larger_center_impossible modules h hn preferred earlier four F hne
    g hgP hgH hlt

/-- The actual smaller actor vanishes when the center is the marked point.
The original conjugation preserves V₂, so the returning point lies in U,
whose inner action on U/Z(U) is trivial. -/
theorem nonabelian_smaller_actor_eq_bot_of_center_eq
    {K : GroupClass.{u}} (h : HigherRankHypothesis K T L V n)
    (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (g : G) (hgP : g ∈ F.P L) (hZ : F.ZU = F.Vi 1) :
    F.terminalDot (conjugate F.ZU g) = ⊥ := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  have hn : 2 ≤ n := by have := h.rank; omega
  have hg := F.P_le_G₂ hn L h.chosen.normalizes hgP
  have hle : conjugate F.ZU g ≤ F.U := by
    rw [hZ]
    exact (conjugate_le_of_normalizes (F.monotone (by omega : 1 ≤ 2)) g hg).trans
      ((F.le_seed 2).trans (le_conjugateSpanBy V F.H))
  apply bot_unique
  rintro _ ⟨a,ha,rfl⟩
  apply (QuotientGroup.eq_one_iff _).mpr
  exact U_le_action_kernel F F.terminalHatAction F.terminalHatAction_apply_mk (hle ha)

/-- Final same-flag recognition reduction: the larger center and every
recognized catalogue row are excluded. The unresolved fixed-line or
whole/exchanged recognition is now confined to the extraspecial-center case,
with the original point-centralizer three-rank bound and trivial smaller actor. -/
theorem nonabelian_extraspecial_recognition
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (preferred : PreferredDimension KnownSimple.IsKnownSimple T n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    F.ZU = F.Vi 1 ∧ F.terminalDot (conjugate F.ZU g) = ⊥ ∧
    ∃ hX : IsElementaryAbelian 2 (F.terminalDot (F.X g)),
      let := hX
      ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
        ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
          (F.terminalDot (F.X g))
          ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
        hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v} ∧
        NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
        ¬ Group.IsSolvable F.TerminalHdot ∧ IsIrreducible F.terminalRepresentation ∧
        2 * (n-1) ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
        primeRank 3 (F.terminalPointCentralizer v) ≤ 1 ∧
        (fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
            Submodule.span (ZMod 2) {v} ∨
          (LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
            ExchangedRecognition.RemainingComponentModels F.terminalRepresentation B v
              (hatSpace F (F.E g)) (F.terminalDot (F.X g)))) := by
  have hZ := nonabelian_center_eq_point modules h hn preferred earlier four F hne g hgP hgH
  obtain ⟨hX,B,v,hg10,hline,hS,hns,hi,hd,hm⟩ :=
    nonabelian_remaining_recognition modules h hn preferred earlier four F hne g hgP hgH
  let := hX
  refine ⟨hZ,nonabelian_smaller_actor_eq_bot_of_center_eq h F g hgP hZ,
    hX,B,v,hg10,hline,hS,hns,hi,hd,
    nonabelian_point_three_rank_of_center_eq h earlier F hne g hgP hgH v hline hZ,?_⟩
  exact hm.imp (fun hh => hh.2.1) id

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
