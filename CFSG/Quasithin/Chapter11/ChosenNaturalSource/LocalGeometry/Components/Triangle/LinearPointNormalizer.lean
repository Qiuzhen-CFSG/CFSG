module
public import Theory.GroupAction.FourPointNormalizer
public import Theory.GroupTheory.ConjugateSpanSupplement
public import Theory.GroupTheory.PResidual.PerfectImage
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LinearMarkedSylow

/-!
# The original point normalizer and cubic-fixed span

For the actual field-four point, the action of N_G(V₁) on V₁ has order
dividing six. The original moving cubic X₁ and Sylow T cover this action,
so N_G(V₁)=C_G(V₁)X₁T. The latter two factors preserve V, hence the
normalizer span is exactly the original U=⟨V^{C_G(V₁)}⟩. The moving cubic
fixes only the identity on V₁; the existing Frattini bound then proves
C_U(X₁) elementary and disjoint from V₁.

The genuine G.2.1 hypothesis is constructed with the original L. Its local
actor is O²(N_L(V₁)), not the perfect residual L₁. In particular the scalar
part has not been dropped. The final application uses the literal source
H=C_G(V₁)X₁T and identifies its U with the already constructed span.
This supplies source geometry for G.2.5; it does not complete the later
chief-module comparison, extension selection, or SL₃(4) exclusion.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004, 11.1.2,
printed p.763, and G.2.1, printed p.332.
-/

open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
public noncomputable section
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

private theorem cartan_normalizes_point (f : InvariantFlag (.sl3 m))
    {X : Subgroup G} (hX : IsCartan T L X) : X ≤ normalizer (f.Vi 0 : Set G) := by
  apply f.cartan_normalizes _ hX 0
  intro i U hU hT
  exact (SL3.flag_inner_unique D S m i U hU hT).trans
    (SL3.flag_inner_unique D S m i (f.space i) (f.dimension i)
      (inf_le_left.trans (f.invariant i))).symm

private theorem point_card_four (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2) :
    Nat.card (f.Vi 0) = 4 := by
  let W : Submodule S.field.Carrier (Fin 3 → S.field.Carrier) := f.space 0
  have hc : Nat.card (f.Vi 0) = Nat.card W :=
    Nat.card_congr (SL3.subspaceEquiv D S m W).toEquiv
  rw [hc]
  change Nat.card W = 4
  rw [Module.natCard_eq_pow_finrank (K := S.field.Carrier),show Module.finrank S.field.Carrier W = 1 from f.dimension 0,S.field.card_eq,hd]
  norm_num

/-- The original point normalizer is exactly G₁X₁T, with the full original
centralizer G₁ and the same cubic and Sylow subgroup. -/
theorem linear_four_point_normalizer
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    {X : Subgroup G} (hX : IsCartan T L X)
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 0) ≤ centralizer (f.Vi 0 : Set G)) :
    normalizer (f.Vi 0 : Set G) =
      (centralizer (f.Vi 0 : Set G) ⊔ (X ⊓ Closure.coreQuotientCentralizer (f.Li 0))) ⊔
        (T : Subgroup G) := by
  let : IsElementaryAbelian 2 (f.Vi 0) := D.centralQuotientPreimage_elementary _
  exact Theory.GroupAction.four_normalizer_eq_centralizer_sup_cubic_sup_sylow
    (f.Vi 0) _ (point_card_four D S m f hd) hcard
    (inf_le_left.trans (cartan_normalizes_point D S m f hX)) hmove T (f.invariant 0)

/-- The source centralizer span is already the span under the whole point
normalizer. No extra normalizer-invariance premise is imposed on U. -/
theorem linear_four_point_spans_eq
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    {X : Subgroup G} (hX : IsCartan T L X)
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 0) ≤ centralizer (f.Vi 0 : Set G)) :
    conjugateSpanBy V (normalizer (f.Vi 0 : Set G)) =
      conjugateSpanBy V (centralizer (f.Vi 0 : Set G)) := by
  rw [linear_four_point_normalizer D S m f hd hX hcard hmove,sup_assoc]
  exact conjugateSpanBy_sup_of_normalizes_seed _ _ _
    (sup_le ((inf_le_left.trans (hX.1.trans inf_le_left)).trans D.normalizes) S.sylow_normalizes)
    ((sup_le (inf_le_left.trans (cartan_normalizes_point D S m f hX)) (f.invariant 0)).trans
      (normalizer_le_normalizer_centralizer (f.Vi 0)))

/-- The original cubic has no fixed point on V₁, and its fixed subgroup
in the actual centralizer span is elementary abelian. -/
theorem linear_four_cubic_fixed_span_elementary
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    {X : Subgroup G} (hX : IsCartan T L X)
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 0) ≤ centralizer (f.Vi 0 : Set G)) :
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    f.Vi 0 ⊓ centralizer (E : Set G) = ⊥ ∧
      IsElementaryAbelian 2 (U ⊓ centralizer (E : Set G) : Subgroup G) := by
  intro E U
  have hEN : E ≤ normalizer (f.Vi 0 : Set G) :=
    inf_le_left.trans (cartan_normalizes_point D S m f hX)
  obtain ⟨_,hUT,hΦ,_⟩ := linear_point_centralizer_span D S m f
  exact ⟨Theory.GroupAction.four_inf_centralizer_eq_bot_of_moving_cubic
    (f.Vi 0) E (point_card_four D S m f hd) hcard hEN hmove,
    Theory.GroupAction.cubic_fixed_elementary_of_frattini_le_four
      (f.Vi 0) E U (point_card_four D S m f hd) hcard hEN hmove
      (T.isPGroup'.to_le hUT) hΦ⟩

/-- Hypothesis G.2.1 for the original L and the full point normalizer.
Its local actor is literally O²(N_L(V₁)), including the odd scalar part. -/
theorem linear_point_source_hypothesis (f : InvariantFlag (.sl3 m)) :
    (ChapterG.Section02.Setup.mk V (f.Vi 0) L (T : Subgroup G)
      (normalizer (f.Vi 0 : Set G))).Hypothesis := by
  let B := ChapterG.Section02.Setup.mk V (f.Vi 0) L (T : Subgroup G)
    (normalizer (f.Vi 0 : Set G))
  let N := L ⊓ normalizer (f.Vi 0 : Set G)
  have hloc : B.L₁ ≤ N := (map_le_range _ _).trans (range_subtype N).le
  have hLi : f.Li 0 ≤ B.L₁ := by
    let : Group.IsNilpotent (N ⧸ pResidual 2 N) := (isPGroup_quotient_pResidual 2).isNilpotent
    exact map_mono (solvableResidual_le_of_solvable_quotient (pResidual 2 N))
  have hne : f.Vi 0 ≠ V := by
    intro he
    have hs := (Coordinates.sl3 m).preimage_injective
      (he.trans (Coordinates.sl3 m).preimage_top.symm)
    have hdim := f.dimension 0
    rw [hs,finrank_top] at hdim
    change Module.finrank S.field.Carrier (Fin 3 → S.field.Carrier) = 1 at hdim
    rw [Module.finrank_fin_fun] at hdim
    norm_num at hdim
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect S.source.maximal_faithful.1.1
  exact {
    elementary := D.elementary
    point_ne_bot := f.V_ne_bot 0
    point_le := D.centralQuotientPreimage_le _
    residual := pResidual_eq_top_of_isPerfect 2
    V_le_T := D.le_sylow
    T_normalizes_point := f.invariant 0
    T_normalizes_V := S.sylow_normalizes
    T_normalizes_L := D.sylow_normalizes_component
    sylow_LT := ⟨T.subtype le_sup_right,map_subgroupOf_eq_of_le le_sup_right⟩
    H_le := le_rfl
    local_le := sup_le (hloc.trans inf_le_right) (f.invariant 0)
    sylow_H := ⟨T.subtype (f.invariant 0),map_subgroupOf_eq_of_le (f.invariant 0)⟩
    characteristic_two := (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
      (Chapter1.mem_He_iff.mp (f.normalizer_mem_He S 0))
    local_normalizes_V := sup_le ((hloc.trans inf_le_left).trans D.normalizes) S.sylow_normalizes
    quotient_nonzero := hne
    irreducible := fun A hPA hAV hn => linear_point_interval_irreducible D S m f A hPA hAV
      (hLi.trans (le_sup_left.trans hn)) }

/-- Apply the genuine G.2.1 input to the literal H=G₁X₁T and U of 11.1.2.
The elementary fixed subgroup is disjoint from the original point. -/
theorem linear_four_original_centralizer_setup
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    {X : Subgroup G} (hX : IsCartan T L X)
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 0) ≤ centralizer (f.Vi 0 : Set G)) :
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let H := (centralizer (f.Vi 0 : Set G) ⊔ E) ⊔ (T : Subgroup G)
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    (ChapterG.Section02.Setup.mk V (f.Vi 0) L (T : Subgroup G) H).Hypothesis ∧
      conjugateSpanBy V H = U ∧ H ≤ normalizer (U : Set G) ∧
      IsElementaryAbelian 2 (U ⊓ centralizer (E : Set G) : Subgroup G) ∧
      Disjoint (U ⊓ centralizer (E : Set G)) (f.Vi 0) := by
  intro E H U
  have hH : normalizer (f.Vi 0 : Set G) = H :=
    linear_four_point_normalizer D S m f hd hX hcard hmove
  have hspan : conjugateSpanBy V H = U := by
    rw [←hH]
    exact linear_four_point_spans_eq D S m f hd hX hcard hmove
  obtain ⟨hfixed,helem⟩ := linear_four_cubic_fixed_span_elementary D S m f hd hX hcard hmove
  refine ⟨hH ▸ linear_point_source_hypothesis D S m f,hspan,
    hspan ▸ le_normalizer_conjugateSpanBy V H,helem,?_⟩
  exact (disjoint_iff.mpr hfixed).symm.mono_left inf_le_right

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
