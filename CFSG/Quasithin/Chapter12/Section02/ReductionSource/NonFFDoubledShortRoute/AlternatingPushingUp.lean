module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSymplecticReciprocal
-- Internal continuation of the reciprocal argument in this theorem family.
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSymplecticReciprocal
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSevenBounds
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.PushingUpConstrainedFinite
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourcePlacement

/-!
# Relative normality in both alternating doubled pushing-up rows

The A7 marking gives the original component central quotient cubic rank at
least two. The reciprocal index-two alternative would make that component
nonnormal in an SQTK group, contradicting the commuting-conjugate cubic-rank
bound. This supplies the original Fitting escape, complementing the existing
A6 escape theorem.

For either marking, the intersection residual maps onto A6 or A7 through
its full two-core and central quotient. Its action on the escaping constrained
component has solvable kernel. A simple section with cubic rank two cannot
occur in a group with cyclic Sylow three-subgroups. Thus the component's
central quotient has cubic rank at least two; the C.2.7 bound on its covering
center and the SQTK commuting-conjugate bound make it normal in the original
reciprocal overgroup. The ordinary branch is normal by C.3. The applications
retain the same witness, Fitting escape, whole source orbit, both residual
cores and fixed-subgroup identity.

These are relative-normality and reciprocal steps of C.4.5 and 4.4.6. They
do not exclude the normal component or prove odd-normalizer control. Its
parabolic action and module exclusions remain necessary for both alternating
rows and the final non-FF contradiction.

Source: Aschbacher--Smith A.3.8(3), C.3.2--4, C.4.5 and 4.2.12--4.4.6,
printed pp.46,149--152,610--620, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter4 Chapter4.Section04
open Chapter4.Section02.RankOneReciprocalEscape
open Chapter4.Section04.NormalizedRankOneOddControl
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem cubic_rank_two_of_simple_section
    {A S Q : Type*} [Group A] [Group S] [IsSimpleGroup S] [Group Q] [Finite Q]
    (hS : ¬ Group.IsSolvable S) (h3 : 2 ≤ primeRank 3 S)
    (π : A →* S) (hπ : Function.Surjective π)
    (r : A →* Q) [Group.IsSolvable r.ker] : 2 ≤ primeRank 3 Q := by
  by_contra! hr
  let m : Group.SolvableKernelModel A r.range := {
    kernel := r.ker
    normal := inferInstance
    solvable := inferInstance
    quotientEquiv := QuotientGroup.quotientKerEquivRange r }
  obtain ⟨U,f,hf⟩ := m.simple_section hS ⊤
    (π.comp (topEquiv : (⊤ : Subgroup A) ≃* A).toMonoidHom)
    (hπ.comp topEquiv.surjective)
  have hU : primeRank 3 U ≤ 1 :=
    (primeRank_subgroup_le 3 U).trans ((primeRank_subgroup_le 3 r.range).trans (by omega))
  let P : Sylow 3 U := Classical.choice inferInstance
  have hc := P.isCyclic_of_odd_of_primeRank_le_one (by decide) hU
  have hh := P.primeRank_le_one_of_surjective hc f hf
  omega

private theorem constrained_normal_of_cubic_simple_section
    {S : Type*} [Group S] [IsSimpleGroup S]
    {H M F R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (hS : ¬ Group.IsSolvable S) (h3 : 2 ≤ primeRank 3 S)
    (π : F →* S) (hπ : Function.Surjective π)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) : K.Normal := by
  obtain ⟨r,hker,_⟩ := constrained_normalized_inner_representation h hn K hK hq hout
  let := hker
  exact h.constrained_component_normal_of_central_threeRank K hK hq hout hfK
    (cubic_rank_two_of_simple_section hS h3 π hπ r)

/-- The genuine A7 marking excludes the reciprocal index-two case. -/
theorem sourceOrbit_seven_reciprocal_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 4 → ZMod 2))
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    EscapeCase L V A := by
  let := h.quasisimple
  obtain ⟨m⟩ := hmodel
  let e := (D.componentCentralQuotientEquiv h.quasisimple).trans
    ((centerQuotientCongr m.groupEquiv).trans
      ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot
        (by norm_num : 4 ≤ Nat.card (Fin 7)))).trans QuotientGroup.quotientBot))
  apply D.sourceOrbit_reciprocal_escape_of_cubic_rank h _ A hA ho hnot
  rw [primeRank_congr 3 e]
  exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)

/-- In both alternating doubled rows, the literal constrained escaping
component is normal in the original reciprocal overgroup. The full two-core
and central quotient are retained in the argument. -/
theorem sourceOrbit_alternating_witness_constrained_normal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {n : ℕ} (hn : n = 6 ∨ n = 7)
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (σ : Representation (ZMod 2) (alternatingGroup (Fin n)) Y)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) : K.Normal := by
  obtain ⟨m⟩ := hmodel
  let e := (D.componentCentralQuotientEquiv h.quasisimple).trans
    ((centerQuotientCongr m.groupEquiv).trans
      ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot
        (by simp only [Nat.card_eq_fintype_card,Fintype.card_fin]; omega :
          4 ≤ Nat.card (Fin n)))).trans QuotientGroup.quotientBot))
  let := h.quasisimple
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
  let : IsSimpleGroup (alternatingGroup (Fin n)) := e.symm.isSimpleGroup
  let : Group.IsPerfect (alternatingGroup (Fin n)) := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  rcases hw with ⟨_,_,_,_,_,_,hc,_,hNF,_,_,⟨c,_⟩,_⟩
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let π : F →* alternatingGroup (Fin n) := e.toMonoidHom.comp
    ((QuotientGroup.mk' (center (L ⧸ pCore 2 L))).comp
      (c.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F))))
  have hπ : Function.Surjective π := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (c.surjective.comp (QuotientGroup.mk'_surjective _)))
  exact constrained_normal_of_cubic_simple_section hc
    ((normal_subgroupOf_iff_le_normalizer hc.component_le).mp hNF)
    (Group.IsPerfect.not_isSolvable _)
    (alternatingGroup.TwoThreeCycles.two_le_primeRank (by omega)) π hπ K hK hq hout hfK

/-- The original Fitting escape in either alternating row selects a component
normal in H, in both the ordinary and constrained source branches. -/
theorem sourceOrbit_alternating_witness_escape_normal_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {n : ℕ} (hn : n = 6 ∨ n = 7)
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (σ : Representation (ZMod 2) (alternatingGroup (Fin n)) Y)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (he : ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H) :
    ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧ K.Normal ∧
      (IsComponent H K ∨ generalizedFitting K = pCore 2 K) := by
  have hc := hw.2.2.2.2.2.2.1
  have he' : ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H :=
    fun hh => he (hh.trans (subgroupOf_mono H inf_le_right))
  obtain ⟨K,hK,hq,hout,_,hcases⟩ := hc.ordinary_or_constrained_escape he'
  refine ⟨K,hK,hq,hout,?_,hcases⟩
  rcases hcases with ho | hfK
  · exact hc.ordinary_component_normal K ho
  · exact D.sourceOrbit_alternating_witness_constrained_normal h hn σ hmodel hw K hK hq hout hfK

/-- Actual A7 reciprocal application, retaining the same witness, Fitting
escape, full source orbit and its residual two-core. Normality concerns H,
not the ambient simple group. -/
theorem sourceOrbit_seven_reciprocal_normal_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 4 → ZMod 2))
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ∃ J H W : Subgroup G, Witness L V A J H W ∧
      ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
        (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H ∧
      let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      D.sourceOrbit ≤ J.pCoreIn 2 ∧ D.sourceOrbit ≤ F.pCoreIn 2 ∧
      D.sourceOrbit = ⁅D.sourceOrbit,F⁆ ∧
      D.sourceOrbit ⊓ centralizer (F : Set G) = ⊥ ∧
      ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
        ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧ K.Normal ∧
        (IsComponent H K ∨ generalizedFitting K = pCore 2 K) := by
  obtain ⟨J,H,W,hw,he⟩ := D.sourceOrbit_seven_reciprocal_escape h σ hmodel A hA ho hnot
  obtain ⟨_,hWJ,hWF,hcomm,hfix⟩ :=
    D.sourceOrbit_whole_pushingUp_residual_data h hmany hnon hA ho hw
  exact ⟨J,H,W,hw,he,hWJ,hWF,hcomm,hfix,
    D.sourceOrbit_alternating_witness_escape_normal_component h (Or.inr rfl) σ hmodel hw he⟩

/-- Actual A6 reciprocal application, retaining the same witness, Fitting
escape, full source orbit and its residual two-core. Normality concerns H,
not the ambient simple group. -/
theorem sourceOrbit_six_reciprocal_normal_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (alternatingNatural 6)))
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ∃ J H W : Subgroup G, Witness L V A J H W ∧
      ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
        (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H ∧
      let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      D.sourceOrbit ≤ J.pCoreIn 2 ∧ D.sourceOrbit ≤ F.pCoreIn 2 ∧
      D.sourceOrbit = ⁅D.sourceOrbit,F⁆ ∧
      D.sourceOrbit ⊓ centralizer (F : Set G) = ⊥ ∧
      ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
        ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧ K.Normal ∧
        (IsComponent H K ∨ generalizedFitting K = pCore 2 K) := by
  obtain ⟨J,H,W,hw,he⟩ := D.sourceOrbit_six_reciprocal_escape h hmodel A hA ho hnot
  obtain ⟨_,hWJ,hWF,hcomm,hfix⟩ :=
    D.sourceOrbit_whole_pushingUp_residual_data h hmany hnon hA ho hw
  exact ⟨J,H,W,hw,he,hWJ,hWF,hcomm,hfix,
    D.sourceOrbit_alternating_witness_escape_normal_component h (Or.inl rfl) (alternatingNatural 6) hmodel hw he⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
