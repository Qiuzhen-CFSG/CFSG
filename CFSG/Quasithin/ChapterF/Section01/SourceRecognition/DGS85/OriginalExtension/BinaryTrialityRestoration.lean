module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.BinaryTrialityQuotients
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.TrialityNative
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.OddLocalBorels
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityTwo.Basic
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.Basic

/-!
# Original binary triality restoration and the all-degree extension

A genuine reduced binary triality comparison gives full endpoint core
quotients of orders 504 and 42. Inclusion of the unchanged original local
factors, source rank-one classification, and nonsolvability of the arms
endpoint recover PSL₂(8) and PSL₂(2). Their odd outer orders force both
original local Borels to normalize S. Thus S = O₂(B), and the original
endpoints and full Borel coincide with their reduced counterparts.

The resulting isomorphism preserves every reduced endpoint and middle
marking, in either orientation. Combining it with nonbinary native lifting
restores a genuine type-preserving automorphism extension in every positive
triality degree, without assuming finiteness of the ambient completion.
The marked reduced comparison remains the earlier recognition input.

Source: DGS, Groups and Graphs (1985), (15.2), pp.226–228, including the
binary triality obstruction on p.228; Aschbacher–Smith F.1.9–12, pp.261–264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.BinaryTriality
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open SourceCompletion.TrialityTwo

/-- The quotient sizes are those of the full binary parabolics, so the
central endpoint retains its odd factor of order seven. -/
theorem parabolic_core_quotient_card (a : Node) :
    Nat.card (Parabolics.parabolic parameters a ⧸ pCore 2 (Parabolics.parabolic parameters a)) =
      if a = .arms then 504 else 42 := by
  have hc : Nat.card (pCore 2 (Parabolics.parabolic parameters a)) =
      Nat.card (radical parameters a) := by
    rw [← card_map_of_injective (Parabolics.parabolic parameters a).subtype_injective,
      parabolic_twoCore_map parameters rfl a]
  have hh := (pCore 2 (Parabolics.parabolic parameters a)).card_mul_index
  rw [hc,parabolic_card a] at hh
  change Nat.card (radical parameters a) * Nat.card
    (Parabolics.parabolic parameters a ⧸ pCore 2 (Parabolics.parabolic parameters a)) = _ at hh
  cases a
  · rw [RadicalCoordinates.radical_arms_card parameters rfl] at hh
    norm_num [parameters,Parameters.q,binaryParameters] at hh ⊢
    omega
  · rw [RadicalCoordinates.radical_central_card parameters rfl] at hh
    norm_num [parameters,Parameters.q,binaryParameters,
      show Node.central ≠ Node.arms from by decide] at hh ⊢
    omega

theorem arms_not_solvable : ¬ Group.IsSolvable (Parabolics.parabolic parameters .arms) := by
  intro hs
  let := hs
  let : Group.IsSolvable (localFactor parameters .arms) :=
    Group.isSolvable_of_isSolvable_injective
      (inclusion_injective (localFactor_le_parabolic parameters .arms))
  let e := (localFactorArmsQuotientEquivPSL2 parameters rfl).trans
    (Theory.PSL2.sl2QuotientEquiv (ExtensionField parameters)).symm
  let : Group.IsSolvable SL(2,ExtensionField parameters) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  have hF : 2 < Nat.card (ExtensionField parameters) := by
    rw [card_extensionField]
    decide
  let := Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_perfect hF
  let := Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_simple hF
  exact Group.IsPerfect.not_isSolvable SL(2,ExtensionField parameters) inferInstance

variable {G : Type*} [Group G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} (h : HypothesisF11 L S)

include h in
/-- Recover an original local quotient from its reduced binary endpoint;
no marking of the local factor or its quotient is assumed. -/
theorem original_local_quotient (j : Fin 2) (a : Node)
    (e : Source.parabolic L (SuzukiContainment.reducedSylow L S) j ≃*
      Parabolics.parabolic parameters a) :
    ClassicalGroup.IsPSL (L j ⧸ pCore 2 (L j)) 2 (2^(if a = .arms then 3 else 1)) := by
  let := h.finite_local j
  have hd := local_quotient_card_dvd_reduced h j
  rw [Nat.card_congr (LocalCoreTransport.quotientEquiv 2 e).toEquiv,
    parabolic_core_quotient_card a] at hd
  cases a
  · apply linear_three_of_card_dvd_504 (h.quotient j) _ hd
    intro hs
    have hP := ((SuzukiContainment.reduced_hypothesis h).parabolic_solvable_iff_local_quotient j).mpr hs
    let := hP
    exact arms_not_solvable (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  · exact linear_one_of_card_dvd_42 (h.quotient j) hd

variable (i : Bool) (e : Iso (reducedAmalgam L S) (TrialityNative.amalgam 1 Nat.zero_lt_one i))

include h e in
/-- Odd outer orders in both original local quotients force both whole
local Borels to normalize the same original S. -/
theorem original_borel_normalizes : commonBorel L S ≤ normalizer (S : Set G) := by
  have hb (j : Fin 2) : borel (L j) S ≤ normalizer (S : Set G) := by
    fin_cases j
    · have he := original_local_quotient h 0 (TrialityNative.side i) e.left
      exact odd_linear_borel_normalizes_of_finite_parabolics h 0
        (by cases i <;> decide : Odd (if TrialityNative.side i = .arms then 3 else 1)) he
    · have he := original_local_quotient h 1 (TrialityNative.side (!i)) e.right
      exact odd_linear_borel_normalizes_of_finite_parabolics h 1
        (by cases i <;> decide : Odd (if TrialityNative.side (!i) = .arms then 3 else 1)) he
  exact sup_le (sup_le (hb 0) (hb 1)) S.le_normalizer

include h e in
/-- Binary triality admits no original two-power enlargement: this is an
equality of the literal source subgroups, with the full odd Borel retained. -/
theorem original_sylow_eq_reduced : S = SuzukiContainment.reducedSylow L S := by
  apply le_antisymm _ (SuzukiContainment.reducedSylow_le h)
  exact le_pCoreIn_of_normalizes h.S_isP le_sup_right (original_borel_normalizes h i e)

/-- Restore the supplied binary marking by the identity on original elements. -/
@[expose] def originalIso : Iso (originalAmalgam L S) (TrialityNative.amalgam 1 Nat.zero_lt_one i) :=
  (NativeRestoration.originalIsoReduced (original_sylow_eq_reduced h i e)).trans e

/-- The restored maps retain both reduced restrictions and the entire middle
map, rather than only the two abstract endpoint groups. -/
theorem originalIso_restrictions :
    (∀ x : Source.parabolic L (SuzukiContainment.reducedSylow L S) 0,
      (originalIso h i e).left (inclusion (SuzukiContainment.reduced_parabolic_le h 0) x) = e.left x) ∧
    (∀ x : commonBorel L (SuzukiContainment.reducedSylow L S),
      (originalIso h i e).middle (inclusion (SuzukiContainment.reduced_commonBorel_le h) x) = e.middle x) ∧
    (∀ x : Source.parabolic L (SuzukiContainment.reducedSylow L S) 1,
      (originalIso h i e).right (inclusion (SuzukiContainment.reduced_parabolic_le h 1) x) = e.right x) :=
  NativeRestoration.originalIsoReduced_trans_reduced h (original_sylow_eq_reduced h i e) e

include h e in
theorem original_borel_eq_reduced :
    commonBorel L S = commonBorel L (SuzukiContainment.reducedSylow L S) :=
  congrArg (commonBorel L) (original_sylow_eq_reduced h i e)

include h e in
theorem original_borel_index_one :
    (commonBorel L (SuzukiContainment.reducedSylow L S)).relIndex (commonBorel L S) = 1 := by
  rw [← original_borel_eq_reduced h i e,relIndex_self]

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.BinaryTriality

namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.TrialityNative
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics SourceCompletion

/-- Every positive triality degree restores both original endpoint maps into
a genuine type-preserving extension. Degree one is proved directly from its
local quotients; higher degrees use the native lift, retaining even extensions. -/
theorem exists_original_extension_all_degrees
    {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 L S) (m : ℕ) (hm : 0 < m) (i : Bool)
    (e : Iso (reducedAmalgam L S) (amalgam m hm i)) :
    ∃ E : UnitaryNonbinary.SourceExtension
        (Parabolics.parabolic (binaryParameters m hm) (side i))
        (Parabolics.parabolic (binaryParameters m hm) (side (!i))),
      ∃ f : Iso (originalAmalgam L S) E.amalgam,
        (∀ x : Source.parabolic L (SuzukiContainment.reducedSylow L S) 0,
          (f.left (inclusion (SuzukiContainment.reduced_parabolic_le h 0) x) :
            MulAut (BinaryCarrier m hm)) = MulAut.conj (e.left x).val) ∧
        (∀ x : Source.parabolic L (SuzukiContainment.reducedSylow L S) 1,
          (f.right (inclusion (SuzukiContainment.reduced_parabolic_le h 1) x) :
            MulAut (BinaryCarrier m hm)) = MulAut.conj (e.right x).val) := by
  by_cases hm1 : m = 1
  · subst m
    let P := Parabolics.parabolic (binaryParameters 1 hm) (side i)
    let Q := Parabolics.parabolic (binaryParameters 1 hm) (side (!i))
    have hPQ : P ⊓ Q = Parabolics.borel (binaryParameters 1 hm) := by
      cases i
      · exact parabolic_inf_binary _ rfl
      · exact (inf_comm _ _).trans (parabolic_inf_binary _ rfl)
    let j : Iso (amalgam 1 hm i)
        (UnitaryNonbinary.SourceExtension.nativeAmalgam (P₀ := P) (P₁ := Q)) := {
      left := MulEquiv.refl _
      right := MulEquiv.refl _
      middle := MulEquiv.subgroupCongr hPQ.symm
      left_commutes := fun _ => Subtype.ext rfl
      right_commutes := fun _ => Subtype.ext rfl }
    let k := j.trans (TrialityNonbinary.innerComparison P Q (TrialityNonbinary.conj_injective 1 hm))
    let f := (BinaryTriality.originalIso h i e).trans k
    refine ⟨TrialityNonbinary.innerExtension P Q,f,?_,?_⟩
    · intro x
      change MulAut.conj (((BinaryTriality.originalIso h i e).left
        (inclusion (SuzukiContainment.reduced_parabolic_le h 0) x)).val) = _
      rw [(BinaryTriality.originalIso_restrictions h i e).1]
    · intro x
      change MulAut.conj (((BinaryTriality.originalIso h i e).right
        (inclusion (SuzukiContainment.reduced_parabolic_le h 1) x)).val) = _
      rw [(BinaryTriality.originalIso_restrictions h i e).2.2]
  · have hm2 : 1 < m := by omega
    obtain ⟨f,_,hl,hr⟩ := exists_original_extension_iso h m hm i e hm2
    exact ⟨extension h m hm i e hm2,f,hl,hr⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.TrialityNative
