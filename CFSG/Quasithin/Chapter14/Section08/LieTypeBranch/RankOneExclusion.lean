module

public import CFSG.Quasithin.MainForward.SourceFamilies
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels
public import CFSG.Quasithin.ClassificationModels.Families

/-!
# The rank-one exclusion in Theorem D

A member L of the actual local family L(G,T) gives a proper subgroup
J = ⟨L,T⟩ and a C-component inside J. In a rank-one model every proper
Sylow overgroup lies in the solvable Sylow normalizer. Thus J is solvable,
contradicting the nontrivial perfect C-component. Both L(G,T) and its
faithful subfamily L_f(G,T) are consequently empty.

The concrete Borel theorems supply the required facts for PSL₂(2^f),
PSU₃(2^f), and Sz(2^(2m+1)), through the actual model equivalences.
The unitary parameter remains the fixed-field order. The K-class stays
arbitrary in this local deduction; no classification theorem is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the
reduction to Theorem D (14.8.2), printed pp.1078–1079, with the rank-one
Borel structure from F.1.3(1), pp.259–260. This proves the rank-one
family exclusion, not the remaining rank-two and parameter classification.
-/

public section

namespace CFSG.Quasithin.Chapter14.Section08.LieTypeBranch

open Theory.GroupTheory MainForward

universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}

/-- The actual local family is empty when every proper Sylow overgroup lies
in its solvable rank-one Borel. -/
theorem localComponents_eq_empty_of_rankOneSylowFacts
    (h : IsSimpleQTKE K G) (T : Sylow 2 G)
    (hfacts : ChapterF.Source.RankOneSylowFacts T) : localComponents T = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro L hL
  obtain ⟨_, _, _, hJproper, _⟩ := localComponents_local_setup h T hL
  have hJB := hfacts.unique_maximal (L ⊔ (T : Subgroup G)) le_sup_right
    (lt_top_iff_ne_top.mpr hJproper)
  let := hfacts.solvable
  let : Group.IsSolvable (L ⊔ (T : Subgroup G) : Subgroup G) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJB)
  exact hL.1.not_isSolvable inferInstance

/-- The faithful local family is a subfamily of the empty local family. -/
theorem faithfulLocalComponents_eq_empty_of_rankOneSylowFacts
    (h : IsSimpleQTKE K G) (T : Sylow 2 G)
    (hfacts : ChapterF.Source.RankOneSylowFacts T) :
    faithfulLocalComponents T = ∅ := by
  rw [faithfulLocalComponents, localComponents_eq_empty_of_rankOneSylowFacts h T hfacts,
    Set.empty_inter]

/-- All concrete rank-one models in F.1.1 have empty local families under
the genuine simple QTKE hypotheses. -/
theorem localComponents_eq_empty_of_rankOneModel
    (h : IsSimpleQTKE K G) (T : Sylow 2 G)
    (hmodel : ChapterF.Source.IsRankOneModel G) : localComponents T = ∅ :=
  localComponents_eq_empty_of_rankOneSylowFacts h T (hmodel.rankOneSylowFacts T)

/-- The concrete rank-one Borel theorem also excludes the faithful family. -/
theorem faithfulLocalComponents_eq_empty_of_rankOneModel
    (h : IsSimpleQTKE K G) (T : Sylow 2 G)
    (hmodel : ChapterF.Source.IsRankOneModel G) : faithfulLocalComponents T = ∅ :=
  faithfulLocalComponents_eq_empty_of_rankOneSylowFacts h T (hmodel.rankOneSylowFacts T)

/-- The linear family, using an arbitrary finite field of the specified order
and its actual projective matrix-group equivalence. -/
theorem localFamilies_eq_empty_of_psl2
    (h : IsSimpleQTKE K G) (T : Sylow 2 G) {f : ℕ} (hf : 0 < f)
    (hmodel : ClassicalGroup.IsPSL G 2 (2 ^ f)) :
    localComponents T = ∅ ∧ faithfulLocalComponents T = ∅ :=
  ⟨localComponents_eq_empty_of_rankOneModel h T (.linear f hf hmodel),
    faithfulLocalComponents_eq_empty_of_rankOneModel h T (.linear f hf hmodel)⟩

/-- The unitary family retains the field order `(2^f)^2`, its Frobenius
involution, and the actual projective unitary equivalence. -/
theorem localFamilies_eq_empty_of_psu3
    (h : IsSimpleQTKE K G) (T : Sylow 2 G) {f : ℕ} (hf : 0 < f)
    (hmodel : ClassicalGroup.IsPSU G 3 (2 ^ f)) :
    localComponents T = ∅ ∧ faithfulLocalComponents T = ∅ :=
  ⟨localComponents_eq_empty_of_rankOneModel h T (.projective_unitary f hf hmodel),
    faithfulLocalComponents_eq_empty_of_rankOneModel h T (.projective_unitary f hf hmodel)⟩

/-- The Suzuki family uses the literal matrix carrier over the field of order
`2^(2*m+1)`, transported through the supplied equivalence. -/
theorem localFamilies_eq_empty_of_suzuki
    (h : IsSimpleQTKE K G) (T : Sylow 2 G) {m : ℕ}
    (hmodel : Nonempty (G ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
    localComponents T = ∅ ∧ faithfulLocalComponents T = ∅ :=
  ⟨localComponents_eq_empty_of_rankOneModel h T (.suzuki m hmodel),
    faithfulLocalComponents_eq_empty_of_rankOneModel h T (.suzuki m hmodel)⟩

omit [Finite G] in
/-- The complete Bender list consists of actual rank-one models. Its stricter
simple-group parameter ranges imply the positive ranges of F.1.1. -/
theorem isRankOneModel_of_bender (hmodel : ClassificationModels.IsBenderModel G) :
    ChapterF.Source.IsRankOneModel G := by
  cases hmodel with
  | linear f hf hi => exact .linear f (by omega) hi
  | unitary f hf hi => exact .projective_unitary f (by omega) hi
  | suzuki m _ hi => exact .suzuki m hi

/-- Every Bender model has empty L(G,T) in the simple QTKE source setup. -/
theorem localComponents_eq_empty_of_bender
    (h : IsSimpleQTKE K G) (T : Sylow 2 G)
    (hmodel : ClassificationModels.IsBenderModel G) : localComponents T = ∅ :=
  localComponents_eq_empty_of_rankOneModel h T (isRankOneModel_of_bender hmodel)

/-- Every Bender model has empty L_f(G,T) in the simple QTKE source setup. -/
theorem faithfulLocalComponents_eq_empty_of_bender
    (h : IsSimpleQTKE K G) (T : Sylow 2 G)
    (hmodel : ClassificationModels.IsBenderModel G) : faithfulLocalComponents T = ∅ :=
  faithfulLocalComponents_eq_empty_of_rankOneModel h T (isRankOneModel_of_bender hmodel)

/-- The nonempty-family input of Theorem D excludes the entire Bender list,
without assuming a rank restriction or a classification conclusion. -/
theorem not_isBenderModel_of_faithfulLocalComponents_nonempty
    (h : IsSimpleQTKE K G) (T : Sylow 2 G)
    (hne : (faithfulLocalComponents T).Nonempty) :
    ¬ ClassificationModels.IsBenderModel G := by
  intro hmodel
  exact hne.ne_empty (faithfulLocalComponents_eq_empty_of_bender h T hmodel)

end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
