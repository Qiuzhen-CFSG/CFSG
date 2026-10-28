module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.Assembly

/-!
# The remaining local geometry for odd PSL₂

The whole-group component case settles any invariant family containing a
nontrivial actor of rank at most one. For the other families it suffices to
construct, outside each proper Sylow overgroup containing the weak-closure
normalizer, a genuine rank-one E-member. The latter obligation is kept
explicit as `LargeFamilyEscapeAt`; no model geometry is asserted here.

The E-member predicate retains the local tau, intrinsic radical and two-core
quotients, and two-residual convention of E.1.2. A witness must verify those
conditions, including the Sylow intersection and the quotient-image rank.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.2, E.1.5 and E.1.14(6), printed pp.209--210 and 214; the last cites
Aschbacher (1982), *GF(2)-representations of finite groups*, Lemma 4.10.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration

open Subgroup
open ValuesEvenClassical.RankOneUpper

variable {G : Type*} [Group G] [Finite G]

/-- Local witnesses still required when every nontrivial family member in T
has rank at least two. The overgroup and weak closure are literal ambient
subgroups; the E-member rank is taken in its intrinsic E1 or E2 quotient. -/
def LargeFamilyEscapeAt (T : Sylow 2 G) : Prop :=
  ∀ Ω : Set (Subgroup G), IsElementaryFamily Ω →
    (∀ A ∈ Ω, A ≤ (T : Subgroup G) → A ≠ ⊥ → 1 < Group.rank A) →
    ∀ M : Subgroup G, (T : Subgroup G) ≤ M → M ≠ ⊤ →
      normalizer (weakClosure (T : Subgroup G) Ω : Set G) ≤ M →
      ∃ A : Subgroup G, A ∈ Ω ∧ A ≤ (T : Subgroup G) ∧
        ∃ H : Subgroup G, IsEMemberAt 1 (T : Subgroup G) A H ∧ ¬ H ≤ M

/-- The model calculation may use the classification of maximal overgroups:
escaping a maximal overgroup also escapes the given proper subgroup. -/
theorem largeFamilyEscapeAt_of_maximal_escape (T : Sylow 2 G)
    (hescape : ∀ Ω : Set (Subgroup G), IsElementaryFamily Ω →
      (∀ A ∈ Ω, A ≤ (T : Subgroup G) → A ≠ ⊥ → 1 < Group.rank A) →
      ∀ M : Subgroup G, IsCoatom M → (T : Subgroup G) ≤ M →
        normalizer (weakClosure (T : Subgroup G) Ω : Set G) ≤ M →
        ∃ A : Subgroup G, A ∈ Ω ∧ A ≤ (T : Subgroup G) ∧
          ∃ H : Subgroup G, IsEMemberAt 1 (T : Subgroup G) A H ∧ ¬ H ≤ M) :
    LargeFamilyEscapeAt T := by
  intro Ω hΩ hlarge M hTM hM hNM
  obtain ⟨M', hM', hMM'⟩ := (eq_top_or_exists_le_coatom M).resolve_left hM
  obtain ⟨A, hA, hAT, H, hH, hHM'⟩ :=
    hescape Ω hΩ hlarge M' hM' (hTM.trans hMM') (hNM.trans hMM')
  exact ⟨A, hA, hAT, H, hH, fun hHM => hHM' (hHM.trans hMM')⟩

/-- The small-actor branch is discharged by the top E2-member; only the
specified large-family geometry remains. -/
theorem isEGeneratedAt_of_component_and_large_escape (T : Sylow 2 G)
    (hcomponent : ∀ A : Subgroup G, IsElementaryAbelian 2 A →
      A ≤ (T : Subgroup G) → A ≠ ⊥ → ECaseComponent (T : Subgroup G) A ⊤)
    (hescape : LargeFamilyEscapeAt T) : IsEGeneratedAt 1 T := by
  classical
  intro Ω hΩ
  by_cases hsmall : ∃ A : Subgroup G, A ∈ Ω ∧ A ≤ (T : Subgroup G) ∧
      A ≠ ⊥ ∧ Group.rank A ≤ 1
  · obtain ⟨A, hA, hAT, hne, hr⟩ := hsmall
    have hm : IsEMemberAt 1 (T : Subgroup G) A ⊤ :=
      isEMemberAt_top_of_component_and_rank T A (hΩ.1 A hA) hAT
        (hcomponent A (hΩ.1 A hA) hAT hne) hr
    apply top_unique
    exact (show (⊤ : Subgroup G) ≤ eSubgroup 1 (T : Subgroup G) A from
      le_sSup hm).trans ((le_iSup
        (fun B : {B : Subgroup G // B ∈ Ω ∧ B ≤ (T : Subgroup G)} =>
          eSubgroup 1 (T : Subgroup G) B.1) ⟨A, hA, hAT⟩).trans le_sup_left)
  · by_contra hproper
    have hlarge : ∀ A ∈ Ω, A ≤ (T : Subgroup G) → A ≠ ⊥ →
        1 < Group.rank A := by
      intro A hA hAT hne
      exact Nat.lt_of_not_ge (fun hr => hsmall ⟨A, hA, hAT, hne, hr⟩)
    have hT : (T : Subgroup G) ≤
        eFamilySubgroup 1 (T : Subgroup G) Ω ⊔
          normalizer (weakClosure (T : Subgroup G) Ω : Set G) :=
      (Subgroup.le_normalizer.trans
        (normalizer_le_weakClosure_normalizer (T : Subgroup G) hΩ)).trans le_sup_right
    obtain ⟨A, hA, hAT, H, hH, hHM⟩ :=
      hescape Ω hΩ hlarge _ hT hproper le_sup_right
    apply hHM
    exact (show H ≤ eSubgroup 1 (T : Subgroup G) A from le_sSup hH).trans
      ((le_iSup
        (fun B : {B : Subgroup G // B ∈ Ω ∧ B ≤ (T : Subgroup G)} =>
          eSubgroup 1 (T : Subgroup G) B.1) ⟨A, hA, hAT⟩).trans le_sup_left)

/-- The local calculation must work for every Sylow subgroup, as required by
the public definition of E-generation. -/
theorem isEGenerated_of_component_and_large_escape
    (hcomponent : ∀ (T : Sylow 2 G) (A : Subgroup G), IsElementaryAbelian 2 A →
      A ≤ (T : Subgroup G) → A ≠ ⊥ → ECaseComponent (T : Subgroup G) A ⊤)
    (hescape : ∀ T : Sylow 2 G, LargeFamilyEscapeAt T) : IsEGenerated 1 G :=
  fun T => isEGeneratedAt_of_component_and_large_escape T (hcomponent T) (hescape T)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration
