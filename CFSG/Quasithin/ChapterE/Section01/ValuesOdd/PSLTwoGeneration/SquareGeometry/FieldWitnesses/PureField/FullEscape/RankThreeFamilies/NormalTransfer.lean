module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.EscapeTransport
public import BenderSuzuki.External.Hall.Basic
public import Theory.ElementaryAbelian.Quotient

/-!
# Lifting escaping E-members from a normal subgroup

Suppose a normal subgroup supplements the ambient Sylow subgroup and contains
all members of the original family in that Sylow. Restrict the family by the
literal subtype map, omitting only the identity subgroup. Its weak closure
maps exactly onto the original weak closure, so its normalizer lies in the
restriction of the proposed proper overgroup.

An escaping E-member in the normal subgroup therefore escapes the original
overgroup. If ambient tau equals the selected actor, E.1.8's embedding theorem
lifts the witness with its intrinsic E1/E2 quotients, ranks, residual and local
tau unchanged. Normality ensures the Sylow restriction is exactly the required
intersection. The empty-family case is included in the weak-closure equality.

`RankThreeFamilies.escape_of_innerModel_escape` applies this to the canonical
inner extension of the full quadratic semilinear group.
Source: Aschbacher--Smith, E.1.2, E.1.5 and E.1.8, printed pp.210--211.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankThreeFamilies

/-- Transfer through the actual normal inclusion, preserving the original
family and its weak-closure normalizer. The smaller-group escape theorem
remains an explicit input for its independent producer. -/
theorem escape_of_normal_subgroup {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (T : Sylow 2 G)
    (hgen : (T : Subgroup G) ⊔ N = ⊤)
    (hescape : ∀ Q : Sylow 2 N, LargeFamilyEscapeAt Q)
    (Ω : Set (Subgroup G)) (hΩ : IsElementaryFamily Ω)
    (hlarge : ∀ A ∈ Ω, A ≤ (T : Subgroup G) → A ≠ ⊥ → 1 < Group.rank A)
    (hinner : ∀ A ∈ Ω, A ≤ (T : Subgroup G) → A ≤ N)
    (htau : ∀ A ∈ Ω, A ≤ (T : Subgroup G) → A ≠ ⊥ → tau (T : Subgroup G) A = A)
    (M : Subgroup G) (hTM : (T : Subgroup G) ≤ M) (hM : M ≠ ⊤)
    (hNM : normalizer (weakClosure (T : Subgroup G) Ω : Set G) ≤ M) :
    ∃ A ∈ Ω, A ≤ (T : Subgroup G) ∧
      ∃ H, IsEMemberAt 1 (T : Subgroup G) A H ∧ ¬ H ≤ M := by
  let Q := BenderSuzuki.External.hallSylowSubgroupOfNormal T N
  have hQ : (Q : Subgroup N) = (T : Subgroup G).subgroupOf N :=
    BenderSuzuki.External.hallSylowSubgroupOfNormal_coe T N
  let ΩN : Set (Subgroup N) := {B | B.map N.subtype ∈ Ω ∧ B ≠ ⊥}
  have hΩN : IsElementaryFamily ΩN := by
    constructor
    · intro B hB
      let : IsElementaryAbelian 2 (B.map N.subtype) := hΩ.1 _ hB.1
      let e := (B.equivMapOfInjective N.subtype N.subtype_injective).symm
      exact IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective
    · intro g B hB
      have he : (B.map (MulAut.conj g).toMonoidHom).map N.subtype =
          (B.map N.subtype).map (MulAut.conj (g : G)).toMonoidHom := by
        rw [map_map, map_map]
        rfl
      refine ⟨?_, ?_⟩
      · rw [he]
        exact hΩ.2 g _ hB.1
      · intro h
        exact hB.2 ((map_eq_bot_iff_of_injective B (MulAut.conj g).injective).mp h)
  have hW : (weakClosure (Q : Subgroup N) ΩN).map N.subtype =
      weakClosure (T : Subgroup G) Ω := by
    rw [hQ]
    apply le_antisymm
    · apply map_le_iff_le_comap.mpr
      apply sSup_le
      rintro B ⟨hB, hBT⟩
      apply map_le_iff_le_comap.mp
      exact le_sSup ⟨hB.1, map_le_iff_le_comap.mpr hBT⟩
    · apply sSup_le
      rintro A ⟨hA, hAT⟩
      by_cases hbot : A = ⊥
      · exact hbot ▸ bot_le
      have hAN := hinner A hA hAT
      rw [← map_subgroupOf_eq_of_le hAN]
      apply map_mono
      apply le_sSup
      refine ⟨⟨?_, ?_⟩, comap_mono hAT⟩
      · rwa [map_subgroupOf_eq_of_le hAN]
      · intro h
        apply hbot
        rw [← map_subgroupOf_eq_of_le hAN, h, Subgroup.map_bot]
  have hMN : M.subgroupOf N ≠ ⊤ := by
    intro h
    have hNM' : N ≤ M := by
      intro x hx
      exact (show (⟨x, hx⟩ : N) ∈ M.subgroupOf N from h ▸ mem_top _)
    exact hM (top_unique (hgen ▸ sup_le hTM hNM'))
  have hQM : (Q : Subgroup N) ≤ M.subgroupOf N := by
    rw [hQ]
    exact comap_mono hTM
  have hWM : normalizer (weakClosure (Q : Subgroup N) ΩN : Set N) ≤ M.subgroupOf N := by
    apply map_le_iff_le_comap.mp
    exact (le_normalizer_map N.subtype).trans (hW ▸ hNM)
  have hlargeN : ∀ A ∈ ΩN, A ≤ (Q : Subgroup N) → A ≠ ⊥ → 1 < Group.rank A := by
    intro A hA hAT hAb
    have hATG : A.map N.subtype ≤ (T : Subgroup G) := by
      apply map_le_iff_le_comap.mpr
      change A ≤ (T : Subgroup G).subgroupOf N
      rwa [← hQ]
    have hAbG : A.map N.subtype ≠ ⊥ := by
      intro h
      exact hAb ((map_eq_bot_iff_of_injective A N.subtype_injective).mp h)
    have hr := hlarge _ hA.1 hATG hAbG
    rwa [← Group.rank_congr (A.equivMapOfInjective N.subtype N.subtype_injective)] at hr
  obtain ⟨A, hA, hAQ, H, hH, hHM⟩ :=
    hescape Q ΩN hΩN hlargeN (M.subgroupOf N) hQM hMN hWM
  have hAT : A.map N.subtype ≤ (T : Subgroup G) := by
    apply map_le_iff_le_comap.mpr
    change A ≤ (T : Subgroup G).subgroupOf N
    rwa [← hQ]
  have hAb : A.map N.subtype ≠ ⊥ := by
    intro h
    exact hA.2 ((map_eq_bot_iff_of_injective A N.subtype_injective).mp h)
  refine ⟨A.map N.subtype, hA.1, hAT, H.map N.subtype, ?_, ?_⟩
  · apply hH.map_of_comap N.subtype N.subtype_injective (T : Subgroup G) hQ.symm
    rw [htau _ hA.1 hAT hAb]
    exact map_mono hH.1.2.2.1
  · exact fun h => hHM (map_le_iff_le_comap.mp h)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankThreeFamilies
