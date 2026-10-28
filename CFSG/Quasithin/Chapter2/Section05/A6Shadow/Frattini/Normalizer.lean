module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.Earlier
public import CFSG.Quasithin.Chapter2.Section01To03.Elementary

/-!
# Sylow normalizers of largest local pairs

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Lemma
2.5.10(2), printed p.557. Extend the base U to a Sylow subgroup of
N_G(O₂(L)). The beta overgroup theorem keeps that Sylow subgroup in beta;
characteristic two of the normalizer, supplied by 2.5.10(1), makes it a local
base. Global maximality of |U| forces equality. All cores are genuine pCore
images and all normalizers are ambient.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

/-- Source 2.5.10(2), using ambient normalizers of the actual local two-core. -/
@[expose] def SourceNormalizerCondition (d : EarlierSetup κ G) : Prop :=
  ∀ (U L : Subgroup G), (U, L) ∈ largestLocalPairs d.M d.H →
    ∃ P : Sylow 2 (normalizer (twoCore L : Set G)),
      (P : Subgroup (normalizer (twoCore L : Set G))).map
        (normalizer (twoCore L : Set G)).subtype = U

/-- The genuine maximality argument of 2.5.10(2). The sole additional source
input is 2.5.10(1), characteristic two of the indicated ambient normalizers. -/
theorem sourceNormalizerCondition_of_characteristic_two (d : EarlierSetup κ G)
    (hchar : ∀ (U L : Subgroup G), (U, L) ∈ localPairsIn (Chapter1.He G) d.M d.H →
      normalizer (twoCore L : Set G) ∈ Chapter1.He G) :
    SourceNormalizerCondition d := by
  intro U L hUL
  let N := normalizer (twoCore L : Set G)
  have hQL : twoCore L ≤ L := (map_le_range _ _).trans_eq L.range_subtype
  have hn : ((twoCore L).subgroupOf L).Normal := by
    have he : (twoCore L).subgroupOf L = pCore 2 L := by
      rw [twoCore, subgroupOf, comap_map_eq_self_of_injective L.subtype_injective]
    rw [he]
    infer_instance
  have hLN : L ≤ N := (normal_subgroupOf_iff_le_normalizer hQL).mp hn
  have hUN : U ≤ N := hUL.1.1.2.2.2.1.trans hLN
  have hNne : twoCore N ≠ ⊥ := by
    intro he
    have hQ : twoCore L ≤ twoCore N :=
      le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L) (twoCore L).le_normalizer le_rfl
    exact hUL.1.1.2.2.1 (bot_unique (he ▸ hQ))
  have hNM : ¬ N ≤ d.M := fun h => hUL.1.1.2.2.2.2 (hLN.trans h)
  obtain ⟨P, hUP, hPbeta⟩ := beta_exists_sylow hUL.1.1.1 hUN
  have hPair : ((P : Subgroup N).map N.subtype, N) ∈ localPairs (Chapter1.He G) d.M :=
    ⟨hPbeta, hchar U L hUL.1, hNne,
      (map_le_range _ _).trans_eq N.range_subtype, hNM⟩
  have hsize := hUL.2 _ ⟨N, hPair⟩
  exact ⟨P, (eq_of_le_of_card_ge hUP hsize).symm⟩

end CFSG.Quasithin.Chapter2.A6Shadow.Frattini
