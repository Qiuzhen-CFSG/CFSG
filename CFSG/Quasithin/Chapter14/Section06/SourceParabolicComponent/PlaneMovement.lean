module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.Input
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.Commutator.ConjugateSpan
/-!
# Movement of the original source plane

The two-residual of the first intersection acts nontrivially on the
four-group V. A proper nonzero commutator would have order two and would
be centralized, contradicting commutator idempotence. Thus [V,A] = V,
and the same seed identity generates the full I-span by its two-residual.

Source: Aschbacher--Smith, 14.6.10(5), printed p.1029, the assertion
U = [U,I₀] preceding the C.2.7 model comparison.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
variable {G : Type*} [Group G] [Finite G]

private theorem plane_commutator_eq (V A : Subgroup G)
    (hV : Nat.card V = 4) (hA : IsPPerfect 2 A)
    (hn : A ≤ normalizer (V : Set G))
    (hm : ¬ A ≤ centralizer (V : Set G)) : ⁅V,A⁆ = V := by
  let C := ⁅V,A⁆
  have hCV : C ≤ V := le_normalizer_iff_commutator_le_left.mp hn
  have hne : C ≠ ⊥ := by
    intro he
    apply hm
    rw [←commutator_eq_bot_iff_le_centralizer,commutator_comm]
    exact he
  have hd : Nat.card C ∣ 4 := hV ▸ card_dvd_of_le hCV
  have hp : 0 < Nat.card C := Nat.card_pos
  have hb : Nat.card C ≤ 4 := Nat.le_of_dvd (by decide) hd
  have hc : Nat.card C = 2 ∨ Nat.card C = 4 := by
    have h1 : Nat.card C ≠ 1 := fun hc => hne (card_eq_one.mp hc)
    interval_cases hh : Nat.card C <;> norm_num at *
  rcases hc with hc | hc
  · have hcent : A ≤ centralizer (C : Set G) :=
      (normalizer_commutator_ge_right V A).trans (normalizer_le_centralizer_of_card_two C hc)
    have he : ⁅C,A⁆ = ⊥ := by
      rw [commutator_comm,commutator_eq_bot_iff_le_centralizer]
      exact hcent
    have hpV : IsPGroup 2 V := (IsPGroup.iff_card).mpr ⟨2,by norm_num [hV]⟩
    exact (hne ((commutator_isPPerfect_idempotent A V hA hpV hn).symm.trans he)).elim
  · apply eq_of_le_of_card_ge hCV
    rw [hV,hc]

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G))
    (hlocal : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (H ⊓ centralizer ({u} : Set G)))

include hG hempty hM hunique hmany hcard e hab H hH hu hindex hmove hproduct hU3 hlocal


/-- The original first intersection residual generates the literal source plane by commutators. -/
theorem source_parabolic_plane_moved
    (I : Subgroup G)
    (hI : I ∈ outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)
    (hout : ¬ I ⊓ M ≤ Mc) :
    ⁅localModule T M, (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype⁆ = localModule T M := by
  let A := (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
    (sourceResidual M Mc ⊓ I).subtype
  have hcover := (source_lemma_14_6_6_3 hG T hempty hM hunique hmany hcard e hab
    H hH u hu hindex hmove hproduct I hI.2.1 hout).1
  obtain ⟨hSyl,_⟩ := source_suitable_intersection_sylow hG T hempty hM hunique
    hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI
  obtain ⟨_,_,_,ha⟩ := source_intersection_parabolic_data hG T hempty hM hunique
    hmany hcard e hab H hH u hu hindex hmove hproduct I hI.2.1 hSyl hcover
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hMc,_⟩ :=
    source_lemma_14_1_18 hG T hempty hM hunique hmany hcard e
  apply plane_commutator_eq _ A hcard (isPPerfect_embedded_pResidual 2 _)
    (((map_subtype_le _).trans inf_le_left).trans
      ((sourceResidual_le M Mc).trans (le_normalizer_conjugateSpanBy _ M)))
  intro hc
  apply ha
  exact (hc.trans (centralizer_le
    (show centralInvolutions T ≤ localModule T M from le_conjugateSpanBy _ _))).trans_eq hMc.symm

/-- The full original I-span is generated by its actual two-residual action. -/
theorem source_parabolic_global_span_moved
    (I : Subgroup G)
    (hI : I ∈ outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)
    (hout : ¬ I ⊓ M ≤ Mc) :
    conjugateSpanBy (localModule T M) I =
      ⁅conjugateSpanBy (localModule T M) I,(pResidual 2 I).map I.subtype⁆ := by
  apply conjugateSpanBy_eq_commutator_of_seed _ I ((pResidual 2 I).map I.subtype)
    ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype) (map_subtype_le _)
  · exact I.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image I (pResidual 2 I))
  · exact embedded_pResidual_mono 2 inf_le_right
  · exact (source_parabolic_plane_moved hG T hempty hM hunique hmany hcard e hab H hH
      u hu hindex hmove hproduct hU3 hlocal I hI hout).symm

end CFSG.Quasithin.Chapter14.Section06
