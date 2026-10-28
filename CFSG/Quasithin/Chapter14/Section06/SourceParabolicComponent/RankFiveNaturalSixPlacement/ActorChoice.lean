module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.RankFiveNaturalSixPlacement.FixedCore
public import Theory.GroupTheory.CardFourAutomorphismStabilizer
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.RankFiveNaturalSixCrossing

/-!
# Choosing the centralizing conjugator in the rank-five branch

The action of T₀ on the original four-group fixes the central point, so its
image has order at most two. The suitable involution conclusions show that
Tᵤ has nontrivial image, hence the same image. Correcting any representative
of T₀/Tᵤ by an element of Tᵤ produces t centralizing the plane. The index-two
and normalizer identities give t²∈Tᵤ and t∈N(Tᵤ).

The actual block-conjugate consumer then applies this same t to the original
component and core, proving that its conjugate module escapes O₂(I).

Source: Aschbacher–Smith, original14.6.10(5), printed p.1030.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section08
namespace CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSixPlacement
variable {G : Type*} [Group G] [Finite G]

private theorem centralizer_escape_of_index_two (A B V Z : Subgroup G)
    (hAB : A ≤ B) (hi : A.relIndex B = 2)
    (hBV : B ≤ normalizer (V : Set G)) (hV : Nat.card V = 4)
    (hZV : Z ≤ V) (hZ : Nat.card Z = 2) (hBZ : B ≤ centralizer (Z : Set G))
    (hmove : ¬ A ≤ centralizer (V : Set G)) :
    ∃ t ∈ B, t ∈ centralizer (V : Set G) ∧ t ∉ A ∧ t ^ 2 ∈ A := by
  let f := setupSeedAction B V hBV
  obtain ⟨z,hzne,_⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZ
  let zV : V := ⟨z,hZV z.property⟩
  have hzV : zV ≠ 1 := fun hh => hzne (Subtype.ext (congrArg (fun v : V => (v:G)) hh))
  have hbound : Nat.card f.range ≤ 2 :=
    card_mulAut_subgroup_le_two_of_fixed_point hV zV hzV f.range (by
      rintro g ⟨b,rfl⟩
      apply Subtype.ext
      change (b:G)*(z:G)*(b:G)⁻¹ = z
      rw [←hBZ b.property z z.property,mul_inv_cancel_right])
  let J := (A.subgroupOf B).map f
  have hJne : J ≠ ⊥ := by
    intro hz
    apply hmove
    intro a ha
    have hf : f ⟨a,hAB ha⟩ = 1 := by
      exact show f ⟨a,hAB ha⟩ ∈ (⊥ : Subgroup (MulAut V)) from
        hz ▸ mem_map_of_mem f ha
    exact (setupSeedAction_ker B V hBV).le hf
  have hcard := J.one_lt_card_iff_ne_bot.mpr hJne
  have he : J = f.range := eq_of_le_of_card_ge (map_le_range _ _) (by omega)
  have hout : ¬ B ≤ A := by
    intro hle
    have hh := relIndex_eq_one.mpr hle
    omega
  obtain ⟨b,hb,hbA⟩ := SetLike.not_le_iff_exists.mp hout
  obtain ⟨a,ha,hea⟩ := (show f ⟨b,hb⟩ ∈ J from he ▸ ⟨⟨b,hb⟩,rfl⟩)
  let t : G := b * (a:G)⁻¹
  have htB : t ∈ B := B.mul_mem hb (B.inv_mem a.property)
  have htC : t ∈ centralizer (V : Set G) := by
    change (⟨t,htB⟩ : B) ∈ (centralizer (V : Set G)).subgroupOf B
    apply (setupSeedAction_ker B V hBV).le
    change f (⟨b,hb⟩ * a⁻¹) = 1
    rw [map_mul,map_inv,hea,mul_inv_cancel]
  have htA : t ∉ A := by
    intro ht
    have hh := A.mul_mem ht ha
    change b * (a:G)⁻¹ * (a:G) ∈ A at hh
    rw [inv_mul_cancel_right] at hh
    exact hbA hh
  have hsq : t^2 ∈ A := by
    have hh := (A.subgroupOf B).mul_self_mem_of_index_two hi (⟨t,htB⟩ : B)
    change t*t ∈ A at hh
    simpa only [pow_two] using hh
  exact ⟨t,htB,htC,htA,hsq⟩

open Chapter12.Section08 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

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

omit hU3 hlocal in
/-- The original suitable-normalizer coset has a representative centralizing
the plane; its square lies in Tᵤ and it normalizes Tᵤ. -/
theorem source_plane_centralizing_element :
    let T0 := suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u
    let Tu := (T : Subgroup G) ⊓ centralizer ({u} : Set G)
    ∃ t ∈ T0, t ∈ centralizer (localModule T M : Set G) ∧ t ∉ Tu ∧
      t ^ 2 ∈ Tu ∧ t ∈ normalizer (Tu : Set G) := by
  let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  let T0 := suitableQuotientCentralizer h u
  let Tu := (T : Subgroup G) ⊓ centralizer ({u} : Set G)
  have hi := source_lemma_14_6_3_1 hG T hempty hM hunique hmany hcard e hab H hH
    u hu hindex hmove hproduct
  have hTu0 : Tu ≤ T0 := by
    change Tu ≤ suitableQuotientCentralizer h u
    rw [hi.2.2.2.1]
    exact le_sup_right
  have hn : T0 ≤ normalizer (localModule T M : Set G) :=
    inf_le_left.trans h.T_normalizes_V
  have hZV : centralInvolutions T ≤ localModule T M := h.point_lt.le
  have hTZ : T0 ≤ centralizer (centralInvolutions T : Set G) :=
    (inf_le_left.trans h.T_le_H).trans h.H_centralizes
  have hnon : ¬ Tu ≤ centralizer (localModule T M : Set G) := by
    intro hh
    apply (source_suitable_core_and_residual hG T hempty hM hunique hmany hcard e
      hab H hH u hu hindex hmove hproduct).1
    exact fun x hx => ⟨hx.1,hh ⟨h.QH_le_T hx.1,hx.2⟩⟩
  obtain ⟨t,ht,htV,htA,htsq⟩ := centralizer_escape_of_index_two Tu T0
    (localModule T M) (centralInvolutions T) hTu0 hi.1 hn hcard hZV h.point_card hTZ hnon
  refine ⟨t,ht,htV,htA,htsq,?_⟩
  have he : (T : Subgroup G) ⊓ normalizer (Tu : Set G) = T0 := hi.2.2.2.2
  exact (he ▸ ht).2

/-- The source choice above discharges the element premise of the actual
block-conjugate escape theorem. -/
theorem source_plane_centralizing_block_escape
    (I C : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hTI : (T : Subgroup G) ⊓ I = (T : Subgroup G) ⊓ centralizer ({u} : Set G))
    (hCI : C ≤ I) (hIC : I ≤ normalizer (C : Set G))
    (hgen : C ⊔ ((T : Subgroup G) ⊓ I) = I) (hC : ChapterC.IsShort C) :
    let T0 := suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u
    ∃ t ∈ T0, t ∈ centralizer (localModule T M : Set G) ∧ t ∉ I ∧
      t ^ 2 ∈ I ∧ t ∈ normalizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G) ∧
      ¬ ((ChapterC.blockU C).map C.subtype).map (MulAut.conj t).toMonoidHom ≤
        I.pCoreIn 2 := by
  obtain ⟨t,ht,htV,htA,htsq,htN⟩ := source_plane_centralizing_element hG T hempty hM hunique
    hmany hcard e hab H hH u hu hindex hmove hproduct
  have htT : t ∈ (T : Subgroup G) := ht.1
  have htI : t ∉ I := fun hh => htA (hTI ▸ ⟨htT,hh⟩)
  have htNI : t ∈ normalizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G) := hTI ▸ htN
  have hsq : t^2 ∈ I := (hTI ▸ htsq).2
  have hs := (source_suitable_intersection_sylow hG T hempty hM hunique hmany hcard e
    hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1).1
  refine ⟨t,ht,htV,htI,hsq,htNI,?_⟩
  exact source_parabolic_block_conjugate_escape T _ M Mc I C hI hCI hIC hs hgen hC
    t htT htI htNI (by simpa only [pow_two] using hsq)

end CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSixPlacement
