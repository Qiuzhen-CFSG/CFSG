module

public import GorensteinWalter.Classification
public import Theory.GroupTheory.CharacteristicTwoDihedralEightRecognition
public import Theory.GroupTheory.SylowCoprimeEquivalence
public import Theory.Alternating.SevenQuasisimpleExtension
public import Theory.SpecificGroups.AlternatingSeven.DihedralLocals.Nongeneration
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.MixedSixteen
public import CFSG.Quasithin.ChapterF.Section06.Elementary.Residual
public import Theory.GroupTheory.Amalgam.Reversal

/-!
# The marked local pair for the alternating-seven extension

Intersecting two characteristic-two vertices with the actual two-residual
would give two S4 subgroups containing one Sylow D8. Lemma F.6.6 makes their
join the entire residual, contradicting the explicit A7 nongeneration
calculation, which also applies through the central cover projection.
The remaining mixed case is the already recognized compatible amalgam:
C2 times S4 on one side and S3 times D8 on the other.

Source: Aschbacher--Smith F.6.18(9), printed p.310, using F.6.5(2)(v).
The component models are supplied by the actual split-sixteen source sieve.
-/

public section
open Subgroup Theory.GroupTheory Equiv
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G]

private theorem odd_alternating_seven_sylow
    (K : Type*) [Group K] [Finite K]
    (hZ : Odd (Nat.card (center K))) (e : K ⧸ center K ≃* alternatingGroup (Fin 7))
    (S : Sylow 2 K) : Nat.card S = 8 ∧ Nonempty (S ≃* DihedralGroup 4) := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  let U := AlternatingSeven.DihedralLocals.fixedSylow
  let a : S ≃* U := Sylow.equivOfSurjectiveCoprime f hf
    (by rw [hk]; exact hZ.coprime_two_left) S U
  have hU : Nat.card U = 8 := AlternatingSeven.DihedralLocals.fixedTwoGroup_card
  obtain ⟨m, _, ⟨b⟩⟩ := GorensteinWalter.hasDihedralSylowTwo_alternatingGroupSeven U
  have hm : m = 2 := by
    have hc := Nat.card_congr b.toEquiv
    rw [hU, DihedralGroup.nat_card] at hc
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    norm_num only [show 2 ^ 2 = 4 by decide]
    omega
  subst m
  exact ⟨(Nat.card_congr a.toEquiv).trans hU, ⟨a.trans b⟩⟩

/-- Two good vertices would restrict to two S4 subgroups generating the
actual odd central A7 cover, contrary to its fixed-Sylow nongeneration. -/
theorem not_both_characteristic_two_of_alternating_seven_residual
    {G₁ G₂ : Subgroup G} (h : IsGoldschmidtTriple G₁ G₂)
    (hFstar : pResidual 2 G = generalizedFitting G)
    (hq : IsQuasisimple (pResidual 2 G))
    (hT16 : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 16)
    (hZ : Odd (Nat.card (center (pResidual 2 G))))
    (e : pResidual 2 G ⧸ center (pResidual 2 G) ≃* alternatingGroup (Fin 7))
    (h₁ : generalizedFitting G₁ = pCore 2 G₁)
    (h₂ : generalizedFitting G₂ = pCore 2 G₂) : False := by
  let K := pResidual 2 G
  let : IsQuasisimple K := hq
  obtain ⟨T, hT⟩ := h.intersection_sylow
  have hcT : Nat.card T = 16 := by rw [← hT]; exact hT16
  have hKne := Theory.AlternatingSevenExtension.proper_of_sylow_sixteen T hcT K hZ e
  have hKi : K.index = 2 := by
    rw [← Theory.AlternatingSevenExtension.action_preimage K hFstar.symm e,
      index_comap_of_surjective _
        (Theory.AlternatingSevenExtension.action_surjective K hFstar.symm hKne e),
      alternatingGroup.index_eq_two]
  obtain ⟨S, hS⟩ := h.subnormal_intersection_sylow K (inferInstance : K.Normal).isSubnormal
  obtain ⟨hcS, ⟨eS⟩⟩ := odd_alternating_seven_sylow K hZ e S
  have hcross (A : Subgroup G) (hTA : G₁ ⊓ G₂ ≤ A) : ¬ A ≤ K := by
    intro hAK
    have hTK : G₁ ⊓ G₂ ≤ K := hTA.trans hAK
    have hh : Nat.card (G₁ ⊓ G₂ : Subgroup G) = Nat.card S := by
      rw [hS, Nat.card_congr (subgroupOfEquivOfLe hTK).toEquiv]
    omega
  have hS₁ : (S : Subgroup K) ≤ G₁.subgroupOf K := by rw [hS]; exact comap_mono inf_le_left
  have hS₂ : (S : Subgroup K) ≤ G₂.subgroupOf K := by rw [hS]; exact comap_mono inf_le_right
  obtain ⟨e₁⟩ := symmetric_four_intersection_of_characteristic_two K G₁ hKi h₁
    (by rw [h.local_card_eq_three_mul_intersection, hT16]) (hcross G₁ inf_le_left) S eS hS₁
  obtain ⟨e₂⟩ := symmetric_four_intersection_of_characteristic_two K G₂ hKi h₂
    (by rw [h.symm.local_card_eq_three_mul_intersection, inf_comm G₂ G₁, hT16])
    (hcross G₂ inf_le_right) S eS hS₂
  have hgen : G₁.subgroupOf K ⊔ G₂.subgroupOf K = ⊤ := by
    apply (map_injective (f := K.subtype) K.subtype_injective)
    rw [Subgroup.map_sup, subgroupOf_map_subtype, subgroupOf_map_subtype,
      ← MonoidHom.range_eq_map, range_subtype]
    apply le_antisymm (sup_le inf_le_right inf_le_right)
    apply h.twoResidual_eq_sup.le.trans
    apply sup_le
    · exact (le_inf (map_subtype_le _) (map_pResidual_le 2 G₁.subtype)).trans le_sup_left
    · exact (le_inf (map_subtype_le _) (map_pResidual_le 2 G₂.subtype)).trans le_sup_right
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker ≤ center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  exact AlternatingSeven.DihedralLocals.central_cover_symmetricFour_pair_not_generate
    f hf hk S (G₁.subgroupOf K) (G₂.subgroupOf K) hS₁ hS₂ e₁ e₂ hgen

open Theory.GroupTheory.RankTwoAmalgam

/-- The original row-nine pair is the compatible mixed-sixteen amalgam,
allowing only an interchange of its original vertices. -/
theorem alternating_seven_row_nine_amalgam
    {G₁ G₂ : Subgroup G} (h : IsGoldschmidtTriple G₁ G₂)
    (hcore : pCore 2 G = ⊥)
    (hFstar : pResidual 2 G = generalizedFitting G)
    (hq : IsQuasisimple (pResidual 2 G))
    (hT16 : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 16)
    (hZ : Odd (Nat.card (center (pResidual 2 G))))
    (eQ : pResidual 2 G ⧸ center (pResidual 2 G) ≃* alternatingGroup (Fin 7)) :
    let α := RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right
    Nonempty (RankTwoAmalgam.Iso α MixedSixteen.standard) ∨
      Nonempty (RankTwoAmalgam.Iso α.reverse MixedSixteen.standard) := by
  classical
  have hT' : Nat.card (G₂ ⊓ G₁ : Subgroup G) = 16 := by simpa only [inf_comm] using hT16
  by_cases h₁ : generalizedFitting G₁ = pCore 2 G₁
  · have h₂ : generalizedFitting G₂ ≠ pCore 2 G₂ := fun h₂ =>
      not_both_characteristic_two_of_alternating_seven_residual
        h hFstar hq hT16 hZ eQ h₁ h₂
    exact Or.inl (h.mixed_sixteen_case hcore h₁ h₂ hT16)
  · by_cases h₂ : generalizedFitting G₂ = pCore 2 G₂
    · obtain ⟨e⟩ := h.symm.mixed_sixteen_case hcore h₂ h₁ hT'
      let swap : RankTwoAmalgam.Iso
          (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right).reverse
          (RankTwoAmalgam.ofSubgroups G₂ (G₂ ⊓ G₁) G₁ inf_le_left inf_le_right) := {
        left := MulEquiv.refl _
        middle := MulEquiv.subgroupCongr (inf_comm G₁ G₂)
        right := MulEquiv.refl _
        left_commutes := fun _ => rfl
        right_commutes := fun _ => rfl }
      exact Or.inr ⟨swap.trans e⟩
    · have hsmall := h.intersection_card_of_neither_characteristic_two hcore h₁ h₂
      omega

open GLS3.Chapter5 GLS3.Chapter5.OddCentralCovers

/-- The actual component models discharge both central-quotient hypotheses
in the marked row-nine conclusion. -/
theorem source_alternating_seven_row_nine_amalgam
    {G₁ G₂ : Subgroup G} (h : IsGoldschmidtTriple G₁ G₂)
    (hcore : pCore 2 G = ⊥)
    (hFstar : pResidual 2 G = generalizedFitting G)
    (hq : IsQuasisimple (pResidual 2 G))
    (eT : (G₁ ⊓ G₂ : Subgroup G) ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (hm : Nonempty (pResidual 2 G ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (pResidual 2 G ≃* TripleSeven)) :
    let α := RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right
    Nonempty (RankTwoAmalgam.Iso α MixedSixteen.standard) ∨
      Nonempty (RankTwoAmalgam.Iso α.reverse MixedSixteen.standard) := by
  let K := pResidual 2 G
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have hcT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 16 := by
    rw [Nat.card_congr eT.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
    norm_num [Nat.card_eq_fintype_card]
  obtain ⟨f, hf⟩ : ∃ f : Covering K (alternatingGroup (Fin 7)), Odd (Nat.card (center K)) := by
    rcases hm with hm | hm
    · obtain ⟨j⟩ := hm
      refine ⟨Covering.ofMulEquiv j, ?_⟩
      rw [Nat.card_congr (centerCongr j).toEquiv, alternatingGroup.center_eq_bot (by simp)]
      simp
    · obtain ⟨j⟩ := hm
      refine ⟨tripleSevenCovering.comp (Covering.ofMulEquiv j), ?_⟩
      rw [Nat.card_congr (centerCongr j).toEquiv, tripleSeven_center_card]
      decide
  let e : K ⧸ center K ≃* alternatingGroup (Fin 7) :=
    (QuotientGroup.quotientMulEquivOfEq f.ker_eq_center_of_isSimple.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f.toMonoidHom f.surjective)
  exact alternating_seven_row_nine_amalgam h hcore hFstar hq hcT hf e

end CFSG.Quasithin.ChapterF.SourceAssembly
