module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianNormalCubic
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianNormalBorel
public import Theory.GroupTheory.RankOneInnerSplitting
public import Theory.GroupTheory.QuotientIntersection
public import Theory.SpecificGroups.SL2.SylowNormalizerCard
/-!
# Splitting the original point residual in the normal PSL₂ branch

The proved inner action and cubic centralizer give the internal direct
product L₁-star=(L₁-star intersect K-star) times C_L₁-star(K-star).
The multiplication equivalence retains the actual inclusions. The
original E₉ then supplies a cubic divisor in the component intersection.

The Borel through T intersect K has star order 2^n(2^n-1). Its literal
quotient image contains the component intersection: the full O₂(H)
kernel lies in the original point core R₁, hence in T and M. Therefore
three divides 2^n-1, proving n even. No identification of O₂(L₁) with
L₁ intersect O₂(L) is made.

Source: Aschbacher--Smith 12.6.31, printed pp.835--836, refs/quasithin.pdf.
All earlier geometric inputs remain explicit. The field-size deduction
is supplied in AbelianNormalFour; the other Lie rows and the universal
natural reduction remain obligations of the source assembly.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
    (T : Subgroup G) = H)

include hz hTV hTz hH hKH hK hgen in
/-- The actual two factors multiply isomorphically onto the original L₁-star. -/
theorem SourceHypothesis.original_abelian_normal_linearTwo_split
    (hn : (K.subgroupOf H).Normal) {n : ℕ} (hn2 : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n)) :
    let A := actorImage H (D.fullSetup hZ T z).L₁
    let B := actorImage H K
    let C := A ⊓ centralizer (B : Set (H ⧸ pCore 2 H))
    A = (A ⊓ B) ⊔ C ∧
      ∃ e : (A ⊓ B : Subgroup (H ⧸ pCore 2 H)) × C ≃* A,
        ∀ b c, (e (b,c) : H ⧸ pCore 2 H) = (b : H ⧸ pCore 2 H) * c := by
  let E := D.fullSetup hZ T z
  let A := actorImage H E.L₁
  let B := actorImage H K
  let C := A ⊓ centralizer (B : Set (H ⧸ pCore 2 H))
  let q := QuotientGroup.mk' (pCore 2 H)
  let : B.Normal := hn.map q (QuotientGroup.mk'_surjective _)
  have hLH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  have hTA : actorImage H T ≤ normalizer (A : Set (H ⧸ pCore 2 H)) := by
    have ht : (T : Subgroup G) ≤ normalizer (E.L₁ : Set G) :=
      (le_inf hTH hTV).trans (S.original_module_normalizer_normalizes_residual D hZ z hTV hH)
    rintro _ ⟨x,hx,rfl⟩
    apply (E.L₁.subgroupOf H).le_normalizer_map q
    apply mem_map_of_mem
    rw [←subgroupOf_normalizer_eq hLH]
    exact ht hx
  have hstar : B ⊔ A ⊔ actorImage H T = ⊤ := by
    have hg := hgen
    rw [conjugateSpan_eq_of_normal H K T hKH hTH hn] at hg
    unfold B A actorImage
    rw [←Subgroup.map_sup,←Subgroup.map_sup,←subgroupOf_sup hKH hLH,
      ←subgroupOf_sup (sup_le hKH hLH) hTH,hg,subgroupOf_self,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  obtain ⟨_,_,_,d,_⟩ := S.original_point_star_core_quotient D hZ z hz hTz hH
  let : IsElementaryAbelian 3 (A ⧸ pCore 2 A) :=
    IsElementaryAbelian.of_injective d.toMonoidHom d.injective
  obtain ⟨F,hF,hfin,hcardF,⟨eK⟩⟩ := hm
  let := hF
  let := hfin
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcardF)
  let eB : B ≃* SL(2,F) := (componentStarEquiv H K hKH hK).symm.trans
    (eK.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm)
  have hzB : center B = ⊥ := by
    apply bot_unique
    intro x hx
    have he : eB x = 1 := mem_bot.mp
      (BenderSuzuki.Converse.center_SL2_eq_bot.le ((centerCongr eB) ⟨x,hx⟩).property)
    exact mem_bot.mpr (eB.map_eq_one_iff.mp he)
  have hr : primeRank 3 B = 1 := by
    rw [primeRank_equiv 3 eB]
    exact Matrix.SL2.binary_threeRank_eq_one (F := F)
  have hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n) := ⟨F,hF,hfin,hcardF,⟨eK⟩⟩
  have hs : A = (A ⊓ B) ⊔ C := split_inner_supplement_of_elementary_core_quotient A B (actorImage H T)
    (pCore_quotient_pCore_eq_bot 2) hzB hr (S.original_star_three_rank D hZ z hz hH)
    (S.original_abelian_normal_linearTwo_inner D hZ z hz hTz hH hn hKH hK hn2 hmodel)
    hTA hstar
    (S.original_abelian_normal_linearTwo_centralizer_ne_bot D hZ z hz hTz hH hn hKH hK hn2 hmodel)
  have hd : Disjoint (A ⊓ B) C := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    have hc : (⟨x,hx.1.2⟩ : B) ∈ center B := by
      rw [mem_center_iff]
      intro b
      exact Subtype.ext (hx.2.2 b b.property)
    exact mem_bot.mpr (congrArg (fun b : B => b.val)
      (show (⟨x,hx.1.2⟩ : B) = 1 from mem_bot.mp (hzB ▸ hc)))
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting (A ⊓ B) C hd
    (inf_le_right.trans (le_centralizer_iff.mp (show C ≤ centralizer (B : Set _) from inf_le_right)))
  exact ⟨hs,e.trans (MulEquiv.subgroupCongr hs.symm),he⟩

include hz hTV hTz hbound hTI hns hH hKH hK in
/-- The order of the Borel through the original T intersection K, in H/O₂(H). -/
theorem SourceHypothesis.original_abelian_normal_linearTwo_borel_star_card
    (hn : (K.subgroupOf H).Normal) (hout : ¬ K ≤ M L)
    {n : ℕ} (hn2 : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n)) :
    Nat.card (actorImage H (K ⊓ M L)) = 2^n * (2^n - 1) := by
  obtain ⟨P,_,_,hB⟩ := S.original_abelian_normal_linearTwo_borel_star
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hn hout hn2 hm
  let e : (K ⧸ pCore 2 K) ≃* actorImage H K := componentStarEquiv H K hKH hK
  let Pstar := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨F,hF,hfin,hcardF,⟨eK⟩⟩ := hm
  let := hF
  let := hfin
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcardF)
  let eB : actorImage H K ≃* SL(2,F) := e.symm.trans
    (eK.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm)
  have he : Nat.card (normalizer (Pstar : Set (actorImage H K))) =
      Nat.card (normalizer (Pstar.mapSurjective (f := eB.toMonoidHom) eB.surjective : Set SL(2,F))) := by
    change Nat.card (normalizer (Pstar : Set (actorImage H K))) =
      Nat.card (normalizer (((Pstar : Subgroup (actorImage H K)).map eB.toMonoidHom) : Set SL(2,F)))
    rw [←map_normalizer_eq_of_bijective (Pstar : Subgroup (actorImage H K)) (f := eB.toMonoidHom) eB.bijective,
      card_map_of_injective eB.injective]
    simp only [Sylow.coe_coe]
  rw [←hB,card_map_of_injective (actorImage H K).subtype_injective,he]
  simpa only [Sylow.coe_coe,hcardF] using
    Matrix.SpecialLinearGroup.card_sylow_normalizer_even
      (Pstar.mapSurjective (f := eB.toMonoidHom) eB.surjective)

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The split original E₉ forces a cubic in the component's marked Borel,
so the defining field exponent in the normal PSL₂ branch is even. -/
theorem SourceHypothesis.original_abelian_normal_linearTwo_even
    (hn : (K.subgroupOf H).Normal) (hout : ¬ K ≤ M L)
    {n : ℕ} (hn2 : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n)) : Even n := by
  let E := D.fullSetup hZ T z
  let A := actorImage H E.L₁
  let B := actorImage H K
  let C := A ⊓ centralizer (B : Set (H ⧸ pCore 2 H))
  obtain ⟨hs,e,he⟩ := S.original_abelian_normal_linearTwo_split
    D hZ z hz hTV hTz hH hKH hK hgen hn hn2 hm
  obtain ⟨_,_,hC⟩ := S.original_abelian_normal_linearTwo_centralizer_card
    D hZ z hz hTV hTz hH hKH hK hgen hn hn2 hm
  let P : Sylow 3 E.L₁ := Classical.choice inferInstance
  let P₀ := (P : Subgroup E.L₁).map E.L₁.subtype
  have hPA : actorImage H P₀ ≤ A := map_mono (comap_mono (map_subtype_le _))
  have h9 : 9 ∣ Nat.card A := by
    have hh := card_dvd_of_le hPA
    have hp := (S.original_point_sylow_star D hZ z hz hTz hH P).2.1
    change Nat.card (actorImage H P₀) = 9 at hp
    rwa [hp] at hh
  have h3 : 3 ∣ Nat.card (A ⊓ B : Subgroup (H ⧸ pCore 2 H)) := by
    rw [←Nat.card_congr e.toEquiv,Nat.card_prod,hC] at h9
    exact (mul_dvd_mul_iff_right (by decide : (3:ℕ) ≠ 0)).mp h9
  have hAM : A ≤ actorImage H (M L) := map_mono (comap_mono
    ((map_subtype_le _).trans (inf_le_left.trans L.le_normalizer)))
  have hkM : (QuotientGroup.mk' (pCore 2 H)).ker ≤ (M L).subgroupOf H := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact S.chosen.sylow_normalizes_component
      ((S.original_point_core_eq D hZ z hz hTz).2.2
        (S.original_core_le_point_core D hZ z hH (mem_map_of_mem H.subtype hx)))
  have him : actorImage H (K ⊓ M L) = B ⊓ actorImage H (M L) := by
    change ((K ⊓ M L).comap H.subtype).map (QuotientGroup.mk' (pCore 2 H)) =
      (K.comap H.subtype).map (QuotientGroup.mk' (pCore 2 H)) ⊓
        ((M L).comap H.subtype).map (QuotientGroup.mk' (pCore 2 H))
    rw [comap_inf]
    exact map_inf_of_ker_le _ _ _ hkM
  have hAB : A ⊓ B ≤ actorImage H (K ⊓ M L) := by
    rw [him]
    exact le_inf inf_le_right (inf_le_left.trans hAM)
  have hdiv := h3.trans (card_dvd_of_le hAB)
  rw [S.original_abelian_normal_linearTwo_borel_star_card
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hn hout hn2 hm] at hdiv
  have hodd : ¬ 3 ∣ 2^n := fun h =>
    (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
  exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mp
    ((Nat.prime_three.dvd_mul.mp hdiv).resolve_left hodd)

end CFSG.Quasithin.Chapter12.Section06
