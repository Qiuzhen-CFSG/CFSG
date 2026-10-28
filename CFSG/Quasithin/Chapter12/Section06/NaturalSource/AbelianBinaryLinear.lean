module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianBinaryFour
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree

/-!
# The binary linear rows in the original abelian component sieve

The literal quotient of KT by its two-core contains the normal image
K/O₂(K), supplemented by the image of the original Sylow subgroup.
For PSL₃(2), this image is the simple generalized Fitting subgroup, so
the proved binary E-generation theorem applies. For PSL₅(2),
a single compatible marking gives two generating flag overgroups.
The outer flag is solvable; the middle flag has its actual PSL₃(2)
quotient, including the graph extension. The PSL₄(2) case reuses the
previously proved exclusion from its two solvable flags. E-generation
lifts through each retained two-group kernel and the whole KT kernel.

The original nontrivial V makes KT even, so its generation parameter is
one. Source 12.6.29 then puts K in M, contradicting the escaping component.
All earlier geometry remains explicit; this proves these normal-component
exclusions, not the full 12.6.31 module or subgroup identifications.

Source: Aschbacher--Smith 12.6.31, printed p.836, using E.1.12--14,
printed p.214, and 12.6.29, printed p.835.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open ChapterE.ValuesEvenClassical.BinaryUpper

private theorem sqtk_two_quotient {X : Type*} [Group X] [Finite X]
    (hX : IsSQTK KnownSimple.IsKnownSimple X) (Q : Subgroup X) [Q.Normal]
    (hQ : IsPGroup 2 Q) : IsSQTK KnownSimple.IsKnownSimple (X ⧸ Q) := by
  refine ⟨?_, hX.isKGroup.quotient Q⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  rw [primeRank_quotient_eq_of_isTwoGroup p ho Q hQ]
  exact hX.stronglyQuasithin p hp ho

private theorem binary_middle_isEGenerated {X : Type*} [Group X] [Finite X]
    (hX : IsSQTK KnownSimple.IsKnownSimple X) (hm : HasBinaryMiddleSection X) :
    ChapterE.IsEGenerated 1 X := by
  obtain ⟨Q,hQ,hp,hs,⟨e⟩,P,hgen⟩ := hm
  let := hQ
  let := hs
  exact ChapterE.IsEGenerated.of_normal_two_subgroup Q hp
    (ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.isEGenerated_of_source
      (sqtk_two_quotient hX Q hp) e P (by decide) (by norm_num) hgen)

private theorem binary_normal_isEGenerated {X : Type*} [Group X] [Finite X]
    (hX : IsSQTK KnownSimple.IsKnownSimple X) (C : Subgroup X) [C.Normal]
    (P : Sylow 2 X) {d : ℕ} (hd : d = 3 ∨ d = 5)
    (e : C ≃* PSL d) (hgen : C ⊔ (P : Subgroup X) = ⊤)
    (hcore : pCore 2 X = ⊥) : ChapterE.IsEGenerated 1 X := by
  rcases hd with rfl | hd
  · let : IsSimpleGroup (PSL 3) := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
    let : Group.IsPerfect (PSL 3) := Atlas.psl_perfect 3 (by decide)
    let : IsSimpleGroup C := e.isSimpleGroup
    let : Group.IsPerfect C := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hf := (simple_two_quotient_structure C (Group.IsPerfect.not_isMulCommutative C)
      (isPGroup_quotient_of_sup_eq_top C P P.isPGroup' hgen) hcore).1
    let eg : generalizedFitting X ≃* PSL 3 := (MulEquiv.subgroupCongr hf).trans e
    let : IsSimpleGroup (generalizedFitting X) := eg.isSimpleGroup
    exact ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.isEGenerated_of_source
      hX eg P (by decide) (by norm_num) (by rwa [hf])
  · obtain ⟨e',_,ho,hm,hP,hg⟩ := exists_sylowAligned_structured_generating_flags (Or.inr hd) C P e hgen
    have hgeneration (Q : Subgroup X) (hQ : Q ∈ binaryFlagFamily C P e') :
        ChapterE.IsEGenerated 1 Q := by
      rcases hQ with rfl | hQ
      · let := ho
        exact ChapterE.isEGenerated_one_of_solvable
      · obtain rfl := hQ
        rcases hm with ⟨_,hs⟩ | ⟨_,hs⟩
        · let := hs
          exact ChapterE.isEGenerated_one_of_solvable
        · exact binary_middle_isEGenerated (hX.subgroup _) hs
    apply ChapterE.IsEGeneratedAt.isEGenerated (T := P)
    intro Ω hΩ
    apply top_unique
    change ⊤ ≤ ChapterE.ChiefOrbit.generationTarget 1 P Ω
    rw [←hg]
    exact sSup_le fun Q hQ => ChapterE.ChiefOrbit.overgroup_le_generationTarget P Q
      (hP Q hQ) hΩ (hgeneration Q hQ)

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

include hz hTV hTz hbound hTI hns in
/-- The escaping T-invariant subgroup has no intrinsic binary PSL quotient
of degree three, four or five. Every quotient kernel and the original H
are retained; no generation bound or model flag is assumed. -/
theorem SourceHypothesis.original_escaping_binaryLinear_impossible
    {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz) (hKH : K ≤ H)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) (hout : ¬ K ≤ M L)
    {d : ℕ} (hd : d = 3 ∨ d = 4 ∨ d = 5)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) d 2) : False := by
  classical
  by_cases hd4 : d = 4
  · subst d
    exact S.original_escaping_binaryFour_impossible D hZ z hz hTV hTz hbound hTI hns hTK hout hm
  have h35 : d = 3 ∨ d = 5 := by omega
  obtain ⟨F,hF,hfin,hcard,⟨e₀⟩⟩ := hm
  let := hF
  let := hfin
  let := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hcard)
  let e : (K ⧸ pCore 2 K) ≃* PSL d := e₀.trans (Atlas.fieldEquivPSL d eF)
  let J := K ⊔ (T : Subgroup G)
  let Ki := K.subgroupOf J
  let : Ki.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hTK)
  let q := QuotientGroup.mk' (pCore 2 J)
  let C := Ki.map q
  let : C.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let P := (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).mapSurjective
    (QuotientGroup.mk'_surjective (pCore 2 J))
  let eKi : Ki ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let eC : C ≃* PSL d := (coreQuotientEquivImage 2 Ki).symm.trans
    ((QuotientGroup.congr _ _ eKi (pCore_map_iso 2 eKi)).trans e)
  have hCP : C ⊔ (P : Subgroup (J ⧸ pCore 2 J)) = ⊤ := by
    change (K.subgroupOf J).map q ⊔ ((T : Subgroup G).subgroupOf J).map q = ⊤
    rw [←Subgroup.map_sup,←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
    exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hJH : J ≤ H := sup_le hKH (fun x hx => hH.1.2 (Or.inr hx))
  have hz2 : orderOf (z : G) = 2 := orderOf_eq_prime_iff.mpr
    ⟨elemPow_eq_one_of_isElementaryAbelian _ z.property,fun he => hz (Subtype.ext he)⟩
  have hGz : IsSQTK KnownSimple.IsKnownSimple (D.fullSetup hZ T z).Gz := by
    rw [(D.fullSetup hZ T z).Gz_eq]
    exact S.source.simpleQTKE.involution_centralizer_sqtk hz2
  have hs : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe (hJH.trans hH.2.1))).mp (hGz.subgroup _)
  have hg : ChapterE.IsEGenerated 1 J :=
    ChapterE.IsEGenerated.of_normal_two_subgroup (pCore 2 J) pCore_isPGroup
      (binary_normal_isEGenerated (sqtk_two_quotient hs _ pCore_isPGroup) C P h35 eC hCP
        (pCore_quotient_pCore_eq_bot 2))
  have hdV : 2 ∣ Nat.card V := (IsElementaryAbelian.isPGroup 2 V).card_eq_or_dvd.resolve_left
    (fun h => S.chosen.ne_bot (Subgroup.card_eq_one.mp h))
  have hdJ : 2 ∣ Nat.card J := hdV.trans
    (card_dvd_of_le (S.chosen.le_sylow.trans (le_sup_right : (T : Subgroup G) ≤ J)))
  have hn := ChapterE.ExceptionalValues.generationParameter_eq_one_of_upper
    (fun ho => ho.not_two_dvd_nat hdJ) hg
  exact hout (le_sup_left.trans (S.original_generation_one_overgroup_le D hZ z hz hTV hTz
    hbound hTI hns (show (T : Subgroup G) ≤ J from le_sup_right) hn))

end CFSG.Quasithin.Chapter12.Section06
