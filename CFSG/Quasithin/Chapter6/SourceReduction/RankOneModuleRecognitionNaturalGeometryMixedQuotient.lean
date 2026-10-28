module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryUnitaryExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.LocalStructure
public import Theory.GroupTheory.NormalSymmetricThreeExtension
public import Theory.GroupTheory.SpecificGroups.KleinFourFullAction
public import Theory.GroupTheory.PCoreProduct

/-!
# The marked right quotient of the natural mixed amalgam

Let J be the actual right parabolic of the escaping A5/S3 source pair.
The specified B/O2(B) marking extends to an S3-valued action on J because
all automorphisms of S3 are inner. Pair it with the actual conjugation
action on Z_S, whose image contains the original fixed-free cubic.
Since B centralizes Z_S, these actions jointly map onto their direct product.
The source parabolic order proves that their joint kernel is exactly O2(J).

Thus J/O2(J) is S3 times C3 or S3, with a quotient equation on every original
representative. Its core has index two or four in the original Sylow group.
The final application keeps the same escaping subgroup and full source overlap,
as well as the previously proved exclusions of both binary unitary models.

These are local structure results. Recognition of the whole mixed amalgam,
the contained S5 parabolic escape, initial 6.1.4–5 and the remaining geometry
through unconditional 6.1.27 remain with
qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith 6.1.19, printed p.675, and F.1.12(I),
printed pp.262–264 (`refs/quasithin.pdf`).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalMixedQuotient
local notation "S3" => Equiv.Perm (Fin 3)

private theorem three_conj_bijective : Function.Bijective (MulAut.conj : S3 →* MulAut S3) := by
  constructor
  · apply MulAut.conj_injective_of_center_eq_bot
    apply bot_unique
    intro x hx
    exact NormalSymmetricThreePairRank.symmetricThree_center_trivial x (mem_center_iff.mp hx)
  · intro a
    obtain ⟨x,hx⟩ := NormalSymmetricThreePairRank.symmetricThree_aut_inner a
    exact ⟨x,hx.symm⟩

private theorem three_core : pCore 2 S3 = ⊥ := by
  have hh := ker_eq_twoCore_of_surjective_perm_three (MonoidHom.id S3) Function.surjective_id
    (IsPGroup.ker_isPGroup_of_injective Function.injective_id)
  exact hh.symm.trans MonoidHom.ker_id

private theorem three_range {H : Type*} [Group H] (b : H →* S3)
    (hthree : 3 ∣ Nat.card b.range) :
    (Nat.card b.range = 3 ∨ Nat.card b.range = 6) ∧ pCore 2 b.range = ⊥ := by
  have hd : Nat.card b.range ∣ 6 := by
    simpa only [Nat.card_perm,Nat.card_fin,show Nat.factorial 3=6 from rfl] using
      b.range.card_subgroup_dvd_card
  have hc : Nat.card b.range = 3 ∨ Nat.card b.range = 6 := by
    have hm := Nat.mem_divisors.mpr ⟨hd,(by decide : 6 ≠ 0)⟩
    rw [show Nat.divisors 6 = {1,2,3,6} by decide] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    omega
  refine ⟨hc,?_⟩
  rcases hc with hc | hc
  · have hp : IsPGroup 3 b.range := IsPGroup.of_card (n := 1) (by simpa using hc)
    have hh := (pCore_isPGroup (p := 2) (G := b.range)).disjoint_of_coprime
      (hp.to_subgroup ⊤) (by decide : Nat.Coprime 2 3)
    simpa only [disjoint_top] using hh
  · have he : b.range = ⊤ := b.range.eq_top_of_card_eq (hc.trans (by
      rw [Nat.card_perm,Nat.card_fin]; rfl))
    let e := (MulEquiv.subgroupCongr he).trans topEquiv
    apply (Subgroup.map_injective (f := e.toMonoidHom) e.injective)
    rw [pCore_map_iso,three_core,Subgroup.map_bot]

private theorem product_surjective {H : Type*} [Group H]
    (a b : H →* S3) (N : Subgroup H)
    (ha : Function.Surjective (a.comp N.subtype)) (hb : N ≤ b.ker) :
    Function.Surjective (a.prod b.rangeRestrict) := by
  rintro ⟨x,y⟩
  obtain ⟨g,hg⟩ := b.rangeRestrict_surjective y
  obtain ⟨n,hn⟩ := ha (x*(a g)⁻¹)
  refine ⟨(n : H)*g,Prod.ext ?_ ?_⟩
  · change a ((n : H)*g)=x
    rw [map_mul,show a n=x*(a g)⁻¹ from hn,inv_mul_cancel_right]
  · apply Subtype.ext
    change b ((n : H)*g) = y.val
    rw [map_mul,show b n=1 from hb n.property,one_mul]
    exact congrArg Subtype.val hg

private theorem product_kernel {H U : Type*} [Group H] [Finite H] [Group U] [Finite U]
    (hp : IsPGroup 2 U) (hcard : Nat.card H=9*Nat.card U)
    (a b : H →* S3) (N : Subgroup H)
    (ha : Function.Surjective (a.comp N.subtype)) (hb : N ≤ b.ker)
    (hthree : 3 ∣ Nat.card b.range) :
    (a.prod b.rangeRestrict).ker = pCore 2 H := by
  let f := a.prod b.rangeRestrict
  have hf := product_surjective a b N ha hb
  obtain ⟨hc,hcore⟩ := three_range b hthree
  have he := f.ker.card_mul_index
  rw [index_ker,f.range_eq_top_of_surjective hf,card_top,Nat.card_prod,
    Nat.card_perm,Nat.card_fin,hcard] at he
  change Nat.card f.ker * (6 * Nat.card b.range) = 9 * Nat.card U at he
  have hd : Nat.card f.ker ∣ Nat.card U := by
    rcases hc with hc | hc
    · rw [hc] at he
      exact ⟨2,by omega⟩
    · rw [hc] at he
      exact ⟨4,by omega⟩
  obtain ⟨j,hj⟩ := hp.exists_card_eq
  have hk : IsPGroup 2 f.ker := IsPGroup.of_card_dvd_pow (hj ▸ hd)
  have ht : pCore 2 (S3 × b.range)=⊥ := by rw [pCore_prod,three_core,hcore,bot_prod_bot]
  have hh := f.comap_pCore_of_ker_isPGroup hf hk
  rwa [ht,MonoidHom.comap_bot] at hh

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalMixedQuotient

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalMixedQuotient
local notation "S3" => Equiv.Perm (Fin 3)
private theorem normal_section_action {G : Type*} [Group G]
    (B J : Subgroup G) (hBJ : B ≤ J) (hJB : J ≤ normalizer (B : Set G))
    (e : (B ⧸ pCore 2 B) ≃* S3) :
    ∃ a : J →* S3, ∀ b : B,
      a (inclusion hBJ b)=e (QuotientGroup.mk' (pCore 2 B) b) := by
  let u := MulEquiv.ofBijective (MulAut.conj : S3 →* MulAut S3) three_conj_bijective
  let r := B.normalizerMonoidHom.comp (inclusion hJB)
  let a := u.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp
    ((pCore 2 B).quotientAut.comp r))
  refine ⟨a,?_⟩
  intro b
  apply u.injective
  change u (u.symm _) = u _
  rw [u.apply_symm_apply]
  have hr : r (inclusion hBJ b)=MulAut.conj b := by ext x; rfl
  change (MulAut.congr e) ((pCore 2 B).quotientAut (r (inclusion hBJ b))) = _
  rw [hr]
  apply MulEquiv.ext
  intro x
  obtain ⟨y,rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 B))) x
  change e (((pCore 2 B).quotientAut (MulAut.conj b))
    (e.symm (e (QuotientGroup.mk' (pCore 2 B) y)))) =
      e (QuotientGroup.mk' (pCore 2 B) b) * e (QuotientGroup.mk' (pCore 2 B) y) *
        (e (QuotientGroup.mk' (pCore 2 B) b))⁻¹
  rw [e.symm_apply_apply,quotientAut_apply_mk]
  change e (QuotientGroup.mk' (pCore 2 B) (b*y*b⁻¹)) = _
  rw [map_mul,map_mul,map_inv,map_mul,map_mul,map_inv]
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalMixedQuotient

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R B : Subgroup G}
local notation "S3" => Equiv.Perm (Fin 3)

/-- The actual two actions on the right parabolic, with the original
S3 quotient marking, exact joint two-core kernel and quotient equation. -/
@[expose] def NaturalCubicRightQuotientData
    (T : Sylow 2 G) (L R B : Subgroup G)
    (e : (B ⧸ pCore 2 B) ≃* S3) : Prop :=
    let J := ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1
    let Z := ZS (T : Subgroup G) L R
    ∃ (hBJ : B ≤ J) (hJN : J ≤ normalizer (Z : Set G))
      (a : J →* S3) (eZ : MulAut Z ≃* S3),
      let b := eZ.toMonoidHom.comp (Z.normalizerMonoidHom.comp (inclusion hJN))
      Function.Surjective (a.prod b.rangeRestrict) ∧
      (a.prod b.rangeRestrict).ker = pCore 2 J ∧
      (∀ x : B, a (inclusion hBJ x)=e (QuotientGroup.mk' (pCore 2 B) x)) ∧
      (Nat.card b.range=3 ∨ Nat.card b.range=6) ∧
      ∃ d : (J ⧸ pCore 2 J) ≃* S3 × b.range,
        ∀ x : J, d (QuotientGroup.mk' (pCore 2 J) x)=(a x,b.rangeRestrict x)

/-- Extend the original cubic quotient marking and pair it with the actual
Z_S action. The resulting quotient map has precisely the full two-core as
kernel and satisfies the displayed equation on every representative. -/
theorem natural_cubic_amalgam_right_quotient
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (hF : ChapterF.Source.HypothesisF11 ![L,B] (T : Subgroup G))
    (e : (B ⧸ pCore 2 B) ≃* S3)
    (hBI : B ≤ Escape.I (T : Subgroup G) L R) :
    NaturalCubicRightQuotientData T L R B e := by
  let J := ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1
  let Z := ZS (T : Subgroup G) L R
  obtain ⟨c,hcL,hcTL,hcN,hc3,hcf⟩ := natural_four_exists_cubic h hnat
  have hJE := (natural_cubic_amalgam_overlap h hnat hF e hcL hcTL hc3).2.1
  change J = B ⊔ (zpowers c ⊔ (T : Subgroup G)) at hJE
  have hBJ : B ≤ J := by rw [hJE]; exact le_sup_left
  have hcJ : c ∈ J := by rw [hJE]; exact mem_sup_right (mem_sup_left (mem_zpowers c))
  have hJN : J ≤ normalizer (Z : Set G) := by
    rw [hJE]
    exact sup_le (hBI.trans (Subgroup.centralizer_le_normalizer _))
      (sup_le (zpowers_le.mpr hcN) h.sylow_normalizes_ZS)
  have hJB : J ≤ normalizer (B : Set G) := by
    dsimp only [J]
    rw [ChapterF.Source.parabolic_eq_sup_commonBorel]
    exact sup_le B.le_normalizer (hF.commonBorel_normalizes_local 1)
  obtain ⟨a,ha⟩ := NaturalMixedQuotient.normal_section_action B J hBJ hJB e
  have hZcard : Nat.card Z=4 := by
    exact (hnat.sylow_intersection_geometry T h.sylow_normalizes_L).1
  let := h.layer_elementary
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.of_le (show Z ≤ layer L R from inf_le_left)
  let : Nontrivial Z := by
    obtain ⟨z,hz⟩ := ne_bot_iff_exists_ne_one.mp h.ZS_ne_bot
    exact ⟨⟨z,1,hz⟩⟩
  let : IsKleinFour Z := ⟨hZcard,IsElementaryAbelian.exponent_eq_prime⟩
  let eZ := IsKleinFour.autEquivPermThree Z
  let b := eZ.toMonoidHom.comp (Z.normalizerMonoidHom.comp (inclusion hJN))
  have hBk : B.subgroupOf J ≤ b.ker := by
    intro x hx
    change eZ _ = 1
    rw [← eZ.map_one]
    apply congrArg eZ
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    change (x : G)*(z : G)*(x : G)⁻¹=z
    exact mul_inv_eq_iff_eq_mul.mpr ((hBI hx) z z.property).symm
  have haB : Function.Surjective (a.comp (B.subgroupOf J).subtype) := by
    intro y
    obtain ⟨x,hx⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 B))) y
    exact ⟨⟨inclusion hBJ x,x.property⟩,(ha x).trans hx⟩
  have hb3 : orderOf (b ⟨c,hcJ⟩)=3 := by
    apply orderOf_eq_prime
    · rw [←map_pow]
      have hh : (⟨c,hcJ⟩ : J)^3=1 := Subtype.ext (hc3 ▸ pow_orderOf_eq_one c)
      rw [hh,map_one]
    · intro he
      have he' : Z.normalizerMonoidHom (inclusion hJN (⟨c,hcJ⟩ : J))=1 :=
        eZ.injective (he.trans eZ.map_one.symm)
      obtain ⟨z,hz⟩ := ne_bot_iff_exists_ne_one.mp h.ZS_ne_bot
      apply hz
      apply Subtype.ext
      apply hcf z z.property
      exact congrArg Subtype.val (DFunLike.congr_fun he' z)
  have hthree : 3 ∣ Nat.card b.range := by
    have hh := orderOf_dvd_natCard (b.rangeRestrict ⟨c,hcJ⟩)
    rw [← orderOf_coe] at hh
    change orderOf (b ⟨c,hcJ⟩) ∣ Nat.card b.range at hh
    rwa [hb3] at hh
  have heL : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) := by
    obtain ⟨F,_,_,_,hF,eL,_⟩ := hnat
    exact ⟨eL.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL.trans
      (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some)⟩
  have hcard : Nat.card J=9*Nat.card T := (hF.mixed_local_orders heL.some e).2.2
  have hk := NaturalMixedQuotient.product_kernel T.isPGroup' hcard a b (B.subgroupOf J) haB hBk hthree
  have hs := NaturalMixedQuotient.product_surjective a b (B.subgroupOf J) haB hBk
  let d := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (a.prod b.rangeRestrict) hs)
  exact ⟨hBJ,hJN,a,eZ,hs,hk,ha,(NaturalMixedQuotient.three_range b hthree).1,d,fun _ => rfl⟩

/-- The two genuine right-vertex quotients, together with their exact
Sylow-to-core orders. No bound on the size of either original core is assumed. -/
theorem natural_cubic_amalgam_right_models_and_sizes
    (hnat : IsNaturalModule L (layer L R) 2)
    (hF : ChapterF.Source.HypothesisF11 ![L,B] (T : Subgroup G))
    (e : (B ⧸ pCore 2 B) ≃* S3)
    (hr : NaturalCubicRightQuotientData T L R B e) :
    let J := ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1
    (Nonempty ((J ⧸ pCore 2 J) ≃* S3 × alternatingGroup (Fin 3)) ∧
      Nat.card T = 2 * Nat.card (pCore 2 J)) ∨
    (Nonempty ((J ⧸ pCore 2 J) ≃* S3 × S3) ∧
      Nat.card T = 4 * Nat.card (pCore 2 J)) := by
  let J := ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1
  obtain ⟨hBJ,hJN,a,eZ,_,_,_,hc,d,_⟩ := hr
  let Z := ZS (T : Subgroup G) L R
  let b := eZ.toMonoidHom.comp (Z.normalizerMonoidHom.comp (inclusion hJN))
  change Nat.card b.range=3 ∨ Nat.card b.range=6 at hc
  have heL : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) := by
    obtain ⟨F,_,_,_,hF,eL,_⟩ := hnat
    exact ⟨eL.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL.trans
      (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some)⟩
  have hJ : Nat.card J=9*Nat.card T := (hF.mixed_local_orders heL.some e).2.2
  have hQ := (pCore 2 J).card_mul_index
  rw [index_eq_card,Nat.card_congr d.toEquiv,Nat.card_prod,Nat.card_perm,Nat.card_fin,hJ] at hQ
  change Nat.card (pCore 2 J) * (6 * Nat.card b.range) = 9 * Nat.card T at hQ
  rcases hc with hc | hc
  · have hA : b.range = alternatingGroup (Fin 3) := by
      apply eq_of_le_of_card_ge
      · intro x hx
        have hpow : (⟨x,hx⟩ : b.range)^3=1 := by
          simpa only [hc] using (pow_card_eq_one' (x := (⟨x,hx⟩ : b.range)))
        have cert : ∀ x : S3, x^3=1 → x.sign=1 := by decide +kernel
        exact Equiv.Perm.mem_alternatingGroup.mpr (cert x (congrArg Subtype.val hpow))
      · rw [hc,nat_card_alternatingGroup,Nat.card_fin]
        decide
    left
    refine ⟨⟨d.trans ((MulEquiv.refl S3).prodCongr (MulEquiv.subgroupCongr hA))⟩,?_⟩
    rw [hc] at hQ
    change Nat.card T = 2 * Nat.card (pCore 2 J)
    omega
  · have htop : b.range=⊤ := b.range.eq_top_of_card_eq (hc.trans (by
      rw [Nat.card_perm,Nat.card_fin]; rfl))
    right
    refine ⟨⟨d.trans ((MulEquiv.refl S3).prodCongr
      ((MulEquiv.subgroupCongr htop).trans topEquiv))⟩,?_⟩
    rw [hc] at hQ
    change Nat.card T = 4 * Nat.card (pCore 2 J)
    omega
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G]
/-- The same original escaping subgroup, source pair and faithful local
triple, with both unitary exclusions and the marked right-vertex quotient.
The two possible quotient models retain their exact Sylow-to-core orders. -/
@[expose] def NaturalEscapingAmalgamRightData (T : Sylow 2 G) (L R P N M : Subgroup G) : Prop :=
  ∃ B : Subgroup G, B ≤ P ⊔ N.pCoreIn 2 ∧
    B ≤ Escape.I (T : Subgroup G) L R ∧ (¬ B ≤ M) ∧
    Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) ∧
    ChapterF.Source.HypothesisF11 ![L,B] (T : Subgroup G) ∧
    Group.IsSolvable (ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1) ∧
    ChapterF.Source.LocallyRankOneTriple
      (fun i => (ChapterF.Source.parabolic ![L,B] (T : Subgroup G) i).subgroupOf
        (ChapterF.Source.generated ![L,B] (T : Subgroup G)))
      ((ChapterF.Source.commonBorel ![L,B] (T : Subgroup G)).subgroupOf
        (ChapterF.Source.generated ![L,B] (T : Subgroup G))) ∧ NaturalUnitaryAmalgamExclusion T L B ∧
    ∀ e : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3),
      NaturalCubicRightQuotientData T L R B e ∧
      let J := ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1
      (Nonempty ((J ⧸ pCore 2 J) ≃*
          Equiv.Perm (Fin 3) × alternatingGroup (Fin 3)) ∧
        Nat.card T = 2 * Nat.card (pCore 2 J)) ∨
      (Nonempty ((J ⧸ pCore 2 J) ≃*
          Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ∧
        Nat.card T = 4 * Nat.card (pCore 2 J))

variable [Finite G] {T : Sylow 2 G} {L M R P N : Subgroup G}
/-- Construct the right-vertex quotient on the same escaping subgroup;
retain its original inclusions, full overlap and both unitary exclusions. -/
theorem natural_escaping_amalgam_right_quotient
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (d : NaturalEscapingAmalgamUnitaryData T L R P N M) :
    NaturalEscapingAmalgamRightData T L R P N M := by
  obtain ⟨B,hBK,hBI,hBM,he,hF,hsolv,htriple,hno⟩ := d
  refine ⟨B,hBK,hBI,hBM,he,hF,hsolv,htriple,hno,fun e => ?_⟩
  have hr := natural_cubic_amalgam_right_quotient h hnat hF e hBI
  exact ⟨hr,natural_cubic_amalgam_right_models_and_sizes hnat hF e hr⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
