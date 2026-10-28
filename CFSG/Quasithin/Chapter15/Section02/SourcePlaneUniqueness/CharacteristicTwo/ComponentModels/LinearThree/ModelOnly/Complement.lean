module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.ModelOnly.Action
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.BinaryComplement

/-!
# A complementary cubic factor from the original quotient action

The actual K action on X/O2(X) preserves its marked parabolic and Sylow.
The native binary model makes this action inner. Its kernel supplies the
second cubic residual, normal in K and invariant under the original S;
its commutator with the full X lies in O2(X).

This generalizes the established complementary-factor argument to the
model-only Branch. No MS classification is needed. The original quotient
maps and both cores remain intact, and Source applies the resulting factor
to the canonical-seed normalizer contradiction.

Source: Aschbacher--Smith 15.2.23, printed p.1116.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section02
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree.ModelOnly
variable {G : Type*} [Group G]
private def quotientActor (X A : Subgroup G) (hn : A ≤ normalizer (X : Set G)) :
    A →* MulAut (X ⧸ pCore 2 X) :=
  (quotientAut (pCore 2 X)).comp (X.normalizerMonoidHom.comp (inclusion hn))

private theorem quotientActor_mk (X A : Subgroup G) (hn : A ≤ normalizer (X : Set G))
    (a : A) (x : X) :
    quotientActor X A hn a (QuotientGroup.mk' (pCore 2 X) x) =
      QuotientGroup.mk' (pCore 2 X) (X.normalizerMonoidHom (inclusion hn a) x) :=
  quotientAut_apply_mk _ _ _

private theorem quotientActor_inner (X A : Subgroup G) (hn : A ≤ normalizer (X : Set G))
    (a : A) (ha : (a : G) ∈ X) :
    quotientActor X A hn a = MulAut.conj (QuotientGroup.mk' (pCore 2 X) ⟨a,ha⟩) := by
  ext z
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) z
  rw [quotientActor_mk]
  change QuotientGroup.mk' (pCore 2 X) ((⟨a,ha⟩ : X) * x * (⟨a,ha⟩ : X)⁻¹) = _
  simp only [map_mul,map_inv,MulAut.conj_apply]

variable [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)


private theorem quotientActor_preserves (X A L : Subgroup G)
    (hn : A ≤ normalizer (X : Set G)) (hL : A ≤ normalizer (L : Set G))
    (a : A) :
    ((L.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
      (quotientActor X A hn a).toMonoidHom =
      (L.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)) := by
  apply eq_of_le_of_card_ge
  · rintro z ⟨q,⟨x,hx,rfl⟩,rfl⟩
    exact ⟨X.normalizerMonoidHom (inclusion hn a) x,
      (mem_normalizer_iff.mp (hL a.property) x).mp hx, (quotientActor_mk X A hn a x).symm⟩
  · exact (card_map_of_injective (quotientActor X A hn a).injective).symm.le

private theorem transported_preserves {D : Type*} [Group D]
    (e : (X ⧸ pCore 2 X) ≃* D) (A L : Subgroup G)
    (hn : A ≤ normalizer (X : Set G)) (hL : A ≤ normalizer (L : Set G))
    (a : A) :
    (((L.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map e.toMonoidHom).map
      ((MulAut.congr e) (quotientActor X A hn a)).toMonoidHom =
      ((L.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map e.toMonoidHom := by
  rw [map_map]
  have he : ((MulAut.congr e) (quotientActor X A hn a)).toMonoidHom.comp e.toMonoidHom =
      e.toMonoidHom.comp (quotientActor X A hn a).toMonoidHom := by ext z; simp
  rw [he,← map_map,quotientActor_preserves X A L hn hL]

/-- The actual K-action on X/O₂(X) is implemented inside the marked opposite
parabolic. The marking is the original H-intersection marking. -/
theorem Branch.binary_action_implemented
    {F : Type} [Field F] [Finite F] (b : Branch M I X 1 F)
    (hI : PlaneEscapes Mc ZS I) (hout : ¬ X ≤ Mc)
    (hn : I ≤ normalizer (X : Set G)) :
    let K := (pResidual 2 H).map H.subtype
    let L := (pResidual 2 (K ⊓ X : Subgroup G)).map (K ⊓ X).subtype
    ∃ (e : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.SL)
      (j : K →* Matrix.PSL3Two.lineParabolicSL),
      (((L.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map e.toMonoidHom =
        Matrix.PSL3Two.MarkedAutomorphisms.lineA) ∧
      (∀ (k : K) (x : X),
        e (QuotientGroup.mk' (pCore 2 X)
          (X.normalizerMonoidHom (⟨k,hn ((le_sup_left.trans
            (d.residual_sup_planeSylow_le hI)).trans inf_le_right k.property)⟩) x)) =
          (j k : Matrix.PSL3Two.SL) * e (QuotientGroup.mk' (pCore 2 X) x) * (j k : Matrix.PSL3Two.SL)⁻¹) := by
  classical
  let K := (pResidual 2 H).map H.subtype
  let L := (pResidual 2 (K ⊓ X : Subgroup G)).map (K ⊓ X).subtype
  have hKI : K ≤ I := (le_sup_left.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
  have hKX := hKI.trans hn
  have hKL : K ≤ normalizer (L : Set G) :=
    (le_sup_left.trans (d.residual_sup_planeSylow_le hI)).trans
      (b.binary_factor_normalized d hI hout hn)
  obtain ⟨e,_,_,hmark⟩ := b.binary_factor_marking d hI
  let a : K →* MulAut Matrix.PSL3Two.SL :=
    (MulAut.congr e).toMonoidHom.comp (quotientActor X K hKX)
  have hex (k : K) : ∃ g ∈ Matrix.PSL3Two.lineParabolicSL, a k = MulAut.conj g := by
    apply Matrix.PSL3Two.MarkedAutomorphisms.preserving_residual_is_conj _ (Or.inr rfl)
    rw [Matrix.PSL3Two.MarkedAutomorphisms.line_residual,← hmark]
    exact transported_preserves e K L hKX hKL k
  let j : K →* Matrix.PSL3Two.lineParabolicSL := {
    toFun k := ⟨Classical.choose (hex k),(Classical.choose_spec (hex k)).1⟩
    map_one' := by
      apply Subtype.ext
      apply Matrix.PSL3Two.MarkedAutomorphisms.conj_injective
      change MulAut.conj (Classical.choose (hex 1)) = MulAut.conj 1
      rw [← (Classical.choose_spec (hex 1)).2,map_one,map_one]
    map_mul' k l := by
      apply Subtype.ext
      apply Matrix.PSL3Two.MarkedAutomorphisms.conj_injective
      change MulAut.conj (Classical.choose (hex (k*l))) =
        MulAut.conj (Classical.choose (hex k) * Classical.choose (hex l))
      rw [← (Classical.choose_spec (hex (k*l))).2,map_mul,map_mul,
        ← (Classical.choose_spec (hex k)).2,← (Classical.choose_spec (hex l)).2] }
  refine ⟨e,j,hmark,?_⟩
  intro k x
  have he := DFunLike.congr_fun (Classical.choose_spec (hex k)).2
    (e (QuotientGroup.mk' (pCore 2 X) x))
  change e (quotientActor X K hKX k (e.symm (e (QuotientGroup.mk' (pCore 2 X) x)))) = _ at he
  rw [e.symm_apply_apply,quotientActor_mk] at he
  exact he


/-- A faithful binary marking realizes the actual residual action on the
opposite A₄. Its restriction to the literal K₁ is onto. -/
theorem Branch.binary_residual_action
    {F : Type} [Field F] [Finite F] (b : Branch M I X 1 F)
    (hI : PlaneEscapes Mc ZS I) (hout : ¬ X ≤ Mc)
    (hn : I ≤ normalizer (X : Set G)) :
    let K := (pResidual 2 H).map H.subtype
    let L := (pResidual 2 (K ⊓ X : Subgroup G)).map (K ⊓ X).subtype
    ∃ (e : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.SL)
      (j : K →* Matrix.PSL3Two.MarkedAutomorphisms.lineA),
      (L.subgroupOf K).map j = ⊤ ∧
      (∀ (k : K) (hk : (k : G) ∈ X),
        (j k : Matrix.PSL3Two.SL) = e (QuotientGroup.mk' (pCore 2 X) ⟨k,hk⟩)) ∧
      (∀ (k : K) (x : X),
        e (QuotientGroup.mk' (pCore 2 X)
          (X.normalizerMonoidHom (⟨k,hn ((le_sup_left.trans
            (d.residual_sup_planeSylow_le hI)).trans inf_le_right k.property)⟩) x)) =
          (j k : Matrix.PSL3Two.SL) * e (QuotientGroup.mk' (pCore 2 X) x) * (j k : Matrix.PSL3Two.SL)⁻¹) := by
  classical
  let K := (pResidual 2 H).map H.subtype
  let L := (pResidual 2 (K ⊓ X : Subgroup G)).map (K ⊓ X).subtype
  obtain ⟨e,j,hmark,heq⟩ := b.binary_action_implemented d hI hout hn
  have hp : IsPPerfect 2 j.range :=
    (isPPerfect_embedded_pResidual 2 H).of_surjective j.rangeRestrict j.rangeRestrict_surjective
  have hj (k : K) : (j k : Matrix.PSL3Two.SL) ∈ Matrix.PSL3Two.MarkedAutomorphisms.lineA := by
    rw [← Matrix.PSL3Two.MarkedAutomorphisms.line_residual]
    exact mem_map_of_mem Matrix.PSL3Two.lineParabolicSL.subtype
      (le_pResidual_of_isPPerfect j.range hp ⟨k,rfl⟩)
  let jA : K →* Matrix.PSL3Two.MarkedAutomorphisms.lineA := {
    toFun k := ⟨j k,hj k⟩
    map_one' := Subtype.ext (by simp)
    map_mul' k l := Subtype.ext (by simp) }
  have hinner (k : K) (hk : (k : G) ∈ X) :
      (jA k : Matrix.PSL3Two.SL) = e (QuotientGroup.mk' (pCore 2 X) ⟨k,hk⟩) := by
    apply Matrix.PSL3Two.MarkedAutomorphisms.conj_injective
    apply MulEquiv.ext
    intro z
    obtain ⟨w,rfl⟩ := e.surjective z
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) w
    change (j k : Matrix.PSL3Two.SL) * e (QuotientGroup.mk' (pCore 2 X) x) *
      (j k : Matrix.PSL3Two.SL)⁻¹ = _
    rw [← heq k x]
    change e (QuotientGroup.mk' (pCore 2 X) ((⟨k,hk⟩ : X) * x * (⟨k,hk⟩ : X)⁻¹)) = _
    simp only [map_mul,map_inv,MulAut.conj_apply]
  have hLK : L ≤ K := (map_subtype_le _).trans inf_le_left
  have hLX : L ≤ X := (map_subtype_le _).trans inf_le_right
  refine ⟨e,jA,top_unique ?_,hinner,heq⟩
  intro a _
  have ha : (a : Matrix.PSL3Two.SL) ∈
      ((L.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map e.toMonoidHom := by
    rw [hmark]
    exact a.property
  obtain ⟨q,⟨x,hx,rfl⟩,he⟩ := ha
  refine ⟨⟨x,hLK hx⟩,hx,Subtype.ext ?_⟩
  exact (hinner ⟨x,hLK hx⟩ (hLX hx)).trans he


private def coreNormalizerAction (X : Subgroup G) :
    normalizer (X : Set G) →* MulAut (X ⧸ pCore 2 X) :=
  (quotientAut (pCore 2 X)).comp X.normalizerMonoidHom

private def coreQuotientCentralizer (X : Subgroup G) : Subgroup G :=
  (coreNormalizerAction X).ker.map (normalizer (X : Set G)).subtype

omit [Finite G] in
private theorem coreQuotientCentralizer_normalized (X : Subgroup G) :
    normalizer (X : Set G) ≤ normalizer (coreQuotientCentralizer X : Set G) := by
  have hh := (coreNormalizerAction X).ker.le_normalizer_map (normalizer (X : Set G)).subtype
  rw [show normalizer ((coreNormalizerAction X).ker : Set (normalizer (X : Set G))) = ⊤ from
    normalizer_eq_top _,← MonoidHom.range_eq_map,range_subtype] at hh
  exact hh

omit [Finite G] in
private theorem coreQuotientCentralizer_mem (X : Subgroup G)
    (a : normalizer (X : Set G)) :
    (a : G) ∈ coreQuotientCentralizer X ↔ coreNormalizerAction X a = 1 :=
  mem_map_iff_mem (normalizer (X : Set G)).subtype_injective

omit [Finite G] in
private theorem coreQuotientCentralizer_commutator (X : Subgroup G) :
    ⁅X,coreQuotientCentralizer X⁆ ≤ X.pCoreIn 2 := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro a ha x hx
  obtain ⟨a,ha,rfl⟩ := ha
  have hfix := DFunLike.congr_fun ha (QuotientGroup.mk' (pCore 2 X) ⟨x,hx⟩)
  change quotientAut (pCore 2 X) (X.normalizerMonoidHom a)
    (QuotientGroup.mk' (pCore 2 X) ⟨x,hx⟩) = _ at hfix
  rw [quotientAut_apply_mk] at hfix
  have hm := QuotientGroup.eq_iff_div_mem.mp hfix
  simpa only [pCoreIn,div_eq_mul_inv,commutatorElement_def,map_mul,map_inv,
    Subgroup.subtype_apply,Subgroup.coe_mul,Subgroup.coe_inv,normalizerMonoidHom_apply_apply_coe] using mem_map_of_mem X.subtype hm



private theorem residual_core_quotient_card_of_nine
    (K L E : Subgroup G) (_hLK : L ≤ K) (hEK : E ≤ K)
    (hnE : K ≤ normalizer (E : Set G))
    (hpK : IsPPerfect 2 K) (hpE : IsPPerfect 2 E)
    (hK : Nat.card (K ⧸ pCore 2 K) = 9)
    (hL : Nat.card (L ⧸ pCore 2 L) = 3)
    (hgen : L ⊔ E = K) (hne : E ≠ K) :
    Nat.card (E ⧸ pCore 2 E) = 3 := by
  let E' := E.subgroupOf K
  let e := subgroupOfEquivOfLe hEK
  let : E'.Normal := normal_subgroupOf_of_le_normalizer hnE
  have heq : Nat.card (E' ⧸ pCore 2 E') = Nat.card (E ⧸ pCore 2 E) :=
    Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv
  have hi := (inferInstance : E'.Normal).isSubnormal.quotientCoreImageEquiv 2
  have hcard := (E'.map (QuotientGroup.mk' (pCore 2 K))).card_subgroup_dvd_card
  rw [← Nat.card_congr hi.toEquiv,heq,hK] at hcard
  obtain ⟨n,hn,hc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (show Nat.card (E ⧸ pCore 2 E) ∣ 3^2 from hcard)
  interval_cases n
  · have hE : E = ⊥ := card_eq_one.mp
      (card_eq_one_of_isPPerfect_of_core_quotient_card_one hpE hc)
    rw [hE,sup_bot_eq] at hgen
    rw [hgen,hK] at hL
    norm_num at hL
  · exact hc
  · exfalso
    apply hne
    have ht : E'.map (QuotientGroup.mk' (pCore 2 K)) = ⊤ := by
      apply eq_top_of_card_eq
      rw [← Nat.card_congr hi.toEquiv,heq,hK,hc]
      norm_num
    have htop : (⊤ : Subgroup K) ≤ E' := by
      apply isPPerfect_le_of_map_le_of_kernel_normalizes
        (QuotientGroup.mk' (pCore 2 K)) ⊤ E'
        (hpK.of_surjective (topEquiv : (⊤ : Subgroup K) ≃* K).symm.toMonoidHom
          (topEquiv : (⊤ : Subgroup K) ≃* K).symm.surjective)
      · rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
      · exact le_normalizer_of_normal
      · rw [ht]; exact le_top
    have hh := congrArg (map K.subtype) (top_unique htop)
    simpa only [E',map_subgroupOf_eq_of_le hEK,← MonoidHom.range_eq_map,range_subtype] using hh


private theorem complement_of_core_action_kernel
    (X K L S : Subgroup G)
    (hKX : K ≤ normalizer (X : Set G))
    (hKL : K ≤ normalizer (L : Set G))
    (hSK : S ≤ normalizer (K : Set G))
    (hSX : S ≤ normalizer (X : Set G))
    (hpK : IsPPerfect 2 K) (hpL : IsPPerfect 2 L) (hLK : L ≤ K)
    (hK : Nat.card (K ⧸ pCore 2 K) = 9)
    (hL : Nat.card (L ⧸ pCore 2 L) = 3)
    (hcover : L ⊔ (K ⊓ coreQuotientCentralizer X) = K)
    (hne : K ⊓ coreQuotientCentralizer X ≠ K) :
    ∃ E : Subgroup G, E ≤ K ∧ IsPPerfect 2 E ∧
      Nat.card (E ⧸ pCore 2 E) = 3 ∧ S ≤ normalizer (E : Set G) ∧
      K ≤ normalizer (E : Set G) ∧ L ⊔ E = K ∧ ⁅X,E⁆ ≤ X.pCoreIn 2 := by
  let N := K ⊓ coreQuotientCentralizer X
  let E := (pResidual 2 N).map N.subtype
  have hKN : K ≤ normalizer (N : Set G) :=
    (le_inf K.le_normalizer (hKX.trans (coreQuotientCentralizer_normalized X))).trans
      inf_normalizer_le_normalizer_inf
  have hSN : S ≤ normalizer (N : Set G) :=
    (le_inf hSK (hSX.trans (coreQuotientCentralizer_normalized X))).trans
      inf_normalizer_le_normalizer_inf
  have hEK : E ≤ K := (map_subtype_le _).trans inf_le_left
  have hKE : K ≤ normalizer (E : Set G) := hKN.trans
    (normalizer_le_normalizer_characteristic_image N (pResidual 2 N))
  have hpE : IsPPerfect 2 E := isPPerfect_embedded_pResidual 2 N
  have hgen : L ⊔ E = K := by
    let : (L.subgroupOf (L ⊔ N)).Normal :=
      normal_subgroupOf_of_le_normalizer (hcover.le.trans hKL)
    let : (N.subgroupOf (L ⊔ N)).Normal :=
      normal_subgroupOf_of_le_normalizer (hcover.le.trans hKN)
    have hh := embedded_pResidual_sup_of_relative_normal 2 L N
    rw [(pResidual_eq_top_iff 2 L).mpr hpL,← MonoidHom.range_eq_map,range_subtype,
      hcover,(pResidual_eq_top_iff 2 K).mpr hpK,← MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  refine ⟨E,hEK,hpE,residual_core_quotient_card_of_nine K L E hLK hEK hKE hpK hpE
    hK hL hgen ?_,hSN.trans (normalizer_le_normalizer_characteristic_image N (pResidual 2 N)),
    hKE,hgen,?_⟩
  · intro he
    apply hne
    exact le_antisymm inf_le_left (he.symm.le.trans (map_subtype_le (pResidual 2 N)))
  · exact (commutator_mono le_rfl ((map_subtype_le _).trans inf_le_right)).trans
      (coreQuotientCentralizer_commutator X)


include d in
/-- The actual binary component has an S-invariant complementary cubic
factor centralizing X modulo O₂(X). No commutator premise is assumed. -/
theorem Branch.binary_complementary_factor
    {F : Type} [Field F] [Finite F] (b : Branch M I X 1 F)
    (hI : PlaneEscapes Mc ZS I) (hout : ¬ X ≤ Mc)
    (hn : I ≤ normalizer (X : Set G)) :
    let K := (pResidual 2 H).map H.subtype
    let L := (pResidual 2 (K ⊓ X : Subgroup G)).map (K ⊓ X).subtype
    ∃ E : Subgroup G, E ≤ K ∧ IsPPerfect 2 E ∧
      Nat.card (E ⧸ pCore 2 E) = 3 ∧ planeSylow T ZS ≤ normalizer (E : Set G) ∧
      K ≤ normalizer (E : Set G) ∧ L ⊔ E = K ∧ ⁅X,E⁆ ≤ X.pCoreIn 2 := by
  let K := (pResidual 2 H).map H.subtype
  let L := (pResidual 2 (K ⊓ X : Subgroup G)).map (K ⊓ X).subtype
  have hKI : K ≤ I := (le_sup_left.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
  have hKX := hKI.trans hn
  have hKL : K ≤ normalizer (L : Set G) :=
    (le_sup_left.trans (d.residual_sup_planeSylow_le hI)).trans
      (b.binary_factor_normalized d hI hout hn)
  have hSK : planeSylow T ZS ≤ normalizer (K : Set G) :=
    (inf_le_left.trans d.geometry.outside.1.1.2).trans
      (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pResidual 2 H)))
  have hSX : planeSylow T ZS ≤ normalizer (X : Set G) :=
    ((le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right).trans hn
  obtain ⟨e,j,hfull,hinner,heq⟩ := b.binary_residual_action d hI hout hn
  have hker (k : K) : j k = 1 ↔ (k : G) ∈ coreQuotientCentralizer X := by
    rw [show (k : G) ∈ coreQuotientCentralizer X ↔
      coreNormalizerAction X ⟨k,hKX k.property⟩ = 1 from
      coreQuotientCentralizer_mem X ⟨k,hKX k.property⟩]
    constructor
    · intro hk
      apply MulEquiv.ext
      intro q
      obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) q
      apply e.injective
      change e (quotientAut (pCore 2 X) (X.normalizerMonoidHom ⟨k,hKX k.property⟩)
        (QuotientGroup.mk' (pCore 2 X) x)) = e (QuotientGroup.mk' (pCore 2 X) x)
      rw [quotientAut_apply_mk]
      have hh := heq k x
      rw [hk] at hh
      simpa only [Subgroup.coe_one,one_mul,inv_one,mul_one] using hh
    · intro hk
      apply Subtype.ext
      apply Matrix.PSL3Two.MarkedAutomorphisms.conj_injective
      apply MulEquiv.ext
      intro z
      obtain ⟨q,rfl⟩ := e.surjective z
      obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) q
      have hh := heq k x
      have hf := DFunLike.congr_fun hk (QuotientGroup.mk' (pCore 2 X) x)
      change quotientAut (pCore 2 X) (X.normalizerMonoidHom ⟨k,hKX k.property⟩)
        (QuotientGroup.mk' (pCore 2 X) x) = _ at hf
      rw [quotientAut_apply_mk] at hf
      rw [hf] at hh
      change (j k : Matrix.PSL3Two.SL) * e (QuotientGroup.mk' (pCore 2 X) x) *
        (j k : Matrix.PSL3Two.SL)⁻¹ = _
      simpa only [Subgroup.coe_one,map_one,MulAut.one_apply] using hh.symm
  have hkerG : j.ker.map K.subtype = K ⊓ coreQuotientCentralizer X := by
    ext x
    constructor
    · rintro ⟨k,hk,rfl⟩
      exact ⟨k.property,(hker k).mp hk⟩
    · intro hx
      exact ⟨⟨x,hx.1⟩,(hker ⟨x,hx.1⟩).mpr hx.2,rfl⟩
  have hLK : L ≤ K := (map_subtype_le _).trans inf_le_left
  have hcover : L ⊔ (K ⊓ coreQuotientCentralizer X) = K := by
    have hh := congrArg (comap j) hfull
    rw [comap_map_eq,comap_top] at hh
    have hm := congrArg (map K.subtype) hh
    rwa [Subgroup.map_sup,map_subgroupOf_eq_of_le hLK,hkerG,
      ← MonoidHom.range_eq_map,range_subtype] at hm
  have hne : K ⊓ coreQuotientCentralizer X ≠ K := by
    intro he
    have htop : j.ker = ⊤ := by
      apply map_injective K.subtype_injective
      rw [hkerG,he,← MonoidHom.range_eq_map,range_subtype]
    have hj : (L.subgroupOf K).map j = ⊥ :=
      (Subgroup.map_eq_bot_iff _).mpr (by rw [htop]; exact le_top)
    have hz : Nat.card Matrix.PSL3Two.MarkedAutomorphisms.lineA = 1 := by
      rw [hfull] at hj
      simpa only [card_top,card_bot] using congrArg (fun A : Subgroup Matrix.PSL3Two.MarkedAutomorphisms.lineA => Nat.card A) hj
    have hc : Nat.card Matrix.PSL3Two.MarkedAutomorphisms.lineA = 12 := by
      rw [← Matrix.PSL3Two.MarkedAutomorphisms.line_residual]
      exact Matrix.PSL3Two.MarkedAutomorphisms.card_line_residual
    omega
  have hKcard : Nat.card (K ⧸ pCore 2 K) = 9 := by
    obtain ⟨eH⟩ := d.geometry.quotient
    let ew := RegularWreathProduct.congr SLTwoPermThree.sl2Two_equiv_perm_three.some.symm
      (MulEquiv.refl (Multiplicative (ZMod 2)))
    obtain ⟨er⟩ := WreathTwoResidual.residual_core_quotient_equiv_elementaryNine (eH.trans ew)
    let ek : pResidual 2 H ≃* K :=
      (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
    rw [← Nat.card_congr (QuotientGroup.congr _ _ ek (pCore_map_iso 2 ek)).toEquiv,
      Nat.card_congr er.toEquiv]
    simp [Nat.card_eq_fintype_card]
  exact complement_of_core_action_kernel X K L (planeSylow T ZS) hKX hKL hSK hSX
    (isPPerfect_embedded_pResidual 2 H) (isPPerfect_embedded_pResidual 2 (K ⊓ X)) hLK
    hKcard (b.binary_factor_core_quotient_card d hI) hcover hne


end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree.ModelOnly
