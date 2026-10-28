module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Swapped.CommonActor
public import Theory.GroupTheory.ComponentPairRankDescent

/-!
# Rank and displacement of a component-moving cubic actor

The stabilizer of a component in the elementary actor acts faithfully on it:
an element centralizing one component also centralizes its conjugate because
it commutes with the swapping actor. The index-two component normalizer and
the automorphism two-rank bound therefore give actor rank at most three.
The starred cubic condition bounds its fixed codimension by six, both on the
original module and on its full fixed quotient.

The final application retains the actual pure-point quotient, conjugation
action and source MS fixed-subgroup premise. The remaining exclusion uses
this same actor in `PrimeMovement` and `DiagonalExclusion`.
Source: Aschbacher--Smith D.3.5--9 and 12.1.4,
printed pp.195--201,790--791 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi

/-- The stabilizer inside an elementary actor moving a self-centralizing pair
acts faithfully on either component. -/
theorem moving_pair_stabilizer_faithful
    {Q : Type*} [Group Q] (C E : Subgroup Q) [IsMulCommutative E]
    {a : Q} (ha : a ∈ E)
    (hcent : centralizer ((C ⊔ C.map (MulAut.conj a).toMonoidHom : Subgroup Q) : Set Q) = ⊥) :
    Function.Injective (C.normalizerMonoidHom.comp
      (inclusion (show E ⊓ normalizer (C : Set Q) ≤ normalizer (C : Set Q) from inf_le_right))) := by
  let B := E ⊓ normalizer (C : Set Q)
  let f := C.normalizerMonoidHom.comp (inclusion (show B ≤ normalizer (C : Set Q) from inf_le_right))
  apply f.ker_eq_bot_iff.mp
  apply bot_unique
  intro b hb
  have hc : (b : Q) ∈ centralizer (C : Set Q) := by
    change inclusion (show B ≤ normalizer (C : Set Q) from inf_le_right) b ∈ C.normalizerMonoidHom.ker at hb
    rw [normalizerMonoidHom_ker] at hb
    exact hb
  have hba : Commute (b : Q) a := congrArg Subtype.val
    ((IsMulCommutative.is_comm (M := E)).comm (⟨b,b.property.1⟩ : E) ⟨a,ha⟩)
  have hc' : (b : Q) ∈ centralizer (C.map (MulAut.conj a).toMonoidHom : Set Q) := by
    rintro _ ⟨c,hcC,rfl⟩
    have hbc : Commute (b : Q) c := (hc c hcC).symm
    exact ((hba.mul_right hbc).mul_right hba.inv_right).eq.symm
  have hp : (b : Q) ∈ centralizer ((C ⊔ C.map (MulAut.conj a).toMonoidHom : Subgroup Q) : Set Q) := by
    have hh : C ⊔ C.map (MulAut.conj a).toMonoidHom ≤ centralizer ({(b : Q)} : Set Q) :=
      sup_le (fun c hcC => mem_centralizer_singleton_iff.mpr (hc c hcC))
        (fun c hcC => mem_centralizer_singleton_iff.mpr (hc' c hcC))
    exact fun c hcC => mem_centralizer_singleton_iff.mp (hh hcC)
  exact Subtype.ext (mem_bot.mp (hcent ▸ hp))

/-- A moving elementary actor over a component with automorphism two-rank
at most two has rank at most three. -/
theorem moving_pair_rank_le_three
    {Q : Type*} [Group Q] [Finite Q]
    (C E : Subgroup Q) (hE : IsElementaryTwo E)
    (hindex : (normalizer (C : Set Q)).index = 2)
    (hmove : ¬ E ≤ normalizer (C : Set Q))
    (hcent : ∀ a ∈ E, a ∉ normalizer (C : Set Q) →
      centralizer ((C ⊔ C.map (MulAut.conj a).toMonoidHom : Subgroup Q) : Set Q) = ⊥)
    (hr : primeRank 2 (MulAut C) ≤ 2) :
    rank E = rank (E ⊓ normalizer (C : Set Q)) + 1 ∧ rank E ≤ 3 := by
  obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp hmove
  let := hE.2
  let N := normalizer (C : Set Q)
  let B := E ⊓ N
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective
    (inclusion (show B ≤ E from inf_le_left)) (inclusion_injective _)
  let f := C.normalizerMonoidHom.comp (inclusion (show B ≤ N from inf_le_right))
  have hf : Function.Injective f := moving_pair_stabilizer_faithful C E ha (hcent a ha han)
  have hp : primeRank 2 B ≤ 2 := (Theory.GroupTheory.primeRank_le_of_injective 2 f hf).trans hr
  have hBcard : Nat.card B ≤ 4 := by
    let : IsElementaryAbelian 2 (⊤ : Subgroup B) := IsElementaryAbelian.of_injective (⊤ : Subgroup B).subtype (⊤ : Subgroup B).subtype_injective
    have hh := (primeRank_le_iff_elementary_card_le B).mp hp (⊤ : Subgroup B) inferInstance
    simpa only [Nat.card_congr (topEquiv : (⊤ : Subgroup B) ≃* B).toEquiv, show 2 ^ 2 = 4 from rfl] using hh
  have hi : B.relIndex E = 2 := by
    apply relIndex_eq_two_iff_exists_notMem_and'.mpr
    refine ⟨a,ha,fun hh => han hh.2,?_⟩
    intro b hb
    by_cases hn : b ∈ N
    · exact Or.inr ⟨hb,hn⟩
    · exact Or.inl ⟨E.mul_mem ha hb,(N.mul_mem_iff_of_index_two hindex).mpr
        (iff_of_false han hn)⟩
  have hc := (B.subgroupOf E).card_mul_index
  change Nat.card (B.subgroupOf E) * B.relIndex E = Nat.card E at hc
  rw [Nat.card_congr (subgroupOfEquivOfLe (show B ≤ E from inf_le_left)).toEquiv,hi] at hc
  have hBp : IsPGroup 2 B := IsElementaryAbelian.isPGroup 2 B
  obtain ⟨b,hb⟩ := hBp.exists_card_eq
  have he : rank E = rank B + 1 := by
    change Nat.log 2 (Nat.card E) = Nat.log 2 (Nat.card B) + 1
    rw [←hc,hb,←pow_succ,Nat.log_pow (by decide : 1 < 2),Nat.log_pow (by decide : 1 < 2)]
  refine ⟨he,?_⟩
  have hcE : Nat.card E ≤ 8 := by omega
  have hh := Nat.log_mono_right (b := 2) hcE
  exact hh

/-- A concrete moving actor on the original action and its full fixed quotient. -/
@[expose] def SmallMovingCubicActorPair
    {Q U : Type*} [Group Q] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) Q U) (C₁ C₂ : Subgroup Q) : Prop :=
    (normalizer (C₁ : Set Q)).index = 2 ∧
    ∃ E : Subgroup Q, E ∈ ChapterD.QhatStar ρ ∧
      rank E = rank (E ⊓ normalizer (C₁ : Set Q)) + 1 ∧ rank E ≤ 3 ∧
      fixedCodim ρ E ≤ 6 ∧ fixedCodim (fixedQuotient ρ ⊤) E ≤ 6 ∧
      ∃ a ∈ E, orderOf a = 2 ∧ a ∉ normalizer (C₁ : Set Q) ∧
        C₁.map (MulAut.conj a).toMonoidHom = C₂ ∧
        Function.Injective (C₁.normalizerMonoidHom.comp
          (inclusion (show E ⊓ normalizer (C₁ : Set Q) ≤ normalizer (C₁ : Set Q) from inf_le_right)))

/-- The common actor has rank at most three and moves at most six dimensions,
with the same actor retained on the quotient by the full fixed space. -/
theorem common_cubic_actor_small_mover
    {Q U K : Type*} [Group Q] [Finite Q] [Group K]
    [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) Q U) (C : Subgroup Q) (t : Q)
    (hne : C ≠ C.map (MulAut.conj t).toMonoidHom)
    [(C ⊔ C.map (MulAut.conj t).toMonoidHom).Normal]
    (hcent : centralizer ((C ⊔ C.map (MulAut.conj t).toMonoidHom : Subgroup Q) : Set Q) = ⊥)
    (hpair : CommonCubicActorPair ρ C (C.map (MulAut.conj t).toMonoidHom) K)
    (hr : primeRank 2 (MulAut K) ≤ 2) :
    SmallMovingCubicActorPair ρ C (C.map (MulAut.conj t).toMonoidHom) := by
  obtain ⟨E,hE,hmove,hCs⟩ := hpair
  have hC := hCs C (by simp)
  let : Finite K := Finite.of_equiv C hC.2.1.some.toEquiv
  let : (C ⊔ C.conjBy t).Normal := by
    change (C ⊔ C.map (MulAut.conj t).toMonoidHom).Normal
    infer_instance
  have hindex : (normalizer (C : Set Q)).index = 2 :=
    ComponentPairRankDescent.component_normalizer_index_two_of_normal_pair C hC.1 t hne
  let N := normalizer (C : Set Q)
  let : N.Normal := normal_of_index_eq_two hindex
  have hN : normalizer (C.map (MulAut.conj t).toMonoidHom : Set Q) = N := by
    rw [←C.map_normalizer_eq_of_bijective (MulAut.conj t).bijective]
    exact normal_iff_map_conj_eq.mp (inferInstance : N.Normal) t
  have hm : ¬ E ≤ N := by
    intro hh
    apply hmove
    exact le_inf hh (hN.symm ▸ hh)
  have hc : ∀ a ∈ E, a ∉ N →
      centralizer ((C ⊔ C.map (MulAut.conj a).toMonoidHom : Subgroup Q) : Set Q) = ⊥ := by
    intro a _ han
    have he := (NormPair.conjugate_eq_or_eq_of_normalizer_index_two hindex hne.symm a).resolve_left
      (fun he => han (mem_normalizer_iff_map_conj_eq.mpr he))
    rwa [he]
  have hrC : primeRank 2 (MulAut C) ≤ 2 := by
    rw [primeRank_equiv 2 (MulAut.congr hC.2.1.some)]
    exact hr
  obtain ⟨he,hrE⟩ := moving_pair_rank_le_three C E hE.1.2.1 hindex hm hc hrC
  have hd : fixedCodim ρ E ≤ 6 :=
    ((actionRatio_le_nat_iff ρ hE.1.2.1 2).mp
      (hE.1.2.2.2.le.trans hE.1.1)).trans (by omega)
  have hdq : fixedCodim (fixedQuotient ρ ⊤) E ≤ 6 := by
    have hh := fixedCodim_quotient_add_subrepresentation_le ρ (fixedSubrepresentation ρ ⊤) E
    exact (Nat.le_add_right _ _).trans (hh.trans hd)
  obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp hm
  let := hE.1.2.1.2
  have ha1 : a ≠ 1 := fun hh => han (hh ▸ N.one_mem)
  have ha2 : orderOf a = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha) ha1
  have hmap := (NormPair.conjugate_eq_or_eq_of_normalizer_index_two hindex hne.symm a).resolve_left
    (fun he => han (mem_normalizer_iff_map_conj_eq.mpr he))
  exact ⟨hindex,E,hE,he,hrE,hd,hdq,a,ha,ha2,han,hmap,
    moving_pair_stabilizer_faithful C E ha (hc a ha han)⟩

theorem small_pair_centralizer_eq_bot
    {Q : Type*} [Group Q] [Finite Q]
    (C₁ C₂ : Subgroup Q) (h₁ : IsComponent Q C₁) (h₂ : IsComponent Q C₂)
    [IsSimpleGroup C₁] [IsSimpleGroup C₂]
    (hne : C₁ ≠ C₂) [(C₁ ⊔ C₂).Normal]
    (hquot : IsPGroup 2 (Q ⧸ (C₁ ⊔ C₂))) (hcore : pCore 2 Q = ⊥) :
    centralizer ((C₁ ⊔ C₂ : Subgroup Q) : Set Q) = ⊥ := by
  let N := centralizer ((C₁ ⊔ C₂ : Subgroup Q) : Set Q)
  let := h₁.2
  let := h₂.2
  have hZ₁ : center C₁ = ⊥ :=
    (inferInstance : (center C₁).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative C₁ (center_eq_top_iff.mp he))
  have hZ₂ : center C₂ = ⊥ :=
    (inferInstance : (center C₂).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative C₂ (center_eq_top_iff.mp he))
  have havoid₁ : ¬ C₁ ≤ N := fun hh =>
    Group.IsPerfect.not_isMulCommutative C₁
      (le_centralizer_iff_isMulCommutative.mp (hh.trans (centralizer_le (show C₁ ≤ C₁ ⊔ C₂ from le_sup_left))))
  have havoid₂ : ¬ C₂ ≤ N := fun hh =>
    Group.IsPerfect.not_isMulCommutative C₂
      (le_centralizer_iff_isMulCommutative.mp (hh.trans (centralizer_le (show C₂ ≤ C₁ ⊔ C₂ from le_sup_right))))
  have hp := isTwoGroup_of_normal_avoiding_component_pair C₁ C₂ N h₁ h₂ hne
    hZ₁ hZ₂ hquot havoid₁ havoid₂
  have hle : N ≤ pCore 2 Q := le_sSup ⟨inferInstance,hp⟩
  exact bot_unique (hle.trans hcore.le)

open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original quotient pair supplies the small moving actor without an
additional centralizer or automorphism-rank premise. -/
theorem local_quotient_small_moving_actor
    [IsSimpleGroup (L ⧸ pCore 2 L)]
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) (XiQuotient (localJoin T L)) U)
    (C : Subgroup (XiQuotient (localJoin T L))) (t : localJoin T L)
    (hne : C ≠ C.map (MulAut.conj (QuotientGroup.mk' (pCore 2 (localJoin T L)) t)).toMonoidHom)
    (hnorm : (C ⊔ C.map (MulAut.conj (QuotientGroup.mk' (pCore 2 (localJoin T L)) t)).toMonoidHom).Normal)
    (hpair : C ⊔ C.map (MulAut.conj (QuotientGroup.mk' (pCore 2 (localJoin T L)) t)).toMonoidHom =
      ((localOrbit T L).subgroupOf (localJoin T L)).map (QuotientGroup.mk' (pCore 2 (localJoin T L))))
    (hactor : CommonCubicActorPair ρ C
      (C.map (MulAut.conj (QuotientGroup.mk' (pCore 2 (localJoin T L)) t)).toMonoidHom) (XiQuotient L))
    {p : ℕ} (hp : p.Prime) (hm : ClassicalGroup.IsPSL (XiQuotient L) 2 p) (hlarge : 3 < p) :
    SmallMovingCubicActorPair ρ C
      (C.map (MulAut.conj (QuotientGroup.mk' (pCore 2 (localJoin T L)) t)).toMonoidHom) := by
  obtain ⟨E,hE,hmE,hCs⟩ := hactor
  let H := localJoin T L
  let q := QuotientGroup.mk' (pCore 2 H)
  let C' := C.map (MulAut.conj (q t)).toMonoidHom
  have h₁ := hCs C (by simp)
  have h₂ := hCs C' (by simp [C',q,H])
  let : IsSimpleGroup C := h₁.2.1.some.isSimpleGroup
  let : IsSimpleGroup C' := h₂.2.1.some.isSimpleGroup
  let := hnorm
  let S := ((T : Subgroup G).subgroupOf H).map q
  have hS : IsPGroup 2 S := (T.isPGroup'.comap_subtype).map q
  have hgen : (C ⊔ C') ⊔ S = ⊤ := by
    rw [hpair,←Subgroup.map_sup,←subgroupOf_sup
      (show localOrbit T L ≤ H from le_sup_left)
      (show (T : Subgroup G) ≤ H from le_sup_right),subgroupOf_self,
      map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have hquot := isPGroup_quotient_of_sup_eq_top (C ⊔ C') S hS hgen
  have hcent := small_pair_centralizer_eq_bot C C' h₁.1 h₂.1 hne hquot
    (pCore_quotient_pCore_eq_bot 2)
  apply common_cubic_actor_small_mover ρ C (q t) hne hcent ⟨E,hE,hmE,hCs⟩
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fact p.Prime := ⟨hp⟩
  rw [primeRank_equiv 2 (MulAut.congr e)]
  exact Theory.PSL2.prime_card_automorphism_two_rank F hF hlarge


end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1 Chapter1.XiEmbedding
open Chapter3.Section02 Representation.BinaryOffender.Homogeneous
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}


/-- The original swapped witness has a common moving actor of rank at most
three and fixed codimension at most six on both literal modules. -/
theorem doubleNatural_four_pure_small_moving_actor_of_many_of_omega_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      omegaCenterIn (B.pointSylow w) ⊓ centralizer (L : Set G) ≠ ⊥ →
      let X := PureFourXi.residual T L
      ∃ (P : Sylow 2 G) (A : Sylow 3 X) (K : Subgroup G)
        (F : FundamentalSetup KnownSimple.IsKnownSimple T K),
        let H := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
        SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) X
          ((A : Subgroup X).map X.subtype) H K ∧
        conjugateSpanBy X H = componentOrbit K (T : Subgroup G) ∧
        X < componentOrbit K (T : Subgroup G) ∧
        (∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (XiQuotient K) 2 p ∧
          (p % 8 = 3 ∨ p % 8 = 5) ∧ (p % 24 = 11 ∨ p % 24 = 13)) ∧
        elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (F.moduleSubgroup : Set G) ∧
        F.moduleSubgroup ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
        letI := F.module_elementary
        let Q := XiQuotient (localJoin T K)
        let q := QuotientGroup.mk' (pCore 2 (localJoin T K))
        let K₁ := (K.subgroupOf (localJoin T K)).map q
        ∃ ρ : Representation (ZMod 2) Q (Additive F.moduleSubgroup),
          Function.Injective ρ ∧ Function.Injective (fixedQuotient ρ ⊤) ∧
          (∀ (x : localJoin T K) (v : F.moduleSubgroup),
            (ρ (q x) (Additive.ofMul v)).toMul =
              ⟨(x : G) * v * (x : G)⁻¹,
                (F.join_normalizes_module x.property v).mp v.property⟩) ∧
          cubicRatio ρ ≤ 2 ∧ cubicRatio (fixedQuotient ρ ⊤) ≤ 2 ∧
          ∃ t : localJoin T K, (t : G) ∈ T ∧ (t : G) ∉ normalizer (K : Set G) ∧
            let K₂ := K₁.map (MulAut.conj (q t)).toMonoidHom
            K₁ ≠ K₂ ∧ (K₁ ⊔ K₂).Normal ∧
            K₁ ⊔ K₂ = ((localOrbit T K).subgroupOf (localJoin T K)).map q ∧
            PureFourXi.SmallMovingCubicActorPair ρ K₁ K₂ := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf hne
  obtain ⟨P,A,K,F,hs,he,hstrict,hodd,hJF,hFQ,ρ,hρ,hρq,hact,hρc,hρqc,
      t,ht,htn,hneK,hnK,hpair,hactor⟩ :=
    D.doubleNatural_four_pure_common_cubic_actor_of_many_of_omega_fixed
      h hmany B S w hw hp hfix hf hne
  obtain ⟨_,hmodel⟩ := SwappedSylow.nonnormal_model_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)) hs.toSwappedInput
  let : IsSimpleGroup (XiQuotient K) :=
    SwappedFactorsProof.quotient_simple hs.toSwappedInput hmodel
  obtain ⟨p,hp',ho,hm,h8,h24⟩ := hodd
  let := F.module_elementary
  exact ⟨P,A,K,F,hs,he,hstrict,⟨p,hp',ho,hm,h8,h24⟩,hJF,hFQ,ρ,hρ,hρq,hact,hρc,hρqc,
    t,ht,htn,hneK,hnK,hpair,
    PureFourXi.local_quotient_small_moving_actor ρ _ t hneK hnK hpair hactor hp' hm (by omega)⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
