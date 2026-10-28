module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairCompatibility.QuinticGeometryParallel.LiftedPoint
public import Theory.GroupTheory.PResidual.NormalSup
public import Theory.GroupTheory.PResidual.Restriction
public import Theory.GroupTheory.PResidual.TwiceOddPrime
public import Theory.GroupTheory.PResidual.PrimeOrderGeneration

/-!
# Residuals of the literal quintic preimages without an index assumption

The primitive residual already lies in Jhat. Its full preimage therefore
contains the original residual, so restriction preserves that residual.
Relative normality of the two commuting factors identifies the residual
join. The actual two-group quotient kernels give cyclic-five residual core
quotients, and the original point commutators place the central point in
each intrinsic residual two-core. No index-two premise enters these steps.

Source: Aschbacher--Smith 14.6.12(3), p.1031, and 14.6.15, pp.1034--1035.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open OddNormalizer
namespace SourcePairCompatibility.QuinticGeometryParallel
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem preimage_normalizes (J : Subgroup G) (A B : Subgroup (J ⧸ pCore 2 J))
    (hn : B ≤ normalizer (A : Set _)) :
    actorPreimage J B ≤ normalizer (actorPreimage J A : Set G) :=
  (map_mono ((comap_mono hn).trans (le_normalizer_comap _))).trans (le_normalizer_map _)

private theorem commuting_join_normalizes {D : Type*} [Group D] (A B : Subgroup D)
    (hc : ∀ x ∈ A, ∀ y ∈ B, Commute x y) : A ⊔ B ≤ normalizer (A : Set D) := by
  refine sup_le le_normalizer ((show B ≤ centralizer (A : Set D) from ?_).trans
    (Subgroup.centralizer_le_normalizer _))
  intro y hy x hx
  exact hc x hx y hy

omit [Finite G] in
private theorem preimage_sup (J : Subgroup G) (A B : Subgroup (J ⧸ pCore 2 J)) :
    actorPreimage J A ⊔ actorPreimage J B = actorPreimage J (A ⊔ B) := by
  unfold actorPreimage
  rw [← Subgroup.map_sup,comap_sup_eq _ _ _ (QuotientGroup.mk'_surjective _)]

private theorem transitive_pair_kernel_index {D I : Type*} [Group D] [Finite I]
    (π : D →* Equiv.Perm I) (hc : Nat.card I = 2)
    (ht : ∀ i j, ∃ g : D, π g i = j) : π.ker.index = 2 := by
  have hd : π.ker.index ∣ 2 := by
    rw [index_ker]
    apply π.range.card_subgroup_dvd_card.trans
    rw [Nat.card_perm,hc]
    exact dvd_rfl
  have hn : π.ker.index ≠ 1 := by
    intro he
    have heq := index_eq_one.mp he
    obtain ⟨i,j,hij,_⟩ := Nat.card_eq_two_iff.mp hc
    obtain ⟨g,hg⟩ := ht i j
    have hgker : π g = 1 := show g ∈ π.ker from heq ▸ mem_top g
    exact hij (by simpa only [hgker,Equiv.Perm.one_apply] using hg)
  exact (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hn

private theorem preimage_residual_core_card (J : Subgroup G)
    (A : Subgroup (J ⧸ pCore 2 J)) (hm : Nonempty (A ≃* DihedralGroup 5)) :
    Nat.card (residual (actorPreimage J A) ⧸ pCore 2 (residual (actorPreimage J A))) = 5 := by
  let B := actorPreimage J A
  have hB : B ≤ J := actorPreimage_le J A
  have hmodel : Nonempty (actorImage J B ≃* DihedralGroup 5) := by
    change Nonempty (actorImage J (actorPreimage J A) ≃* DihedralGroup 5)
    rw [actorImage_actorPreimage]
    exact hm
  let q := QuotientGroup.mk' (pCore 2 J)
  let g : B →* actorImage J B := (q.subgroupMap (B.subgroupOf J)).comp
    (subgroupOfEquivOfLe hB).symm.toMonoidHom
  have hg : Function.Surjective g := (q.subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe hB).symm.surjective
  have hk : g.ker ≤ (J.pCoreIn 2).subgroupOf B := by
    intro x hx
    have hzero : q ⟨x,hB x.property⟩ = 1 := congrArg Subtype.val hx
    exact mem_map_of_mem J.subtype ((QuotientGroup.eq_one_iff _).mp hzero)
  have hgk : IsPGroup 2 g.ker := ((isPGroup_pCoreIn 2 J).comap_subtype).to_le hk
  have hc : Nat.card (actorImage J B) = 2*5 := by
    rw [Nat.card_congr hmodel.some.toEquiv,DihedralGroup.nat_card]
  have hr := card_twoResidual_coreQuotient_of_two_kernel (by decide : Odd 5) g hg hgk hc
  let e : pResidual 2 B ≃* residual B :=
    (pResidual 2 B).equivMapOfInjective B.subtype B.subtype_injective
  have hke : IsPGroup 2 e.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective]
    exact IsPGroup.of_card (n := 0) (by simp)
  rwa [Nat.card_congr (e.toMonoidHom.pCoreQuotientEquiv e.surjective hke).toEquiv] at hr

private theorem preimage_residual_ne (J : Subgroup G)
    (A B : Subgroup (J ⧸ pCore 2 J)) (hd : Disjoint A B)
    (hm : Nonempty (A ≃* DihedralGroup 5)) :
    residual (actorPreimage J A) ≠ residual (actorPreimage J B) := by
  let H1 := actorPreimage J A
  let H2 := actorPreimage J B
  intro he
  have hc := preimage_residual_core_card J A hm
  have hdiv : 5 ∣ Nat.card (residual H1) := hc ▸ card_quotient_dvd_card (pCore 2 (residual H1))
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := residual H1) 5 hdiv
  have hx1 : (x:G) ∈ H1 := residual_le H1 x.property
  have hx2 : (x:G) ∈ H2 := residual_le H2 (he ▸ x.property)
  let xJ : J := ⟨x,actorPreimage_le J A hx1⟩
  have hdis : Disjoint (actorImage J H1) (actorImage J H2) := by
    dsimp only [H1,H2]
    rwa [actorImage_actorPreimage,actorImage_actorPreimage]
  have hzero : QuotientGroup.mk' (pCore 2 J) xJ = 1 :=
    Subgroup.disjoint_def.mp hdis (mem_map_of_mem _ hx1) (mem_map_of_mem _ hx2)
  have hcore : (x:G) ∈ J.pCoreIn 2 :=
    mem_map_of_mem J.subtype ((QuotientGroup.eq_one_iff xJ).mp hzero)
  let xQ : J.pCoreIn 2 := ⟨x,hcore⟩
  have ho : orderOf xQ = 5 := (Subgroup.orderOf_coe xQ).symm.trans
    ((Subgroup.orderOf_coe x).trans hx)
  have hcop := (isPGroup_pCoreIn 2 J).orderOf_coprime (by decide : Nat.Coprime 2 5) xQ
  rw [ho] at hcop
  norm_num at hcop

omit [Finite G] in
private theorem subtype_conjugate_map (J : Subgroup G) (A : Subgroup J) (t : J) :
    (A.map (MulAut.conj t).toMonoidHom).map J.subtype =
      (A.map J.subtype).map (MulAut.conj (t:G)).toMonoidHom := by
  rw [map_map,map_map]
  rfl

omit [Finite G] in
private theorem commutator_le_factor_residual_core {H U : Subgroup G}
    [IsElementaryAbelian 2 U] (B : Subgroup G) (hUB : U ≤ B) (hBH : B ≤ H)
    (hn : H ≤ normalizer (U : Set G)) : ⁅U,residual B⁆ ≤ (residual B).pCoreIn 2 := by
  have hUN : U ≤ normalizer (residual B : Set G) :=
    hUB.trans (B.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image B (pResidual 2 B)))
  have hRN : residual B ≤ normalizer (U : Set G) := (residual_le B).trans (hBH.trans hn)
  have hm : U ⊓ residual B ≤ (residual B).pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((IsElementaryAbelian.isPGroup 2 U).to_le inf_le_left)
      inf_le_right ((le_inf hRN (residual B).le_normalizer).trans inf_normalizer_le_normalizer_inf)
  exact (le_inf (le_normalizer_iff_commutator_le_left.mp hRN)
    (le_normalizer_iff_commutator_le_right.mp hUN)).trans hm

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
variable (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation)
    (π : (J ⧸ pCore 2 J) →* Equiv.Perm d.Index)
    (hp : ∀ g i, (f.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (f.ambientFactor d (π g i)).actor)
    (w : SourcePairCompatibility.QuinticOuterAction a f d π)
include hG hempty hM hu hmany hcard e hab hJ hs hp w





omit hp in
/-- The two actual factor residuals generate the original residual. The
containment in Jhat replaces the earlier index-two argument. -/
theorem source_quintic_residual_join :
    ∃ i j : d.Index, i ≠ j ∧ (∀ k, k = i ∨ k = j) ∧
      residual (actorPreimage J (f.ambientFactor d i).actor) ⊔
        residual (actorPreimage J (f.ambientFactor d j).actor) = residual J := by
  obtain ⟨i,j,hij,hall,hjoin,_,hc,_,_⟩ := f.two_factor_moved_decomposition d w.two_factors
  let A := (f.ambientFactor d i).actor
  let B := (f.ambientFactor d j).actor
  let H1 := actorPreimage J A
  let H2 := actorPreimage J B
  have h1 : H1 ⊔ H2 ≤ normalizer (H1 : Set G) := by
    rw [show H1 ⊔ H2 = actorPreimage J (A ⊔ B) from preimage_sup J A B]
    exact preimage_normalizes J A (A ⊔ B) (commuting_join_normalizes A B hc)
  have h2 : H1 ⊔ H2 ≤ normalizer (H2 : Set G) := by
    rw [show H1 ⊔ H2 = actorPreimage J (A ⊔ B) from preimage_sup J A B]
    exact preimage_normalizes J B (A ⊔ B) (by
      rw [sup_comm]; exact commuting_join_normalizes B A (fun x hx y hy => (hc y hy x hx).symm))
  let : (H1.subgroupOf (H1 ⊔ H2)).Normal := normal_subgroupOf_of_le_normalizer h1
  let : (H2.subgroupOf (H1 ⊔ H2)).Normal := normal_subgroupOf_of_le_normalizer h2
  have hPK := source_solvable_minimal_residual_le_Jhat hG T hempty hM hu hmany hcard e hab J hJ hs a
  have hR : residual J ≤ H1 ⊔ H2 := by
    rw [show H1 ⊔ H2 = actorPreimage J (A ⊔ B) from preimage_sup J A B,
      show A ⊔ B = ChapterD.Jhat a.representation from hjoin]
    rintro _ ⟨y,hy,rfl⟩
    refine ⟨y,?_,rfl⟩
    exact hPK (map_pResidual_le 2 (QuotientGroup.mk' (pCore 2 J))
      (mem_map_of_mem (QuotientGroup.mk' (pCore 2 J)) hy))
  refine ⟨i,j,hij,hall,?_⟩
  change (pResidual 2 H1).map H1.subtype ⊔ (pResidual 2 H2).map H2.subtype = _
  rw [embedded_pResidual_sup_of_relative_normal]
  exact embedded_pResidual_eq_of_le_of_residual_le 2
    (sup_le (actorPreimage_le J A) (actorPreimage_le J B)) hR

omit hG hempty hM hu hmany hcard e hab hJ hs hp in
/-- The literal factor residual has its intrinsic cyclic-five core quotient. -/
theorem source_quintic_factor_residual_model (k : d.Index) :
    Nonempty ((residual (actorPreimage J (f.ambientFactor d k).actor) ⧸
      pCore 2 (residual (actorPreimage J (f.ambientFactor d k).actor))) ≃* Multiplicative (ZMod 5)) :=
  ⟨mulEquivOfPrimeCardEq (preimage_residual_core_card J _ (w.dihedral k)) (by simp)⟩

omit hp w in
/-- Original 14.6.12(3) places the point in the intrinsic residual two-core
of each literal factor preimage, without a kernel or index identification. -/
theorem source_factor_residual_point_core (k : d.Index) :
    centralInvolutions T ≤ (residual (actorPreimage J (f.ambientFactor d k).actor)).pCoreIn 2 := by
  let Hk := actorPreimage J (f.ambientFactor d k).actor
  have hpoint : centralInvolutions T ≤ ⁅conjugateSpanBy (localModule T M) J,residual Hk⁆ := by
    have he : (f.ambientFactor d k).actor =
        (d.factor k).actor.map (ChapterD.Jhat a.representation).subtype :=
      ChapterD.RatioDecomposition.Factor.map_actor (d.factor k) (f.embedding a.representation)
    have hh := source_ratio_factor_point hG T hempty hM hu hmany hcard e hab J hJ hs a f d k
    dsimp only at hh
    rw [←he,map_embedded_pResidual] at hh
    exact hh
  have hUQ : conjugateSpanBy (localModule T M) J ≤ J.pCoreIn 2 :=
    (source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1).UH_le_QH
  have hQH : J.pCoreIn 2 ≤ Hk := by
    apply map_mono
    intro x hx
    change QuotientGroup.mk' (pCore 2 J) x ∈ (f.ambientFactor d k).actor
    have he : QuotientGroup.mk' (pCore 2 J) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [he]
    exact (f.ambientFactor d k).actor.one_mem
  exact hpoint.trans (commutator_le_factor_residual_core Hk (hUQ.trans hQH)
    (actorPreimage_le J _) a.normalizes)


/-- The genuine index-two preimage normalizes each literal factor residual.
It is the preimage of the supplied permutation kernel, with no Jhat equality. -/
theorem source_quintic_preserving_preimage :
    (actorPreimage J π.ker).relIndex J = 2 ∧
      ∀ k : d.Index, actorPreimage J π.ker ≤
        normalizer (residual (actorPreimage J (f.ambientFactor d k).actor) : Set G) := by
  have ht := source_ratio_factor_transitive hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π hp
  have hi := transitive_pair_kernel_index π w.two_factors ht
  refine ⟨?_,fun k => ?_⟩
  · change (((π.ker.comap (QuotientGroup.mk' (pCore 2 J))).map J.subtype).comap J.subtype).index = 2
    rw [comap_map_eq_self_of_injective J.subtype_injective]
    exact (π.ker.index_comap_of_surjective (QuotientGroup.mk'_surjective _)).trans hi
  · apply (preimage_normalizes J (f.ambientFactor d k).actor π.ker ?_).trans
      (normalizer_le_normalizer_characteristic_image
        (actorPreimage J (f.ambientFactor d k).actor)
        (pResidual 2 (actorPreimage J (f.ambientFactor d k).actor)))
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (f.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom = _
    simpa only [show π g = 1 from hg,Equiv.Perm.one_apply] using hp g k


/-- The source residual normalizers have index two in the original Sylow
and in J. The actual preserving preimage supplies the overgroup; the source
factor exchanger moves both distinct residuals. No index of Jhat is used. -/
theorem source_quintic_residual_normalizer_indices (hd : d.FittingFull) :
    ∀ k : d.Index,
      ((T : Subgroup G) ⊓ normalizer
        (residual (actorPreimage J (f.ambientFactor d k).actor) : Set G)).relIndex T = 2 ∧
      (J ⊓ normalizer
        (residual (actorPreimage J (f.ambientFactor d k).actor) : Set G)).relIndex J = 2 := by
  have hmore : 1 < Nat.card d.Index := by rw [w.two_factors]; decide
  obtain ⟨_,p,m,_hpm,_hmark,_hmarked,i,j,_hij,hall,_hjoin,hdis,_hcom,_hspace,_hspaceDis,
    _hfixed,_hsupport,_hpoint,t,htT,_ha,_ha',_hsp,_hnq,htij,_htn⟩ :=
    source_ratio_nonsingleton_dihedral hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d hd hmore
  let H1 := actorPreimage J (f.ambientFactor d i).actor
  let H2 := actorPreimage J (f.ambientFactor d j).actor
  have he : H1.map (MulAut.conj (t:G)).toMonoidHom = H2 :=
    (subtype_conjugate_map J ((f.ambientFactor d i).actor.comap
      (QuotientGroup.mk' (pCore 2 J))) t).symm.trans (congrArg (map J.subtype) htij)
  have hr : (residual H1).map (MulAut.conj (t:G)).toMonoidHom = residual H2 := by
    unfold GenerationOne.residual
    rw [map_embedded_pResidual,he]
  have hne : residual H1 ≠ residual H2 := preimage_residual_ne J _ _ hdis (w.dihedral i)
  have hn1 : (t:G) ∉ normalizer (residual H1 : Set G) := by
    intro hn
    exact hne ((mem_normalizer_iff_map_conj_eq.mp hn).symm.trans hr)
  have hn2 : (t:G) ∉ normalizer (residual H2 : Set G) := by
    intro hn
    exact hne (map_injective (MulAut.conj (t:G)).injective
      (hr.trans (mem_normalizer_iff_map_conj_eq.mp hn).symm))
  have hmove (k : d.Index) : ∃ x ∈ (T : Subgroup G),
      x ∉ normalizer (residual (actorPreimage J (f.ambientFactor d k).actor) : Set G) := by
    rcases hall k with hk | hk
    · rw [hk]; exact ⟨t,htT,hn1⟩
    · rw [hk]; exact ⟨t,htT,hn2⟩
  obtain ⟨hi,hn⟩ := source_quintic_preserving_preimage hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π hp w
  intro k
  refine ⟨normalizer_relIndex_eq_two_of_index_two_overgroup (T : Subgroup G) J
    (actorPreimage J π.ker) _ hJ.1.1.2 hi (hn k) (hmove k),?_⟩
  obtain ⟨x,hx,hxn⟩ := hmove k
  exact normalizer_relIndex_eq_two_of_index_two_overgroup J J (actorPreimage J π.ker)
    _ le_rfl hi (hn k) ⟨x,hJ.1.1.2 hx,hxn⟩

end SourcePairCompatibility.QuinticGeometryParallel
end CFSG.Quasithin.Chapter14.Section06
