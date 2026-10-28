module
public import CFSG.Quasithin.Chapter14.Section06.Singleton.QuinticNoIndex.ResidualAction
public import CFSG.Quasithin.Chapter14.Section06.SourcePairCompatibility.QuinticGeometryParallel.ResidualBranch
public import Theory.ElementaryAbelian.FivePlaneGeometry
public import Theory.GroupTheory.PCoreNormalizerAction.Residual

/-!
# The original residual factor normalizers: index two or six

In the residual-closure branch, each original two-perfect factor residual
is normal in O²(J), and its image in O²(J)/O₂(O²(J)) is a line of the
actual elementary five-plane. Normalizing this image is equivalent to
normalizing the factor: the intrinsic two-core normalizes the factor,
and two-perfectness absorbs that kernel. This retains the original quotient
and conjugation maps.

There are six lines. The original Sylow acts irreducibly, so its action on
any partner orbit has no fixed point and that orbit has even size. Its
stabilizer has index two in the Sylow, excluding orbit size four. Thus the
normalizer in Mc has index two or six. The latter case forces three to
divide the relative index of the original J in Mc.

The index-two case feeds the existing critical-pair second-normalizer
argument, giving the actual escaping element, characteristic two and C.2.3.
The index-six case remains an explicit obstruction; this is not the desired
unconditional bound or an exclusion of the quintic outer alternative.
`Source` applies the dichotomy to the literal singleton-owner reduction.
Source: Aschbacher--Smith 14.6.12, printed p.1031, and the normalizer step
of 14.6.15, printed p.1034, with the earlier factor-join index left unassumed.
-/

public section

open Subgroup
open scoped Pointwise IsMulCommutative

private theorem line_orbit_index {D E : Type*} [Group D] [Finite D]
    [Group E] [Finite E] [IsElementaryAbelian 5 E]
    (a : D →* MulAut E) (S : Sylow 2 D) (hE : Nat.card E = 25)
    (hfixed : ∀ L : Subgroup E, Nat.card L = 5 →
      ¬ ∀ s : S, L.map (a s.val).toMonoidHom = L)
    (L : Subgroup E) (hL : Nat.card L = 5)
    (hindex : ((MulAction.stabilizer (MulAut E) L).comap a).relIndex S = 2) :
    ((MulAction.stabilizer (MulAut E) L).comap a).index = 2 ∨
      ((MulAction.stabilizer (MulAut E) L).comap a).index = 6 := by
  let : MulAction D (Subgroup E) := MulAction.compHom (Subgroup E) a
  let N := (MulAction.stabilizer (MulAut E) L).comap a
  have he : N = MulAction.stabilizer D L := rfl
  have horbit : N.index = Nat.card (MulAction.orbit D L) := by
    rw [he, MulAction.index_stabilizer]
    rfl
  have hline (x : MulAction.orbit D L) : Nat.card x.val = 5 := by
    obtain ⟨g,hg⟩ := x.property
    change L.map (a g).toMonoidHom = x.val at hg
    rw [←hg,card_map_of_injective (a g).injective,hL]
  have hle : N.index ≤ 6 := by
    rw [horbit,←IsElementaryAbelian.FivePlaneGeometry.card_lines hE]
    exact Nat.card_le_card_of_injective
      (fun x : MulAction.orbit D L => (⟨x.val,hline x⟩ : {B : Subgroup E // Nat.card B = 5}))
      (fun x y h => Subtype.ext (congrArg (fun z : {B : Subgroup E // Nat.card B = 5} => z.val) h))
  have heven : 2 ∣ N.index := by
    by_contra hh
    rw [horbit] at hh
    obtain ⟨x,hx⟩ := S.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card
      (MulAction.orbit D L) hh
    apply hfixed x.val (hline x)
    intro s
    exact congrArg Subtype.val (hx s)
  have hdiv : N.index ∣ 2 * (S : Subgroup D).index := by
    have hd : N.index ∣ (N ⊓ S).index := index_dvd_of_le inf_le_left
    rw [←relIndex_mul_index inf_le_right,inf_relIndex_right,hindex] at hd
    exact hd
  have hfour : N.index ≠ 4 := by
    intro heq
    rw [heq] at hdiv
    exact S.not_dvd_index ((Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)).mp hdiv)
  have hpos : 0 < N.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  change N.index = 2 ∨ N.index = 6
  omega

private theorem subnormal_quotient_image_card {D : Type*} [Group D] [Finite D]
    (A : Subgroup D) (hA : A.IsSubnormal) :
    Nat.card (A.map (QuotientGroup.mk' (pCore 2 D))) = Nat.card (A ⧸ pCore 2 A) := by
  let q := QuotientGroup.mk' (pCore 2 D)
  let f := q.subgroupMap A
  have hk : f.ker = pCore 2 A := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk',pCore_subnormal_eq_comap 2 hA]
    rfl
  have e := QuotientGroup.quotientKerEquivOfSurjective f (q.subgroupMap_surjective A)
  rw [←Nat.card_congr e.toEquiv,hk]

namespace CFSG.Quasithin.Chapter14.Section06
open Theory.GroupTheory Representation.BinaryOffender
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne OddNormalizer
open OddNormalizer.Quintic.ModuleGeometry (residualPartnerAction residual_partner_normalizes)
namespace Singleton.QuinticNoIndex
open SourcePairCompatibility.QuinticGeometryParallel
variable {G : Type*} [Group G] [Finite G]
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
include hG hempty hM hu hmany hcard e hab hJ hs w

private theorem residual_plane_no_fixed_line
    (hc : residualClosure J Mc = residual J)
    (L : Subgroup (residual J ⧸ pCore 2 (residual J))) (hL : Nat.card L = 5) :
    ¬∀ t : T, L.map (residualPartnerAction Mc J hc
      (inclusion (AlternatingThree.sylow_le_partner T hu) t)).toMonoidHom = L := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have prim := source_quintic_primitive_residual hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π w
  let := prim.elementary
  let R := pResidual 2 (J ⧸ pCore 2 J)
  obtain ⟨c,hcmap⟩ := residual_quotient_equiv (by decide : Odd 5) J
    (IsElementaryAbelian.isPGroup 5 R)
  intro hinv
  let B := (L.map c.toMonoidHom).map R.subtype
  have hBT : ((T : Subgroup G).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) ≤
      normalizer (B : Set (J ⧸ pCore 2 J)) := by
    apply le_normalizer_iff.mpr
    rintro t ⟨t,ht,rfl⟩ b ⟨b,⟨v,hv,rfl⟩,rfl⟩
    let tM : Mc := inclusion (AlternatingThree.sylow_le_partner T hu) ⟨t,ht⟩
    have hcompat : (c (residualPartnerAction Mc J hc tM v) : J ⧸ pCore 2 J) =
        QuotientGroup.mk' (pCore 2 J) t * (c v : J ⧸ pCore 2 J) *
          (QuotientGroup.mk' (pCore 2 J) t)⁻¹ := by
      obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (residual J)) v
      change (c (pCoreNormalizerAction 2 (residual J)
        (inclusion (residual_partner_normalizes Mc J hc) tM)
          (QuotientGroup.mk' (pCore 2 (residual J)) x)) : J ⧸ pCore 2 J) = _
      rw [pCoreNormalizerAction_mk,hcmap,hcmap,←map_inv,←map_mul,←map_mul]
      rfl
    change QuotientGroup.mk' (pCore 2 J) t * (c v : J ⧸ pCore 2 J) *
      (QuotientGroup.mk' (pCore 2 J) t)⁻¹ ∈ B
    rw [←hcompat]
    apply mem_map_of_mem R.subtype
    apply mem_map_of_mem c.toMonoidHom
    exact (hinv ⟨t,ht⟩) ▸ mem_map_of_mem (residualPartnerAction Mc J hc tM).toMonoidHom hv
  have hBR : B ≤ R := map_subtype_le _
  have hRB : R ≤ normalizer (B : Set (J ⧸ pCore 2 J)) :=
    ((le_centralizer_iff_isMulCommutative.mpr (inferInstance : IsMulCommutative R)).trans
      (centralizer_le hBR)).trans (Subgroup.centralizer_le_normalizer _)
  have htop := pResidual_sup_sylow_eq_top
    ((T.subtype hJ.1.1.2).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J)))
  have hn : B.Normal := normalizer_eq_top_iff.mp (top_unique (htop ▸ sup_le hRB hBT))
  have hbcard : Nat.card B = 5 := by
    rw [card_map_of_injective R.subtype_injective,card_map_of_injective c.injective,hL]
  rcases prim.minimal B hn hBR with hb | hb
  · rw [hb,Subgroup.card_bot] at hbcard
    omega
  · rw [hb,source_quintic_residual_plane_card hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π w] at hbcard
    omega

include hp in
/-- Every original factor has partner normalizer index two or six. The
exceptional index forces a cubic divisor of the original relative index. -/
theorem source_quintic_residual_normalizer_alternatives
    (hd : d.FittingFull) (hc : residualClosure J Mc = residual J) (k : d.Index) :
    (Mc ⊓ normalizer
      (residual (actorPreimage J (f.ambientFactor d k).actor) : Set G)).relIndex Mc = 2 ∨
    ((Mc ⊓ normalizer
      (residual (actorPreimage J (f.ambientFactor d k).actor) : Set G)).relIndex Mc = 6 ∧
      3 ∣ J.relIndex Mc) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let K := residual J
  let A := residual (actorPreimage J (f.ambientFactor d k).actor)
  let E := K ⧸ pCore 2 K
  let q := QuotientGroup.mk' (pCore 2 K)
  let L := (A.subgroupOf K).map q
  let φ := residualPartnerAction Mc J hc
  have hAK : A ≤ K := embedded_pResidual_mono 2 (actorPreimage_le J _)
  have hn : K ≤ normalizer (A : Set G) :=
    source_quintic_residual_normalizes_factor hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π hp w k
  let hnA : (A.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer hn
  have hL : Nat.card L = 5 := by
    rw [subnormal_quotient_image_card _ hnA.isSubnormal]
    let eA := subgroupOfEquivOfLe hAK
    rw [Nat.card_congr (QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).toEquiv]
    rw [Nat.card_congr (source_quintic_factor_residual_model T J a f d π w k).some.toEquiv]
    exact Nat.card_zmod 5
  have prim := source_quintic_primitive_residual hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π w
  let := prim.elementary
  obtain ⟨c,_⟩ := residual_quotient_equiv (by decide : Odd 5) J
    (IsElementaryAbelian.isPGroup 5 (pResidual 2 (J ⧸ pCore 2 J)))
  let : IsElementaryAbelian 5 E :=
    IsElementaryAbelian.of_surjective c.symm.toMonoidHom c.symm.surjective
  have hE : Nat.card E = 25 := (Nat.card_congr c.toEquiv).trans
    (source_quintic_residual_plane_card hG T hempty hM hu hmany hcard e hab J hJ hs a f d π w)
  let N := (normalizer (A : Set G)).subgroupOf Mc
  have hstab : (MulAction.stabilizer (MulAut E) L).comap φ = N := by
    ext x
    change L.map (φ x).toMonoidHom = L ↔ (x : G) ∈ normalizer (A : Set G)
    constructor
    · exact mem_normalizer_of_pCoreNormalizerAction_preserves_image K A hAK
        (isPPerfect_embedded_pResidual 2 _) ((pCoreIn_le 2 K).trans hn)
        (inclusion (residual_partner_normalizes Mc J hc) x)
    · exact pCoreNormalizerAction_preserves_image 2 K A
        (inclusion (residual_partner_normalizes Mc J hc) x)
  have hTM := AlternatingThree.sylow_le_partner T hu
  let S := T.subtype hTM
  have hfixed (B : Subgroup E) (hB : Nat.card B = 5) :
      ¬∀ s : S, B.map (φ s.val).toMonoidHom = B := by
    intro hb
    apply residual_plane_no_fixed_line hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π w hc B hB
    intro t
    exact hb ⟨inclusion hTM t,t.property⟩
  have hiT : N.relIndex S = 2 := by
    change ((normalizer (A : Set G)).subgroupOf Mc).relIndex
      ((T : Subgroup G).subgroupOf Mc) = 2
    rw [relIndex_subgroupOf hTM]
    simpa only [inf_relIndex_left] using
      (source_quintic_residual_normalizer_indices hG T hempty hM hu hmany hcard e hab
        J hJ hs a f d π hp w hd k).1
  have halt := line_orbit_index φ S hE hfixed L hL (hstab.symm ▸ hiT)
  rw [hstab] at halt
  simp only [inf_relIndex_left]
  change N.index = 2 ∨ (N.index = 6 ∧ 3 ∣ J.relIndex Mc)
  rcases halt with hi | hi
  · exact Or.inl hi
  · refine Or.inr ⟨hi,?_⟩
    have hJM : J ≤ Mc :=
      (source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1).H_centralizes.trans
        (InitialSource.centralizer_le_partner T hu)
    have hiJ : N.relIndex (J.subgroupOf Mc) = 2 := by
      rw [relIndex_subgroupOf hJM]
      simpa only [inf_relIndex_left] using
        (source_quintic_residual_normalizer_indices hG T hempty hM hu hmany hcard e hab
          J hJ hs a f d π hp w hd k).2
    have hdiv : 6 ∣ 2 * J.relIndex Mc := by
      have hh : N.index ∣ (N ⊓ J.subgroupOf Mc).index := index_dvd_of_le inf_le_left
      rw [←relIndex_mul_index inf_le_right,inf_relIndex_right,hiJ,hi] at hh
      exact hh
    exact (by decide : Nat.Coprime 3 2).dvd_of_dvd_mul_left
      ((by decide : 3 ∣ 6).trans hdiv)

include hp in
/-- The remaining index-six case is separated from the literal critical-pair
consumer. In the other case, all of its normalizer-index premises are proved. -/
theorem source_quintic_residual_branch_dichotomy (hd : d.FittingFull)
    (hc : residualClosure J Mc = residual J) :
    letI : IsElementaryAbelian 2 (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩) :=
      inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J))
    (∃ k : d.Index, (Mc ⊓ normalizer
      (residual (actorPreimage J (f.ambientFactor d k).actor) : Set G)).relIndex Mc = 6 ∧
        3 ∣ J.relIndex Mc) ∨
    (∃ i j : d.Index, i ≠ j ∧
      ∃ c : Quintic.CriticalPair
        (source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1)
          a Mc (actorPreimage J (f.ambientFactor d i).actor),
        let N := normalizer (residual (actorPreimage J (f.ambientFactor d j).actor) : Set G)
        c.endpoint.representative ∈ N ∧ ¬N ≤ Mc ∧
          Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple
            N (Mc.pCoreIn 2) (Mc ⊓ N) ∧
          generalizedFitting N = pCore 2 N ∧
          ((T : Subgroup G) ⊓ N).relIndex T = 2) := by
  classical
  by_cases hi : ∀ k : d.Index, (Mc ⊓ normalizer
      (residual (actorPreimage J (f.ambientFactor d k).actor) : Set G)).relIndex Mc = 2
  · exact Or.inr (source_quintic_residual_branch_secondNormalizer
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d π hp w hd hc hi)
  · obtain ⟨k,hk⟩ := not_forall.mp hi
    exact Or.inl ⟨k,(source_quintic_residual_normalizer_alternatives
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d π hp w hd hc k).resolve_left hk⟩

end Singleton.QuinticNoIndex
end CFSG.Quasithin.Chapter14.Section06
