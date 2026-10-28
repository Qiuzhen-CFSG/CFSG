module
public import Theory.SpecificGroups.Triality.BinaryLocalSections
public import Theory.SpecificGroups.Triality.PerfectTwoNormalizer
public import Theory.SpecificGroups.Triality.ArmsParabolicAtTwo
public import Theory.SpecificGroups.Triality.ParabolicOuterTwo.Extensions
public import Theory.SpecificGroups.Triality.BinarySevenPlane
public import Theory.GroupTheory.PrimeRankNormalIntersection.Kernel
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupTheory.PCoreNormalizerAction.Kernel

/-!
# Seven-rank bounds for local automorphisms of binary triality

The concrete ³D₄(2) model contains an elementary seven-plane. A proper
nonsolvable subgroup normalized by a full Sylow two-subgroup lies in an
arms parabolic: the central parabolic is solvable, while the arms
parabolic equals its local factor at field order two. Its normalizer
therefore has seven-rank at most one.

The outer automorphism group has order dividing three. Thus every
seven-subgroup of an automorphism group stabilizing such a subgroup
acts by inner automorphisms. A seven-free action kernel gives the same
rank bound for the acting group. For the literal two-core quotient of a
subgroup in an ambient group of seven-rank at most two, the elementary
seven-plane forces that action kernel to be seven-free.

These are intrinsic model and quotient-action facts used in the
changed-Sylow argument of Aschbacher–Smith 5.2.2, printed pp.648–649.
The concrete parabolic, outer-action and seven-plane proofs are imported
from the existing triality model.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Triality.Standard.BinaryLocalAutomorphisms
open Parabolics
local notation "M" => BinaryCarrier 1 Nat.zero_lt_one
local notation "P" => binaryParameters 1 Nat.zero_lt_one

/-- Binary triality contains an elementary subgroup of order forty-nine. -/
lemma seven_rank_ge_two : 2 ≤ primeRank 7 M := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact primeRank_ge_of_elementary_embedding
    (by decide : ∀ x : Multiplicative QuaternionSevenPlane.Plane, x ^ 7 = 1)
    (by simp [Nat.card_eq_fintype_card, QuaternionSevenPlane.Plane])
    binarySevenPlane.embedding binarySevenPlane.embedding_injective

/-- A proper nonsolvable Sylow-invariant subgroup has normalizer of seven-rank at most one. -/
lemma normalizer_seven_rank_le_one (S : Sylow 2 M) (R : Subgroup M)
    (hne : R ≠ ⊤) (hns : ¬ Group.IsSolvable R)
    (hn : (S : Subgroup M) ≤ normalizer (R : Set M)) :
    primeRank 7 (normalizer (R : Set M)) ≤ 1 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨_,a,_,hS⟩ := Theory.GroupTheory.SolvableSylowControl.exists_aligned_equiv
    (MulEquiv.refl M) S (unipotentSylow P rfl)
  have hN : normalizer (R : Set M) ≠ ⊤ := by
    intro he
    have hnormal : R.Normal := normalizer_eq_top_iff.mp he
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R hnormal with hb | ht
    · apply hns
      rw [hb]
      infer_instance
    · exact hne ht
  have hmap : (normalizer (R : Set M)).map a.toMonoidHom ≠ ⊤ := by
    intro he
    apply hN
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [he,map_top_of_surjective _ a.surjective]
  have hU : unipotent P ≤ (normalizer (R : Set M)).map a.toMonoidHom := by
    change (S : Subgroup M).map a.toMonoidHom = unipotent P at hS
    rw [←hS]
    exact map_mono hn
  obtain ⟨b,hb⟩ := OddSupplement.le_parabolic 1 Nat.zero_lt_one
    ((normalizer (R : Set M)).map a.toMonoidHom) hU hmap
  have hnsN : ¬ Group.IsSolvable ((normalizer (R : Set M)).map a.toMonoidHom) := by
    intro hs
    let := hs
    exact hns (Group.isSolvable_of_isSolvable_injective
      (f := ((normalizer (R : Set M)).equivMapOfInjective a.toMonoidHom a.injective).toMonoidHom.comp
        (inclusion R.le_normalizer))
      (((normalizer (R : Set M)).equivMapOfInjective a.toMonoidHom a.injective).injective.comp
        (inclusion_injective R.le_normalizer)))
  cases b with
  | central =>
    let := BinaryLocalSections.central_parabolic_solvable
    exact (hnsN (Group.isSolvable_of_isSolvable_injective (inclusion_injective hb))).elim
  | arms =>
    rw [primeRank_equiv 7 ((normalizer (R : Set M)).equivMapOfInjective a.toMonoidHom a.injective)]
    apply (primeRank_mono 7 hb).trans
    rw [parabolic_arms_eq_localFactor_at_two P rfl (by decide)]
    exact PerfectTwoNormalizer.localFactor_odd_primeRank_le_one P rfl .arms (by decide)

/-- Every seven-subgroup of the full automorphism group consists of inner automorphisms. -/
lemma seven_subgroup_inner (A : Subgroup (MulAut M)) (hp : IsPGroup 7 A) :
    A ≤ MulAut.innerSubgroup M := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup M)
  intro a ha
  obtain ⟨k,hk⟩ := hp ⟨a,ha⟩
  have hpow : q a ^ (7 ^ k) = 1 := by
    rw [←map_pow]
    exact (congrArg q (congrArg Subtype.val hk)).trans (map_one q)
  have h3 : orderOf (q a) ∣ 3 := (_root_.orderOf_dvd_natCard _).trans
    (by simpa using ParabolicOuterTwo.outer_card_dvd 1 Nat.zero_lt_one)
  exact (QuotientGroup.eq_one_iff a).mp (orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 7 3).pow_left k)
      (orderOf_dvd_of_pow_eq_one hpow) h3))

/-- A stabilizing action with seven-free kernel has seven-rank at most one. -/
lemma stabilizing_action_seven_rank_le_one
    {A : Type*} [Group A] [Finite A]
    (S : Sylow 2 M) (R : Subgroup M)
    (hne : R ≠ ⊤) (hns : ¬ Group.IsSolvable R)
    (hn : (S : Subgroup M) ≤ normalizer (R : Set M))
    (f : A →* MulAut M) (hk : Nat.Coprime 7 (Nat.card f.ker))
    (hf : ∀ a : A, R.map (f a).toMonoidHom = R) : primeRank 7 A ≤ 1 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let Q : Sylow 7 A := Classical.choice inferInstance
  have hi := injective_comp_subtype_of_coprime_ker f hk (Q : Subgroup A) Q.isPGroup'
  have hr := seven_subgroup_inner ((Q : Subgroup A).map f) (Q.isPGroup'.map f)
  let e : M ≃* MulAut.innerSubgroup M :=
    MonoidHom.ofInjective (conj_injective_of_center_eq_bot (binaryCarrier_center_eq_bot 1 Nat.zero_lt_one))
  let g : Q →* MulAut.innerSubgroup M := (f.comp (Q : Subgroup A).subtype).codRestrict _
    (fun x => hr (mem_map_of_mem f x.property))
  let j := e.symm.toMonoidHom.comp g
  have hj : Function.Injective j := by
    intro x y he
    apply hi
    exact congrArg Subtype.val (e.symm.injective he)
  have he (x : Q) : MulAut.conj (j x) = f x := by
    exact congrArg Subtype.val (e.apply_symm_apply (g x))
  have hJN (x : Q) : j x ∈ normalizer (R : Set M) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [he]
    exact hf x
  let k : Q →* normalizer (R : Set M) := j.codRestrict _ hJN
  rw [Q.primeRank_eq]
  exact (Theory.GroupTheory.primeRank_le_of_injective 7 k
    (fun x y hxy => hj (congrArg Subtype.val hxy))).trans
      (normalizer_seven_rank_le_one S R hne hns hn)

/-- Rank two in the containing triality quotient makes the literal quotient-action
kernel seven-free. Thus a subgroup preserving a proper nonsolvable Sylow-invariant
section has seven-rank at most one, with all original quotient maps retained. -/
lemma core_action_seven_rank_le_one
    {G : Type*} [Group G] [Finite G]
    (K R E B : Subgroup G) (hRK : R ≤ K) (hKE : K ≤ E) (hBE : B ≤ E)
    (hBK : B ≤ normalizer (K : Set G)) (hBR : B ≤ normalizer (R : Set G))
    (e : (K ⧸ pCore 2 K) ≃* M) (hrE : primeRank 7 E ≤ 2)
    (S : Sylow 2 (K ⧸ pCore 2 K))
    (hne : (R.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)) ≠ ⊤)
    (hns : ¬ Group.IsSolvable ((R.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))))
    (hS : (S : Subgroup (K ⧸ pCore 2 K)) ≤
      normalizer ((R.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)) : Set _)) :
    primeRank 7 B ≤ 1 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let f := (pCoreNormalizerAction 2 K).comp (inclusion hBK)
  let q := QuotientGroup.mk' (pCore 2 K)
  let Rbar := (R.subgroupOf K).map q
  have hrK : 2 ≤ primeRank 7 K := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 7 (by decide) (pCore 2 K) pCore_isPGroup,
      primeRank_equiv 7 e]
    exact seven_rank_ge_two
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.center_map_equiv,Subgroup.map_bot,binaryCarrier_center_eq_bot]
  have hrker := pCoreActionKernelIn_rank_add_le K E (by decide : Odd 7) hKE
    (by rw [hz,card_bot]; decide)
  have hkerle : f.ker.map B.subtype ≤ pCoreActionKernelIn 2 K E := by
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨hBE x.property,inclusion hBK x,hx,rfl⟩
  have hrk := primeRank_mono 7 hkerle
  rw [←primeRank_equiv 7 (f.ker.equivMapOfInjective B.subtype B.subtype_injective)] at hrk
  have hkc : Nat.Coprime 7 (Nat.card f.ker) :=
    (show Nat.Prime 7 by decide).coprime_iff_not_dvd.mpr
      (PrimeRank.eq_zero_iff_not_dvd_card.mp (by omega : primeRank 7 f.ker = 0))
  have hf (b : B) : Rbar.map (f b).toMonoidHom = Rbar := by
    let a := K.normalizerMonoidHom (inclusion hBK b)
    have ha : (R.subgroupOf K).map a.toMonoidHom = R.subgroupOf K := by
      apply map_injective K.subtype_injective
      rw [map_map]
      have he : K.subtype.comp a.toMonoidHom =
          (MulAut.conj (b : G)).toMonoidHom.comp K.subtype := by ext x; rfl
      rw [he,←map_map,map_subgroupOf_eq_of_le hRK]
      exact mem_normalizer_iff_map_conj_eq.mp (hBR b.property)
    change ((R.subgroupOf K).map q).map (f b).toMonoidHom = _
    rw [map_map]
    have he : (f b).toMonoidHom.comp q = q.comp a.toMonoidHom := by
      ext x
      exact pCoreNormalizerAction_mk 2 K (inclusion hBK b) x
    rw [he,←map_map,ha]
  let g := (MulAut.congr e).toMonoidHom.comp f
  have hgker : g.ker = f.ker :=
    MonoidHom.ker_comp_of_injective _ _ (MulAut.congr e).injective
  have hne' : Rbar.map e.toMonoidHom ≠ ⊤ := by
    intro hh
    apply hne
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [hh,map_top_of_surjective _ e.surjective]
  have hns' : ¬ Group.IsSolvable (Rbar.map e.toMonoidHom) := by
    intro hs
    let := hs
    exact hns (Group.isSolvable_of_isSolvable_injective
      (f := (Rbar.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom)
      (Rbar.equivMapOfInjective e.toMonoidHom e.injective).injective)
  apply stabilizing_action_seven_rank_le_one
    (S.mapSurjective e.surjective) (Rbar.map e.toMonoidHom) hne' hns'
    ((map_mono hS).trans (le_normalizer_map e.toMonoidHom)) g (hgker.symm ▸ hkc)
  intro b
  rw [map_map]
  have he : (g b).toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp (f b).toMonoidHom := by
    ext x
    change e (f b (e.symm (e x))) = e (f b x)
    rw [e.symm_apply_apply]
  rw [he,←map_map,hf]

end Triality.Standard.BinaryLocalAutomorphisms
