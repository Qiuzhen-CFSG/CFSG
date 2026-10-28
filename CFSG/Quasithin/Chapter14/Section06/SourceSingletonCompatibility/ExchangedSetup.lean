module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairCompatibility.CubicExchangedSetup
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.KernelResidual

/-!
# Lifting the original dihedral pair at its primitive prime

Once the actual actor join has index two, the two commuting dihedral actors
lift to the preimages required by original 14.6.12. The primitive residual
identifies their prime; their product order and the odd valuation of the
ambient quotient give residual order p². The exchange uses the inverse of
the source Sylow element, matching the downstream conjugation convention.
All support and central-point clauses use the same quotient action.

The index remains an explicit input here. Its cubic proof is available;
the quintic outer-action exclusion is a separate ambient source obligation.
Source: Aschbacher--Smith 14.6.12(1)--(3), printed p.1031.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G]

private theorem pair_actorImage (J : Subgroup G) (A : Subgroup (J ⧸ pCore 2 J)) :
    actorImage J ((A.comap (QuotientGroup.mk' (pCore 2 J))).map J.subtype) = A := by
  unfold actorImage subgroupOf
  rw [comap_map_eq_self_of_injective J.subtype_injective,
    map_comap_eq_self (by intro x _; exact QuotientGroup.mk'_surjective _ x)]

private theorem pair_pair_normalizes {D : Type*} [Group D] (A B : Subgroup D)
    (hc : ∀ x ∈ A, ∀ y ∈ B, Commute x y) : A ⊔ B ≤ normalizer (A : Set D) := by
  refine sup_le le_normalizer ((show B ≤ centralizer (A : Set D) from ?_).trans
    (Subgroup.centralizer_le_normalizer _))
  intro y hy x hx
  exact hc x hx y hy

private theorem pair_lift_normalizes (J : Subgroup G)
    (A K : Subgroup (J ⧸ pCore 2 J)) (h : K ≤ normalizer (A : Set _)) :
    (K.comap (QuotientGroup.mk' (pCore 2 J))).map J.subtype ≤
      normalizer (((A.comap (QuotientGroup.mk' (pCore 2 J))).map J.subtype) : Set G) := by
  exact (map_mono ((comap_mono h).trans (le_normalizer_comap _))).trans
    (le_normalizer_map _)

private theorem pair_conj_lift (J : Subgroup G) (A : Subgroup J) (t : J) :
    (A.map (MulAut.conj t).toMonoidHom).map J.subtype =
      (A.map J.subtype).map (MulAut.conj (t : G)).toMonoidHom := by
  rw [map_map,map_map]
  rfl

private theorem pair_not_normalizes_lift (J : Subgroup G) (A : Subgroup J) (t : J)
    (hn : t ∉ normalizer (A : Set J)) :
    (t : G) ∉ normalizer (A.map J.subtype : Set G) := by
  intro h
  apply hn
  have hc : (normalizer (A.map J.subtype : Set G)).comap J.subtype ≤
      normalizer (A : Set J) := by
    simpa only [comap_map_eq_self_of_injective J.subtype_injective] using
      (le_normalizer_comap (H := A.map J.subtype) J.subtype)
  exact hc h

private theorem pair_residual_card {D : Type*} [Group D] [Finite D]
    {p : ℕ} (hp : p = 3 ∨ p = 5)
    (hE : IsElementaryAbelian p (pResidual 2 D))
    (hcard : Nat.card D = 8*p^2) : Nat.card (pResidual 2 D) = p^2 := by
  let := hE
  rcases hp with rfl | rfl
  · obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 3 (pResidual 2 D)).exists_card_eq
    have hv := pResidual_card_padicValNat (G := D) 3 2 (by decide)
    rw [hn,hcard,padicValNat.prime_pow] at hv
    have hv72 : padicValNat 3 (8*3^2) = 2 := by
      exact padicValNat_mul_pow_left (p := 3) (q := 2) 2 3 (by decide)
    rw [hv72] at hv
    simpa [hv] using hn
  · obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 5 (pResidual 2 D)).exists_card_eq
    have hv := pResidual_card_padicValNat (G := D) 5 2 (by decide)
    rw [hn,hcard,padicValNat.prime_pow] at hv
    have hv200 : padicValNat 5 (8*5^2) = 2 := by
      exact padicValNat_mul_pow_left (p := 5) (q := 2) 2 3 (by decide)
    rw [hv200] at hv
    simpa [hv] using hn

variable [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hu hmany hcard e hab

theorem source_ratio_nonsingleton_exchanged_setup_of_index
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hmore : 1 < Nat.card d.Index)
    (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hprim : OddNormalizer.PrimitiveResidual J p)
    (hindex : (ChapterD.Jhat a.representation).index = 2) :
    ∃ H0 H1 H2 : Subgroup G,
      OddNormalizer.ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2 := by
  classical
  let : Fact p.Prime := ⟨by rcases hp with rfl | rfl <;> decide⟩
  obtain ⟨_,r,m,hrm,hmark,hmarked,i,j,_hij,_hall,hjoin,hdis,hcom,hspace,hspaceDis,
    _hfixed,hsupport,hpoint,t,htT,_hact,_hact',_hsp,_hnq,htij,htn⟩ :=
    source_ratio_nonsingleton_dihedral hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d hd hmore
  have hrp : r = p := by
    obtain ⟨l,hl⟩ := hmark i
    let τ := (f.ambientFactor d i).embedding.groupMap
    have hτ := (f.ambientFactor d i).embedding.group_injective
    have hle : l.kernel.map τ ≤ pResidual 2 (J ⧸ pCore 2 J) := by
      rw [l.kernel_eq_twoResidual]
      exact map_pResidual_le 2 τ
    let q : l.kernel →* pResidual 2 (J ⧸ pCore 2 J) :=
      (τ.comp l.kernel.subtype).codRestrict _ (fun x => hle (mem_map_of_mem τ x.property))
    have hq : Function.Injective q := by
      intro x y hxy
      apply Subtype.ext
      apply hτ
      exact congrArg (fun z : pResidual 2 (J ⧸ pCore 2 J) => (z : J ⧸ pCore 2 J)) hxy
    let := hprim.elementary
    have hpk : IsPGroup p l.kernel :=
      (IsElementaryAbelian.isPGroup p (pResidual 2 (J ⧸ pCore 2 J))).of_injective q hq
    have hr : r = 3 ∨ r = 5 := by
      rcases (ChapterD.CyclicSource.primeDimensionOptions_iff r m).mp hrm with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1
    rcases hpk.card_eq_or_dvd with h | h
    · rw [hl.card_kernel] at h
      rcases hr with rfl | rfl <;> norm_num at h
    · rw [hl.card_kernel] at h
      have hrprime : r.Prime := by rcases hr with rfl | rfl <;> decide
      exact (((Nat.dvd_prime hrprime).mp h).resolve_left (Fact.out : p.Prime).ne_one).symm
  subst r
  let A := (f.ambientFactor d i).actor
  let B := (f.ambientFactor d j).actor
  let K := ChapterD.Jhat a.representation
  let q := QuotientGroup.mk' (pCore 2 J)
  let H0 := (K.comap q).map J.subtype
  let H1 := (A.comap q).map J.subtype
  let H2 := (B.comap q).map J.subtype
  have hA : actorImage J H1 = A := pair_actorImage J A
  have hB : actorImage J H2 = B := pair_actorImage J B
  have hjoin' : A ⊔ B = K := hjoin
  have hsize : Nat.card K = (2*p)^2 := by
    obtain ⟨fprod,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hdis
      (by intro x hx y hy; exact (hcom x hx y hy).symm)
    rw [←hjoin', ←Nat.card_congr fprod.toEquiv, Nat.card_prod,
      Nat.card_congr (hmarked i).1.some.toEquiv, Nat.card_congr (hmarked j).1.some.toEquiv,
      DihedralGroup.nat_card, pow_two]
  have hD : Nat.card (J ⧸ pCore 2 J) = 8*p^2 := by
    have h := K.card_mul_index
    rw [hsize,show K.index = 2 from hindex] at h
    rw [←h]
    ring
  have hres : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = p^2 :=
    pair_residual_card hp hprim.elementary hD
  have hdim (k : d.Index) :
      (p = 3 ∧ (Module.finrank (ZMod 2) (f.ambientFactor d k).space = 2 ∨
        Module.finrank (ZMod 2) (f.ambientFactor d k).space = 4)) ∨
      (p = 5 ∧ Module.finrank (ZMod 2) (f.ambientFactor d k).space = 4) := by
    rw [(hmarked k).2]
    rcases (ChapterD.CyclicSource.primeDimensionOptions_iff p m).mp hrm with
      ⟨rfl, rfl | rfl⟩ | ⟨rfl,rfl⟩ <;> simp
  refine ⟨H0,H1,H2,{
    prime := hp
    residual_card := hres
    zero_le := map_subtype_le _
    first_le := map_mono (comap_mono (hjoin' ▸ le_sup_left))
    second_le := map_mono (comap_mono (hjoin' ▸ le_sup_right))
    join_eq := ?_
    index := ?_
    core_le_first := ?_
    core_le_second := ?_
    actors_disjoint := by rwa [hA,hB]
    actors_commute := by rwa [hA,hB]
    first_model := by rw [hA]; exact (hmarked i).1
    second_model := by rw [hB]; exact (hmarked j).1
    normalizes_first := ?_
    normalizes_second := ?_
    exchanged := ?_
    split := ?_
    disjoint := ?_
    first_dimension := ?_
    second_dimension := ?_
    point_first := ?_
    point_second := ?_ }⟩
  · dsimp [H0, H1, H2]
    rw [← Subgroup.map_sup, comap_sup_eq q A B (QuotientGroup.mk'_surjective _), hjoin']
  · change ((K.comap q).map J.subtype |>.comap J.subtype).index = 2
    rw [comap_map_eq_self_of_injective J.subtype_injective]
    exact (K.index_comap_of_surjective (QuotientGroup.mk'_surjective _)).trans hindex
  · apply map_mono
    intro x hx
    change q x ∈ A
    have he : q x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [he]; exact A.one_mem
  · apply map_mono
    intro x hx
    change q x ∈ B
    have he : q x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [he]; exact B.one_mem
  · apply pair_lift_normalizes
    rw [←hjoin']
    exact pair_pair_normalizes A B hcom
  · apply pair_lift_normalizes
    rw [←hjoin',sup_comm]
    exact pair_pair_normalizes B A (fun y hy x hx => (hcom x hx y hy).symm)
  · refine ⟨(t : G)⁻¹,(T : Subgroup G).inv_mem htT,?_,?_⟩
    · intro hn
      apply pair_not_normalizes_lift J (A.comap q) t htn
      change (t : G)⁻¹ ∈ normalizer ((A.comap q).map J.subtype : Set G) at hn
      exact inv_mem_iff.mp hn
    · simpa only [inv_inv] using (pair_conj_lift J (A.comap q) t).symm.trans
        (congrArg (map J.subtype) htij)
  · rw [hA,hB,←hsupport i,←hsupport j]
    exact hspace
  · rw [hA,hB,←hsupport i,←hsupport j]
    exact hspaceDis
  · rw [hA,←hsupport i]
    exact hdim i
  · rw [hB,←hsupport j]
    exact hdim j
  · have h := hpoint i
    dsimp only at h
    rw [map_embedded_pResidual] at h
    exact h
  · have h := hpoint j
    dsimp only at h
    rw [map_embedded_pResidual] at h
    exact h

end CFSG.Quasithin.Chapter14.Section06
