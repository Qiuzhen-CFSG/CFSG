module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairCompatibility
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Source
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.PResidual.CoprimeIndexValuation

/-!
# Cubic exchanged setup for the nonsingleton ratio branch

The nonsingleton cubic branch supplies two commuting, disjoint D₆ actors whose
join is the index-two kernel.  We lift these actors through the original
solvable subgroup and transport the source exchange, support, dimension and
point-commutator data to the embedded factors.  The two actors have order 36;
the index-two kernel therefore forces the ambient 2-quotient to have order 72.
The primitive odd residual is consequently the 3-residual of order 9, so the
literal exchanged-factor consumer applies and places the residual in the
specified two-generalized-Fitting preimage.

Source: Aschbacher--Smith 14.6.12(2)--(3), printed p. 1031, applied to
14.6.17; the source interfaces are `SourcePairCompatibility`,
`SourceDihedralFactors`, and `SourcePrimitiveOddResidual`.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G]

private theorem cubic_actorImage (J : Subgroup G) (A : Subgroup (J ⧸ pCore 2 J)) :
    actorImage J ((A.comap (QuotientGroup.mk' (pCore 2 J))).map J.subtype) = A := by
  unfold actorImage subgroupOf
  rw [comap_map_eq_self_of_injective J.subtype_injective,
    map_comap_eq_self (by intro x _; exact QuotientGroup.mk'_surjective _ x)]

private theorem cubic_pair_normalizes {D : Type*} [Group D] (A B : Subgroup D)
    (hc : ∀ x ∈ A, ∀ y ∈ B, Commute x y) : A ⊔ B ≤ normalizer (A : Set D) := by
  refine sup_le le_normalizer ((show B ≤ centralizer (A : Set D) from ?_).trans
    (Subgroup.centralizer_le_normalizer _))
  intro y hy x hx
  exact hc x hx y hy

private theorem cubic_lift_normalizes (J : Subgroup G)
    (A K : Subgroup (J ⧸ pCore 2 J)) (h : K ≤ normalizer (A : Set _)) :
    (K.comap (QuotientGroup.mk' (pCore 2 J))).map J.subtype ≤
      normalizer (((A.comap (QuotientGroup.mk' (pCore 2 J))).map J.subtype) : Set G) := by
  exact (map_mono ((comap_mono h).trans (le_normalizer_comap _))).trans
    (le_normalizer_map _)

private theorem cubic_conj_lift (J : Subgroup G) (A : Subgroup J) (t : J) :
    (A.map (MulAut.conj t).toMonoidHom).map J.subtype =
      (A.map J.subtype).map (MulAut.conj (t : G)).toMonoidHom := by
  rw [map_map,map_map]
  rfl

private theorem cubic_not_normalizes_lift (J : Subgroup G) (A : Subgroup J) (t : J)
    (hn : t ∉ normalizer (A : Set J)) :
    (t : G) ∉ normalizer (A.map J.subtype : Set G) := by
  intro h
  apply hn
  have hc : (normalizer (A.map J.subtype : Set G)).comap J.subtype ≤
      normalizer (A : Set J) := by
    simpa only [comap_map_eq_self_of_injective J.subtype_injective] using
      (le_normalizer_comap (H := A.map J.subtype) J.subtype)
  exact hc h

private theorem cubic_residual_card {D : Type*} [Group D] [Finite D]
    (hcard : Nat.card D = 72)
    (hp : ∃ p, (p = 3 ∨ p = 5) ∧ IsElementaryAbelian p (pResidual 2 D) ∧
      pResidual 2 D ≠ ⊥) : Nat.card (pResidual 2 D) = 9 := by
  obtain ⟨p,hp,hE,hne⟩ := hp
  let := hE
  rcases hp with rfl | rfl
  · obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 3 (pResidual 2 D)).exists_card_eq
    have hv := pResidual_card_padicValNat (G := D) 3 2 (by decide)
    rw [hn,hcard,padicValNat.prime_pow] at hv
    have hv72 : padicValNat 3 72 = 2 := by
      exact padicValNat_mul_pow_left (p := 3) (q := 2) 2 3 (by decide)
    rw [hv72] at hv
    simpa [hv] using hn
  · obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 5 (pResidual 2 D)).exists_card_eq
    have hv := pResidual_card_padicValNat (G := D) 5 2 (by decide)
    rw [hn,hcard,padicValNat.prime_pow] at hv
    rw [padicValNat.eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 72)] at hv
    have hone : Nat.card (pResidual 2 D) = 1 := by simpa [hv] using hn
    exact (hne (Subgroup.card_eq_one.mp hone)).elim

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

theorem source_ratio_nonsingleton_cubic_exchanged_setup
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hmore : 1 < Nat.card d.Index)
    (hcubic : ∀ k, Nonempty ((f.ambientFactor d k).actor ≃* DihedralGroup 3)) :
    ∃ H0 H1 H2 : Subgroup G,
      OddNormalizer.ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2 := by
  classical
  obtain ⟨hi,hip,_⟩ := source_ratio_nonsingleton_cubic_index_two
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hmore hcubic
  obtain ⟨_,p,m,hpm,_hmark,hmarked,i,j,_hij,_hall,hjoin,hdis,hcom,hspace,hspaceDis,
    _hfixed,hsupport,hpoint,t,htT,_hact,_hact',_hsp,_hnq,htij,htn⟩ :=
    source_ratio_nonsingleton_dihedral hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d hd hmore
  have hp3 : p = 3 := by
    have heq := (Nat.card_congr (hmarked i).1.some.toEquiv).symm.trans
      (Nat.card_congr (hcubic i).some.toEquiv)
    simp only [DihedralGroup.nat_card] at heq
    omega
  subst p
  have hm : m = 1 ∨ m = 2 := by
    rcases (ChapterD.CyclicSource.primeDimensionOptions_iff 3 m).mp hpm with h | h
    · exact h.2
    · norm_num at h
  let A := (f.ambientFactor d i).actor
  let B := (f.ambientFactor d j).actor
  let K := ChapterD.Jhat a.representation
  let q := QuotientGroup.mk' (pCore 2 J)
  let H0 := (K.comap q).map J.subtype
  let H1 := (A.comap q).map J.subtype
  let H2 := (B.comap q).map J.subtype
  have hA : actorImage J H1 = A := cubic_actorImage J A
  have hB : actorImage J H2 = B := cubic_actorImage J B
  have hjoin' : A ⊔ B = K := hjoin
  have hsize : Nat.card K = 36 := by
    obtain ⟨fprod,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hdis
      (by intro x hx y hy; exact (hcom x hx y hy).symm)
    rw [←hjoin', ←Nat.card_congr fprod.toEquiv, Nat.card_prod,
      Nat.card_congr (hcubic i).some.toEquiv, Nat.card_congr (hcubic j).some.toEquiv,
      DihedralGroup.nat_card]
  have hD : Nat.card (J ⧸ pCore 2 J) = 72 := by
    have h := K.card_mul_index
    rw [hsize,show K.index = 2 from hi] at h
    exact h.symm
  have hres : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 3^2 := by
    apply cubic_residual_card hD
    obtain ⟨p,hp,hE,_hr,hne,_hmin⟩ := source_solvable_minimal_elementary_residual
      hG T hempty hM hu hmany hcard e hab J hJ hs
    exact ⟨p,hp,hE,hne⟩
  have hdim (k : d.Index) : Module.finrank (ZMod 2) (f.ambientFactor d k).space = 2 ∨
      Module.finrank (ZMod 2) (f.ambientFactor d k).space = 4 := by
    have h := (hmarked k).2
    rcases hm with hm | hm <;> simp_all
  refine ⟨H0,H1,H2,{
    prime := Or.inl rfl
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
    first_model := by rw [hA]; exact hcubic i
    second_model := by rw [hB]; exact hcubic j
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
    exact hip
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
  · apply cubic_lift_normalizes
    rw [←hjoin']
    exact cubic_pair_normalizes A B hcom
  · apply cubic_lift_normalizes
    rw [←hjoin',sup_comm]
    exact cubic_pair_normalizes B A (fun y hy x hx => (hcom x hx y hy).symm)
  · refine ⟨(t : G)⁻¹,(T : Subgroup G).inv_mem htT,?_,?_⟩
    · intro hn
      apply cubic_not_normalizes_lift J (A.comap q) t htn
      change (t : G)⁻¹ ∈ normalizer ((A.comap q).map J.subtype : Set G) at hn
      exact inv_mem_iff.mp hn
    · simpa only [inv_inv] using (cubic_conj_lift J (A.comap q) t).symm.trans
        (congrArg (map J.subtype) htij)
  · rw [hA,hB,←hsupport i,←hsupport j]
    exact hspace
  · rw [hA,hB,←hsupport i,←hsupport j]
    exact hspaceDis
  · rw [hA,←hsupport i]
    exact Or.inl ⟨rfl,hdim i⟩
  · rw [hB,←hsupport j]
    exact Or.inl ⟨rfl,hdim j⟩
  · have h := hpoint i
    dsimp only at h
    rw [map_embedded_pResidual] at h
    exact h
  · have h := hpoint j
    dsimp only at h
    rw [map_embedded_pResidual] at h
    exact h

theorem source_ratio_nonsingleton_cubic_residual_le_fittingPreimage
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hmore : 1 < Nat.card d.Index)
    (hcubic : ∀ k, Nonempty ((f.ambientFactor d k).actor ≃* DihedralGroup 3)) :
    residual J ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc := by
  obtain ⟨H0,H1,H2,hsetup⟩ := source_ratio_nonsingleton_cubic_exchanged_setup
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hmore hcubic
  exact OddNormalizer.source_minimal_solvable_residual_le_fittingPreimage
    hG T hempty hM hu hmany hcard e hab J hJ.1 a hJ hs 3 H0 H1 H2 hsetup

end CFSG.Quasithin.Chapter14.Section06
