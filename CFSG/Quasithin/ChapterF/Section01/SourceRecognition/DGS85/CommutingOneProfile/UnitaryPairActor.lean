module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.PairCoprimeSplitting
public import Theory.GroupTheory.OmegaPairLinearBlock
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryGeometry.TwoPointRoots.RootTransport

/-!
# The unitary center-pair actor in Chapter 11

The two distinct beta Sylow omega-centers generate a genuine SL₂(2ⁿ)
subgroup. The existing SU₃ and PSU₃ Sylow–involution equivalences give a
linear block through the first omega-center and an involution of the second.
Uniqueness of the involution's Sylow and its exact field order place the
entire second omega-center in that block. Both centers become full Sylows
of this same linear actor.

For the source pair H = <Z_alpha,Z_gamma> Q_beta, the resulting epimorphism
has kernel exactly Q_beta and retains both critical-center images. Alpha
is unrestricted. This supplies the missing actor for the coprime splitting;
it does not kill the complementary factor or prove the later row selection.
Source: DGS85, Groups and Graphs (1985), (11.3), printed pp.169–171;
unitary two-root geometry: GLS4, Chapter 4, Lemma 3.2(d),(h).
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
open BenderSuzuki.ZD.RankOneModelGeometry
open HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open CommutingNontrivial

private instance {F : Type*} [Field F] [Finite F] : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

private def binaryPSLtoSL (n : ℕ) : PSL2BinaryMatrixGroup n ≃*
    SL(2,BenderSuzuki.PFAppendixIII.BinaryGaloisField n) :=
  (MulEquiv.ofBijective (BenderSuzuki.Converse.pi _)
    ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm

private def root_map_equiv {D H : Type*} [Group D] [Finite D] [Group H]
    (e : D ≃* H) (R : Sylow 2 D) (t : D) :
    rootGenerated (R : Subgroup D) t ≃*
      rootGenerated (R.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup H) (e t) := by
  apply ((rootGenerated (R : Subgroup D) t).equivMapOfInjective e.toMonoidHom e.injective).trans
  apply MulEquiv.subgroupCongr
  rw [rootGenerated,rootGenerated,Subgroup.map_sup,
    map_omegaOneAmbient_injective e.toMonoidHom e.injective,MonoidHom.map_zpowers]
  rfl

private theorem omega_center_eq_of_data {D : Type*} [Group D] (R : Sylow 2 D)
    (h : omegaOneAmbient (R : Subgroup D) = (center R).map (R : Subgroup D).subtype)
    [IsElementaryAbelian 2 (omegaOneAmbient (R : Subgroup D))] :
    omegaCenterIn (R : Subgroup D) = omegaOneAmbient (R : Subgroup D) := by
  rw [omegaCenterIn_eq_omegaOneAmbient,←h,omegaOneAmbient_eq_self]

private theorem unitary_omega_root_data {D : Type*} [Group D] [Finite D]
    {n : ℕ} (hn : 2 ≤ n)
    (hi : ClassicalGroup.IsPSU D 3 (2^n) ∨ IsSU D 3 (2^n)) (R : Sylow 2 D) :
    omegaCenterIn (R : Subgroup D) = omegaOneAmbient (R : Subgroup D) ∧
      IsElementaryAbelian 2 (omegaOneAmbient (R : Subgroup D)) ∧
      Nat.card (omegaOneAmbient (R : Subgroup D)) = 2^n ∧
      ∀ t : D, BenderSuzuki.PFAppendixIII.IsInvolution t → t ∉ normalizer (R : Set D) →
        Nonempty ((rootGenerated (R : Subgroup D) t) ≃*
          SL(2,BenderSuzuki.PFAppendixIII.BinaryGaloisField n)) := by
  rcases hi with hi | hi
  · obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := hi
    have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
    obtain ⟨C,hC⟩ := exists_standard_basis J (2^n) hcard hf
    let J₀ := standardForm J
    let e₀ := e.trans (projectiveEquiv J C hC)
    have hdata := HermitianForm.SylowOmega.omega_of_projective_equiv J₀ hn hcard hf rfl e₀ R
    let := hdata.2.1
    refine ⟨omega_center_eq_of_data R hdata.1,hdata.2.1,hdata.2.2,?_⟩
    intro t ht ho
    have ht' : BenderSuzuki.PFAppendixIII.IsInvolution (e₀ t) :=
      ⟨fun he => ht.1 (e₀.injective (he.trans e₀.map_one.symm)),by rw [←map_pow,ht.2,map_one]⟩
    have ho' : e₀ t ∉ normalizer (R.mapSurjective (f := e₀.toMonoidHom) e₀.surjective : Set _) := by
      intro hh
      change e₀ t ∈ normalizer ((R : Subgroup D).map e₀.toMonoidHom : Set _) at hh
      rw [←map_equiv_normalizer_eq] at hh
      obtain ⟨x,hx,he⟩ := hh
      exact ho (e₀.injective he ▸ hx)
    exact ⟨(root_map_equiv e₀ R t).trans
      ((unitary_projective_rootGenerated_equiv J₀ hn hcard hf rfl _ (e₀ t) ht' ho').trans
        (binaryPSLtoSL n))⟩
  · obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := hi
    have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
    obtain ⟨C,hC⟩ := exists_standard_basis J (2^n) hcard hf
    let J₀ := standardForm J
    let e₀ := e.trans (specialEquiv J C hC)
    have hdata := HermitianForm.SylowOmega.omega_of_special_equiv J₀ hn hcard hf rfl e₀ R
    let := hdata.2.1
    refine ⟨omega_center_eq_of_data R hdata.1,hdata.2.1,hdata.2.2,?_⟩
    intro t ht ho
    have ht' : BenderSuzuki.PFAppendixIII.IsInvolution (e₀ t) :=
      ⟨fun he => ht.1 (e₀.injective (he.trans e₀.map_one.symm)),by rw [←map_pow,ht.2,map_one]⟩
    have ho' : e₀ t ∉ normalizer (R.mapSurjective (f := e₀.toMonoidHom) e₀.surjective : Set _) := by
      intro hh
      change e₀ t ∈ normalizer ((R : Subgroup D).map e₀.toMonoidHom : Set _) at hh
      rw [←map_equiv_normalizer_eq] at hh
      obtain ⟨x,hx,he⟩ := hh
      exact ho (e₀.injective he ▸ hx)
    exact ⟨(root_map_equiv e₀ R t).trans
      ((unitary_special_rootGenerated_equiv J₀ hn hcard hf rfl _ (e₀ t) ht' ho').trans
        (binaryPSLtoSL n))⟩

/-- Two distinct Sylow omega-centers in either unitary quotient generate
an actual SL₂ block over the original fixed field degree. -/
theorem unitary_omega_pair_linear {D : Type*} [Group D] [Finite D]
    {n : ℕ} (hn : 2 ≤ n)
    (hi : ClassicalGroup.IsPSU D 3 (2^n) ∨ IsSU D 3 (2^n))
    (hcore : pCore 2 D = ⊥) (R T : Sylow 2 D) (hRT : R ≠ T) :
    let W := omegaCenterIn (R : Subgroup D) ⊔ omegaCenterIn (T : Subgroup D)
    ∃ e : W ≃* SL(2,BenderSuzuki.PFAppendixIII.BinaryGaloisField n),
      ∃ S U : Sylow 2 SL(2,BenderSuzuki.PFAppendixIII.BinaryGaloisField n),
        ((omegaCenterIn (R : Subgroup D)).subgroupOf W).map e.toMonoidHom = S ∧
        ((omegaCenterIn (T : Subgroup D)).subgroupOf W).map e.toMonoidHom = U := by
  let k := BenderSuzuki.PFAppendixIII.BinaryGaloisField n
  have hk : Nat.card k = 2^n := GaloisField.card 2 n (by omega)
  have M : IsRankOneModel D := hi.elim (.projective_unitary n (by omega)) (.special_unitary n (by omega))
  have hu := source_rank_one_sylow_eq_of_common_involution M hcore
  obtain ⟨hR,hRe,hRc,hroot⟩ := unitary_omega_root_data hn hi R
  obtain ⟨hT,hTe,hTc,_⟩ := unitary_omega_root_data hn hi T
  let := hRe
  let := hTe
  have hne : omegaOneAmbient (T : Subgroup D) ≠ ⊥ := by
    intro he
    have hh : Nat.card (omegaOneAmbient (T : Subgroup D)) = 1 := he ▸ card_bot
    have hp := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by omega : n ≠ 0)
    omega
  obtain ⟨t,ht,ht1⟩ := (omegaOneAmbient (T : Subgroup D)).bot_or_exists_ne_one.resolve_left hne
  have ht2 : t^2=1 := elemPow_eq_one_of_isElementaryAbelian t ht
  have ho : t ∉ normalizer (R : Set D) := by
    intro hh
    have hp : IsPGroup 2 (zpowers t) := (IsElementaryAbelian.zpowers_of_pow_eq_one ht2).isPGroup
    have htR := (hp.inf_normalizer_sylow R).le ⟨mem_zpowers t,hh⟩
    exact hRT (hu R T t htR.2 (omegaOneAmbient_le _ ht) ht1 ht2)
  obtain ⟨e₀⟩ := hroot t ⟨ht1,ht2⟩ ho
  have heq := omega_pair_eq_of_linear_block R T hu t (omegaOneAmbient_le _ ht) ht1 ht2
    (hTc.trans hk.symm) e₀
  let W := omegaCenterIn (R : Subgroup D) ⊔ omegaCenterIn (T : Subgroup D)
  have hW : W = rootGenerated (R : Subgroup D) t := by
    rw [show W = omegaCenterIn (R : Subgroup D) ⊔ omegaCenterIn (T : Subgroup D) from rfl,hR,hT]
    exact heq
  let e := (MulEquiv.subgroupCongr hW).trans e₀
  have hSyl (A : Subgroup D) (hAW : A ≤ W) (hA : IsElementaryAbelian 2 A)
      (hc : Nat.card A = 2^n) :
      ∃ S : Sylow 2 SL(2,k), (A.subgroupOf W).map e.toMonoidHom = S := by
    let := hA
    let : IsElementaryAbelian 2 (A.subgroupOf W) := IsElementaryAbelian.subgroupOf hAW
    obtain ⟨S,hS⟩ := sylow_of_linear_card e (A.subgroupOf W)
      (IsElementaryAbelian.isPGroup 2 _) (by
        rw [Nat.card_congr (subgroupOfEquivOfLe hAW).toEquiv,hc,hk])
    exact ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective,by rw [←hS]; rfl⟩
  obtain ⟨S,hS⟩ := hSyl _ le_sup_left (hR.symm ▸ hRe) ((congrArg (fun A : Subgroup D => Nat.card A) hR).trans hRc)
  obtain ⟨U,hU⟩ := hSyl _ le_sup_right (hT.symm ▸ hTe) ((congrArg (fun A : Subgroup D => Nat.card A) hT).trans hTc)
  exact ⟨e,S,U,hS,hU⟩

open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The actual center-pair quotient maps onto its fixed-degree linear block,
with exact beta-core kernel and both critical-center Sylow images. -/
theorem source_unitary_pair_linear_actor
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    {n : ℕ} (hn : 2 ≤ n)
    (hi : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n)) :
    let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
    let k := BenderSuzuki.PFAppendixIII.BinaryGaloisField n
    H ≤ d.localGroup b ∧
      ∃ f : H →* SL(2,k), Function.Surjective f ∧
        f.ker = (Q (family P) b).subgroupOf H ∧
        ∃ R T : Sylow 2 SL(2,k),
          ((Z (family P) a).subgroupOf H).map f = R ∧
          ((Z (family P) c).subgroupOf H).map f = T := by
  let := finite_endpoints h
  let K := d.localGroup b
  let D := K ⧸ pCore 2 K
  let : Finite K := Finite.of_injective (inclusion (d.local_le b)) (inclusion_injective _)
  let : Finite D := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  have Mb : IsRankOneModel D := hi.elim (.projective_unitary n (by omega))
    (.special_unitary n (by omega))
  obtain ⟨hHK,R,T,hRT,hker,ha,hc',hr⟩ := source_pair_actor_map h hB d hc hb hbc hac Mb
  let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
  let q := (QuotientGroup.mk' (pCore 2 K)).comp (inclusion hHK)
  let W := omegaCenterIn (R : Subgroup D) ⊔ omegaCenterIn (T : Subgroup D)
  obtain ⟨e,S,U,hS,hU⟩ := unitary_omega_pair_linear hn hi (pCore_quotient_pCore_eq_bot 2) R T hRT
  let q₁ : H →* W := (MulEquiv.subgroupCongr hr).toMonoidHom.comp q.rangeRestrict
  have hq₁ : Function.Surjective q₁ := (MulEquiv.subgroupCongr hr).surjective.comp q.rangeRestrict_surjective
  have hv (x : H) : (q₁ x : D) = q x := rfl
  have hm (A : Subgroup H) (C : Subgroup D) (hAC : A.map q = C) :
      A.map q₁ = C.subgroupOf W := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      change q y ∈ C
      rw [←hAC]
      exact mem_map_of_mem q hy
    · intro hx
      obtain ⟨y,hy,he⟩ := hAC.symm ▸ hx
      exact ⟨y,hy,Subtype.ext he⟩
  let f := e.toMonoidHom.comp q₁
  refine ⟨hHK,f,e.surjective.comp hq₁,?_,S,U,?_,?_⟩
  · ext x
    change e (q₁ x) = 1 ↔ x.val ∈ Q (family P) b
    rw [←e.map_one,e.injective.eq_iff]
    change q₁ x = 1 ↔ x ∈ (Q (family P) b).subgroupOf H
    rw [←hker]
    exact Subtype.ext_iff
  · rw [show f = e.toMonoidHom.comp q₁ from rfl,←map_map,hm _ _ ha]
    exact hS
  · rw [show f = e.toMonoidHom.comp q₁ from rfl,←map_map,hm _ _ hc']
    exact hU

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
