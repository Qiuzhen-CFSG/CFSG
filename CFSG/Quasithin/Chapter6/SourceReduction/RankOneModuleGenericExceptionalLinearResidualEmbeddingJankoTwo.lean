module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearResidualEmbeddingMathieu
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RankOneFourNormalizer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InvolutionCentralizerOdd
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.InvolutionConjugacy
public import Mathlib.GroupTheory.Perm.Support

/-!
# No linear-three-four section in the Hall–Janko carrier

The unique index-two exponent-four subgroup of the checked Hall–Janko
Sylow is its radical. That radical contains two involutions with different
permutation support sizes, hence in different ambient conjugacy classes.
An embedded PSL₃(4) would contain the radical as its Sylow subgroup, but
all its involutions are conjugate. Thus no such embedding exists.

A subgroup with PSL₃(4) two-core quotient has core of order at most two.
A nontrivial core would centralize a subgroup of order divisible by seven,
contradicting the two checked Hall–Janko involution-centralizer orders.
Removing the core therefore reduces every such section to the forbidden
embedding. The final exports transport this obstruction through the literal
containing-component quotient and apply it to the original residual.

Source: the J₂ row of Aschbacher–Smith A.3.12 and 5.1.12, printed
pp.47–48 and 635 (refs/quasithin.pdf). Finite witnesses use the existing
ATLAS J2G1-p100B0 tables; no new enumeration or trusted computation is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Matrix.PSL3.LinearThree Matrix.PSL3Even.UnipotentGeometry
open Sporadic.LeechRelated.J2
open Sporadic.LeechRelated.J2.ExceptionalParabolics
open Seed PairNormalizer PairNormalizer.RadicalData

private theorem unipotent_fourth_power {F : Type*} [Field F] [CharP F 2]
    (u : unipotent F) : u ^ 4 = 1 := by
  obtain ⟨v,rfl⟩ := (unipotentEquiv F).surjective u
  have hv : v ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2*2 from rfl, pow_mul]
    apply (square_eq_one_iff F _).mpr
    left
    simp only [pow_two,mul_x,CharTwo.add_self_eq_zero]
  rw [← map_pow,hv,map_one]

private theorem radical_has_nonconjugate_involutions :
    ∃ x y : Carrier, x ∈ q₂ ∧ y ∈ q₂ ∧ orderOf x = 2 ∧ orderOf y = 2 ∧
      ¬ IsConj x y := by
  have hx : orderOf (qElement 1) = 2 := by
    rw [← orderOf_injective inclusion inclusion_injective,qElement_inclusion]
    apply orderOf_eq_prime <;> decide +kernel
  have hy : orderOf (qElement 5) = 2 := by
    rw [← orderOf_injective inclusion inclusion_injective,qElement_inclusion]
    apply orderOf_eq_prime <;> decide +kernel
  refine ⟨qElement 1,qElement 5,qElement_mem 1,qElement_mem 5,hx,hy,?_⟩
  intro hc
  obtain ⟨g,hg⟩ := isConj_iff.mp (inclusion.map_isConj hc)
  have hs := congrArg (fun p : Equiv.Perm (Fin 100) => p.support.card) hg
  rw [Equiv.Perm.card_support_conj,qElement_inclusion,qElement_inclusion] at hs
  have h1 : (qTable 1).support.card = 100 := by decide +kernel
  have h5 : (qTable 5).support.card = 80 := by decide +kernel
  rw [h1,h5] at hs
  omega

/-- No actual PSL₃(4) embeds in the Hall--Janko carrier. -/
theorem no_linear_four_embedding_jankoTwo {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 4) (f : PSL(3,F) →* Carrier) : ¬ Function.Injective f := by
  intro hf
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by simpa [Nat.card_eq_fintype_card] using hF)
  let P := unipotentSylow F (by decide : 0 < 2) hF
  obtain ⟨S,hS⟩ := (P.isPGroup'.map f).exists_le_sylow
  let R := SecondParabolic.sylow FirstParabolic.card_l₁
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Carrier S R
  let j := (MulAut.conj g).toMonoidHom.comp f
  have hj : Function.Injective j := (MulAut.conj g).injective.comp hf
  let B := (unipotent F).map j
  have hBs : B ≤ s := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hS
    have he := congrArg (fun Q : Sylow 2 Carrier => (Q : Subgroup Carrier)) hg
    change (S : Subgroup Carrier).map (MulAut.conj g).toMonoidHom = s at he
    rw [he] at hh
    simpa only [map_map, B, j, P, coe_unipotentSylow] using hh
  have hc : Nat.card B = 64 := by
    rw [card_map_of_injective hj,card_unipotent,hF]
    decide
  have hidx : (B.subgroupOf s).index = 2 := by
    have hcard := (B.subgroupOf s).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hBs).toEquiv,hc,card_s] at hcard
    omega
  have hqB : q₂ ≤ B := by
    have hh := q₂_le_of_index_two_exponent_four (B.subgroupOf s) hidx (by
      intro x hx
      obtain ⟨u,hu,he⟩ := hx
      apply Subtype.ext
      change (x : Carrier) ^ 4 = 1
      change j u = (x : Carrier) at he
      rw [← he,← map_pow]
      have hp := congrArg Subtype.val (unipotent_fourth_power (⟨u,hu⟩ : unipotent F))
      change u ^ 4 = 1 at hp
      rw [hp,map_one])
    intro x hx
    exact hh (show (⟨x,q₂_le_s hx⟩ : s) ∈ q₂.subgroupOf s from hx)
  obtain ⟨x,y,hx,hy,hx2,hy2,hxy⟩ := radical_has_nonconjugate_involutions
  obtain ⟨u,hu,he⟩ := hqB hx
  obtain ⟨v,hv,hvE⟩ := hqB hy
  have hu2 : orderOf u = 2 := (orderOf_injective j hj u).symm.trans (he ▸ hx2)
  have hv2 : orderOf v = 2 := (orderOf_injective j hj v).symm.trans (hvE ▸ hy2)
  have huv : IsConj u v :=
    (Matrix.PSL3.EvenInnerCentralizers.involution_isConj_root F (n := 2) (by decide) hF u
      (by intro he; simp [he] at hu2) (by simpa [hu2] using pow_orderOf_eq_one u)).trans
    (Matrix.PSL3.EvenInnerCentralizers.involution_isConj_root F (n := 2) (by decide) hF v
      (by intro he; simp [he] at hv2) (by simpa [hv2] using pow_orderOf_eq_one v)).symm
  exact hxy (he ▸ hvE ▸ j.map_isConj huv)

private theorem jankoTwo_involution_centralizer_not_seven
    (z : Carrier) (hz : orderOf z = 2) :
    ¬ 7 ∣ Nat.card (centralizer ({z} : Set Carrier)) := by
  have hconj {x y : Carrier} (h : IsConj x y) :
      Nat.card (centralizer ({y} : Set Carrier)) =
        Nat.card (centralizer ({x} : Set Carrier)) := by
    obtain ⟨g,hg⟩ := isConj_iff.mp h
    have he : MulAut.conj y = MulAut.congr (MulAut.conj g) (MulAut.conj x) := by
      rw [MulAut.congr_conj]
      exact congrArg MulAut.conj hg.symm
    rw [← MulAut.fixedSubgroup_conj,← MulAut.fixedSubgroup_conj,he]
    exact (Nat.card_congr (MulAut.fixedSubgroupCongr (MulAut.conj g)
      (MulAut.conj x)).toEquiv).symm
  rcases InnerInvolutionCores.involution_fusion z hz with hz | hz
  · rw [hconj hz,Nat.card_congr InnerInvolutionCores.a_centralizer_equiv.toEquiv,
      Nat.card_prod,nat_card_alternatingGroup,Nat.card_fin]
    norm_num [InnerInvolutionCores.E4,
      InnerInvolutionCores.C2,Nat.card_fun,Nat.factorial]
  · rw [hconj hz]
    change ¬ 7 ∣ Nat.card l₁
    rw [FirstParabolic.card_l₁]
    decide

/-- The two-core of a linear-three-four section in the actual J₂ carrier
vanishes, by its order and the involution-centralizer orders. -/
theorem jankoTwo_linear_four_core_eq_bot (B : Subgroup Carrier)
    (hq : Nat.card (B ⧸ pCore 2 B) = 20160) : pCore 2 B = ⊥ := by
  have hd := B.card_subgroup_dvd_card
  rw [FirstParabolic.card_carrier,← (pCore 2 B).card_mul_index,
    show (pCore 2 B).index = 20160 from hq] at hd
  have hd' : Nat.card (pCore 2 B) ∣ 2 * 15 :=
    (Nat.mul_dvd_mul_iff_right (by decide : 0 < 20160)).mp hd
  have hc : Nat.Coprime (Nat.card (pCore 2 B)) 15 := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := B)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 15).pow_left n
  have hd2 : Nat.card (pCore 2 B) ∣ 2 := hc.dvd_of_dvd_mul_right hd'
  by_contra hne
  have hcard : Nat.card (pCore 2 B) = 2 :=
    ((Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd2).resolve_left
      (fun h1 => hne ((pCore 2 B).eq_bot_iff_card.mpr h1))
  let U := (pCore 2 B).map B.subtype
  have hU : Nat.card U = 2 := (card_map_of_injective B.subtype_injective).trans hcard
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 (by rw [hU])
  have hzG : orderOf (z : Carrier) = 2 := (orderOf_coe z).trans hz
  have heq : zpowers (z : Carrier) = U := eq_of_le_of_card_ge
    (zpowers_le.mpr z.property) (by rw [Nat.card_zpowers,hzG,hU])
  have hBN : B ≤ normalizer (U : Set Carrier) :=
    B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  rw [← heq,normalizer_zpowers_eq_centralizer_of_order_two _ hzG] at hBN
  have h7 : 7 ∣ Nat.card B :=
    (by decide : 7 ∣ 20160).trans (hq ▸ card_quotient_dvd_card (pCore 2 B))
  exact jankoTwo_involution_centralizer_not_seven z hzG (h7.trans (card_dvd_of_le hBN))

/-- No subgroup of the actual J₂ carrier has PSL₃(4) as its two-core quotient. -/
theorem no_linear_four_section_jankoTwo (B : Subgroup Carrier)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : (B ⧸ pCore 2 B) ≃* PSL(3,F)) : False := by
  let : Fintype F := Fintype.ofFinite F
  let : Fintype Matrix.PSL3Four.F := Fintype.ofFinite _
  let a : F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hF,Matrix.PSL3Four.card_F])
  have hc := jankoTwo_linear_four_core_eq_bot B
    ((Nat.card_congr e.toEquiv).trans
      ((Nat.card_congr (Atlas.fieldEquivPSL 3 a).toEquiv).trans Matrix.PSL3Four.card_PSL))
  let b : PSL(3,F) ≃* B := e.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot)
  exact no_linear_four_embedding_jankoTwo hF (B.subtype.comp b.toMonoidHom)
    (B.subtype_injective.comp b.injective)

/-- A homomorphism with a two-group kernel cannot realize a linear-three-four
quotient inside the actual Hall--Janko carrier. -/
theorem no_linear_four_jankoTwo_map {K : Type*} [Group K] [Finite K]
    (f : K →* Carrier) (hk : IsPGroup 2 f.ker)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : (K ⧸ pCore 2 K) ≃* PSL(3,F)) : False := by
  have hk' : IsPGroup 2 f.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hk
  let j := MonoidHom.quotientPCoreEquivOfSurjective (p := 2) f.rangeRestrict
    f.rangeRestrict_surjective hk'
  exact no_linear_four_section_jankoTwo f.range hF (j.symm.trans e)

/-- The J₂ row is excluded on the literal intrinsic quotient of any containing
subgroup, even without a diagram-action assumption. -/
theorem linear_four_quotient_excludes_jankoTwo_container
    {G : Type*} [Group G] [Finite G] {K Y : Subgroup G}
    (hKY : K ≤ Y) (C : Subgroup Y) (hKC : K ≤ C.map Y.subtype)
    (hlinear : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) :
    ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Carrier) := by
  rintro ⟨eC⟩
  let i : K →* C :=
    { toFun := fun k => ⟨⟨k,hKY k.property⟩,by
        obtain ⟨c,hc,he⟩ := hKC k.property
        exact (Subtype.ext he : c = ⟨(k : G),hKY k.property⟩) ▸ hc⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hi : Function.Injective i := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : C => ((z : Y) : G)) h)
  let f := eC.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 C)).comp i)
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = (pCore 2 C).comap i := by
      ext k
      change eC (QuotientGroup.mk' (pCore 2 C) (i k)) = 1 ↔ i k ∈ pCore 2 C
      rw [← map_one eC,eC.injective.eq_iff]
      exact QuotientGroup.eq_one_iff (i k)
    rw [he]
    exact pCore_isPGroup.comap_of_injective i hi
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hlinear
  exact no_linear_four_jankoTwo_map f hk hcard e

/-- The preceding carrier exclusion applied to the actual exceptional residual. -/
theorem linear_residual_excludes_jankoTwo_container
    {G : Type*} [Group G] [Finite G] {H Y : Subgroup G}
    (hHY : H ≤ Y) (C : Subgroup Y) (hRC : residual H ≤ C.map Y.subtype)
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Carrier) :=
  linear_four_quotient_excludes_jankoTwo_container ((map_subtype_le (pResidual 2 H)).trans hHY)
    C hRC (linear_residual_quotient hlinear)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
