module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeJoinCore
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.OddThreeParameter
public import Theory.GroupTheory.CoprimeQuotientNormalizer
public import Theory.GroupTheory.PrimeOrderLift
public import Theory.GroupAction.SubgroupConjugation
public import Theory.SpecificGroups.SL2.OddCoreAndRank

/-!
# The SL₂ quotient in the odd ternary extension branch

An involution in the Fitting quotient lifts to an involution of the component
fixed by its normalizing full Sylow two-subgroup. Coprime centralizer lifting
makes its centralizer surject onto the quotient. The centralizer's perfect
residual embeds into the ternary Levi subgroup SL₂(q). Dickson recognition,
with the full Sylow hypothesis in the exceptional SL₂(5) case, identifies
that residual with SL₂(q). Its trivial odd core then makes the surjection
an isomorphism.

Source: Aschbacher–Smith, A.3.21, printed pp.55–56, especially the argument
B = O(B) C_B(z)^∞ with C_B(z)^∞ = L_z in the nonquasisimple branch.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings

private theorem sl2_involution_central {r : ℕ} [Fact r.Prime] (hr : 3 < r)
    (x : SL(2,ZMod r)) (hx : orderOf x = 2) : x ∈ center SL(2,ZMod r) := by
  have hF : (2 : ZMod r) ≠ 0 := fun h =>
    Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < r)
      ((ZMod.natCast_eq_zero_iff 2 r).mp h)
  have hpow : x ^ 2 = 1 := by simpa only [hx] using pow_orderOf_eq_one x
  have hd : (Matrix.SpecialLinearGroup.toGL x).det = 1 := by
    apply Units.ext
    exact x.property
  rcases Matrix.GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one hF
      (Matrix.SpecialLinearGroup.toGL x) (by rw [←map_pow,hpow,map_one]) hd with he | he
  · have hx1 : x = 1 := Matrix.SpecialLinearGroup.toGL_injective (by simpa using he)
    simp [hx1] at hx
  · have hxneg : x = -1 := Subtype.ext (congrArg Units.val he)
    rw [hxneg]
    apply mem_center_iff.mpr
    intro y
    ext i j
    simp

private theorem involution_centralizer_surjective
    {B : Type*} [Group B] [Finite B] {q r : ℕ} [Fact q.Prime] [Fact r.Prime]
    (ho : Odd q) (hr : 3 < r)
    (hF : fittingSubgroup B = pCore q B)
    (e : (B ⧸ fittingSubgroup B) ≃* SL(2,ZMod r))
    (z : B) (hz : orderOf z = 2) :
    Function.Surjective ((QuotientGroup.mk' (fittingSubgroup B)).comp
      (centralizer ({z} : Set B)).subtype) := by
  let F := fittingSubgroup B
  let π := QuotientGroup.mk' F
  have hker : IsPGroup q π.ker := by
    rw [QuotientGroup.ker_mk']
    change IsPGroup q (fittingSubgroup B)
    rw [hF]
    exact pCore_isPGroup
  have horder : orderOf (π z) = 2 :=
    (π.orderOf_map_eq_of_coprime_of_isPGroup_ker hker z (by
      rw [hz]
      exact ho.coprime_two_right)).trans hz
  have hzC : π z ∈ center (B ⧸ F) := by
    apply mem_center_iff.mpr
    intro y
    apply e.injective
    simpa only [map_mul] using
      (mem_center_iff.mp (sl2_involution_central hr (e (π z))
        ((orderOf_injective e.toMonoidHom e.injective (π z)).trans horder))) (e y)
  let Z := zpowers z
  let : Fact (IsPGroup 2 Z) := ⟨IsPGroup.of_card (n := 1) (by simp [Z,Nat.card_zpowers,hz])⟩
  have hZc : Z.map π ≤ center (B ⧸ F) := by
    rw [MonoidHom.map_zpowers]
    exact zpowers_le.mpr hzC
  let : (Z.map π).Normal := ⟨fun x hx g => by
    rw [(mem_center_iff.mp (hZc hx)) g,mul_inv_cancel_right]
    exact hx⟩
  have hcop : Nat.Coprime 2 (Nat.card F) := by
    obtain ⟨n,hn⟩ := (show IsPGroup q F by change IsPGroup q (fittingSubgroup B); rw [hF]; exact pCore_isPGroup).exists_card_eq
    rw [hn]
    exact ho.coprime_two_left.pow_right n
  have he := normalizer_map_quotient_eq_map_normalizer 2 Z F inferInstance hcop
  change normalizer (Z.map π : Set (B ⧸ F)) = (normalizer (Z : Set B)).map π at he
  rw [(Z.map π).normalizer_eq_top,
    show normalizer (Z : Set B) = centralizer ({z} : Set B) from
      normalizer_zpowers_eq_centralizer_of_order_two z hz] at he
  intro y
  obtain ⟨b,hb,hby⟩ := show y ∈ (centralizer ({z} : Set B)).map π by rw [←he]; trivial
  exact ⟨⟨b,hb⟩,hby⟩

private theorem exists_involution_in_normalized_even
    {G : Type*} [Group G] [Finite G] (S B : Subgroup G)
    (hS : IsPGroup 2 S) (hn : S ≤ normalizer (B : Set G))
    (he : 2 ∣ Nat.card B) :
    ∃ z : G, z ∈ B ∧ orderOf z = 2 ∧ S ≤ centralizer ({z} : Set G) := by
  let _ := conjMulDistribMulActionOfLeNormalizer S B hn
  let F := FixedPoints.subgroup S B
  have hm := hS.card_modEq_card_fixedPoints B
  change Nat.card B % 2 = Nat.card F % 2 at hm
  have hd : 2 ∣ Nat.card F := Nat.dvd_of_mod_eq_zero (hm.symm.trans (Nat.mod_eq_zero_of_dvd he))
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := F) 2 hd
  refine ⟨z.val.val,z.val.property,
    (Subgroup.orderOf_coe z.val).trans ((Subgroup.orderOf_coe z).trans hz),?_⟩
  intro s hs
  apply mem_centralizer_singleton_iff.mpr
  have hh := congrArg Subtype.val (z.property (⟨s,hs⟩ : S))
  change s * z.val.val * s⁻¹ = z.val.val at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

private theorem odd_three_perfect_model
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    {q residue : ℕ} [Fact q.Prime]
    (ho : Odd q) (hR : RankThreeLocalStructure H q residue)
    (ι : G →* H) (hι : Function.Injective ι)
    (S : Sylow 2 G) (K : Subgroup G) [Group.IsPerfect K] [Nontrivial K]
    (hn : (S : Subgroup G) ≤ normalizer (K : Set G))
    (unitary : Bool)
    (hm : Chapter1.Section02.LocalModels.IsPSLSign G unitary 3 q ∨
      Chapter1.Section02.LocalModels.IsSLSign G unitary 3 q)
    (z : G) (hz : orderOf z = 2) (hK : K ≤ centralizer ({z} : Set G)) :
    3 < q ∧ Nonempty (K ≃* SL(2,ZMod q)) := by
  obtain ⟨_,_,hs⟩ := hR.involutions
  obtain ⟨_,⟨e⟩,hle⟩ := hs (ι z) ((orderOf_injective ι hι z).trans hz)
  let j : K →* centralizer ({ι z} : Set H) :=
    (ι.comp K.subtype).codRestrict _ (by
      intro x
      apply mem_centralizer_singleton_iff.mpr
      simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, ←map_mul] using congrArg ι
        (mem_centralizer_singleton_iff.mp (hK x.property)))
  let : Group.IsPerfect j.range := Group.IsPerfect.range j
  have hr : j.range ≤ primeToResidual q (centralizer ({ι z} : Set H)) :=
    (le_solvableResidual_of_isPerfect j.range).trans hle
  let f := e.toMonoidHom.comp (j.codRestrict _ (fun x => hr ⟨x,rfl⟩))
  have hf : Function.Injective f :=
    e.injective.comp (fun x y hh => Subtype.ext (hι (congrArg (fun a => a.val.val) hh)))
  have hlarge : 3 < q := by
    by_contra hn
    have he : q = 3 := by
      have := (Fact.out : q.Prime).two_le
      have := Nat.odd_iff.mp ho
      omega
    subst q
    let : Group.IsSolvable (GL (Fin 2) (ZMod 3)) := Matrix.GeneralLinearGroup.three_isSolvable
    let : Group.IsSolvable SL(2,ZMod 3) := Group.isSolvable_of_isSolvable_injective
      (Matrix.SpecialLinearGroup.toGL_injective (n := Fin 2) (R := ZMod 3))
    exact Group.IsPerfect.not_isSolvable K (Group.isSolvable_of_isSolvable_injective hf)
  refine ⟨hlarge,?_⟩
  let a : K ≃* f.range := MonoidHom.ofInjective hf
  let : Group.IsPerfect f.range := Group.IsPerfect.ofSurjective
    (f := a.toMonoidHom) a.surjective
  let : Nontrivial f.range := a.symm.nontrivial
  rcases ChapterA.RankActions.primePerfectSL2Recognition q hlarge f.range
      inferInstance inferInstance with hh | ⟨_,⟨b⟩⟩
  · exact ⟨a.trans hh.some⟩
  · let c : K ≃* SL(2,ZMod 5) := a.trans b
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    let : Fact (3 < Nat.card (ZMod 5)) := ⟨by norm_num⟩
    let : IsQuasisimple K := IsQuasisimple.of_mulEquiv c.symm
    have hfive := ChapterC.Section05.NormalizerControl.EmbeddingSelection.odd_three_sl2_five_parameter
      S K ⟨ZMod 5,inferInstance,inferInstance,Nat.card_zmod 5,⟨c⟩⟩ hn
      (Fact.out : q.Prime) ho unitary hm
    subst q
    exact ⟨c⟩

/-- The involution-centralizer residual in A.3.21 supplies an actual normalized
SL₂(q) supplement to the defining-prime Fitting kernel. -/
theorem odd_three_sl2_supplement
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    {q residue : ℕ} [Fact q.Prime]
    (ho : Odd q) (hR : RankThreeLocalStructure H q residue)
    (ι : G →* H) (hι : Function.Injective ι)
    (S : Sylow 2 G) (B : Subgroup G)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hF : fittingSubgroup B = pCore q B)
    (hquot : NoncentralFitting.PrimeSL2FittingQuotient B)
    (unitary : Bool)
    (hm : Chapter1.Section02.LocalModels.IsPSLSign G unitary 3 q ∨
      Chapter1.Section02.LocalModels.IsSLSign G unitary 3 q) :
    3 < q ∧ ∃ (K : Subgroup G) (hKB : K ≤ B),
      Nonempty (K ≃* SL(2,ZMod q)) ∧
      (S : Subgroup G) ≤ normalizer (K : Set G) ∧
      Function.Surjective ((QuotientGroup.mk' (fittingSubgroup B)).comp (inclusion hKB)) := by
  let : IsQuasisimple (B ⧸ fittingSubgroup B) :=
    NoncentralFitting.fitting_quotient_quasisimple hquot
  obtain ⟨r,hr,hr3,⟨e⟩⟩ := hquot
  let : Fact r.Prime := ⟨hr⟩
  let : Fact (3 < Nat.card (ZMod r)) := ⟨by simpa using hr3⟩
  have htwo : (2 : ZMod r) ≠ 0 := fun h =>
    Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < r)
      ((ZMod.natCast_eq_zero_iff 2 r).mp h)
  let : Nontrivial SL(2,ZMod r) := ⟨⟨-1,1,by
    intro hh
    have hd := Matrix.SpecialLinearGroup.orderOf_neg_one_eq_two htwo
    rw [hh,orderOf_one] at hd
    omega⟩⟩
  let : Nontrivial (B ⧸ fittingSubgroup B) := e.nontrivial
  have heven : 2 ∣ Nat.card B := by
    have hd := orderOf_dvd_natCard (-1 : SL(2,ZMod r))
    rw [Matrix.SpecialLinearGroup.orderOf_neg_one_eq_two htwo] at hd
    rw [←Nat.card_congr e.toEquiv] at hd
    exact hd.trans (card_quotient_dvd_card (fittingSubgroup B))
  obtain ⟨z,hzB,hz,hSz⟩ := exists_involution_in_normalized_even S B S.isPGroup' hn heven
  let zB : B := ⟨z,hzB⟩
  let CB := centralizer ({zB} : Set B)
  let C := B ⊓ centralizer ({z} : Set G)
  let j : C →* CB := (inclusion (show C ≤ B from inf_le_left)).codRestrict CB (by
    intro c
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (mem_centralizer_singleton_iff.mp c.property.2))
  have hj : Function.Surjective j := by
    intro c
    refine ⟨⟨c.val.val,⟨c.val.property,?_⟩⟩,?_⟩
    · apply mem_centralizer_singleton_iff.mpr
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp c.property)
    · rfl
  let π := QuotientGroup.mk' (fittingSubgroup B)
  let g : C →* B ⧸ fittingSubgroup B := π.comp (inclusion (show C ≤ B from inf_le_left))
  have hg : Function.Surjective g := by
    have hs := (involution_centralizer_surjective ho hr3 hF e zB
      ((Subgroup.orderOf_coe zB).symm.trans hz)).comp hj
    exact hs
  let K := (solvableResidual C).map C.subtype
  have hKC : K ≤ C := map_subtype_le _
  have hKB : K ≤ B := hKC.trans inf_le_left
  let f : K →* B ⧸ fittingSubgroup B := π.comp (inclusion hKB)
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    have hh := map_solvableResidual_eq g hg
    rw [solvableResidual_eq_top (G := B ⧸ fittingSubgroup B)] at hh
    apply top_unique
    intro y _
    obtain ⟨c,hc,hcy⟩ := show y ∈ (solvableResidual C).map g by rw [hh]; trivial
    exact ⟨⟨c.val,⟨c,hc,rfl⟩⟩,hcy⟩
  let : Group.IsPerfect K := Group.IsPerfect.map _
  let : Nontrivial K := hf.nontrivial
  have hSC : (S : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf hn (hSz.trans (centralizer ({z} : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hSK : (S : Subgroup G) ≤ normalizer (K : Set G) :=
    hSC.trans (normalizer_le_normalizer_characteristic_image C (solvableResidual C))
  obtain ⟨hq,hmodel⟩ := odd_three_perfect_model ho hR ι hι S K hSK unitary hm z hz
    (hKC.trans inf_le_right)
  exact ⟨hq,K,hKB,hmodel,hSK,hf⟩

/-- The supplement has no odd normal kernel, so the defining prime also
identifies the actual Fitting quotient. -/
theorem odd_three_fitting_quotient
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    {q residue : ℕ} [Fact q.Prime]
    (ho : Odd q) (hR : RankThreeLocalStructure H q residue)
    (ι : G →* H) (hι : Function.Injective ι)
    (S : Sylow 2 G) (B : Subgroup G)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hF : fittingSubgroup B = pCore q B)
    (hquot : NoncentralFitting.PrimeSL2FittingQuotient B)
    (unitary : Bool)
    (hm : Chapter1.Section02.LocalModels.IsPSLSign G unitary 3 q ∨
      Chapter1.Section02.LocalModels.IsSLSign G unitary 3 q) :
    3 < q ∧ Nonempty ((B ⧸ fittingSubgroup B) ≃* SL(2,ZMod q)) := by
  obtain ⟨hq,K,hKB,⟨e⟩,_,hf⟩ := odd_three_sl2_supplement ho hR ι hι S B hn hF hquot unitary hm
  let f := (QuotientGroup.mk' (fittingSubgroup B)).comp (inclusion hKB)
  have htwo : (2 : ZMod q) ≠ 0 := fun h =>
    Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < q)
      ((ZMod.natCast_eq_zero_iff 2 q).mp h)
  have hK : pPrimeCore 2 K = ⊥ :=
    (map_eq_bot_iff_of_injective _ e.injective).mp
      ((pPrimeCore_map_iso 2 e).trans (Matrix.SpecialLinearGroup.pPrimeCore_two_eq_bot htwo))
  let i : f.ker →* pCore q B :=
    ((inclusion hKB).comp f.ker.subtype).codRestrict _ (by
      intro x
      rw [←hF]
      exact (QuotientGroup.eq_one_iff _).mp x.property)
  have hi : Function.Injective i := by
    intro x y hh
    exact Subtype.ext (Subtype.ext (congrArg (fun z => z.val.val) hh))
  have hp : IsPGroup q f.ker := pCore_isPGroup.of_injective i hi
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hc : Nat.Coprime 2 (Nat.card f.ker) := by
    rw [hn]
    exact ho.coprime_two_left.pow_right n
  have hk : f.ker = ⊥ := pPrimeCore_eq_bot_iff.mp hK _ inferInstance hc
  exact ⟨hq,⟨(MulEquiv.ofBijective f ⟨(MonoidHom.ker_eq_bot_iff f).mp hk,hf⟩).symm.trans e⟩⟩

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
