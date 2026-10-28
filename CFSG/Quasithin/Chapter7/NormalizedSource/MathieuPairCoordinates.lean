module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPairSection
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition.Sections

/-!
# Four natural coordinates on the original cocode section

The sum of B/U and its specified conjugate is constructed using the two
literal quotient maps. Its surjectivity follows from P=B B^t; the known
section orders give injectivity. Commuting quotient actions make that
sum equivariant, so two natural coordinates on B/U give four on P/U.
The final helpers retain the original residual kernel and the selected
pair's Sylow image, which has order four.

NonFFSourceMathieuM24Tensor applies these constructions to the same selected
pair and original offender three-space. No tensor with the entire
six-dimensional B/U is asserted.
Source: Aschbacher--Smith, E.2.10(2), 8.2.8(4,5), printed pp.222,718--719,
refs/quasithin.pdf. Final Mathieu/J4 assembly: qt-d-1222-nonff-mathieu.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPair
open Chapter8.Section02.Normalizer.SmallOvergroups
variable {G : Type*} [Group G] [Finite G]
/-- The original pair sum map on the two equal central quotients. -/
theorem section_pair_coordinates (Y P B U : Subgroup G)
    (hBP : B ≤ P) [(U.subgroupOf P).Normal] [(U.subgroupOf B).Normal]
    [IsElementaryAbelian 2 (P ⧸ U.subgroupOf P)]
    [IsElementaryAbelian 2 (B ⧸ U.subgroupOf B)]
    (hYP : Y ≤ normalizer (P : Set G)) (hYU : Y ≤ normalizer (U : Set G))
    (t : Y) (hP : B ⊔ B.map (MulAut.conj t.val).toMonoidHom = P)
    (hcard : Nat.card (B ⧸ U.subgroupOf B) * Nat.card (B ⧸ U.subgroupOf B) =
      Nat.card (P ⧸ U.subgroupOf P)) :
    ∃ e : (Additive (B ⧸ U.subgroupOf B) × Additive (B ⧸ U.subgroupOf B)) ≃ₗ[ZMod 2]
        Additive (P ⧸ U.subgroupOf P),
      ∀ (b c : B), e (Additive.ofMul (QuotientGroup.mk' (U.subgroupOf B) b),
          Additive.ofMul (QuotientGroup.mk' (U.subgroupOf B) c)) =
        Additive.ofMul (QuotientGroup.mk' (U.subgroupOf P) (inclusion hBP b)) +
          Additive.ofMul (sectionAction Y P U hYP hYU t
            (QuotientGroup.mk' (U.subgroupOf P) (inclusion hBP c))) := by
  let Q := P ⧸ U.subgroupOf P
  let Qb := B ⧸ U.subgroupOf B
  let q := QuotientGroup.mk' (U.subgroupOf P)
  let qb := QuotientGroup.mk' (U.subgroupOf B)
  let j : Qb →* Q := QuotientGroup.quotientMapSubgroupOfOfLe le_rfl hBP
  let τ := sectionAction Y P U hYP hYU t
  let μ : Qb × Qb →* Q := j.coprod (τ.toMonoidHom.comp j)
  have hμ : Function.Surjective μ := by
    let N := μ.range.comap q
    have hB : B ≤ N.map P.subtype := by
      intro b hb
      refine ⟨⟨b,hBP hb⟩,?_,rfl⟩
      change q ⟨b,hBP hb⟩ ∈ μ.range
      refine ⟨(qb ⟨b,hb⟩,1),?_⟩
      change j (qb ⟨b,hb⟩) * τ (j 1) = _
      rw [map_one,map_one,mul_one]
      rfl
    have hC : B.map (MulAut.conj t.val).toMonoidHom ≤ N.map P.subtype := by
      rintro _ ⟨b,hb,rfl⟩
      let p : P := P.normalizerMonoidHom (inclusion hYP t) (inclusion hBP ⟨b,hb⟩)
      refine ⟨p,?_,rfl⟩
      change q p ∈ μ.range
      refine ⟨(1,qb ⟨b,hb⟩),?_⟩
      change j 1 * τ (j (qb ⟨b,hb⟩)) = _
      rw [map_one,one_mul]
      rfl
    intro x
    obtain ⟨p,rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf P) x
    have hp : p.val ∈ N.map P.subtype := (hP ▸ sup_le hB hC) p.property
    obtain ⟨z,hz,he⟩ := hp
    have hz' : z = p := Subtype.ext he
    exact hz' ▸ hz
  have hc : Nat.card (Qb × Qb) = Nat.card Q := by rw [Nat.card_prod]; exact hcard
  have hbij : Function.Bijective μ := (Nat.bijective_iff_surjective_and_card μ).mpr ⟨hμ,hc⟩
  let m : (Additive Qb × Additive Qb) →ₗ[ZMod 2] Additive Q :=
    ({ toFun x := Additive.ofMul (μ (x.1.toMul,x.2.toMul))
       map_zero' := μ.map_one
       map_add' x y := μ.map_mul _ _ } :
      (Additive Qb × Additive Qb) →+ Additive Q).toZModLinearMap 2
  have hm : Function.Bijective m := hbij
  refine ⟨LinearEquiv.ofBijective m hm,?_⟩
  intro b c
  rfl

/-- The actual sum of two conjugate sections is equivariant for every
actor whose quotient action commutes with the conjugating element. -/
theorem section_pair_equivariant (Y R P B U : Subgroup G)
    (hRY : R ≤ Y) (hBP : B ≤ P)
    [(U.subgroupOf P).Normal] [(U.subgroupOf B).Normal]
    [IsElementaryAbelian 2 (P ⧸ U.subgroupOf P)]
    [IsElementaryAbelian 2 (B ⧸ U.subgroupOf B)]
    (hYP : Y ≤ normalizer (P : Set G)) (hYU : Y ≤ normalizer (U : Set G))
    (hRB : R ≤ normalizer (B : Set G)) (t : Y)
    (hP : B ⊔ B.map (MulAut.conj t.val).toMonoidHom = P)
    (hcard : Nat.card (B ⧸ U.subgroupOf B) * Nat.card (B ⧸ U.subgroupOf B) =
      Nat.card (P ⧸ U.subgroupOf P))
    (hc : ∀ r : R, Commute (sectionAction Y P U hYP hYU (inclusion hRY r))
      (sectionAction Y P U hYP hYU t)) :
    ∃ e : (Additive (B ⧸ U.subgroupOf B) × Additive (B ⧸ U.subgroupOf B)) ≃ₗ[ZMod 2]
        Additive (P ⧸ U.subgroupOf P),
      (∀ b c : B, e (Additive.ofMul (QuotientGroup.mk' (U.subgroupOf B) b),
          Additive.ofMul (QuotientGroup.mk' (U.subgroupOf B) c)) =
        Additive.ofMul (QuotientGroup.mk' (U.subgroupOf P) (inclusion hBP b)) +
          Additive.ofMul (sectionAction Y P U hYP hYU t
            (QuotientGroup.mk' (U.subgroupOf P) (inclusion hBP c)))) ∧
      ∀ (r : R) (x y : B ⧸ U.subgroupOf B),
        e (Additive.ofMul (sectionAction R B U hRB (hRY.trans hYU) r x),
          Additive.ofMul (sectionAction R B U hRB (hRY.trans hYU) r y)) =
        Additive.ofMul (sectionAction Y P U hYP hYU (inclusion hRY r)
          (e (Additive.ofMul x,Additive.ofMul y)).toMul) := by
  obtain ⟨e,he⟩ := section_pair_coordinates Y P B U hBP hYP hYU t hP hcard
  refine ⟨e,he,?_⟩
  intro r x y
  obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf B) x
  obtain ⟨c,rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf B) y
  rw [sectionAction_apply,sectionAction_apply,he,he]
  let f := sectionAction Y P U hYP hYU
  have hi (b : B) :
      QuotientGroup.mk' (U.subgroupOf P)
        (inclusion hBP (B.normalizerMonoidHom (inclusion hRB r) b)) =
      f (inclusion hRY r) (QuotientGroup.mk' (U.subgroupOf P) (inclusion hBP b)) := rfl
  rw [hi,hi]
  simp only [toMul_add,toMul_ofMul,map_mul,ofMul_mul]
  congr 1
  apply congrArg Additive.ofMul
  simpa only [MulAut.mul_apply] using (MulEquiv.congr_fun (hc r).eq
    (QuotientGroup.mk' (U.subgroupOf P) (inclusion hBP c))).symm

/-- Two natural coordinates on each original summand give four natural
coordinates on the whole section; the conjugating element is retained. -/
theorem section_four_coordinates {N : Type*} [AddCommGroup N] [Module (ZMod 2) N]
    (Y R P B U : Subgroup G) (hRY : R ≤ Y) (hBP : B ≤ P)
    [(U.subgroupOf P).Normal] [(U.subgroupOf B).Normal]
    [IsElementaryAbelian 2 (P ⧸ U.subgroupOf P)]
    [IsElementaryAbelian 2 (B ⧸ U.subgroupOf B)]
    (hYP : Y ≤ normalizer (P : Set G)) (hYU : Y ≤ normalizer (U : Set G))
    (hRB : R ≤ normalizer (B : Set G)) (t : Y)
    (hP : B ⊔ B.map (MulAut.conj t.val).toMonoidHom = P)
    (hcard : Nat.card (B ⧸ U.subgroupOf B) * Nat.card (B ⧸ U.subgroupOf B) =
      Nat.card (P ⧸ U.subgroupOf P))
    (hc : ∀ r : R, Commute (sectionAction Y P U hYP hYU (inclusion hRY r))
      (sectionAction Y P U hYP hYU t))
    (eB : Additive (B ⧸ U.subgroupOf B) ≃ₗ[ZMod 2] (N × N))
    (π : R →* (N ≃ₗ[ZMod 2] N))
    (heB : ∀ (r : R) (z : B ⧸ U.subgroupOf B),
      eB (Additive.ofMul (sectionAction R B U hRB (hRY.trans hYU) r z)) =
        (π r (eB (Additive.ofMul z)).1,π r (eB (Additive.ofMul z)).2)) :
    ∃ e : Additive (P ⧸ U.subgroupOf P) ≃ₗ[ZMod 2] (Fin 2 × Fin 2 → N),
      ∀ (r : R) (z : P ⧸ U.subgroupOf P),
        e (Additive.ofMul (sectionAction Y P U hYP hYU (inclusion hRY r) z)) =
          fun j => π r (e (Additive.ofMul z) j) := by
  obtain ⟨f,_,hf⟩ := section_pair_equivariant Y R P B U hRY hBP hYP hYU hRB t hP hcard hc
  let a := LinearEquiv.piFinTwo (ZMod 2) (fun _ : Fin 2 => N)
  let b := LinearEquiv.piFinTwo (ZMod 2) (fun _ : Fin 2 => (Fin 2 → N))
  let c : ((N × N) × (N × N)) ≃ₗ[ZMod 2] (Fin 2 → Fin 2 → N) :=
    (a.symm.prodCongr a.symm).trans b.symm
  let d : (Fin 2 → Fin 2 → N) ≃ₗ[ZMod 2] (Fin 2 × Fin 2 → N) :=
    LinearEquiv.curry (ZMod 2) N (Fin 2) (Fin 2) |>.symm
  let e := (f.symm.trans (eB.prodCongr eB)).trans (c.trans d)
  refine ⟨e,?_⟩
  intro r z
  obtain ⟨⟨x,y⟩,hx⟩ := f.surjective (Additive.ofMul z)
  have hz : z = (f (x,y)).toMul := congrArg Additive.toMul hx.symm
  have hh := hf r x.toMul y.toMul
  simp only [ofMul_toMul] at hh
  rw [hz,←hh]
  simp only [ofMul_toMul]
  change d (c ((eB.prodCongr eB) (f.symm (f _)))) =
    fun j => π r (d (c ((eB.prodCongr eB) (f.symm (f _)))) j)
  rw [f.symm_apply_apply,f.symm_apply_apply]
  change d (c (eB _,eB _)) = _
  rw [heB,heB]
  ext ⟨j,k⟩
  fin_cases j <;> fin_cases k <;> rfl

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPair
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPair
open Chapter8.Section02.Normalizer.SmallOvergroups
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Commuting images of the original residual and pair, using the exact
residual kernel and the original commutator containment. -/
theorem commuting_pair_images {A : Type*} [Group A] (R I Y : Subgroup G)
    (hRY : R ≤ Y) (hIY : I ≤ Y) (f : Y →* A)
    (hk : (f.comp (inclusion hRY)).ker = pCore 2 R)
    (hc : ⁅R,I⁆ ≤ R.pCoreIn 2) (r : R) (i : I) :
    Commute (f (inclusion hRY r)) (f (inclusion hIY i)) := by
  obtain ⟨c,hc,he⟩ := hc (commutator_mem_commutator r.property i.property)
  have hcy : inclusion hRY c = ⁅inclusion hRY r,inclusion hIY i⁆ := Subtype.ext he
  have hf : f (inclusion hRY c) = 1 := by
    exact show c ∈ (f.comp (inclusion hRY)).ker from hk.symm ▸ hc
  rw [hcy,map_commutatorElement] at hf
  exact commutatorElement_eq_one_iff_mul_comm.mp hf

/-- The selected degree-two pair has even image under any action with
its exact two-core kernel. This uses its literal selected Sylow image. -/
theorem selected_two_image_even {H T M V I : Subgroup G}
    [IsElementaryAbelian 2 V] {i : I} {S : Sylow 2 I}
    (s : Selected H T M V I 2 i S)
    {A : Type*} [Group A] (f : I →* A) (hk : f.ker = pCore 2 I) :
    2 ∣ Nat.card f.range := by
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  let e := subgroupOfEquivOfLe hVI
  have hp : IsPGroup 2 (V.subgroupOf I) :=
    (IsElementaryAbelian.isPGroup 2 V).of_injective e.toMonoidHom e.injective
  have hi : IsPGroup 2 (coreImage I V) :=
    hp.map (QuotientGroup.mk' (pCore 2 I))
  obtain ⟨n,hn⟩ := hi.exists_card_eq
  have hr := s.rank_eq
  rw [rank,hn,Nat.log_pow Nat.one_lt_two] at hr
  have hq : 2 ∣ Nat.card (I ⧸ pCore 2 I) :=
    (show 2 ∣ Nat.card (coreImage I V) from
      by rw [hn,hr]; decide).trans (card_subgroup_dvd_card _)
  let c := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange f)
  rwa [Nat.card_congr c.toEquiv] at hq

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPair
