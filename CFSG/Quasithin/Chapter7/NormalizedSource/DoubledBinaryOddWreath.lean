module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddSymplectic
public import Theory.SpecificGroups.SymplecticFour.OddFrattiniEight
public import Theory.GroupTheory.BinaryFrattiniExtension
public import Theory.SpecificGroups.PSL4.FermatSeven
import all CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddSporadic
import all Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.Basic
import all Theory.SpecificGroups.SymplecticFour.OddFrattiniEight
import all Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.TwoPrimary.PlaneGeometry

/-!
# The odd symplectic outer exclusion for the original binary-three residual

The odd-index plane-pair stabilizer in Sp₄(p) contains a Sylow subgroup
R wr C₂, where R is a Sylow two-subgroup of SL₂(p). Its elementary quotient
is R/Φ(R) × C₂, of order at most eight. The literal projective map kills
only the diagonal scalar, which already lies in the kernel of this quotient.
Thus the quotient is also the full Frattini quotient of the projective Sylow.

An involution outside the base has scalar product of its two coordinates.
The scalar minus one is a square in every R, so this product has trivial
Frattini image. The involution images therefore lie in the union of the
base and the swap axis, a set of at most six elements. Identity and swap
give two distinct images. When the Frattini quotient has order eight,
this invariant subset excludes an order-seven automorphism; the smaller
quotients exclude seven directly. The Burnside basis kernel is a two-group.

Sylow restriction and descent through the entire component center exclude
the original SL₃(2) outer section. The Chapter12 application retains the
same H-star actor, orbit, component and odd residual. Odd G₂, Fermat PSL₄
and Mersenne PSU₄ are the three remaining outer families. In the placed
component branch, the retained binary-three section and the checked
Fermat-field order formula also exclude the actual PSL₄ model.

The proof-only imports intentionally extend the existing plane coordinates,
rank-one Frattini bound and involution-image argument without changing their
public boundaries. Source: Aschbacher--Smith 4.4.10--11, 7.3.4 and 7.6.1,
printed pp.621,699,702, refs/quasithin.pdf. The imported matrix counts retain
the ATLAS attribution and license in LICENSES/ATLAS.txt.
-/

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
public noncomputable section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddWreath
open BinaryWreathFrattini
private abbrev C2 := Multiplicative (ZMod 2)
private instance (R : Type*) [Group R] [Finite R] : Finite (W R) :=
  Finite.of_equiv ((R × R) × C2) SemidirectProduct.equivProd.symm
variable {R : Type*} [Group R] [Finite R]

private def quotientMap (hR : IsPGroup 2 R) : W R →* (R ⧸ frattini R) × C2 := by
  let : Fact (IsPGroup 2 R) := ⟨hR⟩
  let : IsElementaryAbelian 2 (R ⧸ frattini R) := isElementaryAbelian_quotient_frattini
  exact {
    toFun := fun x => (QuotientGroup.mk' (frattini R) (x.left.1*x.left.2),x.right)
    map_one' := by simp
    map_mul' := by
      intro x y
      apply Prod.ext
      · change QuotientGroup.mk' (frattini R)
          ((x.left * action x.right y.left).1 * (x.left * action x.right y.left).2) = _
        have hc : x.right = 1 ∨ x.right = Multiplicative.ofAdd 1 := by
          exact (show ∀ c : C2, c=1 ∨ c=Multiplicative.ofAdd 1 from by decide) x.right
        rcases hc with hc | hc <;>
          simp [action,hc,map_mul,mul_comm,mul_left_comm,mul_assoc]
      · rfl }

private theorem quotientMap_apply (hR : IsPGroup 2 R) (x : W R) :
    quotientMap hR x = (QuotientGroup.mk' (frattini R) (x.left.1*x.left.2),x.right) := rfl

private theorem quotientMap_surjective (hR : IsPGroup 2 R) : Function.Surjective (quotientMap hR) := by
  rintro ⟨v,c⟩
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (frattini R) v
  exact ⟨⟨(x,1),c⟩,by simp [quotientMap_apply]⟩

private theorem quotient_no_seven {P : Type*} [Group P] [Finite P]
    (hR : IsPGroup 2 R) (hsmall : Nat.card (R ⧸ frattini R) ≤ 4)
    (j : W R →* P) (hj : Function.Surjective j)
    (hk : j.ker ≤ (quotientMap hR).ker)
    (hsq : ∀ x : W R, j x ^ 2 = 1 → x.right ≠ 1 →
      QuotientGroup.mk' (frattini R) (x.left.1*x.left.2)=1) :
    ¬ 7 ∣ Nat.card (MulAut P) := by
  let hP := (BinaryWreathFrattini.isPGroup hR).of_surjective j hj
  let : Fact (IsPGroup 2 R) := ⟨hR⟩
  let : IsElementaryAbelian 2 (R ⧸ frattini R) := isElementaryAbelian_quotient_frattini
  let E := (R ⧸ frattini R) × C2
  let : IsElementaryAbelian 2 C2 := {
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      decide +kernel }
  let : IsElementaryAbelian 2 E := {
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      apply Prod.ext
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 (R ⧸ frattini R)) x.1
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 C2) x.2 }
  let f : P →* E := j.liftOfSurjective hj ⟨quotientMap hR,hk⟩
  have hfac (x : W R) : f (j x) = quotientMap hR x := by simp [f]
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨x,rfl⟩ := quotientMap_surjective hR v
    exact ⟨j x,hfac x⟩
  have hphi := Theory.GroupTheory.frattini_le_ker_of_square_image f (fun x =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 E) _)
  have hb : Nat.card (P ⧸ frattini P) ≤ Nat.card E := by
    let : Fact (IsPGroup 2 P) := ⟨hP⟩
    let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
    exact (BinaryFrattiniExtension.elementary_card_le
      ((QuotientGroup.mk' (frattini P)).comp j)
      ((QuotientGroup.mk'_surjective _).comp hj)).trans
      (by simpa [E,Nat.card_prod,Nat.mul_comm,C2] using BinaryWreathFrattini.card_frattini_le hR)
  have hphi_eq : frattini P = f.ker := by
    apply eq_of_le_of_card_ge hphi
    have h1 := card_eq_card_quotient_mul_card_subgroup (frattini P)
    have h2 := card_eq_card_quotient_mul_card_subgroup f.ker
    have hq := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
    rw [hq] at h2
    have hpos := Nat.card_pos (α:=P ⧸ frattini P)
    nlinarith
  let e : P ⧸ frattini P ≃* E :=
    (QuotientGroup.quotientMulEquivOfEq hphi_eq).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have he (x : P) : e (QuotientGroup.mk' (frattini P) x) = f x := rfl
  have hbound : Nat.card (P ⧸ frattini P) ≤ 8 := by
    apply hb.trans
    simpa [E,Nat.card_prod,C2] using Nat.mul_le_mul_right 2 hsmall
  by_cases h8 : Nat.card (P ⧸ frattini P)=8
  · apply DoubledBinaryOddSporadic.no_seven_aut hP h8
    · apply Nat.add_one_le_iff.mpr
      let x : P := j (SemidirectProduct.inr (Multiplicative.ofAdd 1))
      have hx : x^2=1 := by
        dsimp [x]
        rw [←map_pow,←map_pow,show (Multiplicative.ofAdd (1 : ZMod 2))^2=1 by decide,
          map_one,map_one]
      let a : DoubledBinaryOddSporadic.involutionImages (P:=P) :=
        ⟨QuotientGroup.mk' (frattini P) 1,1,one_pow 2,rfl⟩
      let b : DoubledBinaryOddSporadic.involutionImages (P:=P) :=
        ⟨QuotientGroup.mk' (frattini P) x,x,hx,rfl⟩
      have hne : a ≠ b := by
        intro hab
        have hh := congrArg (fun z => (e z.val).2) hab
        change (f 1).2 = (f x).2 at hh
        rw [map_one] at hh
        change (1 : C2) = (f (j _)).2 at hh
        rw [hfac] at hh
        exact (by decide : (1:C2) ≠ Multiplicative.ofAdd 1) hh
      let : Nontrivial (DoubledBinaryOddSporadic.involutionImages (P:=P)) := ⟨⟨a,b,hne⟩⟩
      exact Finite.one_lt_card
    · let I : Set E := {v | v.2=1 ∨ v.1=1}
      let a : DoubledBinaryOddSporadic.involutionImages (P:=P) → I := fun v =>
        ⟨e v,by
          obtain ⟨y,hy,hv⟩ := v.property
          rw [←hv]
          obtain ⟨x,rfl⟩ := hj y
          rw [he,hfac,quotientMap_apply]
          by_cases hc : x.right=1
          · exact Or.inl hc
          · exact Or.inr (hsq x hy hc)⟩
      have ha : Function.Injective a := fun x y h =>
        Subtype.ext (e.injective (congrArg Subtype.val h))
      apply (Nat.card_le_card_of_injective a ha).trans
      have hu : I = {v : E | v.2=1} ∪ {v : E | v.1=1} := rfl
      let a₁ : {v : E // v.2=1} ≃ (R ⧸ frattini R) := {
        toFun := fun v => v.val.1
        invFun := fun v => ⟨(v,1),rfl⟩
        left_inv := fun v => Subtype.ext (Prod.ext rfl v.property.symm)
        right_inv := fun _ => rfl }
      let a₂ : {v : E // v.1=1} ≃ C2 := {
        toFun := fun v => v.val.2
        invFun := fun v => ⟨(1,v),rfl⟩
        left_inv := fun v => Subtype.ext (Prod.ext v.property.symm rfl)
        right_inv := fun _ => rfl }
      have hc₁ := Nat.card_congr a₁
      have hc₂ := Nat.card_congr a₂
      change I.ncard ≤ 6
      rw [hu]
      apply (Set.ncard_union_le _ _).trans
      change Nat.card {v : E // v.2=1} + Nat.card {v : E // v.1=1} ≤ 6
      rw [hc₁,hc₂]
      have hc : Nat.card C2 = 2 := by simp [C2]
      omega
  · let : Fact (IsPGroup 2 P) := ⟨hP⟩
    let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
    obtain ⟨n,hn⟩ := (hP.to_quotient (frattini P)).exists_card_eq
    have hn2 : n ≤ 2 := by
      by_contra! h
      have hh := Nat.pow_le_pow_right (by decide : 0<2) h
      omega
    have hsmall' : Nat.card (P ⧸ frattini P) ≤ 4 := by
      rw [hn]
      exact Nat.pow_le_pow_right (by decide) hn2
    let α := quotientAut (frattini P)
    have hcop : Nat.Coprime 7 (Nat.card α.ker) := by
      obtain ⟨k,hk⟩ := (isPGroup_quotientAut_frattini_kernel hP).exists_card_eq
      rw [hk]
      exact (by decide : Nat.Coprime 7 2).pow_right k
    have hcount : Nat.card α.ker * Nat.card α.range = Nat.card (MulAut P) := by
      rw [←index_ker]; exact α.ker.card_mul_index
    intro hd
    have hh := (hcop.dvd_of_dvd_mul_left (hcount.symm ▸ hd)).trans α.range.card_subgroup_dvd_card
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ n hn] at hh
    interval_cases n <;> norm_num [Fin.prod_univ_succ] at hh


open Theory.SpecificGroups.SymplecticFour
open CentralCovers.OddPrime (negIdentity PSp)
open CentralCovers.OddPrime.LargeSections.TwoPrimary
variable {p : ℕ} [Fact p.Prime]
private abbrev SL := Matrix.SpecialLinearGroup (Fin 2) (ZMod p)

private def wreathEquiv : W (SL (p:=p)) ≃*
    ((SL (p:=p)) × (SL (p:=p))) ⋊[PlaneGeometry.action] C2 := by
  have hact : BinaryWreathFrattini.action (R:=SL (p:=p)) = PlaneGeometry.action := by
    apply MonoidHom.ext
    intro c
    obtain ⟨c,rfl⟩ := (Multiplicative.ofAdd : ZMod 2 ≃ C2).surjective c
    fin_cases c
    · exact (map_one _).trans (map_one _).symm
    · exact PlaneGeometry.action_generator.symm
  exact SemidirectProduct.congr (MulEquiv.refl _) (MulEquiv.refl _) (by intro c; rw [hact]; rfl)

private def wreathEmbedding : W (SL (p:=p)) →* Sp (ZMod p) :=
  PlaneGeometry.inclusion.comp wreathEquiv.toMonoidHom

private theorem wreathEmbedding_injective : Function.Injective (wreathEmbedding (p:=p)) := by
  exact PlaneGeometry.inclusion_injective.comp wreathEquiv.injective

private theorem wreathEmbedding_inl (a b : SL (p:=p)) :
    wreathEmbedding (SemidirectProduct.inl (a,b)) = PlaneGeometry.pairHom (a,b) := by
  simp [wreathEmbedding,wreathEquiv,SemidirectProduct.congr]

private theorem wreathEmbedding_range :
    (wreathEmbedding (p:=p)).range = (PlaneGeometry.inclusion (F:=ZMod p)).range := by
  unfold wreathEmbedding
  rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr wreathEquiv.surjective,
    ←MonoidHom.range_eq_map]

private theorem negative_pair :
    wreathEmbedding (p:=p) (SemidirectProduct.inl (-1,-1)) = negIdentity (ZMod p) := by
  rw [wreathEmbedding_inl]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PlaneGeometry.pairHom,PlaneGeometry.pairMatrix,negIdentity]

private theorem wreathEmbedding_central (x : W (SL (p:=p)))
    (hx : wreathEmbedding x ∈ center (Sp (ZMod p))) :
    x=1 ∨ x=SemidirectProduct.inl (-1,-1) := by
  rcases (CentralCovers.OddPrime.mem_center_iff _).mp hx with hx | hx
  · exact Or.inl (wreathEmbedding_injective (hx.trans (map_one _).symm))
  · exact Or.inr (wreathEmbedding_injective (hx.trans negative_pair.symm))

private theorem negative_square (R : Sylow 2 (SL (p:=p))) :
    ∃ z : R, (z : SL (p:=p)) ^ 2 = -1 := by
  let t : SL (p:=p) := ⟨!![0,1;-1,0],by simp [Matrix.det_fin_two]⟩
  have ht : t^2 = -1 := by
    rw [pow_two]
    apply Subtype.ext
    change (!![0,1;-1,0] : Matrix (Fin 2) (Fin 2) (ZMod p)) * !![0,1;-1,0] = -1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]
  have hz : (-1 : SL (p:=p)) ∈ center (SL (p:=p)) := by
    apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
    refine ⟨-1,by simp,?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_neg,Matrix.scalar_apply]
  exact BinaryFrattiniExtension.central_square_in_sylow R hz ht (by simp)

private theorem wreath_range_odd_index (R : Sylow 2 (SL (p:=p))) :
    ¬ 2 ∣ (BinaryWreathFrattini.map (R : Subgroup (SL (p:=p))).subtype).range.index := by
  let f := BinaryWreathFrattini.map (R : Subgroup (SL (p:=p))).subtype
  have hf := BinaryWreathFrattini.map_injective _ (R : Subgroup (SL (p:=p))).subtype_injective
  have hc : Nat.card f.range = Nat.card R ^ 2 * 2 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
      SemidirectProduct.card,Nat.card_prod]
    simp [pow_two]
  have hi : f.range.index = (R : Subgroup (SL (p:=p))).index ^ 2 := by
    have hh := f.range.card_mul_index
    rw [hc,SemidirectProduct.card,Nat.card_prod] at hh
    have hC : Nat.card C2=2 := by simp [C2]
    change Nat.card R ^ 2 * 2 * f.range.index =
      (Nat.card (SL (p:=p)) * Nat.card (SL (p:=p))) * Nat.card C2 at hh
    rw [hC,←(R : Subgroup (SL (p:=p))).card_mul_index] at hh
    have hp := Nat.card_pos (α:=R)
    nlinarith
  rw [hi]
  exact fun h => R.not_dvd_index (Nat.prime_two.dvd_of_dvd_pow h)

private def sylowEmbedding (R : Sylow 2 (SL (p:=p))) : W R →* Sp (ZMod p) :=
  wreathEmbedding.comp (BinaryWreathFrattini.map (R : Subgroup (SL (p:=p))).subtype)

private theorem sylowEmbedding_injective (R : Sylow 2 (SL (p:=p))) :
    Function.Injective (sylowEmbedding R) :=
  wreathEmbedding_injective.comp (BinaryWreathFrattini.map_injective _ Subtype.val_injective)

private theorem sylowEmbedding_odd_index (ho : Odd p) (R : Sylow 2 (SL (p:=p))) :
    ¬ 2 ∣ (sylowEmbedding R).range.index := by
  rw [sylowEmbedding,MonoidHom.range_comp]
  have he := (BinaryWreathFrattini.map (R : Subgroup (SL (p:=p))).subtype).range.index_map_of_injective
    (f:=wreathEmbedding (p:=p)) wreathEmbedding_injective
  rw [he,wreathEmbedding_range]
  exact Nat.prime_two.not_dvd_mul (wreath_range_odd_index R)
    (OddFrattiniEight.odd_index ho).not_two_dvd_nat

private def projectiveSylowMap (R : Sylow 2 (SL (p:=p))) : W R →* PSp (ZMod p) :=
  (QuotientGroup.mk' (center (Sp (ZMod p)))).comp (sylowEmbedding R)

private theorem projectiveSylow_kernel (R : Sylow 2 (SL (p:=p))) :
    (projectiveSylowMap R).ker ≤ (quotientMap R.isPGroup').ker := by
  intro x hx
  have hx' : wreathEmbedding
      (BinaryWreathFrattini.map (R : Subgroup (SL (p:=p))).subtype x) ∈ center (Sp (ZMod p)) :=
    (QuotientGroup.eq_one_iff _).mp hx
  rcases wreathEmbedding_central _ hx' with hx' | hx'
  · have he : x=1 := (BinaryWreathFrattini.map_injective _ Subtype.val_injective)
      (hx'.trans (map_one _).symm)
    rw [he]
    exact (quotientMap R.isPGroup').map_one
  · have hleft := congrArg SemidirectProduct.left hx'
    have hright := congrArg SemidirectProduct.right hx'
    have hprod : x.left.1*x.left.2=1 := by
      apply Subtype.ext
      change (x.left.1 : SL (p:=p)) * (x.left.2 : SL (p:=p)) = 1
      rw [show (x.left.1 : SL (p:=p)) = -1 from congrArg Prod.fst hleft,
        show (x.left.2 : SL (p:=p)) = -1 from congrArg Prod.snd hleft]
      simp
    change quotientMap R.isPGroup' x = 1
    rw [quotientMap_apply,hprod,map_one]
    exact Prod.ext rfl hright

private theorem projectiveSylow_square (R : Sylow 2 (SL (p:=p)))
    (x : W R) (hx : projectiveSylowMap R x ^ 2 = 1) (hc : x.right ≠ 1) :
    QuotientGroup.mk' (frattini R) (x.left.1*x.left.2)=1 := by
  have hcentral : wreathEmbedding
      (BinaryWreathFrattini.map (R : Subgroup (SL (p:=p))).subtype (x^2)) ∈ center (Sp (ZMod p)) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change projectiveSylowMap R (x^2)=1
    rwa [map_pow]
  have hc' : x.right = Multiplicative.ofAdd 1 := by
    exact ((show ∀ c : C2, c=1 ∨ c=Multiplicative.ofAdd 1 from by decide) x.right).resolve_left hc
  have hmul : (BinaryWreathFrattini.map (R : Subgroup (SL (p:=p))).subtype (x^2)).left.1 =
      (x.left.1 : SL (p:=p)) * (x.left.2 : SL (p:=p)) := by
    rw [BinaryWreathFrattini.map,SemidirectProduct.map_left,pow_two,SemidirectProduct.mul_left]
    simp [action,hc']
  rcases wreathEmbedding_central _ hcentral with h | h
  · have he : x.left.1*x.left.2=1 := Subtype.ext (by
      simpa only [hmul,SemidirectProduct.one_left,SemidirectProduct.left_inl,Prod.fst_one,Subgroup.coe_mul,Subgroup.coe_one] using congrArg (fun y : W (SL (p:=p)) => y.left.1) h)
    rw [he,map_one]
  · obtain ⟨z,hz⟩ := negative_square R
    have he : x.left.1*x.left.2=z^2 := Subtype.ext (by
      rw [show (z^2 : R).val = (z : SL (p:=p))^2 from rfl,hz]
      simpa only [hmul,SemidirectProduct.one_left,SemidirectProduct.left_inl,Prod.fst_one,Subgroup.coe_mul,Subgroup.coe_one] using congrArg (fun y : W (SL (p:=p)) => y.left.1) h)
    let : Fact (IsPGroup 2 R) := ⟨R.isPGroup'⟩
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [he]
    exact pth_power_mem_frattini_of_isPGroup (p:=2) z

/-- Seven is absent from the actual odd-prime projective symplectic Sylow automorphism group. -/
theorem symplectic_four_sylow_no_seven (ho : Odd p) (P : Sylow 2 (PSp (ZMod p))) :
    ¬ 7 ∣ Nat.card (MulAut P) := by
  let R : Sylow 2 (SL (p:=p)) := default
  let a := sylowEmbedding R
  let htwo : IsPGroup 2 a.range := (BinaryWreathFrattini.isPGroup R.isPGroup').of_surjective
    a.rangeRestrict a.rangeRestrict_surjective
  let S : Sylow 2 (Sp (ZMod p)) := htwo.toSylow (sylowEmbedding_odd_index ho R)
  let π := QuotientGroup.mk' (center (Sp (ZMod p)))
  let Q := S.mapSurjective (f:=π) (QuotientGroup.mk'_surjective _)
  let j : W R →* Q := (π.subgroupMap a.range).comp a.rangeRestrict
  have hj : Function.Surjective j := (π.subgroupMap_surjective a.range).comp a.rangeRestrict_surjective
  have hjval (x : W R) : (j x : PSp (ZMod p)) = projectiveSylowMap R x := rfl
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have hp2 := (Fact.out : p.Prime).two_le
    have hpne : p ≠ 2 := by rintro rfl; norm_num at ho
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega) hd
  have hno := quotient_no_seven R.isPGroup' (OddFrattiniEight.sl2_frattini_le_four h2 R) j hj
    (fun x hx => projectiveSylow_kernel R (congrArg Subtype.val hx))
    (fun x hx hc => projectiveSylow_square R x (congrArg Subtype.val hx) hc)
  rw [Nat.card_congr (MulAut.congr (P.equiv Q)).toEquiv]
  exact hno


/-- Field and group markings transfer the same Sylow obstruction. -/
theorem symplectic_four_sylow_no_seven_of_model {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hm : ClassicalGroup.IsPSp Q 2 p)
    (P : Sylow 2 Q) : ¬ 7 ∣ Nat.card (MulAut P) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let a : F ≃+* ZMod p := (ZMod.ringEquivOfPrime F hp
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let b : Q ≃* PSp (ZMod p) := e.trans (CentralCovers.OddPrime.fieldEquivPSp a)
  let R := P.mapSurjective (f:=b.toMonoidHom) b.surjective
  let c : P ≃* R := P.equivMapOfInjective b.toMonoidHom b.injective
  rw [Nat.card_congr (MulAut.congr c).toEquiv]
  exact symplectic_four_sylow_no_seven ho R

private instance : IsSimpleGroup BinaryLinearThree.Group := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  exact Matrix.PSL3Two.equiv.isSimpleGroup
private instance : Group.IsPerfect BinaryLinearThree.Group := Atlas.sl_perfect 3 (by decide)

/-- The original binary-three simple section cannot survive on the outer group
of an odd-prime symplectic four-space. -/
theorem symplectic_four_no_outer_section {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hm : ClassicalGroup.IsPSp Q 2 p)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* BinaryLinearThree.Group) :
    ¬ Function.Surjective f := by
  intro hf
  let P : Sylow 2 Q := default
  let : Group.IsSolvable (fixingSubgroup (MulAut Q) (P : Set Q)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  have hd := MulAut.simple_outer_section_card_dvd_sylow_aut P
    (Group.IsPerfect.not_isSolvable BinaryLinearThree.Group) U f hf
  apply symplectic_four_sylow_no_seven_of_model hp ho hm P
  apply dvd_trans ?_ hd
  rw [Matrix.PSL3Two.card_SL]
  decide

/-- Central descent retains the entire center of the original component. -/
theorem symplectic_four_cover_exclusion {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinearThree.Group,
      Function.Surjective f) :
    ∀ p : ℕ, p.Prime → Odd p → ¬ ClassicalGroup.IsPSp (K ⧸ center K) 2 p := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  obtain ⟨U,f,hf⟩ := ho
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let a := U.equivMapOfInjective j
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  intro p hp hpodd hm
  exact symplectic_four_no_outer_section hp hpodd hm _ (f.comp a.symm.toMonoidHom)
    (hf.comp a.symm.surjective)

/-- The literal binary-three section also excludes the Fermat linear-four
model in the placed-component branch. -/
theorem fermat_linear_four_no_section {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} (hp : ∃ k : ℕ, p = 2 ^ (2 ^ k) + 1) (hm : ClassicalGroup.IsPSL Q 4 p)
    (U : Subgroup Q) (f : U →* BinaryLinearThree.Group) : ¬ Function.Surjective f := by
  intro hf
  have hd : 7 ∣ Nat.card Q := by
    apply dvd_trans ?_ ((card_dvd_of_surjective f hf).trans U.card_subgroup_dvd_card)
    rw [Matrix.PSL3Two.card_SL]
    decide
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  rw [Nat.card_congr e.toEquiv] at hd
  exact Theory.SpecificGroups.PSL4.fermat_seven_not_dvd hp hF hd


/-- The three remaining outer families retain their actual field and group markings. -/
inductive RemainingOuterModel (Q : Type*) [Group Q] : Prop
  | g2_odd (p : ℕ) (hp : p.Prime) (ho : Odd p) (iso : ClassificationModels.IsG2At Q p)
  | linear_four (p : ℕ) (hp : p.Prime) (hf : ∃ k : ℕ, p = 2 ^ (2 ^ k) + 1)
      (iso : ClassicalGroup.IsPSL Q 4 p)
  | unitary_four (p : ℕ) (hp : p.Prime) (hm : ∃ k : ℕ, p + 1 = 2 ^ k)
      (iso : ClassicalGroup.IsPSU Q 4 p)

/-- Inspect the same component's full catalogue after the odd symplectic exclusion. -/
theorem remaining_outer_models {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (hm : ChapterA.Section02.IsTheoremBModel (K ⧸ center K))
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinearThree.Group,
      Function.Surjective f) : RemainingOuterModel (K ⧸ center K) := by
  cases DoubledBinaryOddSymplectic.remaining_outer_models hm ho with
  | symplectic_odd p hp hq e => exact (symplectic_four_cover_exclusion ho p hp hq e).elim
  | g2_odd p hp hq e => exact .g2_odd p hp hq e
  | linear_four p hp hf e => exact .linear_four p hp hf e
  | unitary_four p hp hf e => exact .unitary_four p hp hf e

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddWreath
