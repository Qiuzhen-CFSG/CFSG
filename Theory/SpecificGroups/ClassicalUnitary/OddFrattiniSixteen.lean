module
public import Theory.GroupTheory.BalancedWreathFrattini
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourCardinality
public import Theory.SpecificGroups.ClassicalUnitary.OddFourRanks.Torus
public import Theory.Representation.DegreeTwoFrattini
public import Theory.SpecificGroups.OddClassicalSylowFrattini

/-!
# Four Frattini generators for odd-prime unitary four-space Sylow subgroups

The determinant-one pairs of two-dimensional unitary isometries, extended
by the block swap, embed in the actual special unitary group. Their index
is p⁴(p²+1)(p²-p+1)/2 and is odd for every odd prime p, including p = 3.
The determinant splits over the norm-one scalars. The constrained wreath
bound and the faithful degree-two bound give a Sylow Frattini quotient of
order at most sixteen. Orthonormal transport and the literal projective
map preserve this bound for every stored Hermitian form.

This supplies the final unitary row of the exterior outer-section exclusion
in Aschbacher--Smith 4.4.10--11, printed p.621 of refs/quasithin.pdf. The
finite linear-group counts use the licensed ATLAS support; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

open Subgroup Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.OddFundamental
open Theory.SpecificGroups.ClassicalUnitary
public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.OddFrattiniSixteen
variable {F : Type*} [Field F] (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "U₂" => HermitianForm.unitarySubgroup (form σ hσ 2)
local notation "SU₄" => HermitianForm.specialSubgroup (form σ hσ 4)
local notation "C" => OddFourRanks.normOne (form σ hσ 4)
local notation "C2" => Multiplicative (ZMod 2)

private theorem det_norm (A : U₂) : σ (GeneralLinearGroup.det A.val : F) =
    (GeneralLinearGroup.det A.val : F)⁻¹ := by
  have hu := (form σ hσ 2).mem_unitarySubgroup_iff A.val |>.mp A.property
  have hd := congrArg Matrix.det hu
  have ha : ((form σ hσ 2).conjTranspose A.val.val).det = σ A.val.val.det := by
    change (A.val.val.transpose.map (σ : F →+* F)).det = _
    exact ((σ : F →+* F).map_det A.val.val.transpose).symm.trans
      (congrArg σ (Matrix.det_transpose _))
  simp only [Matrix.det_mul] at hd
  have hform : (form σ hσ 2).form.det = 1 := Matrix.det_one
  rw [hform,mul_one,ha] at hd
  exact (mul_eq_one_iff_eq_inv₀ (Units.ne_zero (GeneralLinearGroup.det A.val))).mp hd

private def det : U₂ →* C :=
  (GeneralLinearGroup.det.comp (form σ hσ 2).unitarySubgroup.subtype).codRestrict _
    (det_norm σ hσ)

private def diagonal (u : Fˣ) : GL (Fin 2) F :=
  ⟨!![u,0;0,1],!![u⁻¹,0;0,1],by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_two],by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_two]⟩

private def detSection : C →* U₂ where
  toFun u := ⟨diagonal u.val,by
    rw [HermitianForm.mem_unitarySubgroup_iff]
    change (form σ hσ 2).conjTranspose (diagonal u.val).val * 1 * (diagonal u.val).val = 1
    rw [mul_one]
    have hu := OddFourRanks.normOne_norm (form σ hσ 4) u
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [diagonal,HermitianForm.conjTranspose,form,Matrix.mul_apply,Fin.sum_univ_two]
    simpa only [form] using hu⟩
  map_one' := by
    apply Subtype.ext; apply Units.ext
    ext i j; fin_cases i <;> fin_cases j <;> simp [diagonal]
  map_mul' u v := by
    apply Subtype.ext; apply Units.ext
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [diagonal,Matrix.mul_apply,Fin.sum_univ_two]

private theorem detSection_spec : (det σ hσ).comp (detSection σ hσ) = MonoidHom.id C := by
  ext u
  simp [det,detSection,diagonal,GeneralLinearGroup.det,Matrix.det_fin_two]

private def pairMatrix : BalancedWreath.base (det σ hσ) →* Matrix (Fin 4) (Fin 4) F where
  toFun x := blockMatrix x.val.1.val.val x.val.2.val.val
  map_one' := blockMatrix_one
  map_mul' _ _ := blockMatrix_mul _ _ _ _

private def pairHom : BalancedWreath.base (det σ hσ) →* SU₄ :=
  (pairMatrix σ hσ).toHomUnits.codRestrict _ fun x => by
    rw [HermitianForm.mem_specialSubgroup_iff]
    have ha := (form σ hσ 2).mem_unitarySubgroup_iff x.val.1.val |>.mp x.val.1.property
    have hb := (form σ hσ 2).mem_unitarySubgroup_iff x.val.2.val |>.mp x.val.2.property
    refine ⟨?_,Units.ext ?_⟩
    · change (form σ hσ 4).conjTranspose (blockMatrix x.val.1.val.val x.val.2.val.val) * 1 *
        blockMatrix x.val.1.val.val x.val.2.val.val = 1
      rw [mul_one,blockMatrix_adj σ hσ (m := 2) (n := 2),←blockMatrix_mul]
      have ha' : (form σ hσ 2).conjTranspose x.val.1.val.val * x.val.1.val.val = 1 := by
        simpa [form] using ha
      have hb' : (form σ hσ 2).conjTranspose x.val.2.val.val * x.val.2.val.val = 1 := by
        simpa [form] using hb
      rw [ha',hb',blockMatrix_one]
    · change (blockMatrix x.val.1.val.val x.val.2.val.val).det = 1
      rw [blockMatrix_det]
      exact congrArg (fun u : C => (u.val : F)) x.property

private theorem pairHom_injective : Function.Injective (pairHom σ hσ) := by
  intro x y h
  have he (i j : Fin 4) := congrArg (fun g : SU₄ => g.val.val i j) h
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext; apply Units.ext
    ext i j
    have hh := he (finSumFinEquiv (m := 2) (n := 2) (.inl i))
      (finSumFinEquiv (m := 2) (n := 2) (.inl j))
    change blockMatrix _ _ _ _ = blockMatrix _ _ _ _ at hh
    simpa only [blockMatrix_inl_inl] using hh
  · apply Subtype.ext; apply Units.ext
    ext i j
    have hh := he (finSumFinEquiv (m := 2) (n := 2) (.inr i))
      (finSumFinEquiv (m := 2) (n := 2) (.inr j))
    change blockMatrix _ _ _ _ = blockMatrix _ _ _ _ at hh
    simpa only [blockMatrix_inr_inr] using hh

private def swapMatrix : Matrix (Fin 4) (Fin 4) F :=
  !![0,0,1,0;0,0,0,1;1,0,0,0;0,1,0,0]

private theorem swap_sq : swapMatrix (F := F) * swapMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMatrix,Matrix.mul_apply,Fin.sum_univ_succ]

private def swap : SU₄ :=
  ⟨⟨swapMatrix,swapMatrix,swap_sq,swap_sq⟩,by
    rw [HermitianForm.mem_specialSubgroup_iff]
    refine ⟨?_,Units.ext ?_⟩
    · have hs : (form σ hσ 4).conjTranspose swapMatrix = swapMatrix (F := F) := by
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [swapMatrix,HermitianForm.conjTranspose,form]
      change (form σ hσ 4).conjTranspose swapMatrix * 1 * swapMatrix = 1
      rw [hs,mul_one,swap_sq]
    · change (swapMatrix (F := F)).det = 1
      let m : Matrix (Fin 4) (Fin 4) ℤ := !![0,0,1,0;0,0,0,1;1,0,0,0;0,1,0,0]
      have h : m.det = 1 := by decide
      have he : m.map (Int.castRingHom F) = swapMatrix := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [m,swapMatrix]
      rw [←he]
      exact ((Int.castRingHom F).map_det m).symm.trans (by rw [h,map_one])⟩

private theorem swap_mul_self : swap σ hσ * swap σ hσ = 1 :=
  Subtype.ext (Units.ext swap_sq)

private def swapHom : C2 →* SU₄ where
  toFun c := if c.toAdd = 0 then 1 else swap σ hσ
  map_one' := by simp
  map_mul' c e := by
    obtain ⟨c,rfl⟩ := (Multiplicative.ofAdd : ZMod 2 ≃ C2).surjective c
    obtain ⟨e,rfl⟩ := (Multiplicative.ofAdd : ZMod 2 ≃ C2).surjective e
    fin_cases c <;> fin_cases e
    · exact (one_mul (1 : SU₄)).symm
    · exact (one_mul (swap σ hσ)).symm
    · exact (mul_one (swap σ hσ)).symm
    · exact (swap_mul_self σ hσ).symm

private theorem swap_pair (x : BalancedWreath.base (det σ hσ)) :
    swap σ hσ * pairHom σ hσ x = pairHom σ hσ (BalancedWreath.swap (det σ hσ) x) * swap σ hσ := by
  apply Subtype.ext; apply Units.ext
  change swapMatrix * blockMatrix x.val.1.val.val x.val.2.val.val =
    blockMatrix x.val.2.val.val x.val.1.val.val * swapMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapMatrix,blockMatrix,Matrix.reindex_apply,Matrix.mul_apply,Fin.sum_univ_succ,
      finSumFinEquiv] <;> rfl

private theorem compatibility (c : C2) :
    (pairHom σ hσ).comp (BalancedWreath.action (det σ hσ) c).toMonoidHom =
      (MulAut.conj (swapHom σ hσ c)).toMonoidHom.comp (pairHom σ hσ) := by
  obtain ⟨c,rfl⟩ := (Multiplicative.ofAdd : ZMod 2 ≃ C2).surjective c
  fin_cases c
  · ext x : 1
    change pairHom σ hσ x = (1 : SU₄) * pairHom σ hσ x * 1⁻¹
    simp
  · ext x : 1
    change pairHom σ hσ (BalancedWreath.swap (det σ hσ) x) =
      swap σ hσ * pairHom σ hσ x * (swap σ hσ)⁻¹
    rw [swap_pair,mul_inv_cancel_right]

private def inclusion : BalancedWreath.W (det σ hσ) →* SU₄ :=
  SemidirectProduct.lift (pairHom σ hσ) (swapHom σ hσ) (compatibility σ hσ)

private theorem swap_not_mem : swap σ hσ ∉ (pairHom σ hσ).range := by
  rintro ⟨x,h⟩
  have he := congrArg (fun g : SU₄ => g.val.val 0 2) h
  change (blockMatrix _ _) 0 2 = 1 at he
  have hz : (blockMatrix x.val.1.val.val x.val.2.val.val) 0 2 = 0 := rfl
  rw [hz] at he
  exact zero_ne_one he

private theorem inclusion_injective : Function.Injective (inclusion σ hσ) := by
  apply (injective_iff_map_eq_one _).mpr
  rintro ⟨x,c⟩ h
  obtain ⟨c,rfl⟩ := (Multiplicative.ofAdd : ZMod 2 ≃ C2).surjective c
  fin_cases c
  · have hx : pairHom σ hσ x = 1 := by
      change pairHom σ hσ x * 1 = 1 at h
      simpa only [mul_one] using h
    have hx' : x = 1 := pairHom_injective σ hσ (hx.trans (map_one (pairHom σ hσ)).symm)
    subst x
    rfl
  · have hx : pairHom σ hσ x * swap σ hσ = 1 := h
    exfalso
    apply swap_not_mem σ hσ
    refine ⟨x⁻¹,?_⟩
    rw [map_inv]
    exact (eq_inv_of_mul_eq_one_right hx).symm

private theorem sylow_frattini_le [Finite F] (h2 : (2 : F) ≠ 0)
    (P : Sylow 2 (BalancedWreath.W (det σ hσ))) : Nat.card (P ⧸ frattini P) ≤ 16 := by
  apply BalancedWreath.sylow_card_frattini_le (det σ hσ) (detSection σ hσ)
    (detSection_spec σ hσ) 8 ?_ P
  intro R
  apply Representation.card_frattini_quotient_le_eight_of_faithful_degree_two R.isPGroup'
    ((Representation.generalLinearNatural 2).comp
      ((form σ hσ 2).unitarySubgroup.subtype.comp (R : Subgroup U₂).subtype))
    ((Representation.generalLinearNatural_injective 2).comp
      (Subtype.val_injective.comp Subtype.val_injective)) h2
  simp

end Theory.SpecificGroups.ClassicalUnitary.OddFrattiniSixteen

namespace Theory.SpecificGroups.ClassicalUnitary.OddFrattiniSixteen
open Theory.SpecificGroups.ClassicalUnitary.OddFundamental.Generation
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourCardinality
variable {F : Type*} [Field F] [Finite F] (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "U₂" => HermitianForm.unitarySubgroup (form σ hσ 2)
local notation "SU₄" => HermitianForm.specialSubgroup (form σ hσ 4)
local notation "C" => OddFourRanks.normOne (form σ hσ 4)

omit [Finite F] in
private theorem det_surjective : Function.Surjective (det σ hσ) := by
  intro u
  exact ⟨detSection σ hσ u,DFunLike.congr_fun (detSection_spec σ hσ) u⟩

private def kerEquiv : (det σ hσ).ker ≃* (form σ hσ 2).specialSubgroup where
  toFun x := ⟨x.val.val,⟨x.val.property,congrArg Subtype.val x.property⟩⟩
  invFun x := ⟨⟨x.val,x.property.1⟩,Subtype.ext x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem card_norm_one {p : ℕ} (hp : 1 ≤ p)
    (hc : Nat.card F = p^2) (hj : ∀ x, σ x = x^p) : Nat.card C = p+1 := by
  have he : OddFourRanks.normOne (form σ hσ 4) = rootsOfUnity (p+1) F := by
    ext u
    change σ (u : F) = (u : F)⁻¹ ↔ u ∈ rootsOfUnity (p+1) F
    rw [hj,mem_rootsOfUnity]
    constructor
    · intro h
      apply Units.ext
      change (u : F)^(p+1)=1
      rw [pow_succ,h,inv_mul_cancel₀ (Units.ne_zero u)]
    · intro h
      apply (mul_eq_one_iff_eq_inv₀ (Units.ne_zero u)).mp
      have h' := congrArg Units.val h
      change (u : F)^(p+1)=1 at h'
      simpa only [pow_succ] using h'
  rw [he]
  let : NeZero (p+1) := ⟨by omega⟩
  apply FiniteField.card_rootsOfUnity_of_dvd
  rw [hc]
  have hp2 : 1 ≤ p^2 := one_le_pow₀ hp
  have heq : p^2-1 = (p+1)*(p-1) := by
    zify [hp,hp2]; ring
  rw [heq]
  exact dvd_mul_right _ _

private theorem card_unitary_two {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hc : Nat.card F = p^2) (hj : ∀ x, σ x = x^p) :
    Nat.card U₂ = (p+1)*(p*(p^2-1)) := by
  have hp : IsPrimePow p := (isPrimePow_nat_iff _).mpr
    ⟨p,1,Fact.out,by decide,by simp⟩
  obtain ⟨e⟩ := nonempty_specialTwoEquiv_odd σ hσ hp ho hc hj
  have hk : Nat.card (FixedBy.subfield F σ) = p :=
    (form σ hσ 2).fixed_card_prime_power hp hc hj
  have hs : Nat.card (form σ hσ 2).specialSubgroup = p*(p^2-1) := by
    rw [Nat.card_congr e.toEquiv,Atlas.card_sl_two,hk]
  have he := (det σ hσ).ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top.mpr (det_surjective σ hσ),card_top,
    Nat.card_congr (kerEquiv σ hσ).toEquiv,hs,
    card_norm_one σ hσ (Fact.out : p.Prime).one_lt.le hc hj] at he
  simpa only [mul_comm] using he.symm

private theorem card_special_four {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hc : Nat.card F = p^2) (hj : ∀ x, σ x = x^p) :
    Nat.card SU₄ = p^6*(p^2-1)*(p^3+1)*(p^4-1) := by
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at ho
  have hp : IsPrimePow p := (isPrimePow_nat_iff _).mpr
    ⟨p,1,Fact.out,by decide,by simp⟩
  obtain ⟨a⟩ := nonempty_specialTwoEquiv_odd σ hσ hp ho hc hj
  have hk : Nat.card (FixedBy.subfield F σ) = p :=
    (form σ hσ 2).fixed_card_prime_power hp hc hj
  have htwo : Nat.card (form σ hσ 2).specialSubgroup = p*(p^2-1) := by
    rw [Nat.card_congr a.toEquiv,Atlas.card_sl_two,hk]
  have hthree := card_special_succ σ hσ (r := p) (e := 1)
    hp2 (by decide) (by simpa using hc) (by simpa using hj) 0
  have hfour := card_special_succ σ hσ (r := p) (e := 1)
    hp2 (by decide) (by simpa using hc) (by simpa using hj) 1
  rw [hfour,hthree,htwo,card_norm_one_three σ hσ hp hc hj,
    card_norm_one_four σ hσ hp hc hj]
  ring

private theorem twice_index {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hc : Nat.card F = p^2) (hj : ∀ x, σ x = x^p) :
    (inclusion σ hσ).range.index * 2 = p^4*(p^2+1)*(p^2-p+1) := by
  have hb := BalancedWreath.card_mul (det σ hσ) (det_surjective σ hσ)
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  rw [card_norm_one σ hσ hp hc hj] at hb
  have hr : Nat.card (inclusion σ hσ).range = Nat.card (BalancedWreath.W (det σ hσ)) :=
    (Nat.card_congr (MonoidHom.ofInjective (inclusion_injective σ hσ)).toEquiv).symm
  have hi := (inclusion σ hσ).range.card_mul_index
  rw [hr] at hi
  apply Nat.eq_of_mul_eq_mul_right (pow_pos (Nat.card_pos (α := U₂)) 2)
  calc
    (inclusion σ hσ).range.index * 2 * Nat.card U₂ ^ 2 =
        (Nat.card (BalancedWreath.W (det σ hσ)) * (p+1)) * (inclusion σ hσ).range.index := by
      rw [hb]; ring
    _ = Nat.card SU₄ * (p+1) := by rw [mul_right_comm,hi]
    _ = _ := by
      rw [card_special_four σ hσ ho hc hj,card_unitary_two σ hσ ho hc hj]
      have hp2 : 1 ≤ p^2 := one_le_pow₀ hp
      have hp4 : 1 ≤ p^4 := one_le_pow₀ hp
      have hpp : p ≤ p^2 := Nat.le_pow (by decide)
      zify [hp,hp2,hp4,hpp]
      ring

private theorem odd_index {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hc : Nat.card F = p^2) (hj : ∀ x, σ x = x^p) : Odd (inclusion σ hσ).range.index := by
  have hm : p % 4 = 1 ∨ p % 4 = 3 := by rw [Nat.odd_iff] at ho; omega
  have hmod : (p^4*(p^2+1)) % 4 = 2 := by
    rcases hm with hm | hm <;> norm_num [Nat.mul_mod,Nat.add_mod,Nat.pow_mod,hm]
  have hodd : Odd (p^2-p+1) := by
    have hpp : p ≤ p^2 := Nat.le_pow (by decide)
    have he : p^2-p+1+p = p^2+1 := by omega
    have h : Even (p^2+1) := (ho.pow (n := 2)).add_odd (by decide)
    rw [←he] at h
    exact (Nat.even_add'.mp h).mpr ho
  have hmod' : (p^4*(p^2+1)*(p^2-p+1)) % 4 = 2 := by
    rw [Nat.mul_mod,hmod]
    rw [Nat.odd_iff] at hodd
    omega
  rw [←twice_index σ hσ ho hc hj] at hmod'
  rw [Nat.odd_iff]
  omega

/-- The norm-one scalar group has the expected order for the stored involution. -/
theorem norm_one_card {p : ℕ} (hp : 1 ≤ p)
    (hc : Nat.card F = p^2) (hj : ∀ x, σ x = x^p) : Nat.card C = p+1 :=
  card_norm_one σ hσ hp hc hj

/-- The actual identity-form unitary two-space has order `(p+1)p(p²-1)`. -/
theorem unitary_two_card {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hc : Nat.card F = p^2) (hj : ∀ x, σ x = x^p) :
    Nat.card U₂ = (p+1)*(p*(p^2-1)) := card_unitary_two σ hσ ho hc hj

/-- The literal determinant-one two-block embedding transfers any Sylow
Frattini bound from U₂ to SU₄, adding only its block swap. -/
theorem identity_frattini_le_of_unitary_two_bound {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hc : Nat.card F = p^2) (hj : ∀ x, σ x = x^p)
    (b : ℕ) (hb : ∀ Q : Sylow 2 U₂, Nat.card (Q ⧸ frattini Q) ≤ b)
    (P : Sylow 2 SU₄) : Nat.card (P ⧸ frattini P) ≤ 2*b := by
  let j := inclusion σ hσ
  let Q : Sylow 2 (BalancedWreath.W (det σ hσ)) := default
  have hinj : Function.Injective j := inclusion_injective σ hσ
  let U : Subgroup j.range := (Q : Subgroup (BalancedWreath.W (det σ hσ))).map
    (MonoidHom.ofInjective hinj).toMonoidHom
  have hUidx : U.index = (Q : Subgroup (BalancedWreath.W (det σ hσ))).index :=
    index_map_of_bijective (MonoidHom.ofInjective hinj).bijective _
  let Sg : Subgroup SU₄ := U.map j.range.subtype
  have hSidx : ¬ 2 ∣ Sg.index := by
    rw [index_map_subtype,hUidx]
    exact Nat.prime_two.not_dvd_mul Q.not_dvd_index (odd_index σ hσ ho hc hj).not_two_dvd_nat
  let S : Sylow 2 SU₄ := ((Q.isPGroup'.map _).map _).toSylow hSidx
  let e₁ : Q ≃* U := Q.equivMapOfInjective (MonoidHom.ofInjective hinj).toMonoidHom
    (MonoidHom.ofInjective hinj).injective
  let e₂ : U ≃* S := U.equivMapOfInjective j.range.subtype Subtype.val_injective
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr (P.equiv S),
    ←Theory.GroupTheory.SylowFrattiniBounds.card_congr (e₁.trans e₂)]
  exact BalancedWreath.sylow_card_frattini_le (det σ hσ) (detSection σ hσ)
    (detSection_spec σ hσ) b hb Q

/-- The actual identity-form SU₄ Sylow Frattini quotient has order at most sixteen. -/
theorem identity_frattini_le {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hc : Nat.card F = p^2) (hj : ∀ x, σ x = x^p) (h2 : (2 : F) ≠ 0)
    (P : Sylow 2 SU₄) : Nat.card (P ⧸ frattini P) ≤ 16 := by
  apply identity_frattini_le_of_unitary_two_bound σ hσ ho hc hj 8 ?_ P
  intro Q
  apply Representation.card_frattini_quotient_le_eight_of_faithful_degree_two Q.isPGroup'
    ((Representation.generalLinearNatural 2).comp
      ((form σ hσ 2).unitarySubgroup.subtype.comp (Q : Subgroup U₂).subtype))
    ((Representation.generalLinearNatural_injective 2).comp
      (Subtype.val_injective.comp Subtype.val_injective)) h2
  simp

end Theory.SpecificGroups.ClassicalUnitary.OddFrattiniSixteen

namespace Theory.SpecificGroups.ClassicalUnitary.OddFrattiniSixteen
variable {F : Type*} [Field F] [Finite F]

/-- Orthonormal transport retains the bound for the original Hermitian form. -/
theorem special_frattini_le (J : HermitianForm 4 F) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hc : Nat.card F = p^2) (hj : ∀ x, J.conj x = x^p)
    (h2 : (2 : F) ≠ 0) (P : Sylow 2 J.specialSubgroup) :
    Nat.card (P ⧸ frattini P) ≤ 16 := by
  obtain ⟨C,e,ep,hC,he,hep⟩ :=
    HermitianForm.IdentityGram.exists_identityGram_transport J p Fact.out hc hj
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr
    (e.subgroupMap (P : Subgroup J.specialSubgroup))]
  exact identity_frattini_le J.conj J.conj_involutive ho hc hj h2
    (P.mapSurjective e.surjective)

/-- The bound descends along the actual map from SU to its image in PGL. -/
theorem projective_frattini_le (J : HermitianForm 4 F) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hc : Nat.card F = p^2) (hj : ∀ x, J.conj x = x^p)
    (h2 : (2 : F) ≠ 0) (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Nat.card (P ⧸ frattini P) ≤ 16 := by
  exact Theory.SpecificGroups.OddClassicalSylowFrattini.card_le_of_surjective
    (ProjectiveKernel.project J) (ProjectiveKernel.project_surjective J)
    (special_frattini_le J ho hc hj h2) P

end Theory.SpecificGroups.ClassicalUnitary.OddFrattiniSixteen
