module
public import Theory.GroupTheory.BalancedWreathFrattini
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.Representation.DegreeTwoFrattini
public import Theory.SpecificGroups.OddClassicalSylowFrattini

/-!
# Four Frattini generators for odd PSL₄ Sylow subgroups

The pairs of GL₂ matrices whose determinants multiply to one, extended by
the interchange of the two blocks, embed in the actual SL₄ matrix group.
Their index is q⁴(q²+1)(q²+q+1)/2, which is odd when q is odd. The split
determinant and the faithful degree-two Frattini bound give at most four
Frattini generators for a Sylow of this subgroup. Sylow conjugacy and the
full projective quotient transfer the bound to PSL₄.

This discharges the linear-four row of the original exterior outer action
in Aschbacher--Smith 4.4.10--11, printed p.621. The finite linear-group
counts reuse the licensed ATLAS support module; see LICENSES/ATLAS.txt
and LICENSES/ATLAS-CITATION.cff.
-/

public section

namespace Theory.SpecificGroups.PSL4.OddFrattiniSixteen
open Subgroup Matrix
open scoped MatrixGroups
variable {F : Type*} [Field F]
local notation "GL₂" => GL (Fin 2) F
local notation "SL₄" => SL(4,F)
local notation "d" => (GeneralLinearGroup.det : GL₂ →* Fˣ)
local notation "C2" => Multiplicative (ZMod 2)

private def block (A B : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  !![A 0 0,A 0 1,0,0;A 1 0,A 1 1,0,0;0,0,B 0 0,B 0 1;0,0,B 1 0,B 1 1]

private theorem block_mul (A B C D : Matrix (Fin 2) (Fin 2) F) :
    block A B * block C D = block (A*C) (B*D) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block,Matrix.mul_apply,Fin.sum_univ_succ]

private theorem block_one : block (1 : Matrix (Fin 2) (Fin 2) F) 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem block_det (A B : Matrix (Fin 2) (Fin 2) F) :
    (block A B).det = A.det * B.det := by
  have he : block A B = Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks A 0 0 B) := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [he,Matrix.det_reindex_self,Matrix.det_fromBlocks_zero₂₁]

private def pairHom : BalancedWreath.base d →* SL₄ where
  toFun x := ⟨block x.val.1.val x.val.2.val, by
    rw [block_det]
    exact congrArg Units.val x.property⟩
  map_one' := Subtype.ext block_one
  map_mul' x y := Subtype.ext (block_mul _ _ _ _).symm

private theorem pairHom_injective : Function.Injective (pairHom (F := F)) := by
  intro x y h
  have he (i j : Fin 4) := congrArg (fun g : SL₄ => g.val i j) h
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact he 0 0
    · exact he 0 1
    · exact he 1 0
    · exact he 1 1
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact he 2 2
    · exact he 2 3
    · exact he 3 2
    · exact he 3 3

private def swapMatrix : Matrix (Fin 4) (Fin 4) F :=
  !![0,0,1,0;0,0,0,1;1,0,0,0;0,1,0,0]

private def swap : SL₄ :=
  ⟨swapMatrix,by
    unfold swapMatrix
    let m : Matrix (Fin 4) (Fin 4) ℤ := !![0,0,1,0;0,0,0,1;1,0,0,0;0,1,0,0]
    have h : m.det = 1 := by decide
    have he : m.map (Int.castRingHom F) =
        (!![0,0,1,0;0,0,0,1;1,0,0,0;0,1,0,0] : Matrix (Fin 4) (Fin 4) F) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [m]
    rw [←he]
    exact ((Int.castRingHom F).map_det m).symm.trans (by rw [h,map_one])⟩

private theorem swap_sq : swap (F := F) * swap = 1 := by
  apply Subtype.ext
  change swapMatrix * swapMatrix = (1 : Matrix (Fin 4) (Fin 4) F)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMatrix,Matrix.mul_apply,Fin.sum_univ_succ]

private def swapHom : C2 →* SL₄ where
  toFun c := if c.toAdd = 0 then 1 else swap
  map_one' := by simp
  map_mul' c e := by
    obtain ⟨c,rfl⟩ := (Multiplicative.ofAdd : ZMod 2 ≃ C2).surjective c
    obtain ⟨e,rfl⟩ := (Multiplicative.ofAdd : ZMod 2 ≃ C2).surjective e
    fin_cases c <;> fin_cases e
    · exact (one_mul (1 : SL₄)).symm
    · exact (one_mul swap).symm
    · exact (mul_one swap).symm
    · exact swap_sq.symm

private theorem swap_pair (x : BalancedWreath.base d) :
    swap * pairHom x = pairHom (BalancedWreath.swap d x) * swap := by
  apply Subtype.ext
  change swapMatrix * block x.val.1.val x.val.2.val = block x.val.2.val x.val.1.val * swapMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapMatrix,block,Matrix.mul_apply,Fin.sum_univ_succ]

private theorem compatibility (c : C2) :
    (pairHom (F := F)).comp (BalancedWreath.action d c).toMonoidHom =
      (MulAut.conj (swapHom c)).toMonoidHom.comp pairHom := by
  obtain ⟨c,rfl⟩ := (Multiplicative.ofAdd : ZMod 2 ≃ C2).surjective c
  fin_cases c
  · ext x : 1
    change pairHom x = (1 : SL₄) * pairHom x * 1⁻¹
    simp
  · ext x : 1
    change pairHom (BalancedWreath.swap d x) = swap * pairHom x * swap⁻¹
    rw [swap_pair,mul_inv_cancel_right]

def inclusion : BalancedWreath.W d →* SL₄ :=
  SemidirectProduct.lift pairHom swapHom compatibility

private theorem swap_not_mem : swap (F := F) ∉ (pairHom (F := F)).range := by
  rintro ⟨x,h⟩
  have he := congrArg (fun g : SL₄ => g.val 0 2) h
  exact zero_ne_one (α := F) he

theorem inclusion_injective : Function.Injective (inclusion (F := F)) := by
  apply (injective_iff_map_eq_one _).mpr
  rintro ⟨x,c⟩ h
  obtain ⟨c,rfl⟩ := (Multiplicative.ofAdd : ZMod 2 ≃ C2).surjective c
  fin_cases c
  · have hx : pairHom x = 1 := by
      change pairHom x * 1 = 1 at h
      simpa only [mul_one] using h
    have hx' : x = 1 := pairHom_injective (hx.trans (map_one pairHom).symm)
    subst x
    rfl
  · have hx : pairHom x * swap = 1 := h
    exfalso
    apply swap_not_mem (F := F)
    refine ⟨x⁻¹,?_⟩
    rw [map_inv]
    exact (eq_inv_of_mul_eq_one_right hx).symm

private def detSection : Fˣ →* GL₂ where
  toFun u := ⟨!![u,0;0,1],!![u⁻¹,0;0,1],by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_two],by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_two]⟩
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' u v := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_two]

private theorem detSection_spec : (d).comp detSection = MonoidHom.id Fˣ := by
  ext u
  simp [detSection,GeneralLinearGroup.det,Matrix.det_fin_two]

theorem sylow_frattini_le [Finite F] (h2 : (2 : F) ≠ 0)
    (P : Sylow 2 (BalancedWreath.W d)) : Nat.card (P ⧸ frattini P) ≤ 16 := by
  apply BalancedWreath.sylow_card_frattini_le d detSection detSection_spec 8 ?_ P
  intro R
  apply Representation.card_frattini_quotient_le_eight_of_faithful_degree_two R.isPGroup'
    ((Representation.generalLinearNatural 2).comp (R : Subgroup GL₂).subtype)
    ((Representation.generalLinearNatural_injective 2).comp Subtype.val_injective) h2
  simp

end Theory.SpecificGroups.PSL4.OddFrattiniSixteen

namespace Theory.SpecificGroups.PSL4.OddFrattiniSixteen
open Subgroup Matrix
open scoped MatrixGroups
variable {F : Type*} [Field F] [Finite F]
local notation "q" => Nat.card F
local notation "GL₂" => GL (Fin 2) F
local notation "d" => (GeneralLinearGroup.det : GL₂ →* Fˣ)

private theorem card_gl_two : Nat.card GL₂ = q * (q-1) * (q^2-1) := by
  let := Fintype.ofFinite F
  rw [Matrix.card_GL_field]
  simp only [Fin.prod_univ_two,Fin.val_zero,Fin.val_one,pow_zero,pow_one,
    ←Nat.card_eq_fintype_card]
  have h : q^2-q=q*(q-1) := by rw [Nat.mul_sub_left_distrib,mul_one,pow_two]
  rw [h]; ring

private theorem card_sl_four_mul :
    Nat.card SL(4,F) * (q-1) = ∏ i : Fin 4, (q^4-q^(i:ℕ)) := by
  rw [card_eq_card_quotient_mul_card_subgroup (center SL(4,F)),
    Atlas.ExceptionalSupport.card_sl_center]
  exact Atlas.ExceptionalSupport.card_psl_mul 4

private theorem count_factor (k : ℕ) (hq : 1 ≤ k) :
    (∏ i : Fin 4, (k^4-k^(i:ℕ))) =
      k^4*(k^2+1)*(k^2+k+1) * (k*(k-1)*(k^2-1))^2 := by
  simp only [Fin.prod_univ_succ,Fin.val_zero,Fin.val_succ,pow_zero,zero_add,
    Finset.univ_unique,Fin.default_eq_zero,Finset.prod_singleton,pow_one]
  have hq2 : 1 ≤ k^2 := one_le_pow₀ hq
  have hq3 : 1 ≤ k^3 := one_le_pow₀ hq
  have hq4 : 1 ≤ k^4 := one_le_pow₀ hq
  have h1 : k ≤ k^4 := Nat.le_pow (by decide)
  have h2 : k^2 ≤ k^4 := Nat.pow_le_pow_right hq (by decide)
  have h3 : k^3 ≤ k^4 := Nat.pow_le_pow_right hq (by decide)
  zify [hq,hq2,hq3,hq4,h1,h2,h3]
  ring

theorem twice_index : (inclusion (F := F)).range.index * 2 = q^4*(q^2+1)*(q^2+q+1) := by
  have hc := BalancedWreath.card_mul d GeneralLinearGroup.det_surjective
  rw [Nat.card_units] at hc
  have hr : Nat.card (inclusion (F := F)).range = Nat.card (BalancedWreath.W d) :=
    (Nat.card_congr (MonoidHom.ofInjective inclusion_injective).toEquiv).symm
  have hi := (inclusion (F := F)).range.card_mul_index
  rw [hr] at hi
  apply Nat.eq_of_mul_eq_mul_right (pow_pos (Nat.card_pos (α := GL₂)) 2)
  calc
    (inclusion (F := F)).range.index * 2 * Nat.card GL₂ ^ 2 =
        (Nat.card (BalancedWreath.W d) * (q-1)) * (inclusion (F := F)).range.index := by rw [hc]; ring
    _ = Nat.card SL(4,F) * (q-1) := by rw [mul_right_comm,hi]
    _ = ∏ i : Fin 4, (q^4-q^(i:ℕ)) := card_sl_four_mul
    _ = _ := by rw [count_factor q Nat.card_pos,card_gl_two]

theorem odd_index (ho : Odd q) : Odd (inclusion (F := F)).range.index := by
  have hm : q % 4 = 1 ∨ q % 4 = 3 := by rw [Nat.odd_iff] at ho; omega
  have hmod : (q^4*(q^2+1)*(q^2+q+1)) % 4 = 2 := by
    rcases hm with hm | hm <;> norm_num [Nat.mul_mod,Nat.add_mod,Nat.pow_mod,hm]
  rw [←twice_index] at hmod
  rw [Nat.odd_iff]
  omega

theorem linear_frattini_le (ho : Odd q) (h2 : (2 : F) ≠ 0)
    (P : Sylow 2 SL(4,F)) : Nat.card (P ⧸ frattini P) ≤ 16 := by
  let j := inclusion (F := F)
  let Q : Sylow 2 (BalancedWreath.W d) := default
  have hj : Function.Injective j := inclusion_injective
  let U : Subgroup j.range := (Q : Subgroup (BalancedWreath.W d)).map
    (MonoidHom.ofInjective hj).toMonoidHom
  have hUidx : U.index = (Q : Subgroup (BalancedWreath.W d)).index :=
    index_map_of_bijective (MonoidHom.ofInjective hj).bijective _
  let Sg : Subgroup SL(4,F) := U.map j.range.subtype
  have hSidx : ¬ 2 ∣ Sg.index := by
    rw [index_map_subtype,hUidx]
    exact Nat.prime_two.not_dvd_mul Q.not_dvd_index (odd_index ho).not_two_dvd_nat
  let S : Sylow 2 SL(4,F) := ((Q.isPGroup'.map _).map _).toSylow hSidx
  let e₁ : Q ≃* U := Q.equivMapOfInjective (MonoidHom.ofInjective hj).toMonoidHom
    (MonoidHom.ofInjective hj).injective
  let e₂ : U ≃* S := U.equivMapOfInjective j.range.subtype Subtype.val_injective
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr (P.equiv S),
    ←Theory.GroupTheory.SylowFrattiniBounds.card_congr (e₁.trans e₂)]
  exact sylow_frattini_le h2 Q

end Theory.SpecificGroups.PSL4.OddFrattiniSixteen

namespace Theory.SpecificGroups.PSL4.OddFrattiniSixteen
open Subgroup
open scoped MatrixGroups
variable {F : Type*} [Field F] [Finite F]

theorem projective_frattini_le (ho : Odd (Nat.card F)) (h2 : (2 : F) ≠ 0)
    (P : Sylow 2 PSL(4,F)) : Nat.card (P ⧸ frattini P) ≤ 16 := by
  exact Theory.SpecificGroups.OddClassicalSylowFrattini.card_le_of_surjective
    (QuotientGroup.mk' (center SL(4,F))) (QuotientGroup.mk'_surjective _)
    (linear_frattini_le ho h2) P

end Theory.SpecificGroups.PSL4.OddFrattiniSixteen
