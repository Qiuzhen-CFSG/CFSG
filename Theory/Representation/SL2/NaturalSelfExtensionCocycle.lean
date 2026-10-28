module
public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.FirstCohomologyLinearTransport
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.CharP.Two
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

/-!
# Derivations for a binary natural self-extension of SL₂

Over a finite field of characteristic two, a derivation from SL₂ into the
binary endomorphisms of its natural module is principal once it vanishes on
the diagonal torus and the Weyl involution. The involution and braid relations
fix the derivative of a unit transvection; torus conjugacy and addition fix
all root elements. Transvection generation completes the argument.

This supplies the splitting step behind DGS85, (9.10)(6), and the chosen
complement used immediately afterward (printed pp.149–150).
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace Representation.SL2NaturalSelfExtension
variable {F : Type*} [Field F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2
local notation "V" => Fin 2 → F
local notation "G" => SL(2,F)
noncomputable abbrev natRep : Representation (ZMod 2) G V :=
  (specialLinearNatural (k := F) 2).restrictScalars (k := ZMod 2)
abbrev upper (x : F) : G := transvection zero_ne_one x
abbrev lower (x : F) : G := transvection one_ne_zero x
def swap : G := ⟨!![0,1;1,0],by simp [det_fin_two,CharTwo.neg_eq]⟩
theorem swap_coe : (swap (F := F)).val = !![0,1;1,0] := by rfl
noncomputable abbrev diagonal (x : F) (hx : x ≠ 0) : G := diag2 x hx

theorem action_upper (x : F) (v : V) : natRep (upper x) v = ![v 0+x*v 1,v 1] := by
  change Matrix.mulVec (upper x).val v = _
  ext i
  fin_cases i <;> simp [upper,transvection_coe,
    mulVec,dotProduct,Fin.sum_univ_two]
theorem action_swap (v : V) : natRep swap v = ![v 1,v 0] := by
  change Matrix.mulVec swap.val v = _
  ext i
  fin_cases i <;> simp [swap,
    mulVec,dotProduct,Fin.sum_univ_two]
theorem action_diagonal (x : F) (hx : x ≠ 0) (v : V) :
    natRep (diagonal x hx) v = ![x*v 0,x⁻¹*v 1] := by
  change Matrix.mulVec (diagonal x hx).val v = _
  ext i
  fin_cases i <;> simp [diagonal,diag2_coe',
    mulVec,dotProduct,Fin.sum_univ_two]
theorem upper_square (x : F) : upper x * upper x = (1 : G) := by
  rw [←transvection_add,CharTwo.add_self_eq_zero,transvection_coeff_zero]
theorem braid : upper (1:F) * swap * upper (1:F) = swap * upper (1:F) * swap := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upper,swap,transvection_coe,mul_apply,vecMul,dotProduct,Fin.sum_univ_two,
      CharTwo.add_self_eq_zero]

variable (d : SL(2,F) → Module.End (ZMod 2) (Fin 2 → F))
  (hd : ∀ (g h : SL(2,F)) (v : Fin 2 → F), d (g*h) v = natRep g (d h v) + d g (natRep h v))

include d hd

theorem derivation_one (v : V) : d (1:G) v = 0 := by
  have hh := hd (1:G) (1:G) v
  simpa only [one_mul,map_one,Module.End.one_apply,add_eq_left] using hh.symm

theorem normalized_upper_one
    (hw : d swap = 0) :
    ∃ A : F →ₗ[ZMod 2] F, ∀ (v : V), d (upper (1:F)) v = ![A (v 0),A (v 1)] := by
  let D := d (upper (1:F))
  have hcomm (v : V) : D (natRep (upper (1:F)) v) = natRep (upper (1:F)) (D v) := by
    have hh := hd (upper (1:F)) (upper (1:F)) v
    rw [upper_square,derivation_one d hd] at hh
    ext i
    exact (CharTwo.add_eq_zero.mp (congrFun hh.symm i)).symm
  let A : F →ₗ[ZMod 2] F := (LinearMap.proj 0).comp
    (D.comp (LinearMap.single (ZMod 2) (fun _ : Fin 2 => F) 0))
  let B : F →ₗ[ZMod 2] F := (LinearMap.proj 0).comp
    (D.comp (LinearMap.single (ZMod 2) (fun _ : Fin 2 => F) 1))
  have hA (x : F) : A x = D ![x,0] 0 := by
    change D (Pi.single 0 x) 0 = _
    apply congrArg (fun v : V => D v 0)
    ext i
    fin_cases i <;> simp
  have hB (x : F) : B x = D ![0,x] 0 := by
    change D (Pi.single 1 x) 0 = _
    apply congrArg (fun v : V => D v 0)
    ext i
    fin_cases i <;> simp
  have haxes (x : F) : D ![x,0] 1 = 0 ∧ D ![0,x] 1 = A x := by
    have hh := hcomm ![0,x]
    have he : ![x,x] = (![x,0] : V) + ![0,x] := by ext i; fin_cases i <;> simp
    rw [action_upper,action_upper] at hh
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
      one_mul,zero_add] at hh
    rw [he,map_add] at hh
    have hh0 := congrFun hh 0
    have hh1 := congrFun hh 1
    simp only [Pi.add_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one] at hh0 hh1
    constructor
    · exact add_eq_right.mp hh1
    · rw [hA]
      exact (add_right_cancel (hh0.trans (add_comm _ _))).symm
  have hshape (v : V) : D v = ![A (v 0)+B (v 1),A (v 1)] := by
    have he : v = ![v 0,0]+![0,v 1] := by ext i; fin_cases i <;> simp
    calc
      D v = D ![v 0,0]+D ![0,v 1] := (congrArg D he).trans (D.map_add _ _)
      _ = _ := by
        ext i
        fin_cases i
        · simp [hA,hB]
        · simp [(haxes _).1,(haxes _).2]
  have hB0 (x : F) : B x = 0 := by
    have hh := congrArg (fun g : G => d g ![x,0]) (braid (F := F))
    simp only [hd,hw,LinearMap.zero_apply,map_zero,add_zero,zero_add,
      map_mul,Module.End.mul_apply] at hh
    change natRep (upper (1:F)) (natRep swap (D ![x,0])) +
      D (natRep swap (natRep (upper (1:F)) ![x,0])) =
        natRep swap (D (natRep swap ![x,0])) at hh
    simp only [hshape,action_upper,action_swap,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_fin_one,map_zero,add_zero,zero_add,one_mul] at hh
    have hh1 := congrFun hh 1
    simpa only [Pi.add_apply,Matrix.cons_val_one,Matrix.cons_val_fin_one,
      CharTwo.add_self_eq_zero] using hh1.symm
  refine ⟨A,fun v => ?_⟩
  rw [hshape,hB0,add_zero]


omit d hd [CharP F 2] in
theorem diagonal_upper (x : F) (hx : x ≠ 0) (y : F) :
    diagonal x hx * upper y = upper (x ^ 2 * y) * diagonal x hx := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonal,diag2_coe',upper,transvection_coe,mul_apply,Fin.sum_univ_two,
      pow_two,mul_assoc,hx,mul_comm,mul_left_comm]
  field_simp

omit d hd in
theorem swap_upper_swap (x : F) : swap * upper x * swap = lower x := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swap,upper,lower,transvection_coe,mul_apply,vecMul,dotProduct,Fin.sum_univ_two]

theorem normalized_upper [Finite F]
    (hw : d swap = 0) (ht : ∀ x (hx : x ≠ 0), d (diagonal x hx) = 0) :
    ∃ A : F →ₗ[ZMod 2] F, ∀ t v,
      d (upper t) v = ![t*A (v 0),A (t*v 1)] := by
  obtain ⟨A,hA⟩ := normalized_upper_one d hd hw
  have hzero (t x : F) :
      d (upper t) ![x,0] 1 = 0 ∧ d (upper t) ![0,x] 0 = 0 := by
    by_cases ht0 : t = 0
    · subst t
      simp only [upper,transvection_coeff_zero,derivation_one d hd,Pi.zero_apply,and_self]
    · let s := (frobeniusEquiv F 2).symm t
      have hs : s ≠ 0 := (map_ne_zero _).mpr ht0
      have hs2 : s^2 = t := frobeniusEquiv_symm_pow_p F 2 t
      have hh (v : V) := congrArg (fun g : G => d g v) (diagonal_upper s hs 1)
      simp only [hd,ht,LinearMap.zero_apply,map_zero,add_zero,zero_add,hs2,mul_one,hA] at hh
      have hfirst := congrFun (hh ![s⁻¹*x,0]) 1
      have hsecond := congrFun (hh ![0,s*x]) 0
      simp only [action_diagonal,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_fin_one,map_zero,mul_zero,mul_inv_cancel_left₀ hs,
        inv_mul_cancel_left₀ hs] at hfirst hsecond
      exact ⟨hfirst.symm,hsecond.symm⟩
  have hdecomp (t : F) (v : V) :
      d (upper t) v = d (upper t) ![v 0,0]+d (upper t) ![0,v 1] := by
    rw [←map_add]
    congr 1
    ext i
    fin_cases i <;> simp
  have hfirst (t x : F) : d (upper t) ![x,0] 0 = t*A x := by
    have hh := congrFun (hd (upper t) (upper (1:F)) ![0,x]) 0
    rw [←transvection_add] at hh
    rw [(hzero (t+1) x).2,hA,action_upper,action_upper] at hh
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
      map_zero,zero_add,one_mul] at hh
    rw [hdecomp] at hh
    simp only [Pi.add_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_fin_one,(hzero t x).2,add_zero] at hh
    exact (CharTwo.add_eq_zero.mp hh.symm).symm
  have hsecond (t x : F) : d (upper t) ![0,x] 1 = A (t*x) := by
    have hh := congrFun (hd (upper (1:F)) (upper t) ![0,x]) 0
    rw [←transvection_add] at hh
    rw [(hzero (1+t) x).2,action_upper,action_upper,hA] at hh
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
      zero_add,one_mul,(hzero t x).2] at hh
    exact CharTwo.add_eq_zero.mp hh.symm
  refine ⟨A,fun t v => ?_⟩
  rw [hdecomp]
  ext i
  fin_cases i
  · change d (upper t) ![v 0,0] 0+d (upper t) ![0,v 1] 0 = t*A (v 0)
    rw [hfirst,(hzero _ _).2,add_zero]
  · change d (upper t) ![v 0,0] 1+d (upper t) ![0,v 1] 1 = A (t*v 1)
    rw [(hzero _ _).1,hsecond,zero_add]

theorem normalized_principal [Finite F]
    (hw : d swap = 0) (ht : ∀ x (hx : x ≠ 0), d (diagonal x hx) = 0) :
    ∃ T : Module.End (ZMod 2) V, ∀ g v,
      d g v = natRep g (T v)-T (natRep g v) := by
  obtain ⟨A,hA⟩ := normalized_upper d hd hw ht
  let T : Module.End (ZMod 2) V :=
    { toFun v := ![A (v 1),A (v 0)]
      map_add' v w := by ext i; fin_cases i <;> simp
      map_smul' c v := by ext i; fin_cases i <;> simp }
  have hup (t : F) (v : V) : d (upper t) v =
      natRep (upper t) (T v)-T (natRep (upper t) v) := by
    rw [hA,action_upper]
    ext i
    fin_cases i <;>
      simp [T,action_upper,CharTwo.sub_eq_add,CharTwo.add_cancel_left,add_comm]
  have hw' (v : V) : d swap v = natRep swap (T v)-T (natRep swap v) := by
    rw [hw,LinearMap.zero_apply]
    simp [T,action_swap]
  have hmul (g h : G)
      (hg : ∀ v, d g v = natRep g (T v)-T (natRep g v))
      (hh : ∀ v, d h v = natRep h (T v)-T (natRep h v)) :
      ∀ v, d (g*h) v = natRep (g*h) (T v)-T (natRep (g*h) v) := by
    intro v
    rw [hd,hg,hh,map_sub,map_mul,Module.End.mul_apply,Module.End.mul_apply]
    abel
  refine ⟨T,fun g => ?_⟩
  apply Matrix.SL2.transvection_induction
    (fun g => ∀ v, d g v = natRep g (T v)-T (natRep g v)) ?_ hmul g
  intro i j hij t
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact hup t
  · change ∀ v, d (lower t) v = natRep (lower t) (T v)-T (natRep (lower t) v)
    rw [←swap_upper_swap]
    exact hmul _ _ (hmul _ _ hw' (hup t)) hw'
  · exact (hij rfl).elim

end Representation.SL2NaturalSelfExtension
