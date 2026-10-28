module
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.Field.ZMod
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic
/-!
# A binary plane fixed by a transvection centralizer

Let W and A be elementary groups of order four. Suppose an action on W × A
contains the full automorphism group of W acting trivially on A, and has no
element of order four. Every actor commuting with a nonidentity point fixer
of that binary-plane group preserves W × 1.

Choose coordinates respecting the given factors and the fixed point. The
point fixer is the standard transvection t, and the binary group supplies a
standard cubic s. A matrix p commuting with t has an explicit block shape.
If p moves W, one of p, ps, pst, ppsps, ppspst has order four. The finite
certificate is kernel checked; all coordinate maps and actions are transported
explicitly before it is used. Only the intrinsic product theorem is public.

Source application: Aschbacher--Smith, proof of 12.9.4, printed p.860 of
refs/quasithin.pdf. This replaces the unproved identification of the two
fixed four-groups by the original Sylow action obstruction.
-/

noncomputable section
open scoped IsMulCommutative
namespace BinaryPlaneCentralizer
open Matrix
abbrev M := Matrix (Fin 4) (Fin 4) (ZMod 2)
def s : M := !![0,1,0,0; 1,1,0,0; 0,0,1,0; 0,0,0,1]
def t : M := !![1,1,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1]
def block (a b c d e f g h i : ZMod 2) : M :=
  !![1,a,b,c; 0,1,0,0; 0,d,e,f; 0,g,h,i]
def orderFour (x : M) : Prop := x ^ 4 = 1 ∧ x ^ 2 ≠ 1
instance (x : M) : Decidable (orderFour x) := inferInstanceAs (Decidable (_ ∧ _))


theorem certificate : ∀ a b c d e f g h i : ZMod 2,
    e*i-f*h = 1 → d ≠ 0 ∨ g ≠ 0 →
    let p := block a b c d e f g h i
    orderFour p ∨ orderFour (p*s) ∨ orderFour (p*s*t) ∨
      orderFour (p*p*s*p*s) ∨ orderFour (p*p*s*p*s*t) := by
  decide +kernel


private theorem binary_ne_zero_eq_one {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  exact (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) x hx

private theorem shape (p : M) (hu : IsUnit p) (hc : Commute p t) :
    p = block (p 0 1) (p 0 2) (p 0 3) (p 2 1) (p 2 2) (p 2 3)
      (p 3 1) (p 3 2) (p 3 3) ∧ p 2 2 * p 3 3 - p 2 3 * p 3 2 = 1 := by
  have he (i j : Fin 4) := congrArg (fun q : M => q i j) hc.eq
  simp only [Matrix.mul_apply,Fin.sum_univ_four,t,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one] at he
  have h10 : p 1 0 = 0 := by simpa using he 0 0
  have h20 : p 2 0 = 0 := by simpa using he 2 1
  have h30 : p 3 0 = 0 := by simpa using he 3 1
  have h12 : p 1 2 = 0 := by simpa using he 0 2
  have h13 : p 1 3 = 0 := by simpa using he 0 3
  have h00 : p 0 0 = p 1 1 := by
    apply add_right_cancel (b := p 0 1)
    simpa [add_comm] using he 0 1
  have hdet : p.det ≠ 0 := isUnit_iff_ne_zero.mp (p.isUnit_iff_isUnit_det.mp hu)
  have hdet' : p.det = p 0 0 * p 1 1 * (p 2 2 * p 3 3 - p 2 3 * p 3 2) := by
    rw [Matrix.det_succ_column_zero]
    simp [Fin.sum_univ_four,h10,h20,h30,Matrix.det_fin_three,h12,h13]
    ring
  have h01 : p 0 0 = 1 := binary_ne_zero_eq_one (by
    intro hz
    simp [hdet',hz] at hdet)
  have h11 : p 1 1 = 1 := h00 ▸ h01
  refine ⟨?_,binary_ne_zero_eq_one ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [block,h10,h20,h30,h12,h13,h01,h11]
  · simpa [hdet',h01,h11] using hdet

theorem plane_preserved
    {H : Type*} [Group H] (f : H →* M)
    (hno4 : ∀ x : H, f x ^ 4 = 1 → f x ^ 2 = 1)
    (c b : H) (hc : f c = s) (hb : f b = t)
    (x : H) (hx : Commute (f x) t) :
    f x 2 0 = 0 ∧ f x 2 1 = 0 ∧ f x 3 0 = 0 ∧ f x 3 1 = 0 := by
  have hu : IsUnit (f x) := (Group.isUnit x).map f
  obtain ⟨he,hd⟩ := shape (f x) hu hx
  have hz : f x 2 1 = 0 ∧ f x 3 1 = 0 := by
    by_contra hh
    have hn : f x 2 1 ≠ 0 ∨ f x 3 1 ≠ 0 := not_and_or.mp hh
    have hcert := certificate (f x 0 1) (f x 0 2) (f x 0 3) (f x 2 1)
      (f x 2 2) (f x 2 3) (f x 3 1) (f x 3 2) (f x 3 3) hd hn
    rw [←he] at hcert
    have ho (y : H) : ¬ orderFour (f y) := fun h => h.2 (hno4 y h.1)
    rcases hcert with h | h | h | h | h
    · exact ho x h
    · exact ho (x*c) (by simpa only [map_mul,hc] using h)
    · exact ho (x*c*b) (by simpa only [map_mul,hc,hb] using h)
    · exact ho (x*x*c*x*c) (by simpa only [map_mul,hc] using h)
    · exact ho (x*x*c*x*c*b) (by simpa only [map_mul,hc,hb] using h)
  refine ⟨?_,hz.1,?_,hz.2⟩
  · simpa [block] using congrArg (fun q : M => q 2 0) he
  · simpa [block] using congrArg (fun q : M => q 3 0) he
abbrev V2 := Fin 2 → ZMod 2
abbrev V4 := Fin 4 → ZMod 2
abbrev E2 := Multiplicative V2
abbrev E4 := Multiplicative V4

private theorem four_finrank {E : Type*} [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (hc : Nat.card E = 4) :
    Module.finrank (ZMod 2) (Additive E) = 2 := by
  apply Nat.pow_right_injective (by decide : 1 < 2)
  have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)
  change Nat.card E = _ at hh
  simpa only [hc,Nat.card_zmod] using hh.symm

theorem four_coordinates {E : Type*} [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (hc : Nat.card E = 4) : Nonempty (E ≃* E2) := by
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive E) (four_finrank hc)
  exact ⟨b.equivFun.toAddEquiv.toMultiplicativeRight⟩

theorem four_point_coordinates {E : Type*} [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (hc : Nat.card E = 4) (z : E) (hz : z ≠ 1) :
    ∃ c : E ≃* E2, c z = Multiplicative.ofAdd ![1,0] := by
  classical
  let z' : Additive E := Additive.ofMul z
  have hz' : z' ≠ 0 := hz
  have hd := four_finrank hc
  have hlt : Submodule.span (ZMod 2) {z'} < ⊤ := lt_top_iff_ne_top.mpr (by
    intro he
    have hh := finrank_span_singleton (K := ZMod 2) hz'
    rw [he,finrank_top,hd] at hh
    omega)
  obtain ⟨y,_,hy⟩ := SetLike.exists_of_lt hlt
  have hli : LinearIndependent (ZMod 2) ![z',y] := by
    apply (LinearIndependent.pair_iff' hz').mpr
    intro a ha
    apply hy
    rw [←ha]
    exact Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_singleton z'))
  let b := basisOfLinearIndependentOfCardEqFinrank hli
    (by simpa only [Fintype.card_fin] using hd.symm)
  let c : E ≃* E2 := b.equivFun.toAddEquiv.toMultiplicativeRight
  refine ⟨c,?_⟩
  change b.equivFun z' = ![1,0]
  have he : b 0 = z' := by simp [b]
  rw [←he]
  ext i
  fin_cases i <;> simp [Module.Basis.equivFun_self]

def flatten : E2 × E2 ≃* E4 where
  toFun x := Multiplicative.ofAdd ![x.1.toAdd 0,x.1.toAdd 1,x.2.toAdd 0,x.2.toAdd 1]
  invFun x := (Multiplicative.ofAdd ![x.toAdd 0,x.toAdd 1],
    Multiplicative.ofAdd ![x.toAdd 2,x.toAdd 3])
  left_inv x := by
    apply Prod.ext <;> ext i <;> fin_cases i <;> rfl
  right_inv x := by ext i; fin_cases i <;> rfl
  map_mul' x y := by ext i; fin_cases i <;> rfl

def s2 : MulAut E2 where
  toFun x := Multiplicative.ofAdd ![x.toAdd 1,x.toAdd 0+x.toAdd 1]
  invFun x := Multiplicative.ofAdd ![x.toAdd 0+x.toAdd 1,x.toAdd 0]
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

def t2 : MulAut E2 where
  toFun x := Multiplicative.ofAdd ![x.toAdd 0+x.toAdd 1,x.toAdd 1]
  invFun x := Multiplicative.ofAdd ![x.toAdd 0+x.toAdd 1,x.toAdd 1]
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

private def linear (a : MulAut E4) : V4 →ₗ[ZMod 2] V4 :=
  { (AddEquiv.toMultiplicative.symm a).toAddMonoidHom with
    map_smul' := ZMod.map_smul (AddEquiv.toMultiplicative.symm a).toAddMonoidHom }

def matrixHom : MulAut E4 →* M where
  toFun a := LinearMap.toMatrix' (linear a)
  map_one' := by
    change LinearMap.toMatrix' (LinearMap.id) = 1
    exact LinearMap.toMatrix'_one
  map_mul' a b := by
    change LinearMap.toMatrix' ((linear a).comp (linear b)) = _
    exact LinearMap.toMatrix'_comp _ _

theorem matrixHom_apply (a : MulAut E4) (i j : Fin 4) :
    matrixHom a i j = (a (Multiplicative.ofAdd (Pi.single j 1))).toAdd i := rfl

theorem matrixHom_injective : Function.Injective matrixHom := by
  intro a b hab
  have hh : linear a = linear b := LinearMap.toMatrix'.injective hab
  ext v i
  exact congrArg (fun f : V4 →ₗ[ZMod 2] V4 => f v.toAdd i) hh

def extend (a : MulAut E2) : MulAut E4 :=
  (MulAut.congr flatten) (a.prodCongr (MulEquiv.refl E2))

theorem extend_s2 : matrixHom (extend s2) =
    !![0,1,0,0; 1,1,0,0; 0,0,1,0; 0,0,0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixHom_apply,extend,flatten,s2,MulAut.congr_apply,MulEquiv.prodCongr]

theorem extend_t2 : matrixHom (extend t2) =
    !![1,1,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixHom_apply,extend,flatten,t2,MulAut.congr_apply,MulEquiv.prodCongr]

private def e0 : E2 := Multiplicative.ofAdd ![1,0]
private def e1 : E2 := Multiplicative.ofAdd ![0,1]

private theorem four_points : ∀ w : E2, w = 1 ∨ w = e0 ∨ w = e1 ∨ w = e0*e1 := by
  decide

theorem t2_unique (a : MulAut E2) (ha : a ≠ 1) (hfix : a e0 = e0) : a = t2 := by
  have he : a e1 = e0*e1 := by
    rcases four_points (a e1) with he | he | he | he
    · have hh := a.injective (he.trans (map_one a).symm)
      exact False.elim ((by decide : e1 ≠ 1) hh)
    · have hh := a.injective (he.trans hfix.symm)
      exact False.elim ((by decide : e1 ≠ e0) hh)
    · exfalso
      apply ha
      apply MulEquiv.ext
      intro w
      rcases four_points w with rfl | rfl | rfl | rfl
      · exact map_one a
      · exact hfix
      · exact he
      · simp only [map_mul,hfix,he,MulAut.one_apply]
    · exact he
  apply MulEquiv.ext
  intro w
  rcases four_points w with rfl | rfl | rfl | rfl
  · simp only [map_one]
  · simpa [t2,e0] using hfix
  · rw [he]
    decide
  · rw [map_mul,hfix,he]
    decide


public theorem product_plane_preserved
    {H W A : Type*} [Group H] [Group W] [Finite W] [IsElementaryAbelian 2 W]
    [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (hW : Nat.card W = 4) (hA : Nat.card A = 4)
    (ρ : H →* MulAut (W × A))
    (hno4 : ∀ x : H, ρ x ^ 4 = 1 → ρ x ^ 2 = 1)
    (hfull : ∀ a : MulAut W, ∃ h : H, ρ h = a.prodCongr (MulEquiv.refl A))
    (b : H) (σ : MulAut W) (hb : ρ b = σ.prodCongr (MulEquiv.refl A))
    (hσ : σ ≠ 1) (z : W) (hz : z ≠ 1) (hσz : σ z = z)
    (x : H) (hx : Commute (ρ x) (ρ b)) : ∀ w : W, (ρ x (w,1)).2 = 1 := by
  obtain ⟨cW,hzW⟩ := four_point_coordinates hW z hz
  obtain ⟨cA⟩ := four_coordinates hA
  let c : (W × A) ≃* E4 := (cW.prodCongr cA).trans flatten
  let j := MulAut.congr c
  let f : H →* M := matrixHom.comp (j.toMonoidHom.comp ρ)
  have he (a : MulAut W) :
      j (a.prodCongr (MulEquiv.refl A)) = extend ((MulAut.congr cW) a) := by
    ext v
    simp [j,c,extend,MulAut.congr_apply,MulEquiv.prodCongr,Prod.map]
  have hσ' : (MulAut.congr cW) σ = t2 := by
    apply t2_unique
    · intro hh
      apply hσ
      exact (MulAut.congr cW).injective (hh.trans (map_one _).symm)
    · change cW (σ (cW.symm e0)) = e0
      change cW z = e0 at hzW
      rw [←hzW,cW.symm_apply_apply,hσz,hzW]
  have hfb : f b = t := by
    change matrixHom (j (ρ b)) = t
    rw [hb,he,hσ',extend_t2]
    rfl
  obtain ⟨a,ha⟩ := hfull ((MulAut.congr cW).symm s2)
  have hfa : f a = s := by
    change matrixHom (j (ρ a)) = s
    rw [ha,he,MulEquiv.apply_symm_apply,extend_s2]
    rfl
  have hn (y : H) (hy : f y ^ 4 = 1) : f y ^ 2 = 1 := by
    have hfour : ρ y ^ 4 = 1 := by
      apply j.injective
      apply matrixHom_injective
      simpa only [f,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,map_pow,map_one] using hy
    have hh := congrArg (fun q => matrixHom (j q)) (hno4 y hfour)
    simpa only [f,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,map_pow,map_one] using hh
  have hc : Commute (f x) t := by
    rw [←hfb]
    exact hx.map (matrixHom.comp j.toMonoidHom)
  obtain ⟨h20,h21,h30,h31⟩ := plane_preserved f hn a b hfa hfb x hc
  intro w
  have hvec : (c (ρ x (w,1))).toAdd = (f x).mulVec (c (w,1)).toAdd := by
    change _ = (LinearMap.toMatrix' (linear (j (ρ x)))).mulVec (c (w,1)).toAdd
    rw [LinearMap.toMatrix'_mulVec]
    change (c (ρ x (w,1))).toAdd = (c (ρ x (c.symm (c (w,1))))).toAdd
    rw [c.symm_apply_apply]
  have hcoord (v : W × A) :
      (c v).toAdd = ![(cW v.1).toAdd 0,(cW v.1).toAdd 1,
        (cA v.2).toAdd 0,(cA v.2).toAdd 1] := rfl
  have h2 := congrArg (fun v : V4 => v 2) hvec
  have h3 := congrArg (fun v : V4 => v 3) hvec
  rw [hcoord,hcoord] at h2 h3
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_four,h20,h21,h30,h31] at h2 h3
  apply cA.injective
  rw [map_one]
  ext i
  fin_cases i
  · exact h2
  · exact h3

end BinaryPlaneCentralizer
