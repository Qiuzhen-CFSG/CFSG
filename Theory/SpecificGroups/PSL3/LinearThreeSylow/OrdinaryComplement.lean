module

public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Normalizers
public import Theory.GroupTheory.SubgroupCenterImageBound
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Cyclic complements to Sylow-center centralizers in PSL₃

For a field of characteristic two, a highest-root element has trace one.
Thus projective commutation with it lifts to exact commutation in SL₃.
Its centralizer consists of upper triangular matrices with equal first and
last diagonal entries. Multiplication by diag(a⁻¹,a,1), with a the ratio
of those entries, factors every Borel element through this centralizer.
The torus diag(a,a⁻¹,1) meets the centralizer trivially and embeds in PSL₃.

For a field of order 2ⁿ, its units give the cyclic complement of order 2ⁿ−1.
Sylow conjugacy transports the factorization to any specified Sylow subgroup
through an actual projective model isomorphism.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the ordinary
PSL₃ case in the proof of E.6.11, printed p.250 (PDF p.261). The torus uses
`LinearThreeFlags.pointTorus`, also used by the Chapter 15 Borel torus
injection; its projective injectivity follows from the existing line-local
projection embedding.
-/

public section

open scoped MatrixGroups
open Subgroup Matrix Matrix.PSL3 Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.LinearThree
variable (F : Type*) [Field F]

/-- The point torus, regarded as an ambient special-linear homomorphism. -/
def complementTorusSL : Fˣ →* SL(3,F) where
  toFun := pointTorus F
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pointTorus]
  map_mul' a b := by
    apply Subtype.ext
    change diagonal _ = diagonal _ * diagonal _
    rw [diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i <;> simp [mul_comm]

def complementTorus : Fˣ →* PSL(3,F) := (projection F).comp (complementTorusSL F)

theorem complementTorus_injective : Function.Injective (complementTorus F) := by
  intro a b h
  have hm (c : Fˣ) : pointTorus F c ∈ lineLocalSL F := by
    rw [mem_lineLocalSL_iff]
    simp [pointTorus]
  have he : (⟨pointTorus F a, hm a⟩ : lineLocalSL F) = ⟨pointTorus F b, hm b⟩ :=
    lineLocal_projection_injective F h
  exact Units.ext (congrArg (fun x : lineLocalSL F => x.val.val 0 0) he)

private theorem root_trace [CharP F 2] (a : F) :
    Matrix.trace (specialLinear F ⟨0,0,a⟩).val = 1 := by
  change Matrix.trace (matrix F ⟨0,0,a⟩) = 1
  simp [matrix, Matrix.trace, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

/-- A projective commutation with a highest-root element lifts exactly.
The root element has trace one in characteristic two, removing scalars. -/
private theorem root_commute_of_projective [CharP F 2] (g : SL(3,F)) (a : F)
    (hc : projection F g * projective F ⟨0,0,a⟩ =
      projective F ⟨0,0,a⟩ * projection F g) :
    g * specialLinear F ⟨0,0,a⟩ = specialLinear F ⟨0,0,a⟩ * g := by
  let u := specialLinear F ⟨0,0,a⟩
  have he : projection F (g*u*g⁻¹) = projection F u := by
    change projection F g * projective F ⟨0,0,a⟩ * (projection F g)⁻¹ = _
    rw [hc, mul_inv_cancel_right]
    rfl
  have hk := (projection F).eq_iff.mp he
  rw [projection_ker] at hk
  obtain ⟨r,_,hr⟩ := SpecialLinearGroup.mem_center_iff.mp hk
  have hv : (g*u*g⁻¹).val = r • u.val := by
    calc
      (g*u*g⁻¹).val = (u * (u⁻¹ * (g*u*g⁻¹))).val := by simp only [mul_inv_cancel_left]
      _ = u.val * Matrix.scalar (Fin 3) r := by rw [SpecialLinearGroup.coe_mul, ← hr]
      _ = r • u.val := by
        ext i j
        simp [Matrix.scalar, Matrix.mul_diagonal, mul_comm]
  have ht : Matrix.trace (g*u*g⁻¹).val = 1 := by
    change Matrix.trace (g.val*u.val*g⁻¹.val) = 1
    rw [Matrix.trace_mul_cycle]
    have hi : g⁻¹.val * g.val = 1 := congrArg Subtype.val (inv_mul_cancel g)
    rw [hi, one_mul]
    exact root_trace F a
  rw [hv, Matrix.trace_smul, root_trace F a, smul_eq_mul, mul_one] at ht
  have hg : g*u*g⁻¹ = u := Subtype.ext (by simpa [ht] using hv)
  exact mul_inv_eq_iff_eq_mul.mp hg

variable [Finite F]

private theorem root_commute_iff (g : SL(3,F)) :
    (∀ a : F, g * specialLinear F ⟨0,0,a⟩ = specialLinear F ⟨0,0,a⟩ * g) ↔
      g ∈ borelSL F ∧ g.val 0 0 = g.val 2 2 := by
  constructor
  · intro h
    have hh : g.val * matrix F ⟨0,0,1⟩ = matrix F ⟨0,0,1⟩ * g.val :=
      congrArg Subtype.val (h 1)
    have h1 := congrArg (fun x => x 0 0) hh
    have h2 := congrArg (fun x => x 0 1) hh
    have h3 := congrArg (fun x => x 1 2) hh
    have h4 := congrArg (fun x => x 0 2) hh
    simp [matrix, Matrix.mul_apply, Fin.sum_univ_three] at h1 h2 h3 h4
    exact ⟨(mem_borelSL_iff F g).mpr ⟨h3,h1,h2⟩, add_right_cancel (h4.trans (add_comm _ _))⟩
  · rintro ⟨hg,he⟩ a
    obtain ⟨h10,h20,h21⟩ := (mem_borelSL_iff F g).mp hg
    apply Subtype.ext
    change g.val * matrix F ⟨0,0,a⟩ = matrix F ⟨0,0,a⟩ * g.val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrix, Matrix.mul_apply, Fin.sum_univ_three, h10,h20,h21,he,
        mul_comm, add_comm]

/-- The whole centralizer of the highest-root group lies in the Borel.
The two extreme diagonal entries of each lift agree. -/
theorem mem_centralizer_projectiveCenter_iff [CharP F 2] (g : SL(3,F)) :
    projection F g ∈ centralizer (projectiveCenter F : Set PSL(3,F)) ↔
      g ∈ borelSL F ∧ g.val 0 0 = g.val 2 2 := by
  rw [← root_commute_iff]
  constructor
  · intro hc a
    apply root_commute_of_projective F g a
    exact (mem_centralizer_iff.mp hc _ ((mem_projectiveCenter F _).mpr ⟨a,rfl⟩)).symm
  · intro hc
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨a,rfl⟩ := (mem_projectiveCenter F x).mp hx
    exact (congrArg (projection F) (hc a)).symm

/-- Every upper triangular matrix is a product of an element centralizing
the highest-root group and an element of the point torus. -/
theorem root_centralizer_factorization [CharP F 2] (g : SL(3,F))
    (hg : g ∈ borelSL F) :
    ∃ c ∈ centralizer (projectiveCenter F : Set PSL(3,F)), ∃ a : Fˣ,
      projection F g = c * complementTorus F a := by
  obtain ⟨h10,h20,h21⟩ := (mem_borelSL_iff F g).mp hg
  have hd : g.val 0 0 * g.val 1 1 * g.val 2 2 = 1 := by
    have hd := g.property
    rw [Matrix.det_fin_three] at hd
    simpa only [h10,h20,h21,mul_zero,zero_mul,sub_zero,add_zero] using hd
  have h00 : g.val 0 0 ≠ 0 := by intro hz; simp [hz] at hd
  have h22 : g.val 2 2 ≠ 0 := by intro hz; simp [hz] at hd
  let a : Fˣ := Units.mk0 (g.val 0 0 / g.val 2 2) (div_ne_zero h00 h22)
  let t := pointTorus F a⁻¹
  refine ⟨projection F (g*t), ?_, a, ?_⟩
  · rw [mem_centralizer_projectiveCenter_iff]
    refine ⟨(borelSL F).mul_mem hg (pointTorus_mem_borel F a⁻¹), ?_⟩
    change (g.val * t.val) 0 0 = (g.val * t.val) 2 2
    simp [t, pointTorus, Matrix.mul_diagonal, a]
    field_simp
  · change projection F g = projection F (g * complementTorusSL F a⁻¹) *
        projection F (complementTorusSL F a)
    rw [map_mul, map_inv, map_inv, inv_mul_cancel_right]

theorem centralizer_sup_complementTorus [CharP F 2] :
    centralizer (projectiveCenter F : Set PSL(3,F)) ⊔ (complementTorus F).range =
      borel F := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      obtain ⟨g,rfl⟩ := projection_surjective F x
      exact mem_map_of_mem _ ((mem_centralizer_projectiveCenter_iff F g).mp hx).1
    · rintro x ⟨a,rfl⟩
      exact mem_map_of_mem _ (pointTorus_mem_borel F a)
  · rintro x ⟨g,hg,rfl⟩
    obtain ⟨c,hc,a,he⟩ := root_centralizer_factorization F g hg
    rw [he]
    exact mul_mem (mem_sup_left hc) (mem_sup_right ⟨a,rfl⟩)

theorem centralizer_inf_complementTorus [CharP F 2] :
    centralizer (projectiveCenter F : Set PSL(3,F)) ⊓ (complementTorus F).range = ⊥ := by
  apply le_bot_iff.mp
  rintro x ⟨hc,a,rfl⟩
  have he := ((mem_centralizer_projectiveCenter_iff F (pointTorus F a)).mp hc).2
  have ha : a = 1 := Units.ext (by simpa [pointTorus] using he)
  simp [ha]

omit [Finite F] in
theorem projectiveCenter_eq_mapped_center : projectiveCenter F =
    (center (unipotent F)).map (unipotent F).subtype := by
  exact (marked_center F (unipotent F) (unipotentEquiv F)).symm

private theorem map_centralizer_equiv {J H : Type*} [Group J] [Group H]
    (e : J ≃* H) (A : Subgroup J) :
    (centralizer (A : Set J)).map e.toMonoidHom =
      centralizer (A.map e.toMonoidHom : Set H) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  obtain ⟨y,rfl⟩ := e.surjective x
  refine ⟨y, mem_centralizer_iff.mpr ?_, rfl⟩
  intro a ha
  apply e.injective
  simpa only [map_mul] using mem_centralizer_iff.mp hx (e a) (mem_map_of_mem _ ha)

/-- The complement transports along an actual model isomorphism and Sylow
conjugacy. The centralizer is in the whole group, not just the normalizer. -/
theorem exists_sylow_center_complement {J : Type*} [Group J] [Finite J]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (e : J ≃* PSL(3,F)) (S : Sylow 2 J) :
    ∃ X : Subgroup J, X ≤ normalizer (S : Set J) ∧
      Nonempty (X ≃* Multiplicative (ZMod (2 ^ n - 1))) ∧
      centralizer ((center S).map (S : Subgroup J).subtype : Set J) ⊔ X =
        normalizer (S : Set J) ∧
      centralizer ((center S).map (S : Subgroup J).subtype : Set J) ⊓ X = ⊥ := by
  let := Fintype.ofFinite F
  have hc : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card, hF]
    simp [Nat.pow_mod, Nat.ne_of_gt hn])
  let : CharP F 2 := ringChar.of_eq hc
  let P := (unipotentSylow F hn hF).mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq J P S
  let f : PSL(3,F) ≃* J := e.symm.trans (MulAut.conj g)
  have hS : (unipotent F).map f.toMonoidHom = (S : Subgroup J) := by
    have hh := congrArg Sylow.toSubgroup hg
    change ((unipotent F).map e.symm.toMonoidHom).map (MulAut.conj g).toMonoidHom = _ at hh
    change (unipotent F).map ((MulAut.conj g).toMonoidHom.comp e.symm.toMonoidHom) = _
    rw [← Subgroup.map_map]
    exact hh
  have hN : (borel F).map f.toMonoidHom = normalizer (S : Set J) := by
    rw [← normalizer_unipotent F hn hF, map_equiv_normalizer_eq, hS]
    rfl
  have hZ : (projectiveCenter F).map f.toMonoidHom =
      (center S).map (S : Subgroup J).subtype := by
    rw [projectiveCenter_eq_mapped_center, map_subgroup_center_eq _ f.injective, hS]
  have hC : (centralizer (projectiveCenter F : Set PSL(3,F))).map f.toMonoidHom =
      centralizer ((center S).map (S : Subgroup J).subtype : Set J) := by
    rw [map_centralizer_equiv, hZ]
  let X := (complementTorus F).range.map f.toMonoidHom
  have hsup : centralizer ((center S).map (S : Subgroup J).subtype : Set J) ⊔ X =
      normalizer (S : Set J) := by
    rw [← hC, ← Subgroup.map_sup, centralizer_sup_complementTorus, hN]
  refine ⟨X, le_sup_right.trans hsup.le, ?_, hsup, ?_⟩
  · let eX : Fˣ ≃* X :=
      (MonoidHom.ofInjective (complementTorus_injective F)).trans
        ((complementTorus F).range.equivMapOfInjective f.toMonoidHom f.injective)
    refine ⟨eX.symm.trans (mulEquivOfCyclicCardEq ?_)⟩
    simp only [Nat.card_units, hF, Nat.card_congr (Multiplicative.toAdd :
      Multiplicative (ZMod (2 ^ n - 1)) ≃ ZMod (2 ^ n - 1)), Nat.card_zmod]
  · rw [← hC, ← Subgroup.map_inf _ _ _ f.injective, centralizer_inf_complementTorus, Subgroup.map_bot]

end Matrix.PSL3.LinearThree
