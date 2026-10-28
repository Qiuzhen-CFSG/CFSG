module
public import Theory.Representation.HermitianTensorThree.UnipotentRadicals
public import Theory.ElementaryAbelian.BinaryRankDifference
import all Theory.Representation.HermitianTensorThree.UnipotentRadicals

/-!
# Fixed-space spans for Hermitian elementary actors

For either elementary unipotent radical, fixed-field root lines have rank n
and hence corank 3n. Their fixed spaces span the eight-dimensional displayed
hyperplane for the plane radical, and the entire Hermitian module for the
point radical. Intersecting each root line with an arbitrary elementary actor
only decreases its relative index. Sylow conjugacy therefore gives a binary
span of dimension at least 8n for every inner elementary actor.

This proves the lower bound needed from H.4.5 without its printed assertion
that the plane radical is nonquadratic on that hyperplane. The Chapter 8
weak-closure consumer transports the bound to its actual automizer dual core.

The implementation import deliberately reuses the package-internal Sylow
conjugator from UnipotentRadicals, as does UnipotentRadicals.LargeActors.
Its public boundary remains unchanged.

Source: Aschbacher--Smith H.4.5, printed p.381 (refs/quasithin.pdf).
-/

open Subgroup Representation Representation.BinaryOffender
open Representation.HermitianTensorThree
open Matrix.PSL3Even.UnipotentGeometry
namespace Representation.HermitianTensorThree.DualCoreSpan
public noncomputable section
variable (n : ℕ) [NeZero n]

private def pointLineHom (x c : E n) : Multiplicative (F n) →* U (E n) where
  toFun t := ⟨x*t.toAdd.val,0,c*t.toAdd.val⟩
  map_one' := by apply U.ext <;> simp
  map_mul' a b := by
    apply U.ext <;> simp [mul_add]

private def planeLineHom (y c : E n) : Multiplicative (F n) →* U (E n) where
  toFun t := ⟨0,y*t.toAdd.val,c*t.toAdd.val⟩
  map_one' := by apply U.ext <;> simp
  map_mul' a b := by
    apply U.ext <;> simp [mul_add]

omit [NeZero n] in
private theorem pointLineHom_injective (x c : E n) (h : x ≠ 0 ∨ c ≠ 0) :
    Function.Injective (pointLineHom n x c) := by
  intro a b hab
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  rcases h with hx | hc
  · exact mul_left_cancel₀ hx (congrArg U.x hab)
  · exact mul_left_cancel₀ hc (congrArg U.c hab)

omit [NeZero n] in
private theorem planeLineHom_injective (y c : E n) (h : y ≠ 0 ∨ c ≠ 0) :
    Function.Injective (planeLineHom n y c) := by
  intro a b hab
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  rcases h with hy | hc
  · exact mul_left_cancel₀ hy (congrArg U.y hab)
  · exact mul_left_cancel₀ hc (congrArg U.c hab)

private theorem rank_range_line (f : Multiplicative (F n) →* U (E n))
    (hf : Function.Injective f) : rank f.range = n := by
  change Nat.log 2 (Nat.card (Set.range f)) = n
  rw [Nat.card_range_of_injective hf, show Nat.card (Multiplicative (F n)) = Nat.card (F n) from rfl,
    card_F, Nat.log_pow Nat.one_lt_two]

omit [NeZero n] in
private theorem pointLine_le (x c : E n) : (pointLineHom n x c).range ≤ V₁ (E n) := by
  rintro _ ⟨a,rfl⟩
  exact (mem_V₁ _ _).mpr rfl

omit [NeZero n] in
private theorem planeLine_le (y c : E n) : (planeLineHom n y c).range ≤ V₂ (E n) := by
  rintro _ ⟨a,rfl⟩
  exact (mem_V₂ _ _).mpr rfl

-- The following spans use the literal elementary root lines, of binary rank n.
private theorem fixed_mem_of_line
    (W : Submodule (ZMod 2) (Space n))
    (Q : Subgroup (U (E n)))
    (hW : ∀ R : Subgroup (U (E n)), R ≤ Q → rank R = n →
      fixedSpace (UnipotentRadicals.ambientAction n)
        (R.map (UnipotentRadicals.unipotentHom n)) ≤ W)
    (f : Multiplicative (F n) →* U (E n)) (hf : Function.Injective f)
    (hfQ : f.range ≤ Q) (X : Space n)
    (hX : ∀ t, UnipotentRadicals.unipotentHom n (f t) X = X) : X ∈ W := by
  apply hW f.range hfQ (rank_range_line n f hf)
  rintro ⟨_,a,ha,rfl⟩
  obtain ⟨t,rfl⟩ := ha
  exact hX t

private theorem plane_corner_fixed (a b : F n) (u : E n) (t : Multiplicative (F n)) :
    UnipotentRadicals.unipotentHom n (planeLineHom n 0 1 t)
      ((HermitianTensorThree.coordinates n).symm (![a,b,0], ![u,0,0])) =
      (HermitianTensorThree.coordinates n).symm (![a,b,0], ![u,0,0]) := by
  apply Subtype.ext
  change matrix (E n) _ * _ * adjoint n (matrix (E n) _) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeLineHom, matrix, HermitianTensorThree.coordinates, adjoint, Matrix.mul_apply,
      Fin.sum_univ_three]

private theorem plane_first_cross_fixed (v : E n) (t : Multiplicative (F n)) :
    UnipotentRadicals.unipotentHom n (planeLineHom n 0 v t)
      ((HermitianTensorThree.coordinates n).symm (![0,0,0], ![0,v,0])) =
      (HermitianTensorThree.coordinates n).symm (![0,0,0], ![0,v,0]) := by
  have ht : sigma n t.toAdd.val = t.toAdd.val := t.toAdd.property
  apply Subtype.ext
  change matrix (E n) _ * _ * adjoint n (matrix (E n) _) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeLineHom, matrix, HermitianTensorThree.coordinates, adjoint, Matrix.mul_apply,
      Fin.sum_univ_three, map_mul, ht]
  all_goals ring_nf
  all_goals simp only [CharTwo.two_eq_zero, mul_zero]

private theorem plane_second_cross_fixed (w : E n) (t : Multiplicative (F n)) :
    UnipotentRadicals.unipotentHom n (planeLineHom n w 0 t)
      ((HermitianTensorThree.coordinates n).symm (![0,0,0], ![0,0,w])) =
      (HermitianTensorThree.coordinates n).symm (![0,0,0], ![0,0,w]) := by
  have ht : sigma n t.toAdd.val = t.toAdd.val := t.toAdd.property
  apply Subtype.ext
  change matrix (E n) _ * _ * adjoint n (matrix (E n) _) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeLineHom, matrix, HermitianTensorThree.coordinates, adjoint, Matrix.mul_apply,
      Fin.sum_univ_three, map_mul, ht]
  all_goals ring_nf
  all_goals simp only [CharTwo.two_eq_zero, mul_zero]

-- Each cross-coordinate is fixed by a fixed-field line in its own direction.
private theorem plane_span_mem
    (W : Submodule (ZMod 2) (Space n))
    (hW : ∀ R : Subgroup (U (E n)), R ≤ V₂ (E n) → rank R = n →
      fixedSpace (UnipotentRadicals.ambientAction n)
        (R.map (UnipotentRadicals.unipotentHom n)) ≤ W)
    (a b : F n) (u v w : E n) :
    (HermitianTensorThree.coordinates n).symm (![a,b,0], ![u,v,w]) ∈ W := by
  have hcorner := fixed_mem_of_line n W (V₂ (E n)) hW (planeLineHom n 0 1)
    (planeLineHom_injective n 0 1 (Or.inr one_ne_zero)) (planeLine_le n 0 1) _
    (plane_corner_fixed n a b u)
  have hv : (HermitianTensorThree.coordinates n).symm (![0,0,0], ![0,v,0]) ∈ W := by
    by_cases hv : v = 0
    · subst v
      change (HermitianTensorThree.coordinates n).symm 0 ∈ W
      simpa only [map_zero] using W.zero_mem
    exact fixed_mem_of_line n W (V₂ (E n)) hW (planeLineHom n 0 v)
      (planeLineHom_injective n 0 v (Or.inr hv)) (planeLine_le n 0 v) _
      (plane_first_cross_fixed n v)
  have hw : (HermitianTensorThree.coordinates n).symm (![0,0,0], ![0,0,w]) ∈ W := by
    by_cases hw : w = 0
    · subst w
      change (HermitianTensorThree.coordinates n).symm 0 ∈ W
      simpa only [map_zero] using W.zero_mem
    exact fixed_mem_of_line n W (V₂ (E n)) hW (planeLineHom n w 0)
      (planeLineHom_injective n w 0 (Or.inl hw)) (planeLine_le n w 0) _
      (plane_second_cross_fixed n w)
  have he : (HermitianTensorThree.coordinates n).symm (![a,b,0], ![u,v,w]) =
      (HermitianTensorThree.coordinates n).symm (![a,b,0], ![u,0,0]) +
      (HermitianTensorThree.coordinates n).symm (![0,0,0], ![0,v,0]) +
      (HermitianTensorThree.coordinates n).symm (![0,0,0], ![0,0,w]) := by
    apply (HermitianTensorThree.coordinates n).injective
    simp only [map_add, LinearEquiv.apply_symm_apply]
    ext i <;> fin_cases i <;> simp
  rw [he]
  exact W.add_mem (W.add_mem hcorner hv) hw

private theorem point_corner_fixed (a b : F n) (u : E n) (t : Multiplicative (F n)) :
    UnipotentRadicals.unipotentHom n (pointLineHom n 0 1 t)
      ((HermitianTensorThree.coordinates n).symm (![a,b,0], ![u,0,0])) =
      (HermitianTensorThree.coordinates n).symm (![a,b,0], ![u,0,0]) :=
by
  have he : pointLineHom n 0 1 t = planeLineHom n 0 1 t := by
    apply U.ext <;> simp [pointLineHom,planeLineHom]
  rw [he]
  exact plane_corner_fixed n a b u t

private theorem point_last_diagonal_fixed (c : F n) (t : Multiplicative (F n)) :
    UnipotentRadicals.unipotentHom n (pointLineHom n 1 0 t)
      ((HermitianTensorThree.coordinates n).symm (![0,0,c], ![0,0,0])) =
      (HermitianTensorThree.coordinates n).symm (![0,0,c], ![0,0,0]) := by
  apply Subtype.ext
  change matrix (E n) _ * _ * adjoint n (matrix (E n) _) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pointLineHom, matrix, HermitianTensorThree.coordinates, adjoint, Matrix.mul_apply,
      Fin.sum_univ_three]

private theorem point_singular_corner_fixed (w : E n) (t : Multiplicative (F n)) :
    UnipotentRadicals.unipotentHom n (pointLineHom n (sigma n w) 1 t)
      ((HermitianTensorThree.coordinates n).symm
        (![0,1,⟨w*sigma n w, by change sigma n (w*sigma n w) = w*sigma n w; rw [map_mul,sigma_involutive]; ring⟩], ![0,0,w])) =
      (HermitianTensorThree.coordinates n).symm
        (![0,1,⟨w*sigma n w, by change sigma n (w*sigma n w) = w*sigma n w; rw [map_mul,sigma_involutive]; ring⟩], ![0,0,w]) := by
  have ht : sigma n t.toAdd.val = t.toAdd.val := t.toAdd.property
  have h4 : (4 : E n) = 0 := by
    calc (4 : E n) = 2 + 2 := by norm_num
         _ = 0 := CharTwo.add_self_eq_zero (2 : E n)
  apply Subtype.ext
  change matrix (E n) _ * _ * adjoint n (matrix (E n) _) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pointLineHom, matrix, HermitianTensorThree.coordinates, adjoint, Matrix.mul_apply,
      Fin.sum_univ_three, map_mul, ht, sigma_involutive n w]
  all_goals ring_nf
  all_goals simp only [CharTwo.two_eq_zero, h4, mul_zero]

private theorem point_span_mem
    (W : Submodule (ZMod 2) (Space n))
    (hW : ∀ R : Subgroup (U (E n)), R ≤ V₁ (E n) → rank R = n →
      fixedSpace (UnipotentRadicals.ambientAction n)
        (R.map (UnipotentRadicals.unipotentHom n)) ≤ W)
    (a b c : F n) (u v w : E n) :
    (HermitianTensorThree.coordinates n).symm (![a,b,c], ![u,v,w]) ∈ W := by
  have hcorner (a b : F n) (u : E n) :=
    fixed_mem_of_line n W (V₁ (E n)) hW (pointLineHom n 0 1)
      (pointLineHom_injective n 0 1 (Or.inr one_ne_zero)) (pointLine_le n 0 1) _
      (point_corner_fixed n a b u)
  have hdiag (c : F n) := fixed_mem_of_line n W (V₁ (E n)) hW (pointLineHom n 1 0)
    (pointLineHom_injective n 1 0 (Or.inl one_ne_zero)) (pointLine_le n 1 0) _
    (point_last_diagonal_fixed n c)
  have hv : (HermitianTensorThree.coordinates n).symm (![0,0,0], ![0,v,0]) ∈ W := by
    by_cases hv : v = 0
    · subst v
      change (HermitianTensorThree.coordinates n).symm 0 ∈ W
      simpa only [map_zero] using W.zero_mem
    exact fixed_mem_of_line n W (V₁ (E n)) hW (pointLineHom n 0 v)
      (pointLineHom_injective n 0 v (Or.inr hv)) (pointLine_le n 0 v) _
      (fun t => by
        have he : pointLineHom n 0 v t = planeLineHom n 0 v t := by
          apply U.ext <;> simp [pointLineHom,planeLineHom]
        rw [he]
        exact plane_first_cross_fixed n v t)
  let d : F n := ⟨w*sigma n w, by change sigma n (w*sigma n w) = w*sigma n w; rw [map_mul,sigma_involutive]; ring⟩
  have hw := fixed_mem_of_line n W (V₁ (E n)) hW (pointLineHom n (sigma n w) 1)
    (pointLineHom_injective n (sigma n w) 1 (Or.inr one_ne_zero))
    (pointLine_le n (sigma n w) 1) _ (point_singular_corner_fixed n w)
  have he : (HermitianTensorThree.coordinates n).symm (![a,b,c], ![u,v,w]) =
      (HermitianTensorThree.coordinates n).symm (![a,b-1,0], ![u,0,0]) +
      (HermitianTensorThree.coordinates n).symm (![0,0,c-d], ![0,0,0]) +
      (HermitianTensorThree.coordinates n).symm (![0,0,0], ![0,v,0]) +
      (HermitianTensorThree.coordinates n).symm (![0,1,d], ![0,0,w]) := by
    apply (HermitianTensorThree.coordinates n).injective
    simp only [map_add, LinearEquiv.apply_symm_apply]
    ext i <;> fin_cases i <;> simp
  rw [he]
  exact W.add_mem (W.add_mem (W.add_mem (hcorner a (b-1) u) (hdiag (c-d))) hv) hw

private theorem eight_coordinates_rank_le
    (W : Submodule (ZMod 2) (Space n))
    (hW : ∀ (a b : F n) (u v w : E n),
      (HermitianTensorThree.coordinates n).symm (![a,b,0], ![u,v,w]) ∈ W) :
    8*n ≤ Module.finrank (ZMod 2) W := by
  let f : ((F n × F n) × (Fin 3 → E n)) → W := fun x =>
    ⟨(HermitianTensorThree.coordinates n).symm
      (![x.1.1,x.1.2,0], ![x.2 0,x.2 1,x.2 2]), hW _ _ _ _ _⟩
  have hi : Function.Injective f := by
    intro x y h
    have hc := congrArg (fun z : W => HermitianTensorThree.coordinates n z.val) h
    dsimp only [f] at hc
    simp only [LinearEquiv.apply_symm_apply] at hc
    change (![x.1.1,x.1.2,0], ![x.2 0,x.2 1,x.2 2]) =
      (![y.1.1,y.1.2,0], ![y.2 0,y.2 1,y.2 2]) at hc
    apply Prod.ext
    · exact Prod.ext (congrArg (fun z => z.1 0) hc) (congrArg (fun z => z.1 1) hc)
    · ext i
      fin_cases i
      · exact congrArg (fun z => z.2 0) hc
      · exact congrArg (fun z => z.2 1) hc
      · exact congrArg (fun z => z.2 2) hc
  have hc := Nat.card_le_card_of_injective f hi
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W),Nat.card_zmod] at hc
  simp only [Nat.card_prod,Nat.card_fun,Nat.card_fin,card_F,card_E,←pow_mul,←pow_add] at hc
  have he := (pow_le_pow_iff_right₀ Nat.one_lt_two).mp hc
  omega

private theorem plane_fixed_span_rank_le
    (W : Submodule (ZMod 2) (Space n))
    (hW : ∀ R : Subgroup (U (E n)), R ≤ V₂ (E n) → rank R = n →
      fixedSpace (UnipotentRadicals.ambientAction n)
        (R.map (UnipotentRadicals.unipotentHom n)) ≤ W) :
    8*n ≤ Module.finrank (ZMod 2) W :=
  eight_coordinates_rank_le n W (plane_span_mem n W hW)

private theorem point_fixed_span_rank_le
    (W : Submodule (ZMod 2) (Space n))
    (hW : ∀ R : Subgroup (U (E n)), R ≤ V₁ (E n) → rank R = n →
      fixedSpace (UnipotentRadicals.ambientAction n)
        (R.map (UnipotentRadicals.unipotentHom n)) ≤ W) :
    8*n ≤ Module.finrank (ZMod 2) W :=
  eight_coordinates_rank_le n W (fun a b u v w => point_span_mem n W hW a b 0 u v w)

omit [NeZero n] in
private theorem intersection_line_corank_le
    (Q A R : Subgroup (U (E n))) [IsElementaryAbelian 2 Q]
    (hAQ : A ≤ Q) (hRQ : R ≤ Q) (hQ : rank Q = 4*n) (hR : rank R = n) :
    Nat.log 2 ((A ⊓ R).relIndex A) ≤ 3*n := by
  rw [inf_relIndex_left]
  have hi : R.relIndex A ≤ R.relIndex Q :=
    relIndex_le_of_le_right hAQ (show R.relIndex Q ≠ 0 from Nat.card_pos.ne')
  have he := log_card_sub_log_card_eq_log_relIndex Q R hRQ
  change rank Q - rank R = Nat.log 2 (R.relIndex Q) at he
  rw [hQ,hR] at he
  have hle := Nat.log_mono_right (b := 2) hi
  omega

private theorem unipotent_fixed_span_rank_le
    (A : Subgroup (U (E n))) [IsElementaryAbelian 2 A]
    (W : Submodule (ZMod 2) (Space n))
    (hW : ∀ R : Subgroup (U (E n)), R ≤ A → Nat.log 2 (R.relIndex A) ≤ 3*n →
      fixedSpace (UnipotentRadicals.ambientAction n)
        (R.map (UnipotentRadicals.unipotentHom n)) ≤ W) :
    8*n ≤ Module.finrank (ZMod 2) W := by
  have hsub (Q : Subgroup (U (E n))) [IsElementaryAbelian 2 Q]
      (hAQ : A ≤ Q) (hQ : rank Q = 4*n)
      (R : Subgroup (U (E n))) (hRQ : R ≤ Q) (hR : rank R = n) :
      fixedSpace (UnipotentRadicals.ambientAction n)
        (R.map (UnipotentRadicals.unipotentHom n)) ≤ W := by
    intro X hX
    apply hW (A ⊓ R) inf_le_left
      (intersection_line_corank_le n Q A R hAQ hRQ hQ hR)
    rintro ⟨_,a,ha,rfl⟩
    exact hX ⟨_,mem_map_of_mem _ ha.2⟩
  rcases elementary_le_plane (E n) A with hA | hA
  · apply point_fixed_span_rank_le n W
    apply hsub (V₁ (E n)) hA
    rw [rank,card_V₁,card_E,←pow_mul,Nat.log_pow Nat.one_lt_two]
    omega
  · apply plane_fixed_span_rank_le n W
    apply hsub (V₂ (E n)) hA
    rw [rank,card_V₂,card_E,←pow_mul,Nat.log_pow Nat.one_lt_two]
    omega

-- Conjugation preserves the fixed-space spanning premise.
private theorem conjugate_spanning
    (A : Subgroup (Space n ≃ₗ[ZMod 2] Space n))
    (W : Submodule (ZMod 2) (Space n)) (k : ℕ)
    (hW : ∀ R : Subgroup (Space n ≃ₗ[ZMod 2] Space n), R ≤ A →
      Nat.log 2 (R.relIndex A) ≤ k → fixedSpace (UnipotentRadicals.ambientAction n) R ≤ W)
    (c : Space n ≃ₗ[ZMod 2] Space n)
    (R : Subgroup (Space n ≃ₗ[ZMod 2] Space n))
    (hR : R ≤ A.map (MulAut.conj c).toMonoidHom)
    (hr : Nat.log 2 (R.relIndex (A.map (MulAut.conj c).toMonoidHom)) ≤ k) :
    fixedSpace (UnipotentRadicals.ambientAction n) R ≤ W.map c.toLinearMap := by
  let d := (MulAut.conj c).symm
  let S := R.map d.toMonoidHom
  have hA : (A.map (MulAut.conj c).toMonoidHom).map d.toMonoidHom = A := by
    rw [map_map]
    change A.map ((MulAut.conj c).symm.toMonoidHom.comp (MulAut.conj c).toMonoidHom) = A
    simp
  have hS : S ≤ A := by
    rw [←hA]
    exact map_mono hR
  have hs : Nat.log 2 (S.relIndex A) ≤ k := by
    rw [←hA,relIndex_map_map_of_injective _ _ d.injective]
    exact hr
  intro X hX
  have hfix : c.symm X ∈ fixedSpace (UnipotentRadicals.ambientAction n) S := by
    rintro ⟨_,a,ha,rfl⟩
    have hx := hX ⟨a,ha⟩
    change c.symm (a (c (c.symm X))) = c.symm X
    rw [c.apply_symm_apply]
    exact congrArg c.symm hx
  exact ⟨c.symm X,hW S hS hs hfix,c.apply_symm_apply X⟩

/-- Fixed spaces of subgroups of corank at most 3n span at least 8n
binary dimensions for every elementary actor inside the Hermitian image. -/
theorem inner_fixed_span_rank_le
    (A : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) [IsElementaryAbelian 2 A]
    (hA : A ≤ binaryImage n)
    (W : Submodule (ZMod 2) (Space n))
    (hW : ∀ R : Subgroup (Space n ≃ₗ[ZMod 2] Space n), R ≤ A →
      Nat.log 2 (R.relIndex A) ≤ 3*n → fixedSpace (UnipotentRadicals.ambientAction n) R ≤ W) :
    8*n ≤ Module.finrank (ZMod 2) W := by
  obtain ⟨c,hc⟩ := UnipotentRadicals.two_subgroup_conjugate_le_unipotent n A
    (IsElementaryAbelian.isPGroup 2 A) hA
  let f := (MulAut.conj (binaryActionHom n c)).toMonoidHom
  let B := (A.map f).comap (UnipotentRadicals.unipotentHom n)
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hi : Function.Injective ((UnipotentRadicals.unipotentHom n).subgroupComap (A.map f)) :=
    fun a b h => Subtype.ext (UnipotentRadicals.unipotentHom_injective n (congrArg Subtype.val h))
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective _ hi
  have hm : B.map (UnipotentRadicals.unipotentHom n) = A.map f := map_comap_eq_self hc
  have hspan := unipotent_fixed_span_rank_le n B
    (W.map (binaryActionHom n c).toLinearMap) (by
      intro R hR hr
      apply conjugate_spanning n A W (3*n) hW (binaryActionHom n c)
      · rw [←hm]
        exact map_mono hR
      · rw [←hm,relIndex_map_map_of_injective _ _ (UnipotentRadicals.unipotentHom_injective n)]
        exact hr)
  rwa [(binaryActionHom n c).finrank_map_eq] at hspan

end
end Representation.HermitianTensorThree.DualCoreSpan
