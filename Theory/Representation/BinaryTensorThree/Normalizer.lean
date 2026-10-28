module
public import Theory.Representation.BinaryTensorThree.WreathCoordinates
public import Theory.Representation.SL3DoubledNaturalOffenders.Centralizer
public import Theory.GroupTheory.NormalProductCoordinate
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# The full linear normalizer of the binary tensor base

A normalizer permutes the two simple factors. For a factor-preserving map,
a nonzero natural block is invertible, by elementary transvections. Removing
this block leaves the scalar multiplicity commutant, giving two actual
invertible tensor factors. Composing with transpose handles factor exchange.
Thus the normalizer of GL₃(2) × GL₃(2) on its nine-dimensional tensor is
exactly the concrete wreath group, without an assumed outer-action marking.

The original Chapter 10 consumer applies this to the image of L₀. The
original exchanger and its two-group action kernel then force the image
of L₀T to be the whole tensor group.
Source: Aschbacher--Smith H.4.4 and §8.3, printed pp.383--385,723--724.
The block argument follows the existing doubled-natural calculation in
SL3DoubledNaturalOffenders/NormalizerCoverage/Factorization.lean.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped TensorProduct
namespace BinaryTensorThree
set_option backward.isDefEq.respectTransparency false

private theorem row_apply (g : Factor) (X : Space) (i : Fin 3) :
    baseAction (1,g) X i = g (X i) := by
  obtain ⟨x,rfl⟩ := coordinates.surjective X
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
    change (0 : Natural) = g 0
    rw [map_zero]
  | tmul x y =>
    rw [baseAction_tmul]
    ext j
    simp only [coordinates_tmul]
    change x i * g y j = g (x i • y) j
    rw [map_smul]
    rfl
  | add x y hx hy =>
    simp only [map_add]
    change _ = g (coordinates x i + coordinates y i)
    rw [map_add]
    exact congrArg₂ (· + ·) hx hy

private theorem column_apply (g : Factor) (X : Space) (i j : Fin 3) :
    baseAction (g,1) X i j = g (fun k => X k j) i := by
  have h := congrArg (fun Y : Space => Y j i) (flip_baseAction (g,1) X)
  simp only [flip_apply,row_apply] at h
  have he : flip X j = (fun k => X k j) := by funext k; rfl
  rw [he] at h
  exact h

private theorem scalar_commutant (f : Natural →ₗ[ZMod 2] Natural)
    (hf : ∀ g : Factor, ∀ v, f (g v) = g (f v)) :
    ∃ c : ZMod 2, ∀ v, f v = c • v := by
  apply Representation.SL3DoubledNaturalOffenders.natural_centralizer_scalar f.toAddMonoidHom
  intro g v
  exact hf (Matrix.SpecialLinearGroup.toLin' g) v

private theorem intertwiner_injective (f : Natural →ₗ[ZMod 2] Natural)
    (hf : f ≠ 0) (φ : Factor → Factor)
    (he : ∀ (g : Factor) v, f (g v) = φ g (f v)) :
    Function.Injective f := by
  apply (LinearMap.ker_eq_bot).mp
  apply (LinearMap.ker_eq_bot').mpr
  intro v hv
  by_contra hne
  obtain ⟨j,hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    apply hne
    funext j
    simpa using not_exists.mp h j
  have hstep (w : Natural) (hw : f w = 0) {i j : Fin 3} (hij : i ≠ j)
      (a : ZMod 2) : f (Pi.single i (a * w j)) = 0 := by
    have h := he (Matrix.SpecialLinearGroup.toLin'
      (Matrix.SpecialLinearGroup.transvection hij a)) w
    have ht : Matrix.SpecialLinearGroup.toLin'
        (Matrix.SpecialLinearGroup.transvection hij a) w = w + Pi.single i (a*w j) := by
      change ((1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) + Matrix.single i j a).mulVec w = _
      simp only [Matrix.add_mulVec,Matrix.one_mulVec,Matrix.single_mulVec_eq]
      congr 1
      funext k
      by_cases hk : k = i <;> simp [hk]
    rw [ht,map_add,hw,map_zero,zero_add] at h
    exact h
  have hs (i : Fin 3) (a : ZMod 2) : f (Pi.single i a) = 0 := by
    by_cases hij : i = j
    · obtain ⟨k,hkj⟩ : ∃ k : Fin 3, k ≠ j := by fin_cases j <;> decide
      have hk : f (Pi.single k 1) = 0 := by
        simpa [hj] using hstep v hv hkj (v j)⁻¹
      subst i
      simpa using hstep (Pi.single k 1) hk hkj.symm a
    · simpa only [div_mul_cancel₀ a hj] using hstep v hv hij (a / v j)
  apply hf
  apply LinearMap.ext
  intro w
  have hw : w = ∑ i : Fin 3, Pi.single i (w i) := by ext i; simp
  rw [hw,map_sum]
  simp [hs]

private theorem row_centralizer (f : Space ≃ₗ[ZMod 2] Space)
    (hf : ∀ g : Factor, ∀ X, f (baseAction (1,g) X) = baseAction (1,g) (f X)) :
    ∃ b : Factor, f = baseAction (b,1) := by
  classical
  let block (i j : Fin 3) : Natural →ₗ[ZMod 2] Natural := {
    toFun v := f (Pi.single j v) i
    map_add' v w := by
      rw [Pi.single_add,map_add]
      rfl
    map_smul' a v := by
      rw [Pi.single_smul,map_smul]
      rfl }
  have hb (i j : Fin 3) (g : Factor) (v : Natural) :
      block i j (g v) = g (block i j v) := by
    have hs : baseAction (1,g) (Pi.single j v) = Pi.single j (g v) := by
      ext k l
      rw [row_apply]
      by_cases hk : k = j <;> simp [hk,Pi.single_eq_of_ne]
    change f (Pi.single j (g v)) i = _
    rw [←hs,hf,row_apply]
    rfl
  choose c hc using fun i j => scalar_commutant (block i j) (hb i j)
  have hformula (X : Space) (i j : Fin 3) : f X i j = ∑ k : Fin 3, c i k * X k j := by
    have hx : X = ∑ k : Fin 3, Pi.single k (X k) := by
      funext k
      simp [Finset.sum_apply]
    conv_lhs => rw [hx,map_sum]
    change (∑ k : Fin 3, f (Pi.single k (X k)) i j) = _
    apply Finset.sum_congr rfl
    intro k hk
    exact congrFun (hc i k (X k)) j
  let b : Natural →ₗ[ZMod 2] Natural := Matrix.mulVecLin c
  have hbi : Function.Injective b := by
    intro v w hvw
    have hfw : f (fun i j => if j = 0 then v i else 0) =
        f (fun i j => if j = 0 then w i else 0) := by
      ext i j
      by_cases hj : j = 0
      · simp only [hformula,hj,ite_true]
        exact congrArg (fun x : Natural => x i) hvw
      · simp only [hformula,hj,ite_false,mul_zero,Finset.sum_const_zero]
    have he := congrArg (fun X : Space => fun i => X i 0) (f.injective hfw)
    simpa using he
  let e : Factor := LinearEquiv.ofBijective b ⟨hbi,Finite.surjective_of_injective hbi⟩
  refine ⟨e,?_⟩
  ext X i j
  rw [column_apply,hformula]
  rfl

/-- A linear map implementing any automorphism on the right natural factor
has invertible tensor factors. -/
theorem tensor_factors_of_right_intertwining
    (f : Space ≃ₗ[ZMod 2] Space) (φ : Factor → Factor)
    (hf : ∀ g : Factor, ∀ X, f (baseAction (1,g) X) = baseAction (1,φ g) (f X)) :
    ∃ a b : Factor, f = baseAction (a,b) := by
  classical
  let block (i j : Fin 3) : Natural →ₗ[ZMod 2] Natural := {
    toFun v := f (Pi.single j v) i
    map_add' v w := by
      rw [Pi.single_add,map_add]
      rfl
    map_smul' a v := by
      rw [Pi.single_smul,map_smul]
      rfl }
  have hb (i j : Fin 3) (g : Factor) (v : Natural) :
      block i j (g v) = φ g (block i j v) := by
    have hs : baseAction (1,g) (Pi.single j v) = Pi.single j (g v) := by
      ext k l
      rw [row_apply]
      by_cases hk : k = j <;> simp [hk,Pi.single_eq_of_ne]
    change f (Pi.single j (g v)) i = _
    rw [←hs,hf,row_apply]
    rfl
  have hex : ∃ i : Fin 3, block i 0 ≠ 0 := by
    by_contra hn
    have hz : f (Pi.single 0 (fun _ => 1)) = 0 := by
      ext i j
      exact congrFun (LinearMap.congr_fun (not_not.mp (not_exists.mp hn i)) (fun _ => 1)) j
    have he := congrArg (fun X : Space => X 0 0) (f.injective (hz.trans f.map_zero.symm))
    simp at he
  obtain ⟨i,hi⟩ := hex
  have hbi := intertwiner_injective (block i 0) hi φ (hb i 0)
  let b : Factor := LinearEquiv.ofBijective (block i 0) ⟨hbi,Finite.surjective_of_injective hbi⟩
  have he (g : Factor) (v : Natural) : b (g v) = φ g (b v) := hb i 0 g v
  let k := f.trans (baseAction (1,b⁻¹))
  have hk (g : Factor) (X : Space) : k (baseAction (1,g) X) = baseAction (1,g) (k X) := by
    ext i j
    change baseAction (1,b⁻¹) (f (baseAction (1,g) X)) i j = _
    rw [hf,row_apply,row_apply,row_apply]
    change _ = g (baseAction (1,b⁻¹) (f X) i) j
    rw [row_apply]
    have hv : b.symm (φ g (f X i)) = g (b.symm (f X i)) := by
      apply b.injective
      rw [b.apply_symm_apply,he,b.apply_symm_apply]
    exact congrFun hv j
  obtain ⟨a,ha⟩ := row_centralizer k hk
  refine ⟨a,b,?_⟩
  ext X i j
  have hh := congrArg (fun u : Space ≃ₗ[ZMod 2] Space => baseAction (1,b) (u X)) ha
  change baseAction (1,b) (baseAction (1,b⁻¹) (f X)) = _ at hh
  have hl : baseAction (1,b) (baseAction (1,b⁻¹) (f X)) = f X := by
    change (baseAction (1,b) * baseAction (1,b⁻¹)) (f X) = _
    rw [←map_mul]
    simp only [Prod.mk_mul_mk,one_mul,mul_inv_cancel]
    change baseAction 1 (f X) = _
    rw [map_one]
    rfl
  rw [hl] at hh
  have hr : baseAction (1,b) * baseAction (a,1) = baseAction (a,b) := by
    rw [←map_mul]
    simp
  change f X i j = baseAction (a,b) X i j
  exact congrArg (fun Y : Space => Y i j) (hh.trans (congrArg (fun u : Space ≃ₗ[ZMod 2] Space => u X) hr))

private def factorMatrixEquiv : Matrix.PSL3Two.SL ≃* Factor :=
  Matrix.PSL3Two.equivGL.trans ((Matrix.GeneralLinearGroup.toLin (n := Fin 3) (R := ZMod 2)).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Natural))

private instance : IsSimpleGroup Factor := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  let : IsSimpleGroup Matrix.PSL3Two.SL := Matrix.PSL3Two.equiv.isSimpleGroup
  exact factorMatrixEquiv.symm.isSimpleGroup

private theorem factor_normal_quotient (N : Subgroup Factor) [N.Normal] (hN : N ≠ ⊥) :
    IsPGroup 2 (Factor ⧸ N) := by
  have hn : N = ⊤ := (Subgroup.Normal.eq_bot_or_eq_top (H := N) inferInstance).resolve_left hN
  subst N
  let : Subsingleton (Factor ⧸ (⊤ : Subgroup Factor)) := QuotientGroup.subsingleton_quotient_top
  exact IsPGroup.of_subsingleton _ _

private theorem factor_twoCore : pCore 2 Factor = ⊥ := by
  rcases Subgroup.Normal.eq_bot_or_eq_top (H := pCore 2 Factor) inferInstance with h | h
  · exact h
  · have hc : Nat.card (pCore 2 Factor) = 168 := by
      rw [h,card_top,←Nat.card_congr factorMatrixEquiv.toEquiv,Matrix.PSL3Two.card_SL]
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := Factor)).exists_card_eq
    have ht : 3 ∣ 2 ^ n := hn ▸ hc ▸ (by decide : 3 ∣ 168)
    exact ((by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow ht)).elim

private theorem factor_center : center Factor = ⊥ := by
  apply bot_unique
  intro x hx
  have hh := ((Subgroup.centerCongr factorMatrixEquiv).symm ⟨x,hx⟩).property
  have he : factorMatrixEquiv.symm x = 1 := Matrix.PSL3Two.center_eq_bot.le hh
  exact factorMatrixEquiv.symm.injective (he.trans factorMatrixEquiv.symm.map_one.symm)

/-- The two natural tensor factors act faithfully, with no scalar kernel over F₂. -/
theorem baseAction_injective : Function.Injective baseAction := by
  intro a b hab
  have he : baseEmbedding a = baseEmbedding b := Subtype.ext hab
  have hw := wreathHom_injective ((wreathHom_base a).trans (he.trans (wreathHom_base b).symm))
  apply Prod.ext
  · simpa [wreathBase] using congrArg (fun w : Wreath => w.left 1) hw
  · simpa [wreathBase] using congrArg (fun w : Wreath => w.left BinaryPermutation.FiveTensorSquare.swapIndex) hw

private theorem flip_conjugates (g : Factor × Factor) :
    flip * baseAction g * flip⁻¹ = baseAction (g.2,g.1) := by
  ext X i j
  change flip (baseAction g (flip X)) i j = baseAction (g.2,g.1) X i j
  rw [flip_baseAction]
  rfl

private theorem flip_mem_normalizer :
    flip ∈ normalizer (baseAction.range : Set (Space ≃ₗ[ZMod 2] Space)) := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro y
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨(g.2,g.1),(flip_conjugates g).symm⟩
  · rintro ⟨g,hg⟩
    refine ⟨(g.2,g.1),?_⟩
    rw [←flip_conjugates g,hg]
    have hf : flip * flip = 1 := by ext X i j; rfl
    have hfi : flip⁻¹ = flip := inv_eq_of_mul_eq_one_left hf
    rw [hfi]
    calc
      flip * (flip * y * flip) * flip = (flip * flip) * y * (flip * flip) := by group
      _ = y := by rw [hf,one_mul,mul_one]

/-- An arbitrary linear normalizer of the base tensor action is already a
base actor or a factor interchange followed by a base actor. -/
theorem normalizer_baseAction_alternatives (f : Space ≃ₗ[ZMod 2] Space)
    (hf : f ∈ normalizer (baseAction.range : Set (Space ≃ₗ[ZMod 2] Space))) :
    (∃ a b : Factor, f = baseAction (a,b)) ∨
      (∃ a b : Factor, f = baseAction (a,b) * flip) := by
  let e := MonoidHom.ofInjective baseAction_injective
  let φ := e.trans ((baseAction.range.normalizerMonoidHom ⟨f,hf⟩).trans e.symm)
  have hconj (g : Factor × Factor) : baseAction (φ g) = f * baseAction g * f⁻¹ := by
    change baseAction (e.symm _) = _
    rw [MonoidHom.apply_ofInjective_symm]
    rfl
  have hact (g : Factor × Factor) (X : Space) :
      f (baseAction g X) = baseAction (φ g) (f X) := by
    rw [hconj]
    change _ = f (baseAction g (f.symm (f X)))
    rw [f.symm_apply_apply]
  rcases automorphism_product_coordinates factor_normal_quotient factor_normal_quotient
    factor_twoCore factor_center φ with ⟨_,hb⟩ | ⟨_,hb⟩
  · left
    apply tensor_factors_of_right_intertwining f (fun g => (φ (1,g)).2)
    intro g X
    have hh : φ (1,g) = (1,(φ (1,g)).2) := Prod.ext (hb g) rfl
    rw [hact,hh]
  · right
    let k := f.trans flip
    have hk (g : Factor) (X : Space) :
        k (baseAction (1,g) X) = baseAction (1,(φ (1,g)).1) (k X) := by
      change flip (f (baseAction (1,g) X)) = _
      have hh : φ (1,g) = ((φ (1,g)).1,1) := Prod.ext rfl (hb g)
      rw [hact,hh,flip_baseAction]
      rfl
    obtain ⟨a,b,hab⟩ := tensor_factors_of_right_intertwining k (fun g => (φ (1,g)).1) hk
    refine ⟨b,a,?_⟩
    apply LinearEquiv.ext
    intro X
    have hh := congrArg (fun u : Space ≃ₗ[ZMod 2] Space => flip (u X)) hab
    change f X = flip (baseAction (a,b) X) at hh
    rw [hh,flip_baseAction]
    rfl

/-- The full binary linear normalizer of GL₃(2) × GL₃(2) is exactly its
concrete tensor wreath group. No outer-action marking is assumed. -/
theorem normalizer_baseAction_range :
    normalizer (baseAction.range : Set (Space ≃ₗ[ZMod 2] Space)) = tensorGroup := by
  apply le_antisymm
  · intro f hf
    rcases normalizer_baseAction_alternatives f hf with ⟨a,b,rfl⟩ | ⟨a,b,rfl⟩
    · exact (baseEmbedding (a,b)).property
    · exact tensorGroup.mul_mem (baseEmbedding (a,b)).property swap.property
  · rw [tensorGroup,Subgroup.closure_le]
    rintro x (⟨g,rfl⟩ | hx)
    · exact baseAction.range.le_normalizer ⟨g,rfl⟩
    · exact hx ▸ flip_mem_normalizer

/-- A linear overgroup containing the tensor base and one actor outside it
is the whole wreath group as soon as it normalizes the base. -/
theorem eq_tensorGroup_of_base_and_outside
    (A : Subgroup (Space ≃ₗ[ZMod 2] Space))
    (hbase : baseAction.range ≤ A)
    (hnorm : A ≤ normalizer (baseAction.range : Set (Space ≃ₗ[ZMod 2] Space)))
    (hout : ∃ f ∈ A, f ∉ baseAction.range) : A = tensorGroup := by
  apply le_antisymm (hnorm.trans_eq normalizer_baseAction_range)
  obtain ⟨f,hf,hout⟩ := hout
  rcases normalizer_baseAction_alternatives f (hnorm hf) with ⟨a,b,rfl⟩ | ⟨a,b,rfl⟩
  · exact (hout ⟨(a,b),rfl⟩).elim
  · have hflip : flip ∈ A := by
      have hh := A.mul_mem (A.inv_mem (hbase ⟨(a,b),rfl⟩)) hf
      simpa only [inv_mul_cancel_left] using hh
    rw [tensorGroup,Subgroup.closure_le]
    rintro x (hx | hx)
    · exact hbase hx
    · exact hx ▸ hflip

end BinaryTensorThree
