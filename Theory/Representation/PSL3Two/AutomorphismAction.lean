module
public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual
public import Mathlib.GroupTheory.SemidirectProduct
/-!
# Extending the concrete Steinberg representation to all automorphisms

Transpose preserves trace-zero endomorphisms and intertwines the adjoint
representation with its inverse-transpose twist. This gives a representation
of the semidirect product of SL₃(2) with its graph involution. Centerlessness
and the natural–dual calculation identify this semidirect product with the
full automorphism group. The resulting representation restricts along the
actual inner-automorphism map to the representation `BinaryLinearThree.S`.

Together with the re-exported natural–dual action, these are the model facts
used in Aschbacher–Smith 13.8.21(1), printed p.956 (1 March 2004 manuscript).
No irreducible-module catalogue or ambient pairing assertion is assumed here.
-/

public section
open Matrix Representation
namespace BinaryLinearThree.AutomorphismAction
private def endTranspose : Module.End (ZMod 2) Vector ≃ₗ[ZMod 2]
    Module.End (ZMod 2) Vector :=
  LinearMap.toMatrix'.trans ((Matrix.transposeLinearEquiv _ _ _ _).trans Matrix.toLin')
private lemma endTranspose_apply (f : Module.End (ZMod 2) Vector) :
    endTranspose f = (LinearMap.toMatrix' f).transpose.toLin' := rfl
private lemma endTranspose_involutive : Function.Involutive endTranspose := by
  intro f
  simp [endTranspose_apply]
private lemma endTranspose_trace (f : Module.End (ZMod 2) Vector) :
    LinearMap.trace (ZMod 2) Vector (endTranspose f) =
      LinearMap.trace (ZMod 2) Vector f := by
  rw [endTranspose_apply, Matrix.trace_toLin'_eq, Matrix.trace_transpose]
  rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_toMatrix']
/-- Transpose on the concrete trace-zero endomorphism space. -/
noncomputable def steinbergTranspose : Steinberg ≃ₗ[ZMod 2] Steinberg where
  toFun f := ⟨endTranspose f.val, by
    change LinearMap.trace (ZMod 2) Vector (endTranspose f.val) = 0
    rw [endTranspose_trace]; exact f.property⟩
  invFun f := ⟨endTranspose f.val, by
    change LinearMap.trace (ZMod 2) Vector (endTranspose f.val) = 0
    rw [endTranspose_trace]; exact f.property⟩
  left_inv f := Subtype.ext (endTranspose_involutive _)
  right_inv f := Subtype.ext (endTranspose_involutive _)
  map_add' f h := Subtype.ext (map_add endTranspose _ _)
  map_smul' c f := Subtype.ext (map_smul endTranspose _ _)
/-- Transpose has square one on the Steinberg module. -/
lemma steinbergTranspose_sq : steinbergTranspose * steinbergTranspose = 1 := by
  ext f : 1
  exact Subtype.ext (endTranspose_involutive _)
/-- Transpose implements the graph automorphism on the adjoint representation. -/
lemma steinbergTranspose_covariance (g : Group) (f : Steinberg) :
    steinbergTranspose (S g f) = S (graph g) (steinbergTranspose f) := by
  apply Subtype.ext
  apply LinearMap.toMatrix'.injective
  change LinearMap.toMatrix' (endTranspose (W g ∘ₗ f.val ∘ₗ W g⁻¹)) =
    LinearMap.toMatrix' (W (graph g) ∘ₗ endTranspose f.val ∘ₗ W (graph g)⁻¹)
  rw [← map_inv graph]
  simp only [endTranspose_apply, LinearMap.toMatrix'_toLin',
    LinearMap.toMatrix'_comp, Matrix.transpose_mul]
  have natMatrix (h : Group) : LinearMap.toMatrix' (W h) = h.val :=
    LinearMap.toMatrix'_toLin' h.val
  simp only [natMatrix, graph_apply,
    inv_inv, SpecialLinearGroup.coe_transpose]
  rw [Matrix.mul_assoc]

private def involutionHom {H : Type*} [_root_.Group H] (t : H) (ht : t * t = 1) :
    Multiplicative (ZMod 2) →* H where
  toFun b := if b.toAdd = 0 then 1 else t
  map_one' := by simp
  map_mul' a b := by
    change (if a.toAdd + b.toAdd = 0 then 1 else t) =
      (if a.toAdd = 0 then 1 else t) * (if b.toAdd = 0 then 1 else t)
    generalize a.toAdd = x
    generalize b.toAdd = y
    fin_cases x <;> fin_cases y
    · exact (one_mul (1 : H)).symm
    · exact (one_mul t).symm
    · exact (mul_one t).symm
    · exact ht.symm
private def graphHom : Multiplicative (ZMod 2) →* MulAut Group :=
  involutionHom graph graph_sq
private abbrev SplitAut := Group ⋊[graphHom] Multiplicative (ZMod 2)
private def splitToAut : SplitAut →* MulAut Group :=
  SemidirectProduct.lift MulAut.conj graphHom (by
    intro b
    ext g h
    simp [MulAut.conj_apply])
private lemma splitToAut_bijective : Function.Bijective splitToAut := by
  constructor
  · apply (splitToAut.ker_eq_bot_iff).mp
    apply le_bot_iff.mp
    intro x hx
    change splitToAut x = 1 at hx
    change MulAut.conj x.left * graphHom x.right = 1 at hx
    by_cases hb : x.right.toAdd = 0
    · have he : graphHom x.right = 1 := by exact if_pos hb
      rw [he, mul_one] at hx
      have hi := MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot
      have hg : x.left = 1 := hi (by simpa using hx)
      apply Subgroup.mem_bot.mpr
      apply SemidirectProduct.ext hg
      exact hb
    · have he : graphHom x.right = graph := by exact if_neg hb
      rw [he] at hx
      have hg : graph = MulAut.conj x.left⁻¹ := by
        calc
          graph = (MulAut.conj x.left)⁻¹ := eq_inv_of_mul_eq_one_right hx
          _ = _ := (map_inv MulAut.conj _).symm
      exact False.elim (graph_not_inner ⟨x.left⁻¹, hg.symm⟩)
  · intro a
    by_cases ha : a ∈ MulAut.innerSubgroup Group
    · obtain ⟨g, rfl⟩ := ha
      exact ⟨SemidirectProduct.inl g, SemidirectProduct.lift_inl _ _ _ _⟩
    · obtain ⟨g, hg⟩ := outer_eq_inner_graph a ha
      refine ⟨⟨g, Multiplicative.ofAdd 1⟩, ?_⟩
      change MulAut.conj g * graph = a
      exact hg.symm
private noncomputable def splitAutEquiv : SplitAut ≃* MulAut Group :=
  MulEquiv.ofBijective splitToAut splitToAut_bijective
private noncomputable def transposeUnit : (Module.End (ZMod 2) Steinberg)ˣ :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv steinbergTranspose
private lemma transposeUnit_sq : transposeUnit * transposeUnit = 1 := by
  apply Units.ext
  apply LinearMap.ext
  intro f
  exact Subtype.ext (endTranspose_involutive _)
private noncomputable def splitSteinberg : SplitAut →* (Module.End (ZMod 2) Steinberg)ˣ :=
  SemidirectProduct.lift S.asGroupHom (involutionHom transposeUnit transposeUnit_sq) (by
    intro b
    have hb : b.toAdd = 0 ∨ b.toAdd = 1 := by
      have h : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      exact h _
    rcases hb with hb | hb
    · have he : b = 1 := hb
      subst b
      ext g : 1
      simp only [map_one, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.one_apply]
    · have he : b = Multiplicative.ofAdd 1 := hb
      subst b
      ext g : 1
      apply Units.ext
      apply LinearMap.ext
      intro f
      change S (graph g) f = steinbergTranspose (S _ (steinbergTranspose f))
      rw [steinbergTranspose_covariance]
      have he : steinbergTranspose (steinbergTranspose f) = f :=
        Subtype.ext (endTranspose_involutive _)
      rw [he])
/-- The full automorphism group acts on the concrete Steinberg space. -/
noncomputable def steinbergAut : Representation (ZMod 2) (MulAut Group) Steinberg :=
  (Units.coeHom _).comp (splitSteinberg.comp splitAutEquiv.symm.toMonoidHom)
/-- Restriction along inner automorphisms is exactly the original adjoint action. -/
lemma steinbergAut_comp_conj : steinbergAut.comp (MulAut.conj : Group →* MulAut Group) = S := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro f
  have he : splitAutEquiv.symm (MulAut.conj g) = SemidirectProduct.inl g := by
    apply splitAutEquiv.injective
    rw [splitAutEquiv.apply_symm_apply]
    change MulAut.conj g = splitToAut (SemidirectProduct.inl g)
    simp [splitToAut]
  change (splitSteinberg (splitAutEquiv.symm (MulAut.conj g))).val f = S g f
  rw [he]
  rfl

/-- Coordinate formula for transpose on trace-zero endomorphisms. -/
lemma steinbergTranspose_apply (f : Steinberg) :
    (steinbergTranspose f).val = (LinearMap.toMatrix' f.val).transpose.toLin' := by
  exact endTranspose_apply f.val

/-- The graph involution acts by transpose in the full extension. -/
lemma steinbergAut_graph : steinbergAut graph = steinbergTranspose.toLinearMap := by
  have he : splitAutEquiv.symm graph =
      SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2)) := by
    apply splitAutEquiv.injective
    rw [splitAutEquiv.apply_symm_apply]
    change graph = splitToAut (SemidirectProduct.inr (Multiplicative.ofAdd 1))
    simp only [splitToAut, SemidirectProduct.lift_inr]
    rfl
  apply LinearMap.ext
  intro f
  change (splitSteinberg (splitAutEquiv.symm graph)).val f = steinbergTranspose f
  rw [he]
  simp only [splitSteinberg, SemidirectProduct.lift_inr]
  rfl

end BinaryLinearThree.AutomorphismAction
