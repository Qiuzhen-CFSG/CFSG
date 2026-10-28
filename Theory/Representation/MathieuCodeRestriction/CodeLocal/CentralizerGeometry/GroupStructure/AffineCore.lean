module

public import Theory.Representation.MathieuCodeRestriction.CodeLocal.CentralizerGeometry.GroupStructure.AffineModel
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoBlocks
public import Theory.LinearAlgebra.BinaryFivePointStabilizer.KernelCard

/-!
# The order-sixteen affine subgroup and the translation-centralizer two-core

The pair-preserving affine maps are exactly those whose value at zero lies
in the marked line and whose linear part lies in its parabolic radical.
Thus their underlying set is the product of that line and the linear radical.
The existing displacement equivalence identifies the latter with maps from
the three-dimensional quotient to the one-dimensional line, giving order
`2 * 8 = 16`.

The linear-part map takes the translation centralizer onto the line parabolic
and has a two-group kernel. Its preimage of the parabolic two-core is therefore
the intrinsic affine two-core. The same preimage is the literal product of all
translations with the pair-preserving subgroup, by the affine decomposition.

Source: Aschbacher (1994), 39.1, as applied in Aschbacher--Smith H.16.2(6),
printed pp.402--403. The native application is in `AffineCore.Native` so that
this model calculation remains independent of `GroupStructure`.
-/

@[expose] public section

open scoped Pointwise
namespace MathieuCode.OctadAffine
open BinaryLinear

private abbrev markedLine (v : Space) := Submodule.span (ZMod 2) {v}

private theorem mem_markedLine (v x : Space) : x ∈ markedLine v ↔ x = 0 ∨ x = v := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    have hc : c = 0 ∨ c = 1 := by exact (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c
    rcases hc with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ _⟩
    · exact ⟨1, one_smul _ _⟩

private theorem affine_apply (f : AffineGroup) (x : Space) :
    f x = f.linear x + f 0 := by
  simpa using f.map_vadd (0 : Space) x

private theorem centralizer_iff (v : Space) (f : AffineGroup) :
    f ∈ Subgroup.centralizer ({translation v} : Set AffineGroup) ↔ f.linear v = v := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h0 := congrArg (fun g : AffineGroup => g 0) h
    change f (v + 0) = v + f 0 at h0
    rw [add_zero, affine_apply] at h0
    exact add_right_cancel h0
  · intro h
    apply AffineEquiv.ext
    intro x
    change f (v + x) = v + f x
    simpa only [vadd_eq_add, h] using f.map_vadd x v

private theorem parabolic_iff (v : Space) (g : GL Space) :
    g ∈ parabolic (markedLine v) ↔ g v = v := by
  constructor
  · intro hg
    rcases (mem_markedLine v (g v)).mp ((hg v).mpr (Submodule.mem_span_singleton_self v)) with hz | hv
    · have hv := g.map_eq_zero_iff.mp hz
      simp [hv]
    · exact hv
  · intro hg x
    change g x ∈ markedLine v ↔ x ∈ markedLine v
    have he : g x = v ↔ x = v := by
      calc
        g x = v ↔ g x = g v := by rw [hg]
        _ ↔ x = v := g.injective.eq_iff
    simp only [mem_markedLine, g.map_eq_zero_iff, he]

private def linearProjection (v : Space) :
    Subgroup.centralizer ({translation v} : Set AffineGroup) →* parabolic (markedLine v) where
  toFun f := ⟨f.val.linear, (parabolic_iff v _).mpr ((centralizer_iff v _).mp f.property)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem linearProjection_surjective (v : Space) : Function.Surjective (linearProjection v) := by
  intro g
  exact ⟨⟨g.val.toAffineEquiv, (centralizer_iff v _).mpr ((parabolic_iff v _).mp g.property)⟩, rfl⟩

private theorem linearProjection_kernel_two (v : Space) : IsPGroup 2 (linearProjection v).ker := by
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro f
  refine ⟨1, ?_⟩
  have hl : f.val.val.linear = 1 := congrArg Subtype.val f.property
  apply Subtype.ext
  apply Subtype.ext
  apply AffineEquiv.ext
  intro x
  change f.val.val (f.val.val x) = x
  rw [affine_apply, affine_apply, hl]
  change x + f.val.val 0 + f.val.val 0 = x
  have hz : f.val.val 0 + f.val.val 0 = 0 := by ext i; exact CharTwo.add_self_eq_zero _
  rw [add_assoc, hz, add_zero]

private theorem fiber_iff (v : Space) (f : AffineGroup) :
    f ∈ fiberKernel v ↔ f 0 ∈ markedLine v ∧ f.linear ∈ radical (markedLine v) := by
  constructor
  · intro hf
    have h0 : f 0 ∈ markedLine v := (mem_markedLine v _).mpr (by simpa using hf 0)
    refine ⟨h0, ?_, ?_⟩
    · intro w hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [map_smul, (centralizer_iff v f).mp (fiberKernel_le_centralizer v hf)]
    · intro x
      have hx : f x - x ∈ markedLine v := by
        rcases hf x with hx | hx
        · rw [hx, sub_self]; exact (markedLine v).zero_mem
        · rw [hx, add_sub_cancel_right]; exact Submodule.mem_span_singleton_self v
      have hh := (markedLine v).sub_mem hx h0
      rw [affine_apply f x] at hh
      convert hh using 1; abel
  · rintro ⟨h0, hf⟩ x
    have hx := (markedLine v).add_mem (hf.2 x) h0
    have he : f x - x = (f.linear x - x) + f 0 := by rw [affine_apply]; abel
    rw [← he, mem_markedLine] at hx
    rcases hx with hx | hx
    · exact Or.inl (sub_eq_zero.mp hx)
    · exact Or.inr (sub_eq_iff_eq_add.mp hx)

private theorem product_iff (v : Space) (f : AffineGroup) :
    f ∈ (translations : Set AffineGroup) * (fiberKernel v : Set AffineGroup) ↔
      f.linear ∈ radical (markedLine v) := by
  constructor
  · rintro ⟨t, ⟨a, rfl⟩, g, hg, rfl⟩
    exact ((fiber_iff v g).mp hg).2
  · intro hf
    refine ⟨translation (f 0), ⟨Multiplicative.ofAdd (f 0), rfl⟩,
      f.linear.toAffineEquiv, ?_, ?_⟩
    · apply (fiber_iff v _).mpr
      exact ⟨by
        change f.linear 0 ∈ markedLine v
        rw [map_zero]
        exact (markedLine v).zero_mem, hf⟩
    · apply AffineEquiv.ext
      intro x
      change f 0 + f.linear x = f x
      exact (add_comm _ _).trans (affine_apply f x).symm

/-- The literal product is the intrinsic two-core of the translation centralizer. -/
theorem translations_mul_fiberKernel_eq_core (v : Space) (_hv : v ≠ 0) :
    (translations : Set AffineGroup) * (fiberKernel v : Set AffineGroup) =
      ((pCore 2 (Subgroup.centralizer ({translation v} : Set AffineGroup))).map
        (Subgroup.centralizer ({translation v} : Set AffineGroup)).subtype : Set AffineGroup) := by
  let : Finite (GL Space) := Finite.of_injective
    (fun g : GL Space => (g : Space → Space)) DFunLike.coe_injective
  have hcore := (linearProjection v).comap_pCore_of_ker_isPGroup
    (linearProjection_surjective v) (linearProjection_kernel_two v)
  rw [SmallParabolicLevi.twoCore_eq_radical] at hcore
  ext f
  rw [product_iff]
  constructor
  · intro hf
    have hc : f ∈ Subgroup.centralizer ({translation v} : Set AffineGroup) :=
      (centralizer_iff v f).mpr (hf.1 v (Submodule.mem_span_singleton_self v))
    refine ⟨⟨f, hc⟩, ?_, rfl⟩
    rw [← hcore]
    exact hf
  · rintro ⟨g, hg, rfl⟩
    rw [← hcore] at hg
    exact hg

private def fiberCoordinates (v : Space) :
    fiberKernel v ≃ (markedLine v × radical (markedLine v)) where
  toFun f :=
    (⟨f.val 0, ((fiber_iff v f.val).mp f.property).1⟩,
      ⟨f.val.linear, ((fiber_iff v f.val).mp f.property).2⟩)
  invFun a := ⟨translation a.1.val * a.2.val.toAffineEquiv, (fiber_iff v _).mpr ⟨by
    change a.1.val + a.2.val 0 ∈ markedLine v
    rw [map_zero, add_zero]
    exact a.1.property, a.2.property⟩⟩
  left_inv f := by
    apply Subtype.ext
    apply AffineEquiv.ext
    intro x
    change f.val 0 + f.val.linear x = f.val x
    exact (add_comm _ _).trans (affine_apply f.val x).symm
  right_inv a := by
    apply Prod.ext
    · apply Subtype.ext
      change a.1.val + a.2.val 0 = a.1.val
      rw [map_zero, add_zero]
    · rfl

private def radicalKernelEquiv (v : Space) : radical (markedLine v) ≃
    Theory.LinearAlgebra.BinaryFivePointStabilizer.kernel v where
  toFun g := ⟨⟨g.val, g.property.1 v (Submodule.mem_span_singleton_self v)⟩,
    (Theory.LinearAlgebra.BinaryFivePointStabilizer.mem_kernel_iff v _).mpr g.property.2⟩
  invFun g := ⟨g.val.val,
    Theory.LinearAlgebra.BinaryFivePointStabilizer.fixes_line v g.val,
    (Theory.LinearAlgebra.BinaryFivePointStabilizer.mem_kernel_iff v g.val).mp g.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The pair-preserving affine subgroup for a nonzero direction has order sixteen. -/
theorem fiberKernel_card (v : Space) (hv : v ≠ 0) : Nat.card (fiberKernel v) = 16 := by
  have hline : Module.finrank (ZMod 2) (markedLine v) = 1 := finrank_span_singleton hv
  have hquot : Module.finrank (ZMod 2) (Space ⧸ markedLine v) = 3 := by
    have h := (markedLine v).finrank_quotient_add_finrank
    rw [hline] at h
    have hspace : Module.finrank (ZMod 2) Space = 4 := by simp
    rw [hspace] at h
    omega
  have hrad : Nat.card (radical (markedLine v)) = 8 := by
    rw [Nat.card_congr (radicalKernelEquiv v),
      Nat.card_congr (Theory.LinearAlgebra.BinaryFivePointStabilizer.kernelDisplacementEquiv v).toEquiv]
    change Nat.card ((Space ⧸ markedLine v) →ₗ[ZMod 2] markedLine v) = 8
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Module.finrank_linearMap, hquot, hline]
    norm_num
  rw [Nat.card_congr (fiberCoordinates v), Nat.card_prod, hrad,
    Module.natCard_eq_pow_finrank (K := ZMod 2), hline]
  norm_num

end MathieuCode.OctadAffine
