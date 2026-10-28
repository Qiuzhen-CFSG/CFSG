module

public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.BinaryKernel.Rigidity
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.BinaryKernel.Translations
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Algebra.CharP.Two

/-!
# The binary translation kernel of the M23 heptad stabilizer

The explicitly certified translations give a homomorphism from the additive
four-dimensional binary space into the actual pointwise heptad kernel.
Evaluation at a complementary point is injective by Witt-design rigidity and
surjective by the coordinate construction, so these translations exhaust the
kernel. This yields a multiplicative equivalence, a compatible coordinate
system, sharp transitivity, order sixteen, commutativity, and exponent two.
The construction is independent of the alternating complement.

Source: Aschbacher, *Sporadic Groups*, Chapter 6, Lemma 19.1 and its M23
specialization; Aschbacher--Smith, §5.2, printed p.655 (PDF p.672).
-/

public section
namespace Sporadic.Mathieu.M23Geometry
open scoped Pointwise

/-- Binary affine coordinates on the actual sixteen-point complement. -/
noncomputable def heptadBinaryPointEquiv : (Fin 4 → ZMod 2) ≃ pairComplement omega :=
  Equiv.ofBijective (fun v => ⟨heptadBinaryPoint v, by
    simp only [pairComplement, Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact heptadBinaryPoint_not_mem v⟩) (by
      constructor
      · intro v w h
        exact heptadBinaryPoint_injective (congrArg Subtype.val h)
      · intro a
        obtain ⟨v, hv⟩ := heptadBinaryPoint_surjective a.val (Finset.mem_sdiff.mp a.property).2
        exact ⟨v, Subtype.ext hv⟩)

@[simp] theorem heptadBinaryPointEquiv_apply (v : Fin 4 → ZMod 2) :
    (heptadBinaryPointEquiv v).val = heptadBinaryPoint v := by rfl

/-- Read the four binary coordinates of a complementary point. -/
noncomputable def heptadBinaryCoordinates : pairComplement omega ≃ (Fin 4 → ZMod 2) :=
  heptadBinaryPointEquiv.symm

private noncomputable def binaryElement (v : Fin 4 → ZMod 2) : heptadKernel := by
  let g : M23 := ⟨heptadBinaryPermutation v, heptadBinaryPermutation_mem v⟩
  have hg : ∀ a ∈ omega, g • a = a := heptadBinaryPermutation_fix v
  have hs : g ∈ heptadStabilizer := by
    apply MulAction.mem_stabilizer_finset'.mpr
    intro a ha
    rwa [hg a ha]
  exact ⟨⟨g, hs⟩, (mem_heptadKernel _).mpr hg⟩

/-- Explicit binary translations as elements of the pointwise heptad kernel. -/
noncomputable def heptadBinaryHom : Multiplicative (Fin 4 → ZMod 2) →* heptadKernel where
  toFun v := binaryElement v.toAdd
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact heptadBinaryPermutation_zero
  map_mul' v w := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact heptadBinaryPermutation_add v.toAdd w.toAdd

@[simp] theorem heptadBinaryHom_coe (v : Multiplicative (Fin 4 → ZMod 2)) :
    (((heptadBinaryHom v : heptadStabilizer) : M23) : Equiv.Perm (Fin 23)) =
      heptadBinaryPermutation v.toAdd := by rfl

private theorem binaryHom_at_origin (v : Multiplicative (Fin 4 → ZMod 2)) :
    ((heptadBinaryHom v : heptadStabilizer) : M23) • heptadBinaryPoint 0 =
      heptadBinaryPoint v.toAdd := by
  change heptadBinaryPermutation v.toAdd (heptadBinaryPoint 0) = _
  rw [heptadBinaryPermutation_translate, add_zero]

theorem heptadBinaryHom_injective : Function.Injective heptadBinaryHom := by
  intro v w h
  have hh := congrArg
    (fun g : heptadKernel => ((g : heptadStabilizer) : M23) • heptadBinaryPoint 0) h
  rw [binaryHom_at_origin, binaryHom_at_origin] at hh
  exact Multiplicative.toAdd.injective (heptadBinaryPoint_injective hh)

/-- The explicit translations exhaust the kernel by evaluation injectivity. -/
theorem heptadBinaryHom_surjective : Function.Surjective heptadBinaryHom := by
  intro g
  let a := heptadKernelEvaluation (heptadBinaryPointEquiv 0) g
  obtain ⟨v, hv⟩ := heptadBinaryPoint_surjective a.val (Finset.mem_sdiff.mp a.property).2
  refine ⟨Multiplicative.ofAdd v, heptadKernel_eval_injective
    (heptadBinaryPoint 0) (heptadBinaryPoint_not_mem 0) ?_⟩
  dsimp only
  rw [binaryHom_at_origin]
  exact hv

/-- The genuine binary translation group of the actual heptad stabilizer. -/
noncomputable def heptadBinaryEquiv : Multiplicative (Fin 4 → ZMod 2) ≃* heptadKernel :=
  MulEquiv.ofBijective heptadBinaryHom ⟨heptadBinaryHom_injective, heptadBinaryHom_surjective⟩

@[simp] theorem heptadBinaryEquiv_coe (v : Multiplicative (Fin 4 → ZMod 2)) :
    (((heptadBinaryEquiv v : heptadStabilizer) : M23) : Equiv.Perm (Fin 23)) =
      heptadBinaryPermutation v.toAdd := by rfl

/-- Restriction of the actual kernel permutations to the sixteen-point complement. -/
noncomputable def heptadKernelComplementAction :
    heptadKernel →* Equiv.Perm (pairComplement omega) where
  toFun g :=
    { toFun := fun a => heptadKernelEvaluation a g
      invFun := fun a => heptadKernelEvaluation a g⁻¹
      left_inv := by
        intro a
        apply Subtype.ext
        exact inv_smul_smul ((g : heptadStabilizer) : M23) a.val
      right_inv := by
        intro a
        apply Subtype.ext
        exact smul_inv_smul ((g : heptadStabilizer) : M23) a.val }
  map_one' := by ext a; rfl
  map_mul' g h := by ext a; rfl

@[simp] theorem heptadKernelComplementAction_apply (g : heptadKernel)
    (a : pairComplement omega) :
    (heptadKernelComplementAction g a).val = ((g : heptadStabilizer) : M23) • a.val := by rfl

/-- The coordinate equivalence intertwines the concrete action with translations. -/
theorem heptadBinaryEquiv_action (v : Fin 4 → ZMod 2) (w : Fin 4 → ZMod 2) :
    heptadKernelComplementAction (heptadBinaryEquiv (Multiplicative.ofAdd v))
      (heptadBinaryPointEquiv w) = heptadBinaryPointEquiv (v + w) := by
  apply Subtype.ext
  exact heptadBinaryPermutation_translate v w

theorem heptadBinaryCoordinates_action (v : Fin 4 → ZMod 2)
    (a : pairComplement omega) :
    heptadBinaryCoordinates
      (heptadKernelComplementAction (heptadBinaryEquiv (Multiplicative.ofAdd v)) a) =
      v + heptadBinaryCoordinates a := by
  obtain ⟨w, rfl⟩ := heptadBinaryPointEquiv.surjective a
  rw [heptadBinaryEquiv_action]
  change heptadBinaryPointEquiv.symm (heptadBinaryPointEquiv (v + w)) =
    v + heptadBinaryPointEquiv.symm (heptadBinaryPointEquiv w)
  simp only [Equiv.symm_apply_apply]

/-- Sharp transitivity of the actual kernel on the complementary points. -/
theorem heptadKernelComplementAction_regular (a b : pairComplement omega) :
    ∃! g : heptadKernel, heptadKernelComplementAction g a = b := by
  let v := heptadBinaryCoordinates b - heptadBinaryCoordinates a
  refine ⟨heptadBinaryEquiv (Multiplicative.ofAdd v), ?_, ?_⟩
  · apply heptadBinaryCoordinates.injective
    rw [heptadBinaryCoordinates_action]
    exact sub_add_cancel _ _
  · intro g hg
    apply heptadKernelEvaluation_injective a
    change heptadKernelComplementAction g a =
      heptadKernelComplementAction (heptadBinaryEquiv (Multiplicative.ofAdd v)) a
    apply heptadBinaryCoordinates.injective
    rw [hg, heptadBinaryCoordinates_action]
    exact (sub_add_cancel _ _).symm

/-- Evaluation identifies the kernel with the complement, for every base point. -/
theorem heptadKernelEvaluation_bijective (a : pairComplement omega) :
    Function.Bijective (heptadKernelEvaluation a) := by
  refine ⟨heptadKernelEvaluation_injective a, ?_⟩
  intro b
  obtain ⟨g, hg, _⟩ := heptadKernelComplementAction_regular a b
  exact ⟨g, hg⟩

/-- Fixing any one complementary point forces a kernel element to be identity. -/
theorem heptadKernel_eq_one_of_fix (g : heptadKernel) {a : Fin 23}
    (ha : a ∉ omega) (hga : ((g : heptadStabilizer) : M23) • a = a) : g = 1 := by
  apply heptadKernel_eval_injective a ha
  simpa only [Subgroup.coe_one, one_smul] using hga

/-- Freeness of the restricted permutation action. -/
theorem heptadKernelComplementAction_fix_iff (g : heptadKernel)
    (a : pairComplement omega) : heptadKernelComplementAction g a = a ↔ g = 1 := by
  constructor
  · intro h
    exact heptadKernel_eq_one_of_fix g (Finset.mem_sdiff.mp a.property).2
      (congrArg Subtype.val h)
  · rintro rfl
    exact congrArg (fun e : Equiv.Perm (pairComplement omega) => e a)
      heptadKernelComplementAction.map_one

/-- The kernel has sixteen elements. -/
theorem heptadKernel_card : Nat.card heptadKernel = 16 := by
  rw [← Nat.card_congr heptadBinaryEquiv.toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_multiplicative, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  decide

theorem heptadKernel_mul_comm (g h : heptadKernel) : g * h = h * g := by
  obtain ⟨v, rfl⟩ := heptadBinaryEquiv.surjective g
  obtain ⟨w, rfl⟩ := heptadBinaryEquiv.surjective h
  rw [← map_mul, ← map_mul, mul_comm v w]

theorem heptadKernel_sq (g : heptadKernel) : g ^ 2 = 1 := by
  obtain ⟨v, rfl⟩ := heptadBinaryEquiv.surjective g
  have hv : v * v = 1 := by
    apply Multiplicative.toAdd.injective
    change v.toAdd + v.toAdd = 0
    ext i
    exact CharTwo.add_self_eq_zero (v.toAdd i)
  rw [pow_two, ← map_mul, hv, map_one]

end Sporadic.Mathieu.M23Geometry
