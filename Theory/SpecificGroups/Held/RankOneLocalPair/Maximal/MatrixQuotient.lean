module

public import Theory.SpecificGroups.Held.RankOneLocalPair.Maximal.MatrixQuotient.FiniteAction
public import Theory.SpecificGroups.Held.RankOneLocalPair.Maximal.MatrixQuotient.LinearImage
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoB
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.Ambient
public import Theory.GroupTheory.PCoreSurjective

/-!
# The actual matrix quotient of Held's max5

The vector labels on the degree-2058 Held permutation model intertwine its
literal max5 generators with two binary matrices. Surjectivity of the labels
makes the compatible matrix unique, hence defines a homomorphism on max5.
The images contain all elementary transvections, so its projective matrix
image is PSL₃(2). Kernel-image counting gives a kernel of order 128. The
trivial two-core of PSL₃(2) identifies this kernel with O₂(max5), and the first
isomorphism theorem gives the required multiplicative equivalence.

This calculation is unconditional; it does not assume simplicity of Held,
a shape for max5, or its maximality. It supplies the matrix-equivalence premise
in the independent maximal-local assembly for Aschbacher–Smith E.1.14(4),
refs/quasithin.pdf, printed p.214. Sources: ATLAS HeG1-max5W1 and the original
Held permutation data, with the inversion convention recorded in
Held/Model/Source/README.md. Discovery and reproduction are in
`MatrixQuotient/Source`.
-/

namespace Held.RankOneLocalPair.MatrixQuotient
open TwoLocalCandidates

private def compatible : Subgroup He where
  carrier := {g | ∃ M : SL, ∀ i, label (representation g i) = M.toLin' (label i)}
  one_mem' := ⟨1, by intro i; simp⟩
  mul_mem' := by
    rintro g h ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨A * B, ?_⟩
    intro i
    change label (representation (g * h) i) = _
    rw [map_mul]
    change label (representation g (representation h i)) = _
    rw [hA, hB, map_mul, LinearEquiv.mul_apply]
  inv_mem' := by
    rintro g ⟨A, hA⟩
    refine ⟨A⁻¹, ?_⟩
    intro i
    apply A.toLin'.injective
    have hi := hA ((representation g)⁻¹ i)
    simpa using hi.symm

private theorem exists_matrix (g : max5) :
    ∃ M : SL, ∀ i, label (representation g.val i) = M.toLin' (label i) := by
  have hm : max5 ≤ compatible := by
    apply (Subgroup.closure_le _).mpr
    rintro x (rfl | hx)
    · exact ⟨generator 0, label_generator 0⟩
    · have hx' : x = max5Second := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨generator 1, label_generator 1⟩
  exact hm g.property

private theorem matrix_unique {A B : SL}
    (h : ∀ i, A.toLin' (label i) = B.toLin' (label i)) : A = B := by
  apply Matrix.SpecialLinearGroup.toLin'_injective
  apply LinearEquiv.ext
  intro v
  obtain ⟨i, rfl⟩ := label_surjective v
  exact h i

private noncomputable def matrixOf (g : max5) : SL := Classical.choose (exists_matrix g)

private theorem matrixOf_spec (g : max5) (i : Fin 2058) :
    label (representation g.val i) = (matrixOf g).toLin' (label i) :=
  Classical.choose_spec (exists_matrix g) i

/-- The actual matrix action determined by the vector labels. -/
public noncomputable def linearAction : max5 →* SL where
  toFun := matrixOf
  map_one' := by
    apply matrix_unique
    intro i
    rw [← matrixOf_spec]
    simp
  map_mul' g h := by
    apply matrix_unique
    intro i
    rw [← matrixOf_spec, map_mul, LinearEquiv.mul_apply, ← matrixOf_spec,
      ← matrixOf_spec]
    rfl

/-- The constructed action intertwines the original Held permutations. -/
public theorem linearAction_spec (g : max5) (i : Fin 2058) :
    label (representation g.val i) = (linearAction g).toLin' (label i) :=
  matrixOf_spec g i

/-- Its images on the literal local generators are the displayed matrices. -/
public theorem linearAction_generator (k : Fin 2) :
    linearAction (Cores.localGenerator 2 k) = generator k := by
  apply matrix_unique
  intro i
  exact (linearAction_spec _ i).symm.trans (label_generator k i)

/-- The matrix action is onto SL₃(2). -/
public theorem linearAction_surjective : Function.Surjective linearAction := by
  apply MonoidHom.range_eq_top.mp
  apply matrix_generators
  intro k
  exact ⟨Cores.localGenerator 2 k, linearAction_generator k⟩

/-- The canonical projective matrix quotient action. -/
public noncomputable def projection : max5 →* Matrix.PSL3Two.PSL :=
  Matrix.PSL3Two.equiv.toMonoidHom.comp linearAction

public theorem projection_surjective : Function.Surjective projection :=
  Matrix.PSL3Two.equiv.surjective.comp linearAction_surjective

/-- Kernel-image counting uses the checked order of the literal max5. -/
public theorem kernel_card : Nat.card projection.ker = 128 := by
  have h := projection.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr projection_surjective,
    Subgroup.card_top, Matrix.PSL3Two.card_PSL,
    InvolutionFixedData.TwoB.max5_card] at h
  omega

public theorem kernel_isPGroup : IsPGroup 2 projection.ker :=
  IsPGroup.of_card (n := 7) kernel_card

/-- The kernel is the intrinsic two-core, not merely a chosen normal word subgroup. -/
public theorem kernel_eq_pCore : projection.ker = pCore 2 max5 := by
  have h := projection.comap_pCore_of_ker_isPGroup projection_surjective kernel_isPGroup
  simpa only [Matrix.PSL3Two.pCore_two_PSL_eq_bot, MonoidHom.comap_bot] using h

/-- The literal max5 core quotient is the actual projective special linear matrix group. -/
public noncomputable def equiv :
    max5 ⧸ pCore 2 max5 ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq kernel_eq_pCore.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective projection projection_surjective)

/-- Proposition-valued export for consumers which choose the equivalence locally. -/
public theorem nonempty_equiv :
    Nonempty (max5 ⧸ pCore 2 max5 ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := ⟨equiv⟩

end Held.RankOneLocalPair.MatrixQuotient
