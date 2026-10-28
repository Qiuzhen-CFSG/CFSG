module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SourceClass
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Kernel
public import Theory.ElementaryAbelian.Extraspecial

/-!
# The monomial model of the literal octad restriction kernel

The shortened Golay code consists of the signs vanishing on the marked octad.
Its semidirect product with the actual Mathieu pointwise octad stabilizer embeds
in the Leech isometry group, centralizes the octad sign, and fixes the octad
lattice pointwise. Conversely a kernel element fixes each coordinate-eight
vector on the octad. The cross-stabilizer theorem makes it monomial, and its
signed permutation coordinates give the inverse of the displayed isomorphism.
Thus subsequent code and permutation calculations concern the literal kernel.

Source: Aschbacher, *Sporadic Groups* (1994), 25.1–25.2, pp.132–133.
The Golay and Leech constructions are the existing CFSG ports of Gerald Höhn
and ATLAS contributors, revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`;
see `LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

@[expose] public noncomputable section
open Atlas.Conway Atlas.Codes Atlas.Lattices
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
namespace KernelModel

/-- Golay signs vanishing on the marked octad. -/
def signCode : Submodule Bit golay where
  carrier := {c | ∀ i : Coordinate, c.val i.val = 0}
  zero_mem' := by intro i; rfl
  add_mem' := by intro c d hc hd i; change c.val i.val + d.val i.val = 0; rw [hc, hd, add_zero]
  smul_mem' := by intro b c hc i; change b * c.val i.val = 0; rw [hc, mul_zero]

/-- The actual Mathieu permutations fixing every marked octad coordinate. -/
def pointwise : Subgroup Mathieu24CodeModel where
  carrier := {g | ∀ i : Coordinate, g.val i.val = i.val}
  one_mem' := by intro i; rfl
  mul_mem' := by intro g h hg hh i; change g.val (h.val i.val) = i.val; rw [hh, hg]
  inv_mem' := by
    intro g hg i
    change g.val.symm i.val = i.val
    rw [Equiv.symm_apply_eq]
    exact (hg i).symm

theorem pointwise_fixes (g : pointwise) (i : Coordinate) : g.val.val i.val = i.val := g.prop i

theorem pointwise_inv_fixes (g : pointwise) (i : Coordinate) : g.val.val.symm i.val = i.val :=
  (g⁻¹).prop i

def signCodeMap (g : pointwise) : signCode →ₗ[Bit] signCode where
  toFun c := ⟨golayPermutationEquiv g.val c.val, by
    intro i
    change c.val.val (g.val.val.symm i.val) = 0
    rw [pointwise_inv_fixes]
    exact c.prop i⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def signCodeEquiv (g : pointwise) : signCode ≃ₗ[Bit] signCode where
  toLinearMap := signCodeMap g
  invFun := signCodeMap g⁻¹
  left_inv c := by
    apply Subtype.ext; apply Subtype.ext; funext i
    exact g.val.val.symm_apply_apply i |> congrArg c.val.val
  right_inv c := by
    apply Subtype.ext; apply Subtype.ext; funext i
    exact g.val.val.apply_symm_apply i |> congrArg c.val.val

def signAction : pointwise →* MulAut (Multiplicative signCode) where
  toFun g := (signCodeEquiv g).toAddEquiv.toMultiplicative
  map_one' := by apply MulEquiv.ext; intro c; rfl
  map_mul' _ _ := by apply MulEquiv.ext; intro c; rfl

abbrev Model := Multiplicative signCode ⋊[signAction] pointwise

def inclusion : Model →* GolayMonomialGroup :=
  SemidirectProduct.map signCode.subtype.toAddMonoidHom.toMultiplicative pointwise.subtype
    (by intro g; rfl)

theorem inclusion_injective : Function.Injective inclusion := by
  intro x y h
  apply SemidirectProduct.ext
  · exact Subtype.ext (congrArg SemidirectProduct.left h)
  · exact Subtype.ext (congrArg SemidirectProduct.right h)

theorem pointwise_word (g : pointwise) (i : Omega) :
    (golayBasis 0).val (g.val.val.symm i) = (golayBasis 0).val i := by
  by_cases hi : (golayBasis 0).val i = 0
  · rw [hi]
    by_contra hh
    have hf := g.prop ⟨g.val.val.symm i, hh⟩
    have he : i = g.val.val.symm i := (g.val.val.apply_symm_apply i).symm.trans hf
    exact hh (he ▸ hi)
  · rw [pointwise_inv_fixes g ⟨i, hi⟩]

theorem embedding_mem_centralizer (m : Model) : monomialEmbedding (inclusion m) ∈ centralizer := by
  apply mem_centralizer.mpr
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  funext i
  change (if m.left.toAdd.val.val i = 0 then
      (if (golayBasis 0).val (m.right.val.val.symm i) = 0 then x.val (m.right.val.val.symm i)
       else -x.val (m.right.val.val.symm i))
    else -(if (golayBasis 0).val (m.right.val.val.symm i) = 0 then x.val (m.right.val.val.symm i)
       else -x.val (m.right.val.val.symm i))) =
    (if (golayBasis 0).val i = 0 then
      (if m.left.toAdd.val.val i = 0 then x.val (m.right.val.val.symm i)
       else -x.val (m.right.val.val.symm i))
    else -(if m.left.toAdd.val.val i = 0 then x.val (m.right.val.val.symm i)
       else -x.val (m.right.val.val.symm i)))
  rw [pointwise_word]
  split_ifs <;> rfl

theorem embedding_fixes_lattice (m : Model) (x : lattice) :
    (monomialEmbedding (inclusion m)).val x.val = x.val := by
  apply Subtype.ext
  funext i
  rw [monomialEmbedding_apply]
  by_cases hi : (golayBasis 0).val i = 0
  · have hx := (mem_lattice_iff_support x.val).mp x.prop
    have hpre : (golayBasis 0).val (m.right.val.val.symm i) = 0 :=
      (pointwise_word m.right i).trans hi
    change (if m.left.toAdd.val.val i = 0 then x.val.val (m.right.val.val.symm i)
      else -x.val.val (m.right.val.val.symm i)) = x.val.val i
    rw [hx i hi, hx _ hpre]
    simp
  · change (if m.left.toAdd.val.val i = 0 then x.val.val (m.right.val.val.symm i)
      else -x.val.val (m.right.val.val.symm i)) = x.val.val i
    rw [m.left.toAdd.prop ⟨i, hi⟩, if_pos rfl, pointwise_inv_fixes m.right ⟨i, hi⟩]

def toKernel : Model →* action.ker where
  toFun m := ⟨⟨monomialEmbedding (inclusion m), embedding_mem_centralizer m⟩,
    (mem_action_ker _).mpr (embedding_fixes_lattice m)⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; exact (monomialEmbedding.comp inclusion).map_one
  map_mul' m n := by apply Subtype.ext; apply Subtype.ext; exact (monomialEmbedding.comp inclusion).map_mul m n

theorem toKernel_injective : Function.Injective toKernel := by
  intro x y h
  exact inclusion_injective (monomialEmbedding_injective (congrArg (fun k : action.ker => k.val.val) h))

private theorem axis_mem (i : Coordinate) : coordinateEight i.val ∈ lattice := by
  rw [mem_lattice_iff_support]
  intro j hj
  have hji : j ≠ i.val := by intro he; subst j; exact i.prop hj
  simp [coordinateEight, coordinateVector, hji]

theorem toKernel_surjective : Function.Surjective toKernel := by
  intro k
  have hfix (i : Coordinate) : k.val.val.val (coordinateEight i.val) = coordinateEight i.val :=
    (mem_action_ker k.val).mp k.prop ⟨_, axis_mem i⟩
  obtain ⟨i⟩ : Nonempty Coordinate := Fintype.card_pos_iff.mp (by rw [coordinate_card]; decide)
  obtain ⟨m, hm⟩ := coordinateEight_fixer_mem_monomial k.val.val i.val (hfix i)
  have hc (j : Coordinate) : m.right.val j.val = j.val ∧ m.left.toAdd.val j.val = 0 :=
    (monomial_axis_fixed_iff m j.val).mp (by rw [hm]; exact hfix j)
  let n : Model := ⟨Multiplicative.ofAdd ⟨m.left.toAdd, fun j => (hc j).2⟩,
    ⟨m.right, fun j => (hc j).1⟩⟩
  refine ⟨n, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hm

/-- Identification with the literal pointwise kernel of the Leech octad action. -/
def kernelEquiv : Model ≃* action.ker :=
  MulEquiv.ofBijective toKernel ⟨toKernel_injective, toKernel_surjective⟩

theorem kernelEquiv_val (m : Model) :
    (kernelEquiv m).val.val = monomialEmbedding (inclusion m) := rfl

end KernelModel
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
