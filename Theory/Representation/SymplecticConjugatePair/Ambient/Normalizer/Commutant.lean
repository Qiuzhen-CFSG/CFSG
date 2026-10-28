module

public import Theory.Representation.SymplecticConjugatePair.Ambient.Normalizer.Coordinates

/-!
# The binary commutant of the derived symplectic graph pair

Two products of opposite long roots are explicit commutators. For either
product `x`, the operator `x + x²` on the natural module projects onto its
hyperbolic plane; on the graph-conjugate module the same polynomial is the
identity. The two complementary natural projections therefore force every
additive intertwiner between the modules to vanish, in both directions.

Conjugating a natural projection by root matrices and composing with the
original projections produces coordinate maps with arbitrary field parameters.
An additive map commuting with the derived group must commute with these
maps, which forces it to be a field scalar. Four-block decomposition then
computes the full binary commutant as the independent scalars on the summands.

Every action to which the commuting hypothesis is applied belongs to the genuine
derived group; normality allows conjugation by arbitrary root matrices. The proof
applies uniformly to the field of order two and larger fields, without assuming
perfectness, irreducibility or inequivalence.

This supplies the commutant input for the paired normalizer in Aschbacher–Smith,
combined manuscript of 1 March 2004, H.7, printed pp.388–389, and the paired
setup preceding Table 7.1.1, printed p.696 of `refs/quasithin.pdf`.
-/

open Matrix Representation Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
open scoped Matrix commutatorElement
namespace SymplecticConjugatePair.Ambient.Normalizer
namespace Commutant
variable {F : Type*} [Field F] [CharP F 2]
local notation "I" => Fin 2 ⊕ Fin 2
local notation "a" => (Sum.inl (0 : Fin 2) : I)
local notation "b" => (Sum.inl (1 : Fin 2) : I)

lemma add_outer_cancel (x y : F) : x + (y + x) = y := by
  rw [add_left_comm x y x, CharTwo.add_self_eq_zero x, add_zero]

def cubic (k : Fin 2) : Sp F :=
  rootElement (if k = 0 then 0 else 2) 1 * rootElement (if k = 0 then 1 else 3) 1

lemma root_inv (r : Fin 8) (t : F) : (rootElement r t)⁻¹ = rootElement r t := by
  apply inv_eq_of_mul_eq_one_left
  rw [RootSubgroup.element_add, CharTwo.add_self_eq_zero, RootSubgroup.element_zero]

lemma cubic_mem (k : Fin 2) : cubic (F := F) k ∈ commutator (Sp F) := by
  have hm : ⁅rootElement (if k = 0 then 1 else 3) (1 : F),
      rootElement (if k = 0 then 0 else 2) 1⁆ ∈ commutator (Sp F) := by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  convert hm using 1
  simp only [commutatorElement_def, root_inv]
  apply Subtype.ext
  ext i j
  change (rootMatrix (if k = 0 then 0 else 2) (1 : F) *
    rootMatrix (if k = 0 then 1 else 3) 1 : Matrix I I F) i j =
    (rootMatrix (if k = 0 then 1 else 3) (1 : F) *
      rootMatrix (if k = 0 then 0 else 2) 1 *
      rootMatrix (if k = 0 then 1 else 3) 1 *
      rootMatrix (if k = 0 then 0 else 2) 1 : Matrix I I F) i j
  fin_cases k <;> rcases i with i|i <;> rcases j with j|j <;>
    fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.fromBlocks, Matrix.single, Matrix.one_apply, CharTwo.add_self_eq_zero]

def plane (k : Fin 2) (v : Vector F) : Vector F :=
  Sum.elim (fun i => if i = k then v (.inl i) else 0)
    (fun i => if i = k then v (.inr i) else 0)

lemma cubic_polynomial (k : Fin 2) (v : Vector F) :
    symplecticNatural 2 (cubic k) v +
      symplecticNatural 2 (cubic k) (symplecticNatural 2 (cubic k) v) = plane k v := by
  ext i
  fin_cases k <;> rcases i with i|i <;> fin_cases i <;>
    simp [cubic, plane, symplecticNatural_apply, rootElement, rootMatrix,
      Matrix.mulVec, dotProduct, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, Matrix.fromBlocks, Matrix.single, Matrix.one_apply,
      CharTwo.add_self_eq_zero, CharTwo.add_cancel_right, add_outer_cancel, add_assoc]

omit [CharP F 2] in

lemma plane_add (v : Vector F) : plane 0 v + plane 1 v = v := by
  ext i
  rcases i with i|i <;> fin_cases i <;> simp [plane]

def planeConj (g : Sp F) (v : Vector F) : Vector F :=
  symplecticNatural 2 g (plane 0 (symplecticNatural 2 g⁻¹ v))

lemma conj_polynomial (g : Sp F) (v : Vector F) :
    symplecticNatural 2 (g * cubic 0 * g⁻¹) v +
      symplecticNatural 2 (g * cubic 0 * g⁻¹)
        (symplecticNatural 2 (g * cubic 0 * g⁻¹) v) = planeConj g v := by
  simp only [map_mul, Module.End.mul_apply, Representation.inv_self_apply]
  rw [← map_add, cubic_polynomial]
  rfl

def planeIndex : I → Fin 2 := Sum.elim id id

def sourceIndex : I → I := Sum.elim ![b, a] ![b, a]

def rootIndex : I → Fin 8 := Sum.elim ![6, 7] ![5, 5]

lemma coordinate_operator (i : I) (t : F) (v : Vector F) :
    plane (planeIndex i) (planeConj (rootElement (rootIndex i) t) v + plane 0 v) =
      Pi.single i (t * v (sourceIndex i)) := by
  simp only [planeConj, root_inv]
  ext j
  rcases i with i|i <;> rcases j with j|j <;> fin_cases i <;> fin_cases j <;>
    simp [planeIndex, sourceIndex, rootIndex, plane,
      symplecticNatural_apply, rootElement, rootMatrix, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks, Matrix.single,
      Matrix.one_apply, CharTwo.neg_eq, CharTwo.add_self_eq_zero,
      CharTwo.add_cancel_right, add_outer_cancel, add_assoc]

/-- Every additive endomorphism commuting with the actual derived natural action is a field scalar. -/
public theorem natural_centralizer_scalar (f : Vector F →+ Vector F)
    (hf : ∀ (g : commutator (Sp F)) v,
      f (symplecticNatural 2 g.val v) = symplecticNatural 2 g.val (f v)) :
    ∃ t : F, ∀ v, f v = t • v := by
  have hp (k : Fin 2) (v : Vector F) : f (plane k v) = plane k (f v) := by
    have h := hf ⟨cubic k, cubic_mem k⟩
    change ∀ v, f (symplecticNatural 2 (cubic k) v) =
      symplecticNatural 2 (cubic k) (f v) at h
    rw [← cubic_polynomial, map_add, h, h, h, cubic_polynomial]
  have hpc (g : Sp F) (v : Vector F) : f (planeConj g v) = planeConj g (f v) := by
    have hm := (inferInstance : (commutator (Sp F)).Normal).conj_mem
      (cubic 0) (cubic_mem 0) g
    have h := hf ⟨g * cubic 0 * g⁻¹, hm⟩
    change ∀ v, f (symplecticNatural 2 (g * cubic 0 * g⁻¹) v) =
      symplecticNatural 2 (g * cubic 0 * g⁻¹) (f v) at h
    rw [← conj_polynomial, map_add, h, h, h, conj_polynomial]
  have hsingle (i : I) (t : F) :
      f (Pi.single i t) = Pi.single i (t * f (Pi.single (sourceIndex i) 1) (sourceIndex i)) := by
    calc
      f (Pi.single i t) = f (plane (planeIndex i)
          (planeConj (rootElement (rootIndex i) t) (Pi.single (sourceIndex i) 1) +
            plane 0 (Pi.single (sourceIndex i) 1))) := by
        congr 1
        simpa using (coordinate_operator i t (Pi.single (sourceIndex i) 1)).symm
      _ = plane (planeIndex i)
          (planeConj (rootElement (rootIndex i) t) (f (Pi.single (sourceIndex i) 1)) +
            plane 0 (f (Pi.single (sourceIndex i) 1))) := by
        rw [hp, map_add, hpc, hp]
      _ = _ := coordinate_operator i t _
  have hb : f (Pi.single b 1) b = f (Pi.single a 1) a := by
    simpa [sourceIndex] using congrFun (hsingle b 1) b
  have hs (i : I) (t : F) :
      f (Pi.single i t) = Pi.single i (t * f (Pi.single a 1) a) := by
    rw [hsingle]
    rcases i with i|i <;> fin_cases i <;> simp [sourceIndex, hb]
  refine ⟨f (Pi.single a 1) a, fun v => ?_⟩
  have hv : v = ∑ i : I, Pi.single i (v i) := by
    ext i
    simp [Finset.sum_apply]
  calc
    f v = ∑ i : I, f (Pi.single i (v i)) := by rw [← map_sum, ← hv]
    _ = ∑ i : I, Pi.single i (v i * f (Pi.single a 1) a) :=
      Finset.sum_congr rfl (fun i _ => hs i (v i))
    _ = f (Pi.single a 1) a • v := by
      ext i
      simp [Finset.sum_apply, mul_comm]

variable [Finite F]

lemma graph_cubic_polynomial (k : Fin 2) (v : Vector F) :
    symplecticNatural 2 (graphAut (cubic k)) v +
      symplecticNatural 2 (graphAut (cubic k))
        (symplecticNatural 2 (graphAut (cubic k)) v) = v := by
  simp only [cubic, map_mul, graphAut_apply, graphEnd_root]
  ext i
  fin_cases k <;> rcases i with i|i <;> fin_cases i <;>
    simp [symplecticNatural_apply, rootElement, rootMatrix, rootPermutation,
      rootParameter, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks, Matrix.single,
      Matrix.one_apply, CharTwo.neg_eq, CharTwo.add_self_eq_zero,
      CharTwo.add_cancel_left, CharTwo.add_cancel_right, add_outer_cancel, add_assoc]
/-- There is no nonzero additive intertwiner from the derived natural module to its graph conjugate. -/
public theorem natural_graph_intertwiner_zero (f : Vector F →+ Vector F)
    (hf : ∀ (g : commutator (Sp F)) v,
      f (symplecticNatural 2 g.val v) = symplecticNatural 2 (graphAut g.val) (f v)) :
    f = 0 := by
  have hp (k : Fin 2) (v : Vector F) : f (plane k v) = f v := by
    have h := hf ⟨cubic k, cubic_mem k⟩
    change ∀ v, f (symplecticNatural 2 (cubic k) v) =
      symplecticNatural 2 (graphAut (cubic k)) (f v) at h
    rw [← cubic_polynomial, map_add, h, h, h, graph_cubic_polynomial]
  apply AddMonoidHom.ext
  intro v
  change f v = 0
  calc
    f v = f (plane 0 v + plane 1 v) := congrArg f (plane_add v).symm
    _ = f v + f v := by rw [map_add, hp, hp]
    _ = 0 := by ext i; exact CharTwo.add_self_eq_zero _

/-- There is no nonzero additive intertwiner from the derived graph conjugate to the natural module. -/
public theorem graph_natural_intertwiner_zero (f : Vector F →+ Vector F)
    (hf : ∀ (g : commutator (Sp F)) v,
      f (symplecticNatural 2 (graphAut g.val) v) = symplecticNatural 2 g.val (f v)) :
    f = 0 := by
  have hp (k : Fin 2) (v : Vector F) : f v = plane k (f v) := by
    have h := hf ⟨cubic k, cubic_mem k⟩
    change ∀ v, f (symplecticNatural 2 (graphAut (cubic k)) v) =
      symplecticNatural 2 (cubic k) (f v) at h
    conv_lhs => rw [← graph_cubic_polynomial k v]
    rw [map_add, h, h, h, cubic_polynomial]
  apply AddMonoidHom.ext
  intro v
  change f v = 0
  calc
    f v = plane 0 (f v) + plane 1 (f v) := (plane_add (f v)).symm
    _ = f v + f v := by rw [← hp 0 v, ← hp 1 v]
    _ = 0 := by ext i; exact CharTwo.add_self_eq_zero _

/-- The additive commutant of the derived graph-conjugate action also consists of field scalars. -/
public theorem graph_centralizer_scalar (f : Vector F →+ Vector F)
    (hf : ∀ (g : commutator (Sp F)) v,
      f (symplecticNatural 2 (graphAut g.val) v) =
        symplecticNatural 2 (graphAut g.val) (f v)) :
    ∃ t : F, ∀ v, f v = t • v := by
  apply natural_centralizer_scalar f
  intro g v
  have hm : graphAut.symm g.val ∈ commutator (Sp F) :=
    Subgroup.characteristic_iff_le_comap.mp
      (inferInstance : (commutator (Sp F)).Characteristic) graphAut.symm g.property
  have h := hf ⟨graphAut.symm g.val, hm⟩ v
  simpa only [MulEquiv.apply_symm_apply] using h

end Commutant
open Commutant
variable {F : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]

/-- The binary commutant of the actual derived pair consists of independent field scalars. -/
public theorem centralizer_block_scalars (q : Space F →ₗ[ZMod 2] Space F)
    (hq : ∀ (g : commutator (Sp F)) v,
      q (derivedPair graphAut g v) = derivedPair graphAut g (q v)) :
    ∃ a b : F, q = blockScalar a b := by
  let inl : Vector F →ₗ[ZMod 2] Space F := LinearMap.inl (ZMod 2) (Vector F) (Vector F)
  let inr : Vector F →ₗ[ZMod 2] Space F := LinearMap.inr (ZMod 2) (Vector F) (Vector F)
  let fst : Space F →ₗ[ZMod 2] Vector F := LinearMap.fst (ZMod 2) (Vector F) (Vector F)
  let snd : Space F →ₗ[ZMod 2] Vector F := LinearMap.snd (ZMod 2) (Vector F) (Vector F)
  let q₁₁ := (fst.comp (q.comp inl)).toAddMonoidHom
  let q₁₂ := (fst.comp (q.comp inr)).toAddMonoidHom
  let q₂₁ := (snd.comp (q.comp inl)).toAddMonoidHom
  let q₂₂ := (snd.comp (q.comp inr)).toAddMonoidHom
  have h₁₁ (g : commutator (Sp F)) (v : Vector F) :
      q₁₁ (symplecticNatural 2 g.val v) = symplecticNatural 2 g.val (q₁₁ v) := by
    have h := congrArg Prod.fst (hq g (v, 0))
    change (q (symplecticNatural 2 g.val v, symplecticNatural 2 (graphAut g.val) 0)).1 =
      symplecticNatural 2 g.val (q (v, 0)).1 at h
    simpa [q₁₁, fst, inl] using h
  have h₁₂ (g : commutator (Sp F)) (v : Vector F) :
      q₁₂ (symplecticNatural 2 (graphAut g.val) v) = symplecticNatural 2 g.val (q₁₂ v) := by
    have h := congrArg Prod.fst (hq g (0, v))
    change (q (symplecticNatural 2 g.val 0, symplecticNatural 2 (graphAut g.val) v)).1 =
      symplecticNatural 2 g.val (q (0, v)).1 at h
    simpa [q₁₂, fst, inr] using h
  have h₂₁ (g : commutator (Sp F)) (v : Vector F) :
      q₂₁ (symplecticNatural 2 g.val v) = symplecticNatural 2 (graphAut g.val) (q₂₁ v) := by
    have h := congrArg Prod.snd (hq g (v, 0))
    change (q (symplecticNatural 2 g.val v, symplecticNatural 2 (graphAut g.val) 0)).2 =
      symplecticNatural 2 (graphAut g.val) (q (v, 0)).2 at h
    simpa [q₂₁, snd, inl] using h
  have h₂₂ (g : commutator (Sp F)) (v : Vector F) :
      q₂₂ (symplecticNatural 2 (graphAut g.val) v) =
        symplecticNatural 2 (graphAut g.val) (q₂₂ v) := by
    have h := congrArg Prod.snd (hq g (0, v))
    change (q (symplecticNatural 2 g.val 0, symplecticNatural 2 (graphAut g.val) v)).2 =
      symplecticNatural 2 (graphAut g.val) (q (0, v)).2 at h
    simpa [q₂₂, snd, inr] using h
  obtain ⟨a, ha⟩ := natural_centralizer_scalar q₁₁ h₁₁
  obtain ⟨b, hb⟩ := graph_centralizer_scalar q₂₂ h₂₂
  have h₁₂zero := graph_natural_intertwiner_zero q₁₂ h₁₂
  have h₂₁zero := natural_graph_intertwiner_zero q₂₁ h₂₁
  refine ⟨a, b, LinearMap.ext (fun v => ?_)⟩
  change q v = (a • v.1, b • v.2)
  have hv : v = (v.1, 0) + (0, v.2) := by simp
  have h₁₂v : (q (0, v.2)).1 = 0 := DFunLike.congr_fun h₁₂zero v.2
  have h₂₁v : (q (v.1, 0)).2 = 0 := DFunLike.congr_fun h₂₁zero v.1
  calc
    q v = q (v.1, 0) + q (0, v.2) := by rw [← map_add, ← hv]
    _ = (a • v.1, b • v.2) := by
      apply Prod.ext
      · change (q (v.1, 0)).1 + (q (0, v.2)).1 = a • v.1
        rw [h₁₂v, add_zero]
        exact ha v.1
      · change (q (v.1, 0)).2 + (q (0, v.2)).2 = b • v.2
        rw [h₂₁v, zero_add]
        exact hb v.2

/-- An operator commutes with the derived graph pair exactly when it is a block scalar. -/
public theorem commutes_iff_blockScalar (q : Space F →ₗ[ZMod 2] Space F) :
    (∀ (g : commutator (Sp F)) v,
      q (derivedPair graphAut g v) = derivedPair graphAut g (q v)) ↔
        ∃ a b : F, q = blockScalar a b := by
  constructor
  · exact centralizer_block_scalars q
  · rintro ⟨a, b, rfl⟩
    exact blockScalar_commutes graphAut a b

end SymplecticConjugatePair.Ambient.Normalizer
