module
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph.Construction
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Algebra.Group.End

/-!
# Exceptional graph maps beyond finite fields

The polynomial exterior-square map commutes with every coefficient embedding and squares to entrywise Frobenius over every field of characteristic two. Perfectness therefore makes it bijective, including over the algebraic closure needed for Lang descent. The exact even-power coefficient formula retains the original finite-field graph map.

Source: the exceptional B₂ isogeny, GLS3 2.5.1 and 2.5.12(e); Aschbacher–Smith 16.1.4.
-/

public section
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
variable {F K : Type*} [Field F] [Field K]

@[expose] def graphEndomorphism [CharP F 2] : Monoid.End (Sp F) := graphEnd

@[simp] theorem graphEndomorphism_apply [CharP F 2] (g : Sp F) : graphEndomorphism g = graphEnd g := by rfl

def coefficientMap (f : F →+* K) : Sp F →* Sp K where
  toFun g := ⟨g.val.map f,SymplecticGroup.map_mem g.property f⟩
  map_one' := by apply Subtype.ext; exact Matrix.map_one f (map_zero f) (map_one f)
  map_mul' g h := by apply Subtype.ext; exact Matrix.map_mul

@[simp] theorem coefficientMap_apply (f : F →+* K) (g : Sp F) (i j : Fin 2 ⊕ Fin 2) :
    (coefficientMap f g).val i j = f (g.val i j) := by rfl

theorem coefficientMap_injective (f : F →+* K) : Function.Injective (coefficientMap f) := by
  intro g h he
  apply Subtype.ext
  exact Matrix.map_injective f.injective (congrArg Subtype.val he)

theorem coefficientMap_graph [CharP F 2] [CharP K 2] (f : F →+* K) (g : Sp F) :
    coefficientMap f (graphEnd g) = graphEnd (coefficientMap f g) := by
  apply Subtype.ext
  ext i j
  change f (graphMatrix g.val i j) = graphMatrix (g.val.map f) i j
  simp only [graphMatrix,minor,Matrix.map_apply,map_add,map_mul]

theorem coefficientMap_root (f : F →+* K) (r : Fin 8) (t : F) :
    coefficientMap f (Representation.OneCohomology.SymplecticFour.rootElement r t) =
      Representation.OneCohomology.SymplecticFour.rootElement r (f t) := by
  apply Subtype.ext
  change (Representation.OneCohomology.SymplecticFour.rootMatrix r t).map f =
    Representation.OneCohomology.SymplecticFour.rootMatrix r (f t)
  fin_cases r <;>
    simp [Representation.OneCohomology.SymplecticFour.rootMatrix,Matrix.fromBlocks_map,
      Matrix.map_add,Matrix.map_sub,Matrix.map_one f (map_zero f) (map_one f)]

theorem graphEnd_square_frobenius [CharP F 2] :
    (graphEnd (F := F)).comp graphEnd = coefficientMap (frobenius F 2) := by
  apply MonoidHom.eq_of_eqOn_dense Representation.OneCohomology.SymplecticFour.rootElements_generate
  rintro _ ⟨⟨r,t⟩,rfl⟩
  change graphEnd (graphEnd _) = coefficientMap (frobenius F 2) _
  rw [graphEnd_root,graphEnd_root,coefficientMap_root]
  fin_cases r <;> simp [rootPermutation,rootParameter,frobenius_def]

theorem graphEnd_bijective_of_perfect [CharP F 2] [PerfectRing F 2] :
    Function.Bijective (graphEnd (F := F)) := by
  have he : (graphEnd (F := F)).comp graphEnd =
      (fieldAutomorphism (frobeniusEquiv F 2)).toMonoidHom := by
    rw [graphEnd_square_frobenius]
    rfl
  have hs : Function.Bijective ((graphEnd (F := F)).comp graphEnd) := by
    rw [he]
    exact (fieldAutomorphism (frobeniusEquiv F 2)).bijective
  exact ⟨fun x y hxy => hs.1 (congrArg graphEnd hxy),fun y => by
    obtain ⟨x,hx⟩ := hs.2 y
    exact ⟨graphEnd x,hx⟩⟩

theorem graphEnd_even_power [CharP F 2] (n : ℕ) (g : Sp F) (i j : Fin 2 ⊕ Fin 2) :
    ((graphEndomorphism (F := F) ^ (2*n)) g).val i j = (g.val i j) ^ (2^n) := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ,pow_add]
    change ((graphEndomorphism ^ (2*n)) ((graphEnd.comp graphEnd) g)).val i j = _
    rw [ih,graphEnd_square_frobenius]
    change ((g.val i j)^2)^(2^n) = _
    rw [←pow_mul,Nat.pow_succ,Nat.mul_comm 2]

theorem coefficientMap_graphPower [CharP F 2] [CharP K 2]
    (f : F →+* K) (n : ℕ) (g : Sp F) :
    coefficientMap f ((graphEndomorphism ^ n) g) =
      (graphEndomorphism ^ n) (coefficientMap f g) := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ,pow_succ]
    change coefficientMap f ((graphEndomorphism ^ n) (graphEnd g)) =
      (graphEndomorphism ^ n) (graphEnd (coefficientMap f g))
    rw [ih,coefficientMap_graph]

theorem graphAut_pow_apply [Finite F] [CharP F 2] (n : ℕ) (g : Sp F) :
    (graphAut ^ n) g = (graphEndomorphism ^ n) g := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ,pow_succ]
    exact ih (graphAut g)
end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
