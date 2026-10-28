module
public import Theory.AlgebraicGroup.RootSystems.SymplecticMatrixCarrier
public import Theory.AlgebraicGroup.Automorphisms.Lang.SquareDifferential
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph.PerfectField

/-!
# Lang surjectivity for the exceptional symplectic graph map

The exceptional graph map is polynomial on the connected symplectic algebraic
carrier. Its square is coefficient Frobenius, so the differential of the square
vanishes in characteristic two. Lang's theorem therefore applies to every
positive power of the graph map. This supplies the algebraically closed step in
the odd-degree graph-involution descent used in Quasithin 2.5.19 and E.6.23.
-/

noncomputable section
open Theory.AlgebraicGroup
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
private abbrev Carrier := (standardSymplecticClosedSubgroup (k := k) 2).carrierVariety
private abbrev Points := Variety.Point (Carrier (k := k))
private abbrev Ix := Fin 2 ⊕ Fin 2
private abbrev e : Points (k := k) ≃* Sp k := symplecticMatrixPointEquiv 2
private def coord (i j : Ix) : (Carrier (k := k)).Coordinates :=
  Sum.inl (symplecticStandardIndexEquiv (k := k) 2 i,symplecticStandardIndexEquiv (k := k) 2 j)
private def graphPoint (x : Points (k := k)) : Points (k := k) := e.symm (graphEnd (e x))

private theorem graphPoint_matrix (x : Points (k := k)) :
    e (graphPoint x) = graphEnd (e x) := by
  exact e.apply_symm_apply _

private theorem graphPoint_entry (x : Points (k := k)) (i j : Ix) :
    (graphPoint x).val (coord i j) = graphMatrix (e x).val i j := by
  have he := symplecticMatrixPointEquiv_entry 2 (graphPoint x) i j
  change (e (graphPoint x)).val i j = (graphPoint x).val (coord i j) at he
  rw [←he,graphPoint_matrix]
  rfl

private def graphMorphism : Morphism (Carrier (k := k)) (Carrier (k := k)) where
  toVariety := {
    toFun := graphPoint
    regular := by
      rintro (⟨i,j⟩ | i)
      · let r := (symplecticStandardIndexEquiv (k := k) 2).symm i
        let s := (symplecticStandardIndexEquiv (k := k) 2).symm j
        refine ⟨MvPolynomial.X (coord (first r) (first s)) * MvPolynomial.X (coord (second r) (second s)) +
          MvPolynomial.X (coord (first r) (second s)) * MvPolynomial.X (coord (second r) (first s)), ?_⟩
        intro x
        have he : (Sum.inl (i,j) : (Carrier (k := k)).Coordinates) = coord r s := by
          simp [coord,r,s]
        rw [he,graphPoint_entry]
        simp only [graphMatrix,minor,evalPolynomial, MvPolynomial.eval₂_add,MvPolynomial.eval₂_mul,
          MvPolynomial.eval₂_X]
        simp only [e,symplecticMatrixPointEquiv_entry,coord]
      · refine ⟨1,?_⟩
        intro x
        cases i
        simpa only [evalPolynomial,MvPolynomial.eval₂_one] using symplecticPoint_scalar 2 (graphPoint x) }
  map_one := by simp [graphPoint]
  map_mul := by intro x y; simp only [graphPoint,map_mul]

private theorem graph_square_coordinate (x : Points (k := k)) (i : (Carrier (k := k)).Coordinates) :
    ((graphMorphism.comp graphMorphism).onPoints x).val i = x.val i ^ 2 := by
  change (graphPoint (graphPoint x)).val i = _
  rcases i with ⟨i,j⟩ | i
  · let r := (symplecticStandardIndexEquiv (k := k) 2).symm i
    let s := (symplecticStandardIndexEquiv (k := k) 2).symm j
    have he : (Sum.inl (i,j) : (Carrier (k := k)).Coordinates) = coord r s := by simp [coord,r,s]
    rw [he]
    have hx := symplecticMatrixPointEquiv_entry 2 (graphPoint (graphPoint x)) r s
    change (e (graphPoint (graphPoint x))).val r s = (graphPoint (graphPoint x)).val (coord r s) at hx
    rw [←hx,graphPoint_matrix,graphPoint_matrix]
    change (((graphEnd (F := k)).comp graphEnd) (e x)).val r s = _
    rw [graphEnd_square_frobenius,coefficientMap_apply,frobenius_def]
    exact congrArg (fun z : k => z ^ 2) (symplecticMatrixPointEquiv_entry 2 x r s)
  · cases i
    rw [symplecticPoint_scalar,symplecticPoint_scalar,one_pow]

private theorem graph_square_differential :
    Bor1.identityTangentMorphismLinearMap ((graphMorphism (k := k)).comp graphMorphism) = 0 := by
  apply LinearMap.ext
  intro D
  apply Bor1.coordinateTangentMap_injective (Carrier (k := k))
  funext i
  let a := Variety.PolynomialFunction.ofPolynomial (Carrier (k := k)) (MvPolynomial.X i)
  have ha : (graphMorphism.comp graphMorphism).toVariety.pullbackAlgHom a = a * a := by
    apply Variety.PolynomialFunction.ext
    intro x
    change evalPolynomial ((graphMorphism.comp graphMorphism).onPoints x).val (MvPolynomial.X i) =
      evalPolynomial x.val (MvPolynomial.X i) * evalPolynomial x.val (MvPolynomial.X i)
    simp only [evalPolynomial_X,graph_square_coordinate,pow_two]
  change D ((graphMorphism.comp graphMorphism).toVariety.pullbackAlgHom a) = 0
  rw [ha,Derivation.leibniz]
  exact CharTwo.add_self_eq_zero _

private def graphPower : ℕ → Morphism (Carrier (k := k)) (Carrier (k := k))
  | 0 => Morphism.id _
  | n+1 => (graphPower n).comp graphMorphism

private theorem graphPower_matrix (n : ℕ) (x : Points (k := k)) :
    e ((graphPower n).onPoints x) = (graphEndomorphism ^ n) (e x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change e ((graphPower n).onPoints (graphPoint x)) = _
    rw [ih,graphPoint_matrix,pow_succ]
    rfl

private theorem graphPower_surjective (n : ℕ) : Function.Surjective (graphPower (k := k) n).onPoints := by
  intro x
  obtain ⟨g,hg⟩ := (graphEnd_bijective_of_perfect (F := k)).surjective.iterate n (e x)
  refine ⟨e.symm g,e.injective ?_⟩
  rw [graphPower_matrix,e.apply_symm_apply]
  exact hg

private theorem graphPower_differential (n : ℕ) :
    Bor1.identityTangentMorphismLinearMap (graphPower (k := k) n) =
      (Bor1.identityTangentMorphismLinearMap graphMorphism) ^ n := by
  induction n with
  | zero =>
    rw [graphPower,Bor1.identityTangentMorphismLinearMap_id,pow_zero]
    exact Module.End.one_eq_id.symm
  | succ n ih =>
    rw [graphPower,Bor1.identityTangentMorphismLinearMap_comp,ih,pow_succ]
    rfl

public theorem graphEnd_lang_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (fun h : Sp k => h * ((graphEndomorphism ^ n) h)⁻¹) := by
  have hs : (Bor1.identityTangentMorphismLinearMap (graphMorphism (k := k))) ^ 2 = 0 := by
    have hh := graph_square_differential (k := k)
    rw [Bor1.identityTangentMorphismLinearMap_comp] at hh
    exact hh
  have hd : Bor1.identityTangentMorphismLinearMap ((graphPower (k := k) n).comp (graphPower n)) = 0 := by
    rw [Bor1.identityTangentMorphismLinearMap_comp,graphPower_differential]
    change (Bor1.identityTangentMorphismLinearMap (graphMorphism (k := k))) ^ n *
      (Bor1.identityTangentMorphismLinearMap graphMorphism) ^ n = 0
    rw [←pow_add]
    exact pow_eq_zero_of_le (by omega : 2 ≤ n+n) hs
  have hlang := langMorphism_surjective_of_square_differential_eq_zero (graphPower (k := k) n)
    (graphPower_surjective n) (standardSymplecticClosedSubgroup_isConnected 2) hd
  intro g
  obtain ⟨x,hx⟩ := hlang (e.symm g)
  refine ⟨e x,?_⟩
  have hh := congrArg e hx
  simpa only [langMorphism_apply,map_mul,map_inv,graphPower_matrix,e.apply_symm_apply] using hh
end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
