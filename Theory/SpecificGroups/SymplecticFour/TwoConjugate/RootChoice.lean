module
public import Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers.NormalForms
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.Geometry
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.Actions
import Mathlib.Tactic.FinCases

/-!
# Choosing a transvection marking for a rooted opposite pair

The exceptional graph automorphism takes the short-root involution type a₂
to the transvection type b₁. Its exterior-square formula fixes the literal
opposition matrix, so it carries an original opposite pair to the opposite
pair of the transported subgroup. It also preserves the standard unipotent
subgroup. Composing the component marking with its inverse therefore keeps
both the original module and Sylow while choosing a transvection marking.

Source: Aschbacher--Smith E.2.7, printed p.220, the replacement of the natural
module by its graph twist before applying G.4.1.
-/

public noncomputable section
open Subgroup Matrix
namespace Theory.SpecificGroups.SymplecticFour.TwoConjugate
open InvolutionTypes InvolutionCentralizers
open DiagramAutomorphisms.ExceptionalGraph
open Representation.OneCohomology.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The graph twist turns an a₂ involution into a transvection. -/
theorem graph_isB1_of_isA2 (x : Sp F) (hx : IsA2 x) : IsB1 (graphAut x) := by
  obtain ⟨g,t,ht,rfl⟩ := isA2_conjugate_root4 x hx
  have hr : graphAut (rootElement 4 t) = rootElement 0 (t^2) := by
    simp only [graphAut_apply,graphEnd_root,rootPermutation,rootParameter]
    rfl
  rw [map_mul,map_mul,map_inv,hr]
  exact (isB1_conj_iff _ _).mpr (root0_isB1 (pow_ne_zero 2 ht))

/-- The fixed opposition matrix is unchanged by the graph twist. -/
theorem graph_opposition : graphAut (opposition (F := F)) = opposition := by
  apply Subtype.ext
  change graphMatrix (fromBlocks 0 1 1 0) = fromBlocks 0 1 1 0
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [graphMatrix,minor,first,second,fromBlocks]

/-- The graph twist preserves the literal two-conjugate construction. -/
theorem oppositePair_map_graph (V : Subgroup (Sp F)) :
    oppositePair (V.map (graphAut (F := F)).toMonoidHom) =
      (oppositePair V).map (graphAut (F := F)).toMonoidHom := by
  have he : (MulAut.conj (opposition (F := F))).toMonoidHom.comp graphAut.toMonoidHom =
      graphAut.toMonoidHom.comp (MulAut.conj (opposition (F := F))).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,
      map_mul,map_inv,graph_opposition]
  simp only [oppositePair,Subgroup.map_sup,Subgroup.map_map,he]

/-- A rooted pair admits a transvection marking with the original Sylow and
original ambient module unchanged. -/
theorem exists_marked_transvection_of_root
    {G : Type*} [Group G] (T V L : Subgroup G) (e : Sp F ≃* L)
    (hmark : T.comap (L.subtype.comp e.toMonoidHom) = unipotent)
    (hr : ∃ x ∈ oppositePair (V.comap (L.subtype.comp e.toMonoidHom)), IsRootElement x) :
    ∃ e' : Sp F ≃* L,
      T.comap (L.subtype.comp e'.toMonoidHom) = unipotent ∧
      ∃ x ∈ oppositePair (V.comap (L.subtype.comp e'.toMonoidHom)), IsB1 x := by
  obtain ⟨x,hx,hroot⟩ := hr
  rcases (isRootElement_iff x).mp hroot with hb | ha
  · exact ⟨e,hmark,x,hx,hb⟩
  let e' : Sp F ≃* L := graphAut.symm.trans e
  have hT : T.comap (L.subtype.comp e'.toMonoidHom) = unipotent := by
    change (T.comap (L.subtype.comp e.toMonoidHom)).comap graphAut.symm.toMonoidHom = _
    rw [hmark]
    exact (comap_equiv_eq_map_symm graphAut.symm _).trans
      EvenBorelTorus.graph_map_unipotent
  have hV : V.comap (L.subtype.comp e'.toMonoidHom) =
      (V.comap (L.subtype.comp e.toMonoidHom)).map graphAut.toMonoidHom := by
    change (V.comap (L.subtype.comp e.toMonoidHom)).comap graphAut.symm.toMonoidHom = _
    exact comap_equiv_eq_map_symm graphAut.symm _
  refine ⟨e',hT,graphAut x,?_,graph_isB1_of_isA2 x ha⟩
  rw [hV,oppositePair_map_graph]
  exact mem_map_of_mem graphAut.toMonoidHom hx

end Theory.SpecificGroups.SymplecticFour.TwoConjugate
