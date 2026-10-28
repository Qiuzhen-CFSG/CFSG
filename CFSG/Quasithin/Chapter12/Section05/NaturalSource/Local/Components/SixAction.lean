module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.Four
public import Theory.Representation.BinaryLinearRecognition.OrthogonalEight.PermutationComparison
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.Quotient

/-!
# The literal irreducible six-space action

Conjugation by G₆ is transported through the original wedge marking.
On L₆ this is the exterior-square action of its actual upper four-by-four
block. The retained comparison with the deleted eight-point module
therefore proves irreducibility for L₆ and every intermediate overgroup.

Normal two-subgroups act trivially, so the action descends through the
literal two-core of each containing component. This is the action needed
to apply the six-dimensional exclusions, not an abstract model assumption.

Source: Aschbacher--Smith, 12.5.2(4) and 12.5.3, printed pp.817--819.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 Representation.SL5ExteriorSquare
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace ExteriorMarking
variable (a : ExteriorMarking D)

def V₆Coordinates : a.Vi 6 ≃* Multiplicative V₆ := a.subspaceCoordinates V₆

private def binaryAutRepresentation (W : Type*) [AddCommGroup W] [Module (ZMod 2) W] :
    Representation (ZMod 2) (MulAut (Multiplicative W)) W where
  toFun g := (AddEquiv.toMultiplicative.symm g).toAddMonoidHom.toZModLinearMap 2
  map_one' := by apply LinearMap.ext; intro v; rfl
  map_mul' g k := by apply LinearMap.ext; intro v; rfl

def sixAction : Representation (ZMod 2) (a.Gi 6) V₆ :=
  (binaryAutRepresentation V₆).comp
    ((MulAut.congr a.V₆Coordinates).toMonoidHom.comp (a.Vi 6).normalizerMonoidHom)

omit [Finite G] in
theorem sixAction_original (g : a.Gi 6) (v : a.Vi 6) :
    a.V₆Coordinates ((a.Vi 6).normalizerMonoidHom g v) =
      Multiplicative.ofAdd (a.sixAction g (a.V₆Coordinates v).toAdd) := by
  change _ = a.V₆Coordinates ((a.Vi 6).normalizerMonoidHom g
    (a.V₆Coordinates.symm (a.V₆Coordinates v)))
  rw [MulEquiv.symm_apply_apply]

omit [Finite G] in
theorem sixAction_residual (l : a.Li 6) (v : V₆) :
    a.sixAction (inclusion (a.Li_le_Gi 6) l) v =
      v6Action (inclusion (parabolicResidual_le 4)
        (a.residualActor 6 (Or.inr (Or.inr (Or.inr rfl))) l)) v := by
  let w : a.subspace V₆ := a.V₆Coordinates.symm (Multiplicative.ofAdd v)
  have he := a.equivariant ⟨l, a.Li_le_L 6 l.property⟩
    ⟨w, a.subspace_le V₆ w.property⟩
  apply Subtype.ext
  have hr := a.residualActor_apply 6 (Or.inr (Or.inr (Or.inr rfl))) l
  change (a.residualActor 6 _ l : Representation.SL5TenDimensional.Group) =
    a.quotientEquiv (QuotientGroup.mk' _ ⟨l, a.Li_le_L 6 l.property⟩) at hr
  change (a.coordinates ⟨(l : G) * (w : G) * (l : G)⁻¹, _⟩).toAdd = _
  rw [he]
  change Representation.SL5TenDimensional.exteriorAction 2 _
    (a.coordinates ⟨w, _⟩).toAdd = _
  rw [← hr]
  congr 1
  exact congrArg (fun z : Multiplicative V₆ => z.toAdd.val)
    (a.V₆Coordinates.apply_symm_apply (Multiplicative.ofAdd v))

private theorem irreducible_equiv {H W U : Type*} [Group H]
    [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup U] [Module (ZMod 2) U]
    {ρ : Representation (ZMod 2) H W} {σ : Representation (ZMod 2) H U}
    (e : ρ.Equiv σ) (hs : Representation.IsIrreducible σ) : Representation.IsIrreducible ρ := by
  let f := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap
  let ef := LinearEquiv.ofBijective f (show Function.Bijective f from e.toLinearEquiv.bijective)
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  exact ef.isSimpleModule_iff.mpr
    ((Representation.irreducible_iff_isSimpleModule_asModule σ).mp hs)

private theorem orthogonal_irreducible : Representation.IsIrreducible
    Representation.BinaryLinearRecognition.orthogonalEightAction := by
  let e : (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)).Equiv
      Representation.BinaryLinearRecognition.orthogonalEightAction := Representation.Equiv.mk
    Representation.BinaryLinearRecognition.naturalEightOrthogonalEquiv
    (fun g => LinearMap.ext (Representation.BinaryLinearRecognition.naturalEightOrthogonalEquiv_alternating g))
  exact irreducible_equiv e.symm (BinaryPermutation.alternatingNatural_isIrreducible (by simp))

def Li₆AlternatingActor : a.Li 6 →* alternatingGroup (Fin 8) :=
  (Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.trans (MulEquiv.refl _)).toMonoidHom.comp
    (Atlas.Order20160A8.sl4TwoEquivPSL.toMonoidHom.comp
      (a.LiLinearHom 6 (Or.inr (Or.inr (Or.inr rfl)))))

theorem Li₆AlternatingActor_surjective : Function.Surjective a.Li₆AlternatingActor :=
  Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.surjective.comp
    (Atlas.Order20160A8.sl4TwoEquivPSL.surjective.comp
      (a.LiLinearHom_surjective 6 (Or.inr (Or.inr (Or.inr rfl)))))

omit [Finite G] in
theorem sixAction_orthogonal (l : a.Li 6) (v : V₆) :
    v6QuadraticIsometry (a.sixAction (inclusion (a.Li_le_Gi 6) l) v) =
      Representation.BinaryLinearRecognition.orthogonalEightAction
        (a.Li₆AlternatingActor l) (v6QuadraticIsometry v) := by
  rw [a.sixAction_residual, v6QuadraticIsometry_action]
  let r : parabolicResidual 4 := a.residualActor 6 (Or.inr (Or.inr (Or.inr rfl))) l
  have he : a.LiLinearHom 6 (Or.inr (Or.inr (Or.inr rfl))) l =
      parabolicFourBlock (inclusion (parabolicResidual_le 4) r) := by
    change parabolicFourResidualQuotientEquiv (QuotientGroup.mk' _ r) = _
    rw [parabolicFourResidualQuotientEquiv_mk]
    apply Subtype.ext
    rfl
  rw [sl4TwoOmegaEquiv_linear]
  change _ = (Atlas.Order20160A8.DeletedEight.orthogonalHom
    (Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
      (Atlas.Order20160A8.sl4TwoEquivPSL (a.LiLinearHom 6 _ l))).val).val _
  rw [he, Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8_orthogonal]
  rfl

theorem sixAction_residual_irreducible : Representation.IsIrreducible
    (a.sixAction.comp (inclusion (a.Li_le_Gi 6))) := by
  let e : Representation.Equiv (a.sixAction.comp (inclusion (a.Li_le_Gi 6)))
      (Representation.BinaryLinearRecognition.orthogonalEightAction.comp a.Li₆AlternatingActor) :=
    Representation.Equiv.mk v6QuadraticIsometry.toLinearEquiv
    (fun g => LinearMap.ext (a.sixAction_orthogonal g))
  exact irreducible_equiv e
    ((Representation.irreducible_comp_surjective_iff a.Li₆AlternatingActor
      a.Li₆AlternatingActor_surjective _).mpr orthogonal_irreducible)

private theorem irreducible_of_comp {H K W : Type*} [Group H] [Group K]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) H W)
    (f : K →* H) [Representation.IsIrreducible (ρ.comp f)] :
    Representation.IsIrreducible ρ := by
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial (ρ.comp f)
  refine { exists_pair_ne := ⟨⊥,⊤,?_⟩, eq_bot_or_eq_top := ?_ }
  · intro he
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule he)
  intro S
  let R : Subrepresentation (ρ.comp f) := ⟨S.toSubmodule, fun k _ hv => S.apply_mem_toSubmodule (f k) hv⟩
  rcases eq_bot_or_eq_top R with hb | ht
  · have he := congrArg Subrepresentation.toSubmodule hb
    exact Or.inl (Subrepresentation.toSubmodule_injective he)
  · have he := congrArg Subrepresentation.toSubmodule ht
    exact Or.inr (Subrepresentation.toSubmodule_injective he)

theorem sixAction_overgroup_irreducible {K : Subgroup G} (hKG : K ≤ a.Gi 6)
    (hLK : a.Li 6 ≤ K) : Representation.IsIrreducible
      (a.sixAction.comp (inclusion hKG)) := by
  let : Representation.IsIrreducible
      ((a.sixAction.comp (inclusion hKG)).comp (inclusion hLK)) := by
    have he : ((a.sixAction.comp (inclusion hKG)).comp (inclusion hLK)) =
        a.sixAction.comp (inclusion (a.Li_le_Gi 6)) := by ext g v; rfl
    rw [he]
    exact a.sixAction_residual_irreducible
  exact irreducible_of_comp (a.sixAction.comp (inclusion hKG)) (inclusion hLK)

/-- The normal two-core acts trivially on the literal irreducible six-space. -/
theorem sixAction_twoCore_le_ker {K : Subgroup G} (hKG : K ≤ a.Gi 6)
    (hLK : a.Li 6 ≤ K) : pCore 2 K ≤ (a.sixAction.comp (inclusion hKG)).ker := by
  let := a.sixAction_overgroup_irreducible hKG hLK
  exact Representation.normal_p_subgroup_le_ker _ _ pCore_isPGroup

end ExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
