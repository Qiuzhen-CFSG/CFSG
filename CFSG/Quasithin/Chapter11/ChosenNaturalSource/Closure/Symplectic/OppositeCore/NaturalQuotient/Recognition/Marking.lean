module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.NaturalQuotient.FixedSpaces
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.ActionOperations

/-!
# The original opposite pair mapped onto its marked SL₂

The faithful first-plane embedding and the full original action on V give
an explicit epimorphism I → SL₂(F). Its kernel is exactly O₂(I), and its
first root image is the standard upper-unipotent Sylow subgroup. Since
[V,W]=V₁, every lift of the root normalizer preserves V₁ and therefore W.
This last statement uses the full original point normalizer G₁.

These are the actor identifications for descent of the literal Q/N action.
Source: Aschbacher--Smith, 11.5.7, printed p.783.
-/

@[expose] public noncomputable section
open Subgroup Theory.SpecificGroups.SymplecticFour
open scoped MatrixGroups
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
open CFSG.Quasithin.Chapter12.Section02 OppositeGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

def pairModelHom (m : MarkedFlag E) (g : Sp E.input.field.Carrier) :
    SL(2,E.input.field.Carrier) →* MulAut V :=
  (FullAction.modelHom m).comp
    ((MulAut.conj g).toMonoidHom.comp OppositeLongRootPair.embedding)

theorem pairModelHom_injective (m : MarkedFlag E) (g : Sp E.input.field.Carrier) :
    Function.Injective (pairModelHom E m g) :=
  (FullAction.modelHom_injective m).comp
    ((MulAut.conj g).injective.comp OppositeLongRootPair.embedding_injective)

theorem pairModelHom_range (m : MarkedFlag E) (g : Sp E.input.field.Carrier) :
    (pairModelHom E m g).range =
      (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m) := by
  rw [pairModelHom,MonoidHom.range_comp,MonoidHom.range_comp,OppositeLongRootPair.embedding_range]

variable (m : MarkedFlag E) (hW : E.W ≤ E.G₁.pCoreIn 2) (g : Sp E.input.field.Carrier)
    (y : L)
    (hi : actionImage (V := V) (oppositeJoin (auxiliaryW E) (y:G)) =
      (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m))

def pairOriginalAction : oppositeJoin (auxiliaryW E) (y:G) →* MulAut V :=
  (largeAction E).comp (inclusion (oppositeJoin_le_large E m hW y.property))

theorem pairOriginalAction_range : (pairOriginalAction E m hW y).range =
    actionImage (V := V) (oppositeJoin (auxiliaryW E) (y:G)) := by
  rw [pairOriginalAction,MonoidHom.range_comp,Subgroup.inclusion_range,
    largeAction_image E _ (oppositeJoin_le_large E m hW y.property)]

def pairAction : oppositeJoin (auxiliaryW E) (y:G) →* SL(2,E.input.field.Carrier) :=
  (MonoidHom.ofInjective (pairModelHom_injective E m g)).symm.toMonoidHom.comp
    ((pairOriginalAction E m hW y).codRestrict (pairModelHom E m g).range (by
      intro i
      rw [pairModelHom_range,← hi,← pairOriginalAction_range E m hW y]
      exact ⟨i,rfl⟩))

theorem pairAction_spec (i : oppositeJoin (auxiliaryW E) (y:G)) :
    pairModelHom E m g (pairAction E m hW g y hi i) = pairOriginalAction E m hW y i := by
  exact congrArg Subtype.val
    ((MonoidHom.ofInjective (pairModelHom_injective E m g)).apply_symm_apply _)

theorem pairAction_surjective : Function.Surjective (pairAction E m hW g y hi) := by
  intro a
  have hm : pairModelHom E m g a ∈ (pairOriginalAction E m hW y).range := by
    rw [pairOriginalAction_range,hi,← pairModelHom_range]
    exact ⟨a,rfl⟩
  obtain ⟨i,he⟩ := hm
  exact ⟨i,(pairModelHom_injective E m g) ((pairAction_spec E m hW g y hi i).trans he)⟩

theorem pairAction_ker : (pairAction E m hW g y hi).ker =
    ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf
      (oppositeJoin (auxiliaryW E) (y:G)) := by
  ext i
  change pairAction E m hW g y hi i = 1 ↔ _
  rw [← (pairModelHom_injective E m g).eq_iff,pairAction_spec,map_one]
  change largeAction E (inclusion (oppositeJoin_le_large E m hW y.property) i) = 1 ↔ _
  rw [← MonoidHom.mem_ker,largeAction_ker]
  change (i:G) ∈ centralizer (V : Set G) ↔ (i:G) ∈ (L ⊔ (T:Subgroup G)).pCoreIn 2
  rw [← large_centralizer_eq_core E]
  exact ⟨fun h => ⟨oppositeJoin_le_large E m hW y.property i.property,h⟩,fun h => h.2⟩


theorem pairOriginalAction_map (A : Subgroup G)
    (hA : A ≤ oppositeJoin (auxiliaryW E) (y:G)) :
    (A.subgroupOf (oppositeJoin (auxiliaryW E) (y:G))).map (pairOriginalAction E m hW y) =
      actionImage (V := V) A := by
  rw [pairOriginalAction,← map_map]
  have he : (A.subgroupOf (oppositeJoin (auxiliaryW E) (y:G))).map
      (inclusion (oppositeJoin_le_large E m hW y.property)) =
      A.subgroupOf (L ⊔ (T : Subgroup G)) := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ha
    · intro hx
      exact ⟨⟨x,hA hx⟩,hx,Subtype.ext rfl⟩
  rw [he,largeAction_image E A (hA.trans (oppositeJoin_le_large E m hW y.property))]

theorem pairAction_map (A : Subgroup G)
    (hA : A ≤ oppositeJoin (auxiliaryW E) (y:G)) :
    ((A.subgroupOf (oppositeJoin (auxiliaryW E) (y:G))).map
      (pairAction E m hW g y hi)).map (pairModelHom E m g) = actionImage (V := V) A := by
  rw [map_map]
  have he : (pairModelHom E m g).comp (pairAction E m hW g y hi) =
      pairOriginalAction E m hW y := MonoidHom.ext (pairAction_spec E m hW g y hi)
  rw [he,pairOriginalAction_map E m hW y A hA]

theorem pairAction_ker_eq_core : (pairAction E m hW g y hi).ker =
    pCore 2 (oppositeJoin (auxiliaryW E) (y:G)) := by
  have hp : IsPGroup 2 (pairAction E m hW g y hi).ker := by
    rw [pairAction_ker]
    exact (isPGroup_pCoreIn 2 _).comap_subtype
  apply le_antisymm (show _ ≤ pCore 2 _ from le_sSup ⟨inferInstance,hp⟩)
  rw [pairAction_ker]
  intro i hi'
  exact marked_pair_core_le_large_core E m hW y.property g hi
    (mem_map_of_mem (oppositeJoin (auxiliaryW E) (y:G)).subtype hi')

private theorem upper_map_embedding {F : Type*} [Field F] :
    (Matrix.SpecialLinearGroup.upperUnipotent F).map OppositeLongRootPair.embedding =
      RootSubgroup.group 0 := by
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    obtain ⟨t,rfl⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent F a).mp ha
    rw [OppositeLongRootPair.embedding_upper]
    exact (RootSubgroup.mem_group_iff 0 _).mpr ⟨t,rfl⟩
  · intro hx
    obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff 0 x).mp hx
    exact ⟨_,(Matrix.SpecialLinearGroup.mem_upperUnipotent F _).mpr ⟨t,rfl⟩,
      OppositeLongRootPair.embedding_upper t⟩

theorem pairAction_root
    (hroot : actionImage (V := V) (auxiliaryW E) =
      ((RootSubgroup.group 0).map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m)) :
    ((auxiliaryW E).subgroupOf (oppositeJoin (auxiliaryW E) (y:G))).map
      (pairAction E m hW g y hi) = Matrix.SpecialLinearGroup.upperUnipotent E.input.field.Carrier := by
  apply map_injective (pairModelHom_injective E m g)
  rw [pairAction_map E m hW g y hi _ le_sup_left,hroot]
  rw [pairModelHom,← map_map,← map_map,upper_map_embedding]


private theorem originalAction_conjugate (A : Subgroup G)
    (hA : A ≤ oppositeJoin (auxiliaryW E) (y:G))
    (i : oppositeJoin (auxiliaryW E) (y:G)) :
    actionImage (V := V) (A.map (MulAut.conj (i:G)).toMonoidHom) =
      (actionImage (V := V) A).map (MulAut.conj (pairOriginalAction E m hW y i)).toMonoidHom := by
  let I := oppositeJoin (auxiliaryW E) (y:G)
  have hAi : A.map (MulAut.conj (i:G)).toMonoidHom ≤ I :=
    (map_mono hA).trans_eq (mem_normalizer_iff_map_conj_eq.mp (I.le_normalizer i.property))
  have he : (A.map (MulAut.conj (i:G)).toMonoidHom).subgroupOf I =
      (A.subgroupOf I).map (MulAut.conj i).toMonoidHom := by
    apply map_injective I.subtype_injective
    rw [map_subgroupOf_eq_of_le hAi,map_map]
    have hc : I.subtype.comp (MulAut.conj i).toMonoidHom =
        (MulAut.conj (i:G)).toMonoidHom.comp I.subtype := rfl
    rw [hc,← map_map,map_subgroupOf_eq_of_le hA]
  rw [← pairOriginalAction_map E m hW y _ hAi,he,
    ← pairOriginalAction_map E m hW y A hA,map_map,map_map]
  congr 1
  apply MonoidHom.ext
  intro a
  change pairOriginalAction E m hW y (i*a*i⁻¹) = _
  simp only [map_mul,map_inv,MulAut.conj_apply,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom]

theorem pairAction_normalizer_lifts
    (hroot : actionImage (V := V) (auxiliaryW E) =
      ((RootSubgroup.group 0).map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m))
    (hmove : ⁅V,auxiliaryW E⁆ = E.V₁) :
    (normalizer (Matrix.SpecialLinearGroup.upperUnipotent E.input.field.Carrier : Set _)).comap
      (pairAction E m hW g y hi) ≤
        normalizer ((auxiliaryW E).subgroupOf (oppositeJoin (auxiliaryW E) (y:G)) : Set _) := by
  let I := oppositeJoin (auxiliaryW E) (y:G)
  let f := pairAction E m hW g y hi
  let ρ := pairOriginalAction E m hW y
  let U := (auxiliaryW E).subgroupOf I
  have hIV := oppositeJoin_normalizes_seed E m y.property hW
  intro i hiN
  have hr : (Matrix.SpecialLinearGroup.upperUnipotent E.input.field.Carrier).map
      (pairModelHom E m g) = actionImage (V := V) (auxiliaryW E) := by
    rw [← pairAction_root E m hW g y hi hroot,pairAction_map E m hW g y hi _ le_sup_left]
  have hn : ρ i ∈ normalizer (actionImage (V := V) (auxiliaryW E) : Set (MulAut V)) := by
    rw [← pairAction_spec E m hW g y hi i,← hr]
    exact le_normalizer_map (H := Matrix.SpecialLinearGroup.upperUnipotent E.input.field.Carrier)
      (pairModelHom E m g) (mem_map_of_mem _ hiN)
  have he := originalAction_conjugate E m hW y (auxiliaryW E) le_sup_left i
  have hne : (actionImage (V := V) (auxiliaryW E)).map
      (MulAut.conj (pairOriginalAction E m hW y i)).toMonoidHom =
      actionImage (V := V) (auxiliaryW E) := mem_normalizer_iff_map_conj_eq.mp hn
  rw [hne] at he
  have hVeq : V.map (MulAut.conj (i:G)).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp (hIV i.property)
  have hnorm : (auxiliaryW E).map (MulAut.conj (i:G)).toMonoidHom ≤ normalizer (V : Set G) := by
    have hh := (map_mono (f := (MulAut.conj (i:G)).toMonoidHom)
      (show auxiliaryW E ≤ normalizer (V : Set G) from le_sup_left.trans hIV)).trans
      (V.le_normalizer_map (MulAut.conj (i:G)).toMonoidHom)
    simpa only [hVeq] using hh
  have hv : E.V₁.map (MulAut.conj (i:G)).toMonoidHom = E.V₁ := by
    rw [← hmove,map_commutator,hVeq]
    exact RadicalAction.commutator_eq_of_image_eq _ _ V le_rfl hnorm
      (le_sup_left.trans hIV) he
  have hiG : (i:G) ∈ E.G₁ := mem_normalizer_iff_map_conj_eq.mpr hv
  exact (auxiliaryW E).le_normalizer_comap I.subtype
    (G₁_normalizes_auxiliaryW E hiG)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
