module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.Geometry.Model
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.LocalIdentification
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.Flag

/-!
# Selecting the opposite action in the original component

Lift the marked symplectic opposition through the original map L → L/O₂(L).
Conjugation of the original W then gives the opposite long root, so its
join has the concrete SL₂ action and the three point-local generators.
The equations hold for every lift of that opposition. Thus a subsequent
Cartan-compatible choice can change the lift in the actual action kernel.

This establishes the action-image part of selection. Containment of X₁ in
the original join and the Cartan-compatible choice remain with the final
opposite-core assembly; neither is inferred merely from its image.
Source: Aschbacher--Smith, 11.5.7, printed p.783.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeGeometry
open Subgroup Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02

private theorem map_conjugate {A B : Type*} [Group A] [Group B]
    (f : A →* B) (H : Subgroup A) (a : A) :
    (H.map f).map (MulAut.conj (f a)).toMonoidHom =
      (H.map (MulAut.conj a).toMonoidHom).map f := by
  rw [map_map, map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  change f a * f x * (f a)⁻¹ = f (a * x * a⁻¹)
  simp only [map_mul, map_inv]

private theorem conjugate_twice {A : Type*} [Group A]
    (H : Subgroup A) (g b : A) :
    (H.map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj (g * b * g⁻¹)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [map_map, map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  change (g * b * g⁻¹) * (g * x * g⁻¹) * (g * b * g⁻¹)⁻¹ =
    g * (b * x * b⁻¹) * g⁻¹
  group

private theorem opposition_root {F : Type*} [Field F] [CharP F 2] :
    (RootSubgroup.group (F := F) 0).map
      (MulAut.conj TwoConjugate.opposition).toMonoidHom = RootSubgroup.group 1 := by
  apply le_antisymm
  · rintro x ⟨a,ha,rfl⟩
    obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff 0 a).mp ha
    change TwoConjugate.opposition * rootElement 0 t * TwoConjugate.opposition⁻¹ ∈ _
    rw [(TwoConjugate.opposition_central_axes t).1]
    exact (RootSubgroup.mem_group_iff 1 _).mpr ⟨t,rfl⟩
  · intro x hx
    obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff 1 x).mp hx
    exact ⟨rootElement 0 t, (RootSubgroup.mem_group_iff 0 _).mpr ⟨t,rfl⟩,
      (TwoConjugate.opposition_central_axes t).1⟩

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The supplied flag is the actual inner-Sylow flag in the same marking. -/
theorem flag_space_alignment (m : MarkedFlag E) (i : Fin 3) :
    m.flag.space i = LocalGeometry.Sp4.ModelFlag.movedStage
      (LocalGeometry.Sp4.alignment m.action) i.succ :=
  LocalGeometry.Sp4.space_inner_unique m.action i (m.flag.space i)
    (m.flag.dimension i) (inf_le_left.trans (m.flag.invariant i))

include E in
private theorem actionImage_sup (A B : Subgroup G)
    (hA : A ≤ L ⊔ (T : Subgroup G)) (hB : B ≤ L ⊔ (T : Subgroup G)) :
    actionImage (V := V) (A ⊔ B) = actionImage (V := V) A ⊔ actionImage (V := V) B := by
  rw [← largeAction_image E _ (sup_le hA hB), subgroupOf_sup hA hB,
    Subgroup.map_sup, largeAction_image E A hA, largeAction_image E B hB]

/-- Every lift of the marked opposition has the required literal pair image.
This remains valid after changing the lift inside the original two-core. -/
theorem pair_image_of_opposition_lift (m : MarkedFlag E)
    (hW : E.W ≤ E.G₁.pCoreIn 2) (g : Sp E.input.field.Carrier)
    (hroot : actionImage (V := V) (auxiliaryW E) =
      ((RootSubgroup.group 0).map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m))
    (y : L)
    (hy : PointModel.quotientMap m y = g * TwoConjugate.opposition * g⁻¹) :
    actionImage (V := V) (oppositeJoin (auxiliaryW E) (y : G)) =
      (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map
        (FullAction.modelHom m) := by
  have hI := oppositeJoin_le_large E m hW y.property
  have hA : auxiliaryW E ≤ L ⊔ (T : Subgroup G) := le_sup_left.trans hI
  have hB : (auxiliaryW E).map (MulAut.conj (y : G)).toMonoidHom ≤
      L ⊔ (T : Subgroup G) := le_sup_right.trans hI
  change actionImage (V := V) (auxiliaryW E ⊔ _) = _
  rw [actionImage_sup E _ _ hA hB, actionImage_conjugate E m _ hA y.property,
    hy, hroot, map_conjugate, conjugate_twice, opposition_root]
  rw [OppositeLongRootPair.pair, Subgroup.map_sup, Subgroup.map_sup]

/-- The original component supplies a lift of the opposite action. Its pair
has the concrete SL₂ marking, core bound and three actual L₁ generators.
The separate Cartan compatibility assertion is not part of this theorem. -/
theorem exists_opposition_lift (m : MarkedFlag E)
    (hW : E.W ≤ E.G₁.pCoreIn 2) (g : Sp E.input.field.Carrier)
    (hlocal : PointModel.image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom)
    (hroot : actionImage (V := V) (auxiliaryW E) =
      ((RootSubgroup.group 0).map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m)) :
    ∃ y : L,
      PointModel.quotientMap m y = g * TwoConjugate.opposition * g⁻¹ ∧
      actionImage (V := V) (oppositeJoin (auxiliaryW E) (y : G)) =
        (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map
          (FullAction.modelHom m) ∧
      (oppositeJoin (auxiliaryW E) (y : G)).pCoreIn 2 ≤
        (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      ∃ l : Fin 3 → G, (∀ i, l i ∈ E.L₁) ∧
        L ≤ (⨆ i, (oppositeJoin (auxiliaryW E) (y : G)).map
          (MulAut.conj (l i)).toMonoidHom) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hs : Function.Surjective (PointModel.quotientMap m) :=
    m.action.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))
  obtain ⟨y,hy⟩ := hs (g * TwoConjugate.opposition * g⁻¹)
  have hi := pair_image_of_opposition_lift E m hW g hroot y hy
  exact ⟨y, hy, hi, marked_pair_core_le_large_core E m hW y.property g hi,
    three_conjugates_of_marked_pair E m hW y.property g hlocal hi⟩

/-- The genuine radical root-image output suffices to construct an opposite
action, its aligned flag and its three source conjugators. No marked-pair
image or local-image identification is an additional hypothesis here. -/
theorem exists_marked_opposite_action (m : MarkedFlag E)
    (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hroot : actionImage (V := V) (auxiliaryW E) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype) :
    ∃ (g : Sp E.input.field.Carrier) (y : L),
      (∀ i : Fin 3, m.flag.space i = LocalGeometry.Sp4.ModelFlag.movedStage g i.succ) ∧
      PointModel.image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom ∧
      PointModel.quotientMap m y = g * TwoConjugate.opposition * g⁻¹ ∧
      actionImage (V := V) (oppositeJoin (auxiliaryW E) (y : G)) =
        (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map
          (FullAction.modelHom m) ∧
      (oppositeJoin (auxiliaryW E) (y : G)).pCoreIn 2 ≤
        (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      ∃ l : Fin 3 → G, (∀ i, l i ∈ E.L₁) ∧
        L ≤ (⨆ i, (oppositeJoin (auxiliaryW E) (y : G)).map
          (MulAut.conj (l i)).toMonoidHom) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let g := LocalGeometry.Sp4.alignment m.action
  have hpoint : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap :=
    flag_space_alignment E m 0
  have hlocal := PointModel.local_identification m g hpoint
  have hr := hroot.trans (FullAction.center_eq_marked_root m g hlocal)
  obtain ⟨y,hy,hi,hc,hl⟩ := exists_opposition_lift E m hW g hlocal hr
  exact ⟨g, y, flag_space_alignment E m, hlocal, hy, hi, hc, hl⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeGeometry
