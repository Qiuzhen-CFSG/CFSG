module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.ProfileActors
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.SimpleCoordinates

/-!
# Pinning an actual linear root actor to its canonical simple root

The faithful panel marking and root-factorization theorem show that the
canonical simple root has the order of a defining-characteristic Sylow
of the actual full SL2 actor. It is a two-group, hence is that full Sylow.
Sylow conjugacy adjusts the given actor isomorphism by an explicit inner
conjugation. The resulting embedding has the full root-generated actor
as range and carries the upper-unipotent matrices onto the SAME simple
root. Its equation retains the supplied full-actor marking and conjugator.

There is no perfectness hypothesis, and the field-two case is included.
The CFSG LinearPlacement application obtains this actor from the original
Chapter 11 quotient map and supplies the placement to FourApplication;
the separate equivariant tensor realization is not constructed here.
Source: Fong--Seitz I (5C), (6A)(b), pp.26,37--38, and the actual
upper-root actor used in II (8B), pp.201--202.
-/

public noncomputable section
open Subgroup
open Matrix (SpecialLinearGroup)
open scoped MatrixGroups Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
private theorem sylow_map_card {A B : Type*} [Group A] [Group B] [Finite A]
    (μ : A ≃* B) (T : Sylow 2 A) :
    Nat.card (T.mapSurjective (f := μ.toMonoidHom) μ.surjective) = Nat.card T := by
  exact (congrArg (fun V : Subgroup B => Nat.card V)
    (Sylow.coe_mapSurjective (f := μ.toMonoidHom) μ.surjective T)).trans
      (card_map_of_injective μ.injective)

private theorem linearSylow_card {F : Type*} [Field F] [Finite F] [CharP F 2]
    (T : Sylow 2 SL(2,F)) : Nat.card T = Nat.card F := by
  calc
    Nat.card T = Nat.card (Multiplicative F) :=
      Nat.card_congr (SpecialLinearGroup.sylowEquivAdditive F 2 T).symm.toEquiv
    _ = Nat.card F := Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F)

variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The canonical simple root is a full Sylow of the actual linear actor. -/
theorem simpleRoot_sylow_of_linear (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : rankOne Q split i ≃* SL(2,F)) :
    ∃ T : Sylow 2 (rankOne Q split i),
      (T : Subgroup (rankOne Q split i)) = (simpleRoot Q split i).subgroupOf (rankOne Q split i) := by
  let A := (simpleRoot Q split i).subgroupOf (rankOne Q split i)
  have hA : IsPGroup 2 A :=
    (split.isTwo.to_le (simpleRoot_le Q split i)).comap_subtype
  obtain ⟨T,hT⟩ := hA.exists_le_sylow
  let ν := (localGroupEquivOfCenterless Q split i hV μ
    Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot).trans
      Atlas.RankOneFieldAutomorphisms.slEquivPSL
  have hcA : Nat.card A = Nat.card F :=
    (Nat.card_congr (subgroupOfEquivOfLe
      (show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left)).toEquiv).trans
      (GTwoSource.simpleRoot_card Q split i hV ν)
  let T' : Sylow 2 SL(2,F) := T.mapSurjective (f := μ.toMonoidHom) μ.surjective
  have hcT' : Nat.card T' = Nat.card F := linearSylow_card T'
  have hcTmap : Nat.card T' = Nat.card T :=
    sylow_map_card μ T
  have hcT : Nat.card T = Nat.card F := hcTmap.symm.trans hcT'
  exact ⟨T,(eq_of_le_of_card_ge hT (by rw [hcT,hcA])).symm⟩

/-- An inner change of the actual linear marking pins its upper Sylow to
this canonical simple root, including the nonperfect field-two case. -/
theorem exists_linear_root_embedding (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : rankOne Q split i ≃* SL(2,F)) :
    ∃ g : SL(2,F), ∃ l : SL(2,F) →* (X ⧸ Q.D),
      Function.Injective l ∧ l.range = rankOne Q split i ∧
      (l.comp (SpecialLinearGroup.upperUnipotentHom F)).range = simpleRoot Q split i ∧
      ∀ a, l a = ((μ.symm ((MulAut.conj g) a) : rankOne Q split i) : X ⧸ Q.D) := by
  obtain ⟨T,hT⟩ := simpleRoot_sylow_of_linear Q split i hV μ
  let T' : Sylow 2 SL(2,F) := T.mapSurjective (f := μ.toMonoidHom) μ.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(2,F) (SpecialLinearGroup.upperUnipotentSylow F 2) T'
  let θ := (MulAut.conj g).trans μ.symm
  let l : SL(2,F) →* X ⧸ Q.D := (rankOne Q split i).subtype.comp θ.toMonoidHom
  have hroot : (SpecialLinearGroup.upperUnipotent F).map (MulAut.conj g).toMonoidHom =
      ((simpleRoot Q split i).subgroupOf (rankOne Q split i)).map μ.toMonoidHom := by
    have hh := congrArg (fun V : Sylow 2 SL(2,F) => (V : Subgroup SL(2,F))) hg
    change (SpecialLinearGroup.upperUnipotent F).map (MulAut.conj g).toMonoidHom =
      (T : Subgroup _).map μ.toMonoidHom at hh
    rwa [hT] at hh
  refine ⟨g,l,Subtype.val_injective.comp θ.injective,?_,?_,fun _ => rfl⟩
  · change ((rankOne Q split i).subtype.comp θ.toMonoidHom).range = _
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr θ.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  · have hinv : μ.symm.toMonoidHom.comp μ.toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      exact μ.symm_apply_apply x
    calc
      (l.comp (SpecialLinearGroup.upperUnipotentHom F)).range =
          (((SpecialLinearGroup.upperUnipotent F).map (MulAut.conj g).toMonoidHom).map
            μ.symm.toMonoidHom).map (rankOne Q split i).subtype := by
        rw [MonoidHom.range_comp,map_map,map_map]
        rfl
      _ = ((((simpleRoot Q split i).subgroupOf (rankOne Q split i)).map μ.toMonoidHom).map
            μ.symm.toMonoidHom).map (rankOne Q split i).subtype := by rw [hroot]
      _ = simpleRoot Q split i := by
        rw [map_map _ μ.symm.toMonoidHom μ.toMonoidHom,hinv,map_id,
          map_subgroupOf_eq_of_le (show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left)]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
