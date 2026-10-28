module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualLinearActor
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.G2CartanExclusion
public import Theory.SpecificGroups.G2.SolvableSylowNormalizer

/-!
# Cartan centralization from a marked G₂ local pair

The literal residual action map transports both local A₅ images to the
same full Sylow subgroup. The G₂ order makes both images proper. A nonzero
natural fixed vector selects the long local, while distinctness selects
the short local. Solvability of the original cubic--Sylow join puts its
image in the Sylow normalizer, discharging the Borel premise of the
concrete cubic Cartan calculation. Its two-group kernel reflects the result
back to the original section centralizer.

The original tensor application is in GenerationTwoCartanRows.
Source: Aschbacher--Smith B.4.6(14) and 9.3.9, printed pp.88,734.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceOldResidualActorPair
open ChapterA.Section03 Chapter4 Atlas.G2 Atlas.G2.LieParabolicSetup
variable {X Y F : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
  [Field F] [Finite F] [CharP F 2]

/-- A fixed natural vector identifies the original long local image. The
solvable Cartan--Sylow join supplies its literal Sylow normalization. -/
theorem g2_factor_centralizes
    (hF : Nat.card F = 4) (q : X →* Y) (J C B E : Subgroup X)
    (hCJ : C ≤ J) (hBJ : B ≤ J) (hEJ : E ≤ J)
    (a : J.map q ≃* Model F) (R : Sylow 2 J)
    (hC : (C.map q).subgroupOf (J.map q) ∈
      localCComponents (R.mapSurjective (q.subgroupMap_surjective J)))
    (hB : (B.map q).subgroupOf (J.map q) ∈
      localCComponents (R.mapSurjective (q.subgroupMap_surjective J)))
    (eC : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hkB : IsPGroup 2 (q.subgroupMap B).ker) (hne : C.map q ≠ B.map q)
    (hEC : E ≤ C) (hEB : E ≤ normalizer (B : Set X))
    (h3 : ∀ x ∈ E, x ^ 3 = 1)
    (hsol : Group.IsSolvable (E.subgroupOf J ⊔ (R : Subgroup J) : Subgroup J))
    (hR : (R : Subgroup J).map (a.toMonoidHom.comp (q.subgroupMap J)) = unipotent)
    (v : Natural.Space F) (hv : v ≠ 0)
    (hU : ∀ u ∈ unipotent (K := F), Natural.action F u v = v)
    (hfix : ∀ b ∈ (B.subgroupOf J).map (a.toMonoidHom.comp (q.subgroupMap J)),
      Natural.action F b v = v) : E ≤ sectionCentralizer B := by
  let f := a.toMonoidHom.comp (q.subgroupMap J)
  have h7 : 7 ∣ Nat.card (Model F) := by rw [Atlas.G2.card_Model,hF]; norm_num
  have hS : (R.mapSurjective (q.subgroupMap_surjective J)).mapSurjective
      (f := a.toMonoidHom) a.surjective = sylow (F := F) := by
    apply Sylow.ext
    change ((R : Subgroup J).map (q.subgroupMap J)).map a.toMonoidHom = unipotent
    rw [map_map]
    exact hR
  have hClocal : (C.subgroupOf J).map f ∈ localCComponents (sylow (F := F)) := by
    rw [←hS]
    exact marked_restriction_local q J C hCJ a R hC
  have hBlocal : (B.subgroupOf J).map f ∈ localCComponents (sylow (F := F)) := by
    rw [←hS]
    exact marked_restriction_local q J B hBJ a R hB
  have hEN : (E.subgroupOf J).map f ≤ normalizer (unipotent (K := F) : Set (Model F)) := by
    let : Group.IsSolvable (E.subgroupOf J ⊔ (R : Subgroup J) : Subgroup J) := hsol
    have hs : Group.IsSolvable ((E.subgroupOf J).map f ⊔ unipotent : Subgroup (Model F)) := by
      rw [←hR,←Subgroup.map_sup]
      exact Group.isSolvable_of_surjective (f.subgroupMap_surjective _)
    exact le_sup_left.trans (Atlas.G2.solvable_sylow_overgroup_normalizes
      (by omega : 2 < Nat.card F) (sylow (F := F)) _ le_sup_right hs)
  exact source_tensor_g2_original_factor_of_fixed_local_pair hF J B C E hBJ hEJ f
    hBlocal (marked_restriction_proper q J B hBJ a h7 eB)
    hClocal (marked_restriction_proper q J C hCJ a h7 eC)
    (marked_restriction_distinct q J C B hCJ hBJ a hne) v hv hU hfix
    hEC hEN hEB (marked_restriction_kernel q J B hBJ a hkB) h3

end CFSG.Quasithin.Chapter10.SourceOldResidualActorPair
