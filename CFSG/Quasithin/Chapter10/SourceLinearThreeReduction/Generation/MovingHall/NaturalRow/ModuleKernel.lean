module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalRow.MinimalParabolic
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.FrattiniSource
public import Theory.GroupTheory.CComponent.SimplePairKernel

/-!
# The actual local natural-module centralizer is a two-group

Thompson movement puts the module centralizer inside the solvable core of
the original minimal parabolic. It therefore misses both nonsolvable
C-components. Their simple SL₂ quotients and Sylow supplement force this
normal kernel to be a two-group. The original central module complement
is retained throughout.

Source: Aschbacher–Smith 10.1.2(3), printed p.742; the argument is the
simple-pair kernel argument of `SourceA5ModuleKernel`, applied over F.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

theorem source_natural_module_centralizer_isTwoGroup
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hnfield : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : ¬ Stellmacher.elementaryAbelianMaxJ ((T.subtype (show (T : Subgroup G) ≤ localJoin T L from
      le_sup_right)) : Subgroup (localJoin T L)) ≤
      centralizer (D.moduleSubgroup.subgroupOf (localJoin T L) : Set (localJoin T L))) :
    IsPGroup 2 (centralizer
      (D.moduleSubgroup.subgroupOf (localJoin T L) : Set (localJoin T L))) := by
  let H := localJoin T L
  let A := L.subgroupOf H
  let U := D.moduleSubgroup.subgroupOf H
  let C := centralizer (U : Set H)
  have hUH : D.moduleSubgroup ≤ H := D.module_le_core.trans (pCoreIn_le 2 H)
  have hLH : L ≤ H := (le_componentOrbit L T).trans le_sup_left
  let : U.Normal := normal_subgroupOf_of_le_normalizer D.join_normalizes_module
  let : C.Normal := inferInstance
  obtain ⟨t,ht,htn,hpair,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  let tH : H := ⟨t,(show (T : Subgroup G) ≤ H from le_sup_right) ht⟩
  let B := A.map (MulAut.conj tH).toMonoidHom
  have hmapA : A.map H.subtype = L := map_subgroupOf_eq_of_le hLH
  have hmapB : B.map H.subtype = L.map (MulAut.conj t).toMonoidHom := by
    rw [show B = A.map (MulAut.conj tH).toMonoidHom from rfl, map_map,
      show H.subtype.comp (MulAut.conj tH).toMonoidHom =
        (MulAut.conj t).toMonoidHom.comp H.subtype from rfl, ←map_map, hmapA]
  have hA : A.IsCComponent := by
    change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
    rw [componentOrbit_sup]
    exact D.maximal.1.1
  have hB : B.IsCComponent := hA.map_equiv (MulAut.conj tH)
  have hne : A ≠ B := by
    intro he
    apply htn
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact hmapB.symm.trans ((congrArg (map H.subtype) he).symm.trans hmapA)
  have hp : A ⊔ B = (localOrbit T L).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,hmapA,hmapB,map_subgroupOf_eq_of_le le_sup_left,hpair]
  let : (A ⊔ B).Normal := hp ▸ normal_subgroupOf_of_le_normalizer
    (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T))
  have hP := source_natural_minimal_parabolic D e n hnfield hF hn
  have hker : C ≤ ChapterB.minimalParabolicCore (T.subtype le_sup_right) hP :=
    ChapterB.RankOneBaumann.reduced_centralizer_le_core _ hP U
      (source_parabolic_module_reduced D) hJ
  let : Group.IsSolvable (ChapterB.minimalParabolicCore (T.subtype le_sup_right) hP) :=
    ChapterB.minimalParabolic_core_solvable _ hP
  let : Group.IsSolvable C := Group.isSolvable_of_isSolvable_injective
    (inclusion_injective hker)
  have hAC : ¬ A ≤ C := fun hc => hA.not_isSolvable
    (Group.isSolvable_of_isSolvable_injective (inclusion_injective hc))
  have hlarge : 4 ≤ Nat.card F := by
    rw [hF]
    exact pow_le_pow_right₀ (by decide : 1 ≤ (2:ℕ)) (by omega : 2 ≤ n)
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hlarge
  let : IsSimpleGroup SL(2,F) := (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).isSimpleGroup
  let a : A ≃* L := subgroupOfEquivOfLe hLH
  let aq := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e
  let : IsSimpleGroup (A ⧸ pCore 2 A) := aq.isSimpleGroup
  let b : A ≃* B := (MulAut.conj tH).subgroupMap A
  let : IsSimpleGroup (B ⧸ pCore 2 B) :=
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm.isSimpleGroup
  apply isTwoGroup_of_normal_avoiding_simpleCore_pair A B
    ((T : Subgroup G).subgroupOf H) C hA hB hne T.isPGroup'.comap_subtype
    ?_ hAC ?_
  · rw [hp, ←subgroupOf_sup (show localOrbit T L ≤ H from le_sup_left)
      (show (T : Subgroup G) ≤ H from le_sup_right), subgroupOf_self]
  · intro hBC
    apply hAC
    intro a ha
    have hc := hBC (mem_map_of_mem (MulAut.conj tH).toMonoidHom ha)
    have hh := (inferInstance : C.Normal).conj_mem _ hc tH⁻¹
    simpa [MulAut.conj_apply,mul_assoc] using hh

end CFSG.Quasithin.Chapter10.MovingHall
