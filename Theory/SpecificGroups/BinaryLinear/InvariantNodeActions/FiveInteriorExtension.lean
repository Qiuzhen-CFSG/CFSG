module
public import Theory.SpecificGroups.PSL3Two.NormalExtension
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.Adjacent
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.EndpointExtension

/-!
# The degree-five interior graph extension

The interior flag has blocks of dimensions one, three, one. Its diagonal
quotient is the actual GL₃(2) action on the middle block. Adjoining a
normalizing two-group gives that group or its full automorphism group.
A graph actor exchanges the interior nodes. The smaller quotient would
force every Sylow overgroup in the interior to be invariant, contradicting
that exchange. Thus the literal extension has quotient Aut(GL₃(2)).

The argument keeps the supplied two-core marking and lifts full preimages;
no split extension or unidentified model is assumed.
Source: Aschbacher--Smith 15.1.22(3), printed p.1100.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace BinaryLinear.InvariantNodeActions
open OuterCyclic SmallParabolicLevi SmallParabolicLevi.TwoNodes
open FiveFlagGeometry.SylowOvergroups

private def interiorCuts : Set (Fin 4) := {i | i.val = 0 ∨ i.val = 3}
private noncomputable def interiorLabel : Fin 5 → Fin 5 := cutLabel interiorCuts

private theorem interiorLabel_eq : interiorLabel = ![0,1,1,1,2] := by
  funext t
  fin_cases t <;> simp [interiorLabel,interiorCuts,cutLabel,
    show (Finset.univ : Finset (Fin 4)) = {0,1,2,3} from by decide,
    Finset.filter_insert,Finset.filter_singleton]

private theorem middle_card : Fintype.card (Block interiorLabel 1) = 3 := by
  classical
  simp only [Block,Fintype.card_subtype]
  simp [interiorLabel_eq,
    show (Finset.univ : Finset (Fin 5)) = {0,1,2,3,4} from by decide,
    Finset.filter_insert,Finset.filter_singleton]

private theorem other_card (k : Fin 5) (hk : k ≠ 1) :
    Fintype.card (Block interiorLabel k) ≤ 1 := by
  classical
  simp only [Block,Fintype.card_subtype]
  fin_cases k <;> simp_all [interiorLabel_eq,
    show (Finset.univ : Finset (Fin 5)) = {0,1,2,3,4} from by decide,
    Finset.filter_insert,Finset.filter_singleton]

private noncomputable def middleCoordinates :
    BlockSpace interiorLabel 1 ≃ₗ[ZMod 2] Space 3 := by
  classical
  exact LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2)
    ((Fintype.equivFin (Block interiorLabel 1)).trans (finCongr middle_card)).symm

private noncomputable def middleProjection :
    (∀ k : Fin 5, BinaryLinear.GL (BlockSpace interiorLabel k)) →*
      BinaryLinear.GL (BlockSpace interiorLabel 1) := Pi.evalMonoidHom _ 1

private theorem middleProjection_bijective : Function.Bijective middleProjection := by
  constructor
  · intro a b he
    funext k
    by_cases hk : k = 1
    · subst k
      exact he
    exact (linearBlock_eq_one_of_card_le_one _ _ (other_card k hk) (a k)).trans
      (linearBlock_eq_one_of_card_le_one _ _ (other_card k hk) (b k)).symm
  · intro a
    exact ⟨Function.update 1 1 a,by simp [middleProjection]⟩

/-- The interior has blocks of dimensions one, three, one; its actual
core quotient is the linear group on the middle block. -/
theorem five_interior_quotient (b : Basis 4) :
    Nonempty ((cutStabilizer b {i : Fin 4 | i.val=0 ∨ i.val=3} ⧸
      pCore 2 (cutStabilizer b {i : Fin 4 | i.val=0 ∨ i.val=3})) ≃* LinearGroup 3) := by
  let e := (MulEquiv.ofBijective middleProjection middleProjection_bijective).trans
    (linearGroupCongr middleCoordinates)
  exact ⟨(flagDiagonalQuotientEquiv b interiorCuts).trans e⟩

variable {G : Type*} [Group G] [Finite G]

/-- A graph actor forces the literal interior Sylow extension to have the
full automorphism quotient. Its exchange of the two interior nodes rules
out equality of the interior and extension core-quotient orders. -/
theorem five_interior_extension_aut
    (K A : Subgroup G) (hn : A ≤ normalizer (K : Set G)) (hA : IsPGroup 2 A)
    (Q : Sylow 2 K) (hQ : (Q : Subgroup K).map K.subtype = A ⊓ K)
    (e : (K ⧸ pCore 2 K) ≃* SL(4+1,ZMod 2))
    (b : Basis 4) (hb : ((A ⊓ K).subgroupOf K).map (coreFlagMap K e) =
      cutStabilizer b Set.univ)
    (C : Subgroup G)
    (hC : C = EquivariantLift.lift K (coreFlagMap K e)
      (cutStabilizer b {i : Fin 4 | i.val=0 ∨ i.val=3}))
    (hnC : A ≤ normalizer (C : Set G))
    (eC : (C ⧸ pCore 2 C) ≃* LinearGroup 3)
    (ho : ∃ a : A, coreFlagAction K A hn e a ∉ MulAut.innerSubgroup _) :
    Nonempty (((C ⊔ A : Subgroup G) ⧸ pCore 2 (C ⊔ A : Subgroup G)) ≃*
      MulAut (LinearGroup 3)) := by
  rcases NormalThreeExtension.normalized_join C A hnC eC hA with hc | ha
  · obtain ⟨eH⟩ := hc
    exfalso
    let q := coreFlagMap K e
    let α := coreFlagAction K A hn e
    let i : Fin 4 := 1
    let P := EquivariantLift.lift K q (minimalParabolic b i)
    have hPK : P ≤ K := EquivariantLift.lift_le K q _
    have hCK : C ≤ K := hC ▸ EquivariantLift.lift_le K q _
    have hPC : P ≤ C := by
      rw [hC]
      apply EquivariantLift.le_lift K q hPK
      rw [coreFlagMap_lift_image]
      apply (cutStabilizer_le_iff b _ _).mpr
      intro j hj he
      change j=i at he
      subst j
      rcases hj with hj | hj <;> norm_num [i] at hj
    have hAC : A ⊓ K ≤ C := by
      rw [hC]
      apply EquivariantLift.le_lift K q inf_le_right
      rw [hb]
      exact (cutStabilizer_le_iff b _ _).mpr (Set.subset_univ _)
    have hAP : A ⊓ K ≤ P := by
      apply EquivariantLift.le_lift K q inf_le_right
      rw [hb]
      exact (cutStabilizer_le_iff b _ _).mpr (Set.subset_univ _)
    have hQC : (Q : Subgroup K) ≤ C.subgroupOf K := by
      intro k hk
      exact hAC (hQ ▸ mem_map_of_mem K.subtype hk)
    let t : C.subgroupOf K ≃* C := subgroupOfEquivOfLe hCK
    let R := (Q.subtype hQC).mapSurjective (f := t.toMonoidHom) t.surjective
    have hRA : (R : Subgroup C).map C.subtype ≤ A := by
      rintro x ⟨y,⟨z,hz,rfl⟩,rfl⟩
      exact (hQ ▸ mem_map_of_mem K.subtype hz).1
    have hcard : Nat.card (C ⧸ pCore 2 C) =
        Nat.card ((C ⊔ A : Subgroup G) ⧸ pCore 2 (C ⊔ A : Subgroup G)) :=
      (Nat.card_congr eC.toEquiv).trans (Nat.card_congr eH.toEquiv).symm
    have hnP : A ≤ normalizer (P : Set G) :=
      normalizes_overgroup_of_join_core_quotient_card C A hnC hA R hRA hcard P
        ((inf_le_inf_left A hCK).trans hAP) hPC
    obtain ⟨a,ha⟩ := ho
    have hPn := EquivariantLift.map_invariant K q hn α
      (coreFlagAction_equivariant K A hn e) hnP a
    rw [coreFlagMap_lift_image] at hPn
    have hnAK : A ≤ normalizer ((A ⊓ K) : Set G) :=
      (le_inf A.le_normalizer hn).trans inf_normalizer_le_normalizer_inf
    have hBn := EquivariantLift.map_invariant K q hn α
      (coreFlagAction_equivariant K A hn e) (D := A ⊓ K) hnAK a
    rw [hb] at hBn
    have hc := (outer_invariant_cuts_iff (by decide) (by decide) b (α a) ha hBn {i}ᶜ).mp hPn i
    have hi : i.rev ∈ ({i} : Set (Fin 4))ᶜ := by decide
    exact (hc.mp hi) (Set.mem_singleton i)
  · exact ha
end BinaryLinear.InvariantNodeActions
