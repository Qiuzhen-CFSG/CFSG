module
public import Theory.GroupTheory.PCoreQuotientSylowOvergroups
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.CoreFlags
public import Theory.GroupTheory.NormalSymmetricThreePairExtension

/-!
# Wreath selection for the endpoint Sylow extension

An actor inducing a graph automorphism exchanges the two endpoint nodes.
If the endpoint and its Sylow extension both had the S₃ × S₃ core quotient,
the equal-order Sylow transport theorem would make every intermediate
Sylow overgroup invariant, including the first endpoint minimal parabolic.
The actual graph action on its flag cuts contradicts that invariance.
The product-or-wreath theorem therefore selects the literal wreath quotient.

All subgroups are full preimages under the given two-core quotient marking;
the proof neither chooses a split extension nor assumes a factor action.
Source: Aschbacher--Smith 15.1.22(3), printed pp.1099--1100.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace BinaryLinear.InvariantNodeActions
open OuterCyclic
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The image of a full preimage under the specified two-core marking. -/
theorem coreFlagMap_lift_image (K : Subgroup G) {m : ℕ}
    (e : (K ⧸ pCore 2 K) ≃* SL(m+1,ZMod 2)) (P : Subgroup (LinearGroup (m+1))) :
    ((EquivariantLift.lift K (coreFlagMap K e) P).subgroupOf K).map (coreFlagMap K e) = P := by
  let q := coreFlagMap K e
  let D := (P.comap q).map K.subtype
  have hD : D.subgroupOf K = P.comap q :=
    comap_map_eq_self_of_injective K.subtype_injective _
  have hi : (D.subgroupOf K).map q = P := by
    rw [hD]
    exact map_comap_eq_self (by rw [q.range_eq_top_of_surjective (coreFlagMap_surjective K e)]; exact le_top)
  have hl := EquivariantLift.lift_map_subgroupOf K q D (map_subtype_le _)
    (by rw [hD]; exact ker_le_comap _ _)
  rw [hi] at hl
  rw [hl]
  exact hi

/-- An outer actor forces the endpoint Sylow extension to have the wreath quotient. -/
theorem endpoint_extension_wreath
    (K A : Subgroup G) (hn : A ≤ normalizer (K : Set G)) (hA : IsPGroup 2 A)
    (Q : Sylow 2 K) (hQ : (Q : Subgroup K).map K.subtype = A ⊓ K)
    {m : ℕ} (hm : m=3 ∨ m=4) (e : (K ⧸ pCore 2 K) ≃* SL(m+1,ZMod 2))
    (b : Basis m) (hb : ((A ⊓ K).subgroupOf K).map (coreFlagMap K e) =
      cutStabilizer b Set.univ)
    (E : Subgroup G)
    (hE : E = EquivariantLift.lift K (coreFlagMap K e)
      (cutStabilizer b {i | i.val=0 ∨ i.val=m-1}ᶜ))
    (hnE : A ≤ normalizer (E : Set G))
    (eE : (E ⧸ pCore 2 E) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (ho : ∃ a : A, coreFlagAction K A hn e a ∉ MulAut.innerSubgroup _) :
    Nonempty (((E ⊔ A : Subgroup G) ⧸ pCore 2 (E ⊔ A : Subgroup G)) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) := by
  rcases NormalSymmetricThreePairExtension.normalized_join E A hnE eE hA with hc | hw
  · obtain ⟨eH⟩ := hc
    exfalso
    let q := coreFlagMap K e
    let α := coreFlagAction K A hn e
    let i : Fin m := ⟨0,by omega⟩
    let P := EquivariantLift.lift K q (minimalParabolic b i)
    have hPK : P ≤ K := EquivariantLift.lift_le K q _
    have hEK : E ≤ K := hE ▸ EquivariantLift.lift_le K q _
    have hPE : P ≤ E := by
      rw [hE]
      apply EquivariantLift.le_lift K q hPK
      rw [coreFlagMap_lift_image]
      apply (cutStabilizer_le_iff b _ _).mpr
      intro j hj he
      change j=i at he
      subst j
      exact hj (Or.inl rfl)
    have hAE : A ⊓ K ≤ E := by
      rw [hE]
      apply EquivariantLift.le_lift K q inf_le_right
      rw [hb]
      exact (cutStabilizer_le_iff b _ _).mpr (Set.subset_univ _)
    have hAP : A ⊓ K ≤ P := by
      apply EquivariantLift.le_lift K q inf_le_right
      rw [hb]
      exact (cutStabilizer_le_iff b _ _).mpr (Set.subset_univ _)
    have hQE : (Q : Subgroup K) ≤ E.subgroupOf K := by
      intro k hk
      exact hAE (hQ ▸ mem_map_of_mem K.subtype hk)
    let t : E.subgroupOf K ≃* E := subgroupOfEquivOfLe hEK
    let R := (Q.subtype hQE).mapSurjective (f := t.toMonoidHom) t.surjective
    have hRA : (R : Subgroup E).map E.subtype ≤ A := by
      rintro x ⟨y,⟨z,hz,rfl⟩,rfl⟩
      exact (hQ ▸ mem_map_of_mem K.subtype hz).1
    have hcard : Nat.card (E ⧸ pCore 2 E) =
        Nat.card ((E ⊔ A : Subgroup G) ⧸ pCore 2 (E ⊔ A : Subgroup G)) :=
      (Nat.card_congr eE.toEquiv).trans (Nat.card_congr eH.toEquiv).symm
    have hnP : A ≤ normalizer (P : Set G) :=
      normalizes_overgroup_of_join_core_quotient_card E A hnE hA R hRA hcard P
        ((inf_le_inf_left A hEK).trans hAP) hPE
    obtain ⟨a,ha⟩ := ho
    have hPn := EquivariantLift.map_invariant K q hn α
      (coreFlagAction_equivariant K A hn e) hnP a
    rw [coreFlagMap_lift_image] at hPn
    have hnAK : A ≤ normalizer ((A ⊓ K) : Set G) :=
      (le_inf A.le_normalizer hn).trans inf_normalizer_le_normalizer_inf
    have hBn := EquivariantLift.map_invariant K q hn α
      (coreFlagAction_equivariant K A hn e) (D := A ⊓ K) hnAK a
    rw [hb] at hBn
    have hc := (outer_invariant_cuts_iff (by omega) (by omega) b (α a) ha hBn {i}ᶜ).mp hPn i
    have hi : i.rev ∈ ({i} : Set (Fin m))ᶜ := by
      change i.rev ≠ i
      intro hh
      have hh' := congrArg Fin.val hh
      simp only [Fin.val_rev] at hh'
      change m - (0+1) = 0 at hh'
      omega
    exact (hc.mp hi) (Set.mem_singleton i)
  · exact hw
end BinaryLinear.InvariantNodeActions
