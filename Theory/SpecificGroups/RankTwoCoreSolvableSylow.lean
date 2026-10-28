module
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.SolvableOvergroups
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableOvergroupGeometry
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableRootOrbit
public import Theory.GroupTheory.SylowNormalizerCentralQuotient
public import Theory.AtlasPort.LinearGroups.G2.SolvableSylowPlacement
public import Theory.AtlasPort.LinearGroups.G2.Simplicity
public import Theory.AtlasPort.LinearGroups.G2.SylowNormalizer
public import Theory.PGroupCore

/-!
# Solvable Sylow overgroups through rank-two model quotients

For SL₃, PSL₃, Sp₄ and G₂ over a field of order 2ⁿ with n≥2, a solvable
overgroup of a Sylow two-subgroup normalizes that Sylow. The matrix and
root Borel theorems establish this in the models; the scalar quotient
handles SL₃. The full inverse image of a Sylow through a two-core quotient
is the original Sylow, so the same normalizer assertion lifts to every
finite group with one of these actual quotients.

Source application: Aschbacher--Smith 14.2.15, printed p.986. The G₂
calculation retains the licensed ATLAS port's attribution through imports.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory
variable {G D : Type*} [Group G] [Finite G] [Group D]

private theorem solvable_overgroup_normalizes_of_twoCore_quotient
    (e : (G ⧸ pCore 2 G) ≃* D)
    (hD : ∀ (P : Sylow 2 D) (B : Subgroup D), Group.IsSolvable B →
      (P : Subgroup D) ≤ B → B ≤ normalizer (P : Set D))
    (P : Sylow 2 G) (B : Subgroup G)
    (hsol : Group.IsSolvable B) (hPB : (P : Subgroup G) ≤ B) :
    B ≤ normalizer (P : Set G) := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let _ := hsol
  have hb := hD (P.mapSurjective hq) (B.map q)
    (Group.isSolvable_of_surjective (q.subgroupMap_surjective B)) (map_mono hPB)
  have hk : q.ker = pCore 2 G := by
    ext x
    change e (QuotientGroup.mk' (pCore 2 G) x) = 1 ↔ _
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hn : (normalizer ((P : Subgroup G).map q : Set D)).comap q =
      normalizer (P : Set G) := by
    rw [comap_normalizer_eq_of_surjective _ hq,comap_map_eq_self
      (show q.ker ≤ (P : Subgroup G) from hk.symm ▸ pCore_isPGroup.le_sylow_of_normal P)]
    rfl
  rw [←hn]
  exact map_le_iff_le_comap.mp hb

variable {F : Type*} [Field F] [Finite F]

theorem solvable_overgroup_normalizes_of_pslThree_twoCore_quotient
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : (G ⧸ pCore 2 G) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (P : Sylow 2 G) (B : Subgroup G)
    (hsol : Group.IsSolvable B) (hPB : (P : Subgroup G) ≤ B) :
    B ≤ normalizer (P : Set G) :=
  solvable_overgroup_normalizes_of_twoCore_quotient e
    (Matrix.PSL3.LinearThree.SolvableOvergroups.solvable_overgroup_le_normalizer_of_two_le F hn hF)
    P B hsol hPB

theorem solvable_overgroup_normalizes_of_slThree_twoCore_quotient
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : (G ⧸ pCore 2 G) ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    (P : Sylow 2 G) (B : Subgroup G)
    (hsol : Group.IsSolvable B) (hPB : (P : Subgroup G) ≤ B) :
    B ≤ normalizer (P : Set G) := by
  apply solvable_overgroup_normalizes_of_twoCore_quotient e _ P B hsol hPB
  intro U A hs hu
  let q := Matrix.PSL3.projection F
  have hq : Function.Surjective q := Matrix.PSL3.projection_surjective F
  let _ := hs
  have hb := Matrix.PSL3.LinearThree.SolvableOvergroups.solvable_overgroup_le_normalizer_of_two_le
    F hn hF (U.mapSurjective hq) (A.map q)
    (Group.isSolvable_of_surjective (q.subgroupMap_surjective A)) (map_mono hu)
  have hk : q.ker ≤ center (Matrix.SpecialLinearGroup (Fin 3) F) := by
    rw [Matrix.PSL3.projection_ker]
  rw [← U.normalizer_comap_of_central_kernel q hq hk]
  exact map_le_iff_le_comap.mp hb

theorem solvable_overgroup_normalizes_of_spFour_twoCore_quotient
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : (G ⧸ pCore 2 G) ≃* Matrix.symplecticGroup (Fin 2) F)
    (P : Sylow 2 G) (B : Subgroup G)
    (hsol : Group.IsSolvable B) (hPB : (P : Subgroup G) ≤ B) :
    B ≤ normalizer (P : Set G) := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hfour : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 2 < 2^2)
      (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn)
  apply solvable_overgroup_normalizes_of_twoCore_quotient e _ P B hsol hPB
  intro U A hs hu
  exact Theory.SpecificGroups.SymplecticFour.solvable_overgroups_of_orthogonal_root_orbits
    hF (by omega) (fun D hs hu =>
      Theory.SpecificGroups.SymplecticFour.solvable_unipotent_point_orbit_orthogonal hfour D hs hu)
    U A hs hu

theorem solvable_overgroup_normalizes_of_gTwo_twoCore_quotient
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : (G ⧸ pCore 2 G) ≃* Atlas.G2.Model F)
    (P : Sylow 2 G) (B : Subgroup G)
    (hsol : Group.IsSolvable B) (hPB : (P : Subgroup G) ≤ B) :
    B ≤ normalizer (P : Set G) := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn)
  apply solvable_overgroup_normalizes_of_twoCore_quotient e _ P B hsol hPB
  intro U A hs hu
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Atlas.G2.Model F) U
    (Atlas.G2.LieParabolicSetup.sylow (F := F))
  let a := MulAut.conj g
  have hU : (U : Subgroup (Atlas.G2.Model F)).map a.toMonoidHom =
      Atlas.G2.unipotent := congrArg Sylow.toSubgroup hg
  let _ := hs
  have hsol : Group.IsSolvable (A.map a.toMonoidHom) :=
    Group.isSolvable_of_surjective (a.toMonoidHom.subgroupMap_surjective A)
  have hUA : Atlas.G2.unipotent ≤ A.map a.toMonoidHom :=
    hU ▸ map_mono hu
  have hN : A.map a.toMonoidHom ≤ normalizer
      ((Atlas.G2.unipotent (K := F) : Subgroup (Atlas.G2.Model F)) : Set (Atlas.G2.Model F)) := by
    rw [Atlas.G2.SylowNormalizer.normalizer_unipotent]
    exact Atlas.G2.SolvableSylowPlacement.le_borel hlarge (A.map a.toMonoidHom) hUA hsol
  rw [← hU, ← map_equiv_normalizer_eq (U : Subgroup (Atlas.G2.Model F)) a] at hN
  exact (map_le_map_iff_of_injective a.injective).mp hN

end Theory.GroupTheory
