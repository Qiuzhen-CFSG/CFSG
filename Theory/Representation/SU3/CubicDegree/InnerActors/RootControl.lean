module

public import Theory.SpecificGroups.SU3.SylowOmega
public import Theory.GroupTheory.CentralCoprimeLiftUnique
public import Theory.GroupTheory.EmbeddedCenterMap
public import Theory.Representation.SU3.CubicDegree.InnerActors.RootGeometry

/-!
# Root control in the actual special unitary group

Every elementary two-subgroup of SU₃(q) lies in the embedded center of a
Sylow two-subgroup, which has order q. The projective torus acts transitively
on the nonidentity elements of the standard root center. Sylow conjugacy
therefore makes every projective Sylow center irreducible under its normalizer.

The scalar projection SU₃ → PSU₃ identifies Sylow groups and their centers.
Uniqueness of involution lifts through its central kernel of exponent three
lifts normalizers as well, retaining the nontrivial scalar center for odd s.
Finally an actual Hermitian basis change removes the standard-form assumption.
There are no representation hypotheses, and the endpoint s = 2 is included.

Source: Huppert II.10.12; the root geometry used with Guralnick--Malle,
Classification of 2F-modules II, Lemma 2.1, and Aschbacher--Smith K.3.3,
printed p.456, under the hypotheses on p.451.
-/

open Subgroup
namespace Representation.SU3.CubicDegree.InnerActors

private theorem invariant_pullback {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (U : Subgroup G)
    (hi : ∀ B ≤ U.map e.toMonoidHom, B ≠ ⊥ →
      normalizer (U.map e.toMonoidHom : Set H) ≤ normalizer (B : Set H) →
        B = U.map e.toMonoidHom) :
    ∀ B ≤ U, B ≠ ⊥ → normalizer (U : Set G) ≤ normalizer (B : Set G) → B = U := by
  intro B hB hne hn
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  apply hi _ (map_mono hB)
  · intro he
    apply hne
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [← Subgroup.map_bot (e.toMonoidHom)] at he
    exact he
  · rw [← map_equiv_normalizer_eq, ← map_equiv_normalizer_eq]
    exact map_mono hn

private theorem normalizer_lift {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hz : f.ker ≤ center G) (hk : IsPGroup 3 f.ker)
    (U : Subgroup G) [IsElementaryAbelian 2 U] (g : G)
    (hg : f g ∈ normalizer (U.map f : Set H)) : g ∈ normalizer (U : Set G) := by
  have hc (t : G) (ht : f t ∈ normalizer (U.map f : Set H))
      (x : G) (hx : x ∈ U) : t * x * t⁻¹ ∈ U := by
    have hm := (mem_normalizer_iff.mp ht (f x)).mp (mem_map_of_mem f hx)
    rw [← map_inv, ← map_mul, ← map_mul] at hm
    obtain ⟨y, hy, he⟩ := hm
    have heq : y = t * x * t⁻¹ :=
      f.eq_of_map_eq_of_pow_eq_one_of_central_pgroup_ker hz hk (by decide : Nat.Coprime 3 2) he
        (elemPow_eq_one_of_isElementaryAbelian y hy)
        (by simpa only [map_pow, map_one, MulAut.conj_apply] using
          congrArg (MulAut.conj t) (elemPow_eq_one_of_isElementaryAbelian x hx))
    exact heq ▸ hy
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · exact hc g hg x
  · intro hx
    have hh := hc g⁻¹ (by simpa only [map_inv] using
      (normalizer (U.map f : Set H)).inv_mem hg) _ hx
    simpa only [inv_inv, inv_mul_cancel_left, mul_inv_cancel_right,
      mul_assoc, inv_mul_cancel, mul_one] using hh

private theorem invariant_central_lift {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f)
    (hz : f.ker ≤ center G) (hk : IsPGroup 3 f.ker)
    (U : Subgroup G) [IsElementaryAbelian 2 U]
    (hi : ∀ D ≤ U.map f, D ≠ ⊥ →
      normalizer (U.map f : Set H) ≤ normalizer (D : Set H) → D = U.map f) :
    ∀ B ≤ U, B ≠ ⊥ → normalizer (U : Set G) ≤ normalizer (B : Set G) → B = U := by
  have hinj {x y : G} (hx : x ∈ U) (hy : y ∈ U) (he : f x = f y) : x = y :=
    f.eq_of_map_eq_of_pow_eq_one_of_central_pgroup_ker hz hk (by decide : Nat.Coprime 3 2) he
      (elemPow_eq_one_of_isElementaryAbelian x hx)
      (elemPow_eq_one_of_isElementaryAbelian y hy)
  intro B hB hne hn
  have he : B.map f = U.map f := by
    apply hi _ (map_mono hB)
    · intro hbot
      apply hne
      apply bot_unique
      intro x hx
      have hfx : f x = f 1 := by
        simpa only [hbot, mem_bot, map_one] using mem_map_of_mem f hx
      exact (mem_bot).mpr (hinj (hB hx) U.one_mem hfx)
    · intro y hy
      obtain ⟨g, rfl⟩ := hf y
      exact le_normalizer_map f
        (mem_map_of_mem f (hn (normalizer_lift f hz hk U g hy)))
  apply le_antisymm hB
  intro x hx
  have hm : f x ∈ B.map f := by
    rw [he]
    exact mem_map_of_mem f hx
  obtain ⟨y, hy, hyx⟩ := hm
  exact hinj (hB hy) hx hyx ▸ hy

open BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm
open BorelTorus BorelTorus.EvenCenterAction

variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
  {s : ℕ} (hs : 2 ≤ s) (hcard : Nat.card F = (2 ^ s) ^ 2)
  (hfixed : Nat.card {x : F // J.conj x = x} = 2 ^ s)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

private instance : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

include hs hcard hfixed hJ in
private theorem projective_center_irreducible [CharP F 2]
    (Q : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∀ B ≤ sylowCenter Q, B ≠ ⊥ →
      normalizer (sylowCenter Q : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤
        normalizer (B : Set (ProjectiveSpecialUnitaryMatrixGroup J)) → B = sylowCenter Q := by
  let R := EvenTwoRank.rootSylow J hJ (by omega) hcard hfixed
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) Q R
  have hm : (Q : Subgroup _).map (MulAut.conj g).toMonoidHom = (R : Subgroup _) :=
    congrArg Sylow.toSubgroup hg
  have hcenter : (sylowCenter Q).map (MulAut.conj g).toMonoidHom = centralImage J hJ := by
    rw [sylowCenter, map_embeddedCenter _ _ (MulAut.conj g).injective, hm]
    exact NormalizedRootCentralizers.rootSylow_center J hs hcard hfixed hJ
  apply invariant_pullback (MulAut.conj g)
  rw [hcenter]
  intro B hB hne hn
  exact (central_irreducible J hJ hcard hfixed B hB
    ((torus_normalizes J hJ).trans hn)).resolve_left hne

include hs hcard hfixed hJ in
private theorem special_center_irreducible [CharP F 2]
    (P : Sylow 2 J.specialSubgroup) :
    ∀ B ≤ sylowCenter P, B ≠ ⊥ →
      normalizer (sylowCenter P : Set J.specialSubgroup) ≤
        normalizer (B : Set J.specialSubgroup) → B = sylowCenter P := by
  let Q := P.mapSurjective J.specialToProjective_surjective
  have hw := SylowOmega.special_sylow_omega J hs hcard hfixed hJ P
  have hq := SylowOmega.projective_sylow_omega J hs hcard hfixed hJ Q
  have hp : omegaOneAmbient (P : Subgroup J.specialSubgroup) = sylowCenter P := hw.1
  have hq' : omegaOneAmbient (Q : Subgroup _) = sylowCenter Q := hq.1
  have hmap : (sylowCenter P).map J.specialToProjective = sylowCenter Q := by
    rw [← hp, ← hq']
    exact SylowOmega.special_sylow_omega_map J P
  let : IsElementaryAbelian 2 (sylowCenter P) := by
    rw [← hp]
    exact hw.2.1
  apply invariant_central_lift J.specialToProjective J.specialToProjective_surjective
    J.specialToProjective_ker_le_center
    (fun x => ⟨1, by simpa using J.specialToProjective_ker_cube x⟩)
  rw [hmap]
  exact projective_center_irreducible J hs hcard hfixed hJ Q

include hs hcard hfixed in
/-- Root control for arbitrary Hermitian forms, expressed using the two exact
field cardinalities. -/
public theorem root_control_of_fixed_card : RootControl J.specialSubgroup s := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := s * 2)
    (by simpa only [Nat.card_eq_fintype_card, pow_mul] using hcard)
  let J₀ := OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  obtain ⟨C, hC⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_standard_basis
    J (2 ^ s) hcard hfixed
  let e := OddPrimeSylow.NormalizedOuter.FormTransport.specialEquiv J C hC
  intro A hA
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨P, hAP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  have hw := SylowOmega.omega_of_special_equiv J₀ hs hcard hfixed rfl e P
  have hU : omegaOneAmbient (P : Subgroup J.specialSubgroup) = sylowCenter P := hw.1
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [← hU, ← omegaOneAmbient_eq_self A]
    exact omegaOneAmbient_mono hAP
  · rw [← hU]
    exact hw.2.2
  · let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
    apply invariant_pullback e
    have he : (sylowCenter P).map e.toMonoidHom = sylowCenter Q := by
      rw [sylowCenter]
      exact map_embeddedCenter (P : Subgroup _) e.toMonoidHom e.injective
    rw [he]
    exact special_center_irreducible J₀ hs hcard hfixed rfl Q

include hs hcard in
/-- Root control for SU₃(2^s), with the prescribed quadratic Frobenius and
without a restriction on the Gram matrix or the scalar center. -/
public theorem root_control (hconj : ∀ x, J.conj x = x ^ (2 ^ s)) :
    RootControl J.specialSubgroup s :=
  root_control_of_fixed_card J hs hcard
    (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 s (by omega) hcard hconj)

end Representation.SU3.CubicDegree.InnerActors
