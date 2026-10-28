module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.DegreeDivisibility.ModelTransitivity.Transport
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryGeometry.TwoPointRoots.StandardRoots.Coordinates

/-!
# Root fusion in the original special and projective unitary models

The fixed-field torus conjugates any nonzero central root to any other.
These central roots are exactly the standard Sylow omega. Projection
transports their fusion to PSU₃. The special root is Sylow because the
scalar projection is injective on two-subgroups and identifies its image
with the known projective root Sylow. Sylow conjugacy then gives the result
for every prescribed Sylow and every actual model equivalence.

Source: GLS4, Chapter 4, Lemma 3.2(b,c), used in Chapter 2, 16.4(c).
-/

noncomputable section
namespace BenderSuzuki.ZD.Source16ModelTransitivity
open Subgroup _root_.BenderSuzuki.MatrixGroups _root_.BenderSuzuki.External
open HermitianForm HermitianForm.BorelTorus HermitianForm.BorelTorus.EvenCenterAction
open RankOneModelGeometry RankOneModelGeometry.UnitaryStandardRoots
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

private instance : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

private theorem binary_charTwo {n : ℕ} (hcard : Nat.card E = (2 ^ n) ^ 2) : CharP E 2 := by
  let := Fintype.ofFinite E
  apply charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
  simpa only [Nat.card_eq_fintype_card,pow_mul] using hcard

public theorem unitary_special_standard_fusion [CharP E 2] :
    ∀ z ∈ omegaOneAmbient (specialRoot J hJ), z ≠ 1 →
      ∀ x ∈ omegaOneAmbient (specialRoot J hJ), x ≠ 1 → IsConj z x := by
  rw [special_omega]
  rintro _ ⟨b,rfl⟩ hb _ ⟨c,rfl⟩ hc
  have hb0 : b.toAdd ≠ 0 := by
    intro he
    have hb1 : b = 1 := Multiplicative.toAdd.injective he
    exact hb (by rw [hb1,map_one])
  have hc0 : c.toAdd ≠ 0 := by
    intro he
    have hc1 : c = 1 := Multiplicative.toAdd.injective he
    exact hc (by rw [hc1,map_one])
  obtain ⟨a,ha⟩ := fixedTorus_transitive J hJ b.toAdd c.toAdd hb0 hc0
  exact isConj_iff.mpr ⟨fixedTorus J hJ a,ha⟩

public theorem unitary_projective_standard_fusion [CharP E 2] :
    ∀ z ∈ omegaOneAmbient (projectiveRoot J hJ), z ≠ 1 →
      ∀ x ∈ omegaOneAmbient (projectiveRoot J hJ), x ≠ 1 → IsConj z x := by
  have he : (omegaOneAmbient (specialRoot J hJ)).map J.specialToProjective =
      omegaOneAmbient (projectiveRoot J hJ) := by
    rw [special_omega,projective_omega,← MonoidHom.range_comp]
    apply congrArg MonoidHom.range
    apply MonoidHom.ext
    intro b
    exact projection_central J hJ b
  rw [← he]
  exact fusion_map _ (unitary_special_standard_fusion J hJ) J.specialToProjective

public theorem unitary_special_root_isSylow {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n) :
    ∃ S : Sylow 2 J.specialSubgroup, (S : Subgroup _) = specialRoot J hJ := by
  let Q := EvenTwoRank.rootSylow J hJ (by omega : 0 < n) hcard hfixed
  let e := (MonoidHom.ofInjective (specialRoot_injective J hJ)).symm.trans
    (MonoidHom.ofInjective (EvenInner.root_injective J hJ))
  have hp : IsPGroup 2 (specialRoot J hJ) := Q.isPGroup'.of_equiv e.symm
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  have hmap : (specialRoot J hJ).map J.specialToProjective = projectiveRoot J hJ := by
    rw [specialRoot,projectiveRoot,← MonoidHom.range_comp]
    apply congrArg MonoidHom.range
    apply MonoidHom.ext
    intro x
    change J.specialToProjective (hermitianUnipotentSU J hJ x) = hermitianUnipotentPSU J hJ x
    apply Subtype.ext
    rw [J.specialToProjective_apply_val]
    rfl
  have hm : (S.mapSurjective J.specialToProjective_surjective :
      Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = Q := by
    apply Q.is_maximal' (S.isPGroup'.map J.specialToProjective)
    change projectiveRoot J hJ ≤ _
    rw [← hmap]
    exact map_mono hS
  refine ⟨S,(eq_of_le_of_card_ge hS ?_).symm⟩
  have hSc := Nat.card_congr (SylowOmega.specialSylowEquivProjective J S).toEquiv
  change Nat.card S = Nat.card (S.map J.specialToProjective) at hSc
  change S.map J.specialToProjective = (Q : Subgroup _) at hm
  rw [hm] at hSc
  exact (hSc.trans (Nat.card_congr e.toEquiv).symm).le

variable {G : Type*} [Group G] [Finite G]
include hJ

public theorem unitary_special_omega_fusion {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (e : G ≃* J.specialSubgroup) (P : Sylow 2 G) :
    ∀ z ∈ omegaOneAmbient (P : Subgroup G), z ≠ 1 →
      ∀ x ∈ omegaOneAmbient (P : Subgroup G), x ≠ 1 → IsConj z x := by
  let : CharP E 2 := binary_charTwo hcard
  obtain ⟨S,hS⟩ := unitary_special_root_isSylow J hJ hn hcard hfixed
  apply sylow_omega_fusion_of_equiv e S _ P
  rw [hS]
  exact unitary_special_standard_fusion J hJ

public theorem unitary_projective_omega_fusion {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (e : G ≃* ProjectiveSpecialUnitaryMatrixGroup J) (P : Sylow 2 G) :
    ∀ z ∈ omegaOneAmbient (P : Subgroup G), z ≠ 1 →
      ∀ x ∈ omegaOneAmbient (P : Subgroup G), x ≠ 1 → IsConj z x := by
  let : CharP E 2 := binary_charTwo hcard
  apply sylow_omega_fusion_of_equiv e
    (EvenTwoRank.rootSylow J hJ (by omega : 0 < n) hcard hfixed) _ P
  exact unitary_projective_standard_fusion J hJ

end BenderSuzuki.ZD.Source16ModelTransitivity
