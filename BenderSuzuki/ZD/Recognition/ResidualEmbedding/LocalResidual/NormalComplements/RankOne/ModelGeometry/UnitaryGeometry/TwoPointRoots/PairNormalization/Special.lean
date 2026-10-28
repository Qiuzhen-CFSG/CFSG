module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryGeometry.TwoPointRoots.PairNormalization.Projective
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryGeometry.TwoPointRoots.SpecialCommutators
public import Theory.SpecificGroups.SU3.SylowOmega

/-!
# Lifting the normalized pair to SU₃

The scalar projection has central odd kernel. Its Sylow-normalizer preimages
and its unique involution lifts transport the genuine projective conjugator.
The full special torus is the preimage of the full projective torus.
The kernel-in-torus calculation is extracted from the checked SpecialBorel
proof, without importing the quasithin chapter into this lower layer.

Source: GLS4, Chapter 4, Lemma 3.2(c),(e),(i), and Huppert II.10.12.
-/

open Subgroup BenderSuzuki BenderSuzuki.PFAppendixIII BenderSuzuki.PFchapter1section1
namespace BenderSuzuki.ZD.RankOneModelGeometry.PairNormalization
open _root_.BenderSuzuki.MatrixGroups HermitianForm External
open HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage
variable {E : Type*} [Field E] (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

private theorem projection_root (z : hermitianUnipotentCoord J) :
    J.specialToProjective (hermitianUnipotentSU J hJ z) = hermitianUnipotentPSU J hJ z := by
  apply Subtype.ext
  rw [specialToProjective_apply_val, hermitianUnipotentPSU_val]
  rfl

private theorem projection_torus (k : Eˣ) :
    J.specialToProjective (hermitianTorusSU J hJ k) = hermitianTorusPSU J hJ k := by
  apply Subtype.ext
  rw [specialToProjective_apply_val, hermitianTorusPSU_val]
  rfl

private theorem root_map :
    (BorelTorus.specialRoot J hJ).map J.specialToProjective = BorelTorus.projectiveRoot J hJ := by
  change (hermitianUnipotentSU J hJ).range.map _ = (hermitianUnipotentPSU J hJ).range
  rw [← MonoidHom.range_comp]
  congr 1
  exact MonoidHom.ext (projection_root J hJ)

private theorem torus_map :
    (BorelTorus.specialTorus J hJ).map J.specialToProjective = BorelTorus.projectiveTorus J hJ := by
  change (hermitianTorusSU J hJ).range.map _ = (hermitianTorusPSU J hJ).range
  rw [← MonoidHom.range_comp]
  congr 1
  exact MonoidHom.ext (projection_torus J hJ)

private theorem kernel_le_specialTorus :
    J.specialToProjective.ker ≤ BorelTorus.specialTorus J hJ := by
  intro x hx
  have hxc : x.val ∈ Subgroup.center (GL (Fin 3) E) := by
    apply Matrix.ProjGenLinGroup.mk_eq_one.mp
    simpa only [J.specialToProjective_apply_val, Subgroup.coe_one] using
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hxc
  obtain ⟨k, hk⟩ := hxc
  have hspecial := (J.mem_specialSubgroup_iff (x : GL (Fin 3) E)).mp x.property
  rw [← hk] at hspecial
  have hu := congrArg (fun A : Matrix (Fin 3) (Fin 3) E => A 0 2) hspecial.1
  have hn : J.conj (k : E) * (k : E) = 1 := by
    simpa [hJ, HermitianForm.conjTranspose, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_three] using hu
  have hd := congrArg (fun a : Eˣ => (a : E)) hspecial.2
  have hcube : (k : E) ^ 3 = 1 := by
    simpa [Matrix.GeneralLinearGroup.det, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.det_fin_three, pow_succ, pow_two] using hd
  have h0 : (J.conj (k : E))⁻¹ = (k : E) := by
    apply inv_eq_of_mul_eq_one_right
    exact hn
  have hci : J.conj (k : E) = (k : E)⁻¹ := eq_inv_of_mul_eq_one_left hn
  have h1 : J.conj (k : E) * (k : E)⁻¹ = (k : E) := by
    rw [hci]
    field_simp
    simpa [pow_succ, pow_two] using hcube.symm
  refine ⟨k, ?_⟩
  apply Subtype.ext
  rw [← hk]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change hermitianTorusMatrix J k i j = (Matrix.scalar (Fin 3) (k : E)) i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianTorusMatrix, Matrix.scalar_apply, h0, h1]

private theorem torus_preimage :
    (BorelTorus.projectiveTorus J hJ).comap J.specialToProjective = BorelTorus.specialTorus J hJ := by
  rw [← torus_map, comap_map_eq, sup_eq_left.mpr (kernel_le_specialTorus J hJ)]

private theorem special_weyl_involution : IsInvolution (hermitianWeylSU J hJ) := by
  constructor
  · intro h
    have hh := congrArg (fun x : J.specialSubgroup => x.val.val 0 0) h
    simp [hermitianWeylSU, hermitianWeylGL, hermitianWeylMatrix] at hh
  · apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, hermitianWeylSU, hermitianWeylGL, hermitianWeylMatrix,
        Matrix.mul_apply, Fin.sum_univ_three]

private theorem normalizer_preimage {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (hc : f.ker ≤ center G) (P : Sylow 2 G) :
    (normalizer (P.map f : Set H)).comap f = normalizer (P : Set G) := by
  rw [← P.normalizer_map_surjective f hf, comap_map_eq,
    sup_eq_left.mpr (hc.trans (center_le_normalizer _))]

private theorem sylow_eq_of_map {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (hc : f.ker ≤ center G)
    (P Q : Sylow 2 G) (he : P.map f = Q.map f) : (P : Subgroup G) = Q := by
  have hn : normalizer (P : Set G) = normalizer (Q : Set G) := by
    rw [← normalizer_preimage f hf hc P, ← normalizer_preimage f hf hc Q, he]
  have hle : (P : Subgroup G) ≤ normalizer (Q : Set G) := hn ▸ P.le_normalizer
  have hi := P.isPGroup'.inf_normalizer_sylow Q
  rw [inf_eq_left.mpr hle] at hi
  exact (P.is_maximal' Q.isPGroup' (inf_eq_left.mp hi.symm)).symm

private theorem mem_right_conjugate {G : Type*} [Group G] (B : Subgroup G) (t x : G) :
    x ∈ rightConjugate B t ↔ t * x * t⁻¹ ∈ B := by
  rw [rightConjugate, Subgroup.conjBy, mem_map_equiv]
  simp [MulAut.conj_apply]

private theorem twoPoint_preimage {G H : Type*} [Group G] [Group H]
    (f : G →* H) (B : Subgroup H) (t : G) :
    twoPoint (B.comap f) t = (twoPoint B (f t)).comap f := by
  ext x
  simp only [twoPoint, mem_inf, mem_comap, mem_right_conjugate, map_mul, map_inv]

private theorem map_preimage_conj {G H : Type*} [Group G] [Group H]
    (f : G →* H) (B : Subgroup H) (g : G) :
    (B.comap f).map (MulAut.conj g).toMonoidHom =
      (B.map (MulAut.conj (f g)).toMonoidHom).comap f := by
  ext x
  simp only [mem_map_equiv, mem_comap]
  change f (g⁻¹ * x * g) ∈ B ↔ (f g)⁻¹ * f x * f g ∈ B
  rw [map_mul, map_mul, map_inv]

variable [Finite E]
private instance : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

private theorem special_root_sylow {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n) :
    ∃ S : Sylow 2 J.specialSubgroup, (S : Subgroup _) = BorelTorus.specialRoot J hJ := by
  let Q := EvenTwoRank.rootSylow J hJ (by omega : 0 < n) hcard hfixed
  have hinj : Function.Injective (hermitianUnipotentSU J hJ) := by
    intro x y he
    apply EvenInner.root_injective J hJ
    simpa only [projection_root] using congrArg J.specialToProjective he
  let e := (MonoidHom.ofInjective hinj).symm.trans
    (MonoidHom.ofInjective (EvenInner.root_injective J hJ))
  have hp : IsPGroup 2 (BorelTorus.specialRoot J hJ) := Q.isPGroup'.of_equiv e.symm
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  have hm : (S.mapSurjective J.specialToProjective_surjective :
      Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = Q := by
    apply Q.is_maximal' (S.isPGroup'.map J.specialToProjective)
    change BorelTorus.projectiveRoot J hJ ≤ _
    rw [← root_map]
    exact map_mono hS
  refine ⟨S, (eq_of_le_of_card_ge hS ?_).symm⟩
  have hSc := Nat.card_congr (SylowOmega.specialSylowEquivProjective J S).toEquiv
  change Nat.card S = Nat.card (S.map J.specialToProjective) at hSc
  change S.map J.specialToProjective = (Q : Subgroup _) at hm
  rw [hm] at hSc
  exact (hSc.trans (Nat.card_congr e.toEquiv).symm).le

/-- The projective conjugator lifts to an actual special-unitary conjugator,
with the full special torus as the literal two-point image. -/
public theorem special_pair {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (P : Sylow 2 J.specialSubgroup) (t : J.specialSubgroup) (ht : IsInvolution t)
    (htB : t ∉ normalizer (P : Set J.specialSubgroup)) :
    ∃ g : J.specialSubgroup,
      (P : Subgroup _).map (MulAut.conj g).toMonoidHom = BorelTorus.specialRoot J hJ ∧
      MulAut.conj g t = hermitianWeylSU J hJ ∧
      (twoPoint (normalizer (P : Set J.specialSubgroup)) t).map
        (MulAut.conj g).toMonoidHom = BorelTorus.specialTorus J hJ := by
  let f := J.specialToProjective
  let Q := P.mapSurjective J.specialToProjective_surjective
  have hpre : (normalizer (Q : Set (ProjectiveSpecialUnitaryMatrixGroup J))).comap f =
      normalizer (P : Set J.specialSubgroup) := normalizer_preimage f
        J.specialToProjective_surjective J.specialToProjective_ker_le_center P
  have htq := Theory.GroupTheory.involution_map_of_odd_kernel f J.odd_card_specialToProjective_ker ht
  have htout : f t ∉ normalizer (Q : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    intro hh
    apply htB
    rw [← hpre]
    exact hh
  obtain ⟨a, hP, ht', hD⟩ := projective_pair J hJ hn hcard hfixed Q (f t) htq htout
  obtain ⟨g, hg⟩ := J.specialToProjective_surjective a
  change f g = a at hg
  have hcomm : f.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj a).toMonoidHom.comp f := by
    apply MonoidHom.ext
    intro x
    change f (g * x * g⁻¹) = a * f x * a⁻¹
    simp only [map_mul, map_inv, hg]
  refine ⟨g, ?_, ?_, ?_⟩
  · obtain ⟨S, hS⟩ := special_root_sylow J hJ hn hcard hfixed
    let R := P.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective
    have hm : R.map f = S.map f := by
      change ((P : Subgroup _).map (MulAut.conj g).toMonoidHom).map f = _
      rw [map_map, hcomm, ← map_map, hS, root_map]
      exact hP
    exact (sylow_eq_of_map f J.specialToProjective_surjective
      J.specialToProjective_ker_le_center R S hm).trans hS
  · apply Theory.GroupTheory.involution_eq_of_central_odd_kernel f
      J.odd_card_specialToProjective_ker J.specialToProjective_ker_le_center
      (show IsInvolution (MulAut.conj g t) from ⟨fun he => ht.ne_one
        ((MulAut.conj g).injective (he.trans (map_one _).symm)), by
          rw [← map_pow, ht.sq_eq_one, map_one]⟩) (special_weyl_involution J hJ)
    have hw : f (hermitianWeylSU J hJ) = hermitianWeylPSU J hJ := by
      apply Subtype.ext
      rw [specialToProjective_apply_val, hermitianWeylPSU_val]
      rfl
    rw [hw]
    exact (DFunLike.congr_fun hcomm t).trans ht'
  · rw [← hpre, twoPoint_preimage, map_preimage_conj, hg, hD, torus_preimage]

end BenderSuzuki.ZD.RankOneModelGeometry.PairNormalization
