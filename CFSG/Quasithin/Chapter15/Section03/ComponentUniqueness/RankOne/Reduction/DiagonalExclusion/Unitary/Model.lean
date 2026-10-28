module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.RankOnePlane.UnitaryField
public import Theory.SpecificGroups.SU3.EvenSemilinear
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearFixer

/-!
# Small invariant two-subgroups and Borel fixers in PSU₃

Every nontrivial elementary subgroup of the unitary root group invariant
under the full torus equals the root center. Its order is 2ⁿ, so a subgroup
of order at most four is trivial when n ≥ 3. An involutory automorphism
fixing the entire Borel is trivial by the proved semilinear coverage and
matrix Borel-fixer calculation. Both statements transport through actual
Hermitian basis changes and Sylow conjugacy.

These are the model calculations used before the inner-action step in
Aschbacher--Smith 15.3.43, printed p.1139. The root calculation is the
same one used for the invariant plane in 15.3.40, printed p.1138; it uses
only the intrinsic Huppert II.10.12 coordinates, not that chapter conclusion.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
open CFSG.Quasithin.ChapterF.Source
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.DiagonalExclusion.UnitaryModel
open RankTwo.RankOnePlane.UnitaryField
variable {F : Type*} [Field F] [Finite F]

private theorem torus_normalizes_root (J : HermitianForm 3 F)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (k : Fˣ) :
    hermitianTorusPSU J hJ k ∈ normalizer ((hermitianUnipotentPSU J hJ).range : Set _) := by
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  apply mem_normalizer_fintype
  rintro _ ⟨z, rfl⟩
  refine ⟨hermitianTorusAction J k z, ?_⟩
  rw [hermitianTorusPSU_mul_unipotent, mul_assoc, mul_inv_cancel, mul_one]

private theorem small_root_subgroup_eq_bot [CharP F 2]
    (J : HermitianForm 3 F) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {q : ℕ} (hq : 4 < q) (hcard : Nat.card F = q ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q)
    (W : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hWR : W ≤ (hermitianUnipotentPSU J hJ).range)
    (hW : Nat.card W ≤ 4) (hsq : ∀ w ∈ W, w ^ 2 = 1)
    (hnorm : normalizer ((hermitianUnipotentPSU J hJ).range : Set _) ≤
      normalizer (W : Set (ProjectiveSpecialUnitaryMatrixGroup J))) : W = ⊥ := by
  let f := hermitianUnipotentPSU J hJ
  have hf : Function.Injective f := BenderSuzuki.Converse.hUPSU_injective J hJ
  let U := W.comap f
  have hUW : U.map f = W := map_comap_eq_self hWR
  by_contra hne
  have hU : U ≠ ⊥ := by
    intro he
    apply hne
    rw [← hUW, he, Subgroup.map_bot]
  have hUsq (z) (hz : z ∈ U) : z ^ 2 = 1 := by
    apply hf
    rw [map_pow, map_one]
    exact hsq (f z) hz
  have hUi (k : Fˣ) (z) (hz : z ∈ U) : hermitianTorusAction J k z ∈ U := by
    change f (hermitianTorusAction J k z) ∈ W
    have hk := hnorm (torus_normalizes_root J hJ k)
    have hh := (mem_normalizer_iff.mp hk (f z)).mp hz
    have he := hermitianTorusPSU_mul_unipotent J hJ k z
    rwa [← mul_inv_eq_iff_eq_mul.mpr he]
  have he := invariant_eq_center J q hcard hfixed U hU hUsq hUi
  have hc : Nat.card W = q := by
    rw [← hUW, card_map_of_injective hf, he, card_center J q hcard hfixed]
  omega

/-- Small elementary two-subgroups invariant under a unitary Borel are trivial
in fixed-field degree at least three. -/
theorem small_invariant_subgroup_eq_bot
    {H : Type*} [Group H] [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hm : ClassicalGroup.IsPSU H 3 (2 ^ n)) (P : Sylow 2 H) (W : Subgroup H)
    (hW : Nat.card W ≤ 4) (hsq : ∀ w ∈ W, w ^ 2 = 1)
    (hWP : W ≤ P) (hN : normalizer (P : Set H) ≤ normalizer (W : Set H)) : W = ⊥ := by
  classical
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hm
  let J0 := Unitary.FormTransport.standardForm J
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J0) :=
    Finite.of_surjective _ (Unitary.suProjection_surjective J0)
  let : CharP F 2 := Unitary.charP_two n (by omega) hcard
  obtain ⟨C, hC⟩ := Unitary.FormTransport.exists_standard_basis J n (by omega) hcard hconj
  let e0 := e.trans (Unitary.FormTransport.projectiveEquiv J C hC)
  obtain ⟨_, _, S, hS, _⟩ := Unitary.standard_su_borel_data J0 n (by omega) hcard hconj rfl
  let Q := S.mapSurjective (Unitary.suProjection_surjective J0)
  have hQ : (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J0)) =
      (hermitianUnipotentPSU J0 rfl).range := by
    change (S : Subgroup J0.specialSubgroup).map (Unitary.suProjection J0) = _
    rw [hS]
    exact Unitary.suRoot_map_projection J0 rfl
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J0)
    (P.mapSurjective (f := e0.toMonoidHom) e0.surjective) Q
  let f := e0.trans (MulAut.conj g)
  have hR : (P : Subgroup H).map f.toMonoidHom = (hermitianUnipotentPSU J0 rfl).range := by
    change (P : Subgroup H).map ((MulAut.conj g).toMonoidHom.comp e0.toMonoidHom) = _
    rw [← map_map]
    exact (congrArg Sylow.toSubgroup hg).trans hQ
  have hnR : normalizer ((hermitianUnipotentPSU J0 rfl).range : Set _) ≤
      normalizer (W.map f.toMonoidHom : Set (ProjectiveSpecialUnitaryMatrixGroup J0)) := by
    have hh := map_mono (f := f.toMonoidHom) hN
    change (normalizer ((P : Subgroup H) : Set H)).map f.toMonoidHom ≤
      (normalizer (W : Set H)).map f.toMonoidHom at hh
    rwa [map_equiv_normalizer_eq, map_equiv_normalizer_eq, hR] at hh
  apply (map_eq_bot_iff_of_injective (f := f.toMonoidHom) _ f.injective).mp
  apply small_root_subgroup_eq_bot J0 rfl
    (lt_of_lt_of_le (by decide : 4 < 2 ^ 3)
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn)) hcard
    (Unitary.fixed_card J0 n (by omega) hcard hconj) (W.map f.toMonoidHom)
    (hR ▸ map_mono hWP)
  · rwa [card_map_of_injective f.injective]
  · rintro w ⟨z, hz, rfl⟩
    rw [← map_pow, hsq z hz, map_one]
  · exact hnR

/-- The full Borel detects involutory automorphisms, with semilinear coverage
proved from the inherited simplicity of the actual model. -/
theorem borel_fixer_eq_one
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSU H 3 (2 ^ n)) (P : Sylow 2 H)
    (a : MulAut H) (ha : a ^ 2 = 1)
    (hfix : ∀ b ∈ normalizer (P : Set H), a b = b) : a = 1 := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hm
  let J0 := Unitary.FormTransport.standardForm J
  obtain ⟨C, hC⟩ := Unitary.FormTransport.exists_standard_basis J n (by omega) hcard hconj
  let f := e.trans (Unitary.FormTransport.projectiveEquiv J C hC)
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J0) := f.isSimpleGroup_congr.mp inferInstance
  let P' := P.mapSurjective (f := f.toMonoidHom) f.surjective
  let b := MulAut.congr f a
  obtain ⟨σ, hσ⟩ := HermitianForm.EvenSemilinear.semilinear_coverage J0 rfl hn hcard hconj b
  have hb : b = 1 := by
    apply HermitianForm.BorelTorus.unitary_semilinear_fixer_eq_one
      J0 rfl hn hcard hconj P' b σ hσ
    · change (MulAut.congr f a) ^ 2 = 1
      rw [← map_pow, ha, map_one]
    · intro x hx
      have hm : x ∈ (normalizer (P : Set H)).map f.toMonoidHom := by
        have hB : (normalizer (P : Set H)).map f.toMonoidHom =
            normalizer (P' : Set (ProjectiveSpecialUnitaryMatrixGroup J0)) :=
          map_equiv_normalizer_eq (P : Subgroup H) f
        exact hB.symm ▸ hx
      obtain ⟨z, hz, rfl⟩ := hm
      change f (a (f.symm (f z))) = f z
      rw [f.symm_apply_apply, hfix z hz]
  exact (MulAut.congr f).injective (hb.trans (map_one _).symm)

end CFSG.Quasithin.Chapter15.Section03.RankOne.DiagonalExclusion.UnitaryModel
