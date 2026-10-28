module
public import Theory.SpecificGroups.SU3.EvenInvolutionResidual
public import Theory.GroupTheory.PResidual.FiniteImage
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.SpecialBorel.Projective
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.FormTransport
public import CFSG.Quasithin.ClassicalModels

/-!
# The intrinsic unitary step in Proposition 16.5.1

If H is PSU₃(2ⁿ), n ≥ 2, S is Sylow two, and v is an involution in S,
then S lies in O²(C_H(v)), embedded back into H. This is the two-residual,
not the two-core or the odd residual.

The matrix calculation is in `SU3.EvenInvolutionResidual`: norm-one torus
commutators generate the root group inside the involution centralizer's
two-residual. The root order identifies that group as Sylow. Sylow conjugacy
and an actual change-of-form isomorphism transport the calculation to the
specified S and v in the arbitrary `IsPSU` model. The fixed-field order is
2ⁿ and the matrix-field order is (2ⁿ)² throughout, including n = 2.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition 16.5.1, unitary paragraph, printed p.1194. Together with the
separate earlier containment from 16.4.8 (printed pp.1187–1188), this is
the intrinsic input to the parent module's ambient placement argument.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
open CFSG.Quasithin.ChapterF.Source.Unitary
open scoped Matrix
namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.UnitaryPlacement.Intrinsic

private theorem map_centralizer_singleton {G K : Type*} [Group G] [Group K]
    (e : G ≃* K) (v : G) :
    (centralizer ({v} : Set G)).map e.toMonoidHom = centralizer ({e v} : Set K) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change e x * e v = e v * e x
    simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp hx)
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hy

private theorem transport {G K : Type*} [Group G] [Group K] [Finite G]
    (e : G ≃* K) (P : Subgroup G) (v : G)
    (h : P ≤ (pResidual 2 (centralizer ({v} : Set G))).map
      (centralizer ({v} : Set G)).subtype) :
    P.map e.toMonoidHom ≤ (pResidual 2 (centralizer ({e v} : Set K))).map
      (centralizer ({e v} : Set K)).subtype := by
  have hm := map_mono (f := e.toMonoidHom) h
  rwa [map_embedded_pResidual, map_centralizer_singleton] at hm

/-- The intrinsic containment in the standard antidiagonal matrix model. -/
theorem standard_sylow_le_twoResidual
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (n : ℕ) (hn : 2 ≤ n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hstd : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (v : ProjectiveSpecialUnitaryMatrixGroup J)
    (hv : v ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hv2 : orderOf v = 2) :
    (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ≤
      (pResidual 2 (centralizer ({v} : Set (ProjectiveSpecialUnitaryMatrixGroup J)))).map
        (centralizer ({v} : Set (ProjectiveSpecialUnitaryMatrixGroup J))).subtype := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ (suProjection_surjective J)
  let : CharP F 2 := charP_two n (by omega) hcard
  have hfixed := fixed_card J n (by omega) hcard hconj
  obtain ⟨_, hRcard, _⟩ := SU3.EvenInvolutionResidual.root_structure J (2 ^ n) hcard hfixed hstd
  let R := (hermitianUnipotentPSU J hstd).range
  have hRp : IsPGroup 2 R := IsPGroup.of_card
    (show Nat.card R = 2 ^ (n * 3) by simpa only [pow_mul] using hRcard)
  obtain ⟨P, hRP⟩ := hRp.exists_le_sylow
  obtain ⟨_, _, S₀, _, _, _, _, _, hS₀, _⟩ :=
    standard_psu_borel_data J n (by omega) hcard hconj hstd
  have hPeq : R = (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    Subgroup.eq_of_le_of_card_ge hRP (by
      rw [Nat.card_congr (P.equiv S₀).toEquiv, hS₀, hRcard])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) P S
  let e := MulAut.conj g
  have hm : (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map e.toMonoidHom = S := by
    change ((g • P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
      Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = _
    rw [hg]
  obtain ⟨w, hw, he⟩ := (show v ∈ (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map
      e.toMonoidHom by rw [hm]; exact hv)
  change e w = v at he
  have hwR : w ∈ R := hPeq.symm ▸ hw
  obtain ⟨z, hz⟩ := hwR
  have hwsq : (hermitianUnipotentPSU J hstd z) ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, hz, he, map_one, ← hv2, pow_orderOf_eq_one]
  have hq : 2 < 2 ^ n := by
    have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
    norm_num at hpow ⊢
    omega
  have hodd : Odd (2 ^ n + 1) := (even_two.pow_of_ne_zero (by omega)).add_one
  have hroot := SU3.EvenInvolutionResidual.root_le_twoResidual
    J (2 ^ n) hcard hfixed hstd hq hodd z hwsq
  have ht := transport e R (hermitianUnipotentPSU J hstd z) hroot
  rw [hPeq, hm, hz, he] at ht
  exact ht

/-- For PSU₃(2ⁿ), n ≥ 2, every Sylow two-subgroup lies in O² of the
centralizer of each of its involutions. The isomorphism is the actual
unitary model supplied by `IsPSU`. -/
theorem sylow_le_twoResidual {H : Type*} [Group H] [Finite H]
    (n : ℕ) (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSU H 3 (2 ^ n))
    (S : Sylow 2 H) (v : H) (hv : v ∈ (S : Subgroup H)) (hv2 : orderOf v = 2) :
    (S : Subgroup H) ≤ (pResidual 2 (centralizer ({v} : Set H))).map
      (centralizer ({v} : Set H)).subtype := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e₀⟩⟩ := hmodel
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J n (by omega) hcard hconj
  let e := e₀.trans (FormTransport.projectiveEquiv J C hC)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J)) :=
    Finite.of_surjective e e.surjective
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hvP : e v ∈ (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J))) :=
    ⟨v, hv, rfl⟩
  have hev : orderOf (e v) = 2 := (e.orderOf_eq v).trans hv2
  have hp := standard_sylow_le_twoResidual (FormTransport.standardForm J)
    n hn hcard hconj rfl P (e v) hvP hev
  have ht := transport e.symm (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup
      (FormTransport.standardForm J))) (e v) hp
  change ((S : Subgroup H).map e.toMonoidHom).map e.symm.toMonoidHom ≤ _ at ht
  rw [map_map] at ht
  have heid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id H := by
    ext x
    exact e.symm_apply_apply x
  rw [heid, map_id, e.symm_apply_apply] at ht
  exact ht
end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.UnitaryPlacement.Intrinsic
