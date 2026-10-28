module

public import BenderSuzuki.SE.Models
public import BenderSuzuki.External.Huppert.II.theorem_8_27
public import BenderSuzuki.External.Huppert.II.theorem_10_12
public import Theory.SpecificGroups.Suzuki.SylowOmegaGeometry

/-!
# Selecting Sz(8) among the concrete Bender models

A Sylow subgroup of order 64 with eight square-one elements cannot belong to
binary PSL₂, whose Sylow subgroups have exponent two. If its center contains
those eight elements, the unitary family is impossible as well: the Sylow
order forces q = 4, but the center then has order four. In the Suzuki family,
the Sylow order q² forces q = 8.

The consumer is the intrinsic residual recognition theorem in
`SuzukiRecognition.Identification`. All family alternatives carry actual
isomorphisms to the concrete Bender matrix models.

Sources: Aschbacher--Smith, J.2.9, printed p.438 (PDF p.449);
Huppert II.8.2(a), II.10.12 and Huppert--Blackburn XI.3.1--3.3.
-/

public section

open Subgroup BenderSuzuki BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterJ.Centralizers.SuzukiRecognition
variable {X : Type*} [Group X] [Finite X]

private theorem residual_center_card_lower_bound
    (P : Sylow 2 X) (V : Subgroup X) (hVcard : Nat.card V = 8)
    (hV : ∀ x : X, x ∈ V ↔ x ∈ (P : Subgroup X) ∧ x ^ 2 = 1)
    (hC : ∀ v : X, v ∈ V → v ≠ 1 →
      centralizer ({v} : Set X) = (P : Subgroup X)) :
    8 ≤ Nat.card (center P) := by
  have hVP : V ≤ (P : Subgroup X) := fun x hx => ((hV x).mp hx).1
  have hZ : V.subgroupOf (P : Subgroup X) ≤ center P := by
    intro v hv
    rw [mem_center_iff]
    intro x
    apply Subtype.ext
    by_cases hv1 : (v : X) = 1
    · simp [hv1]
    · exact mem_centralizer_singleton_iff.mp
        (show (x : X) ∈ centralizer ({(v : X)} : Set X) by
          rw [hC v hv hv1]
          exact x.property)
  have hc := Subgroup.card_le_of_le hZ
  rw [Nat.card_congr (subgroupOfEquivOfLe hVP).toEquiv, hVcard] at hc
  exact hc

private theorem not_psl2_of_residual_geometry
    (P : Sylow 2 X) (hPcard : Nat.card P = 64)
    (V : Subgroup X) (hVcard : Nat.card V = 8)
    (hV : ∀ x : X, x ∈ V ↔ x ∈ (P : Subgroup X) ∧ x ^ 2 = 1)
    (n : ℕ) (hn : 2 ≤ n) (e : X ≃* PSL2BinaryMatrixGroup n) : False := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hfield : Nat.card (BinaryGaloisField n) = 2 ^ n :=
    GaloisField.card 2 n (by omega)
  obtain ⟨a⟩ := External.huppert_II_8_2_a_sylow_equiv_additive hfield Q
  let f : P ≃* Multiplicative (BinaryGaloisField n) :=
    (e.subgroupMap (P : Subgroup X)).trans a.symm
  have hsq (x : P) : x ^ 2 = 1 := by
    apply f.injective
    rw [map_pow, map_one]
    change (2 : ℕ) • Multiplicative.toAdd (f x) = 0
    simp only [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  have heq : V = (P : Subgroup X) := by
    ext x
    rw [hV]
    exact ⟨And.left, fun hx => ⟨hx, congrArg (fun z : P => (z : X)) (hsq ⟨x, hx⟩)⟩⟩
  have hc : Nat.card V = Nat.card P := congrArg (fun H : Subgroup X => Nat.card H) heq
  omega

private theorem not_psu3_of_residual_geometry
    (P : Sylow 2 X) (hPcard : Nat.card P = 64)
    (hcenter : 8 ≤ Nat.card (center P))
    (n : ℕ) (hn : 2 ≤ n)
    (E : Type) [Field E] [Finite E] (J : HermitianForm 3 E)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hEcard : Nat.card E = (2 ^ n) ^ 2)
    (hfix : Nat.card {z : E // J.conj z = z} = 2 ^ n)
    (e : X ≃* ProjectiveSpecialUnitaryMatrixGroup J) : False := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv X e.toEquiv
  obtain ⟨_, rho, pinf, _, _, _, ⟨R, H, _, _, _, _, _, _, hRcard, hRderived,
      hRcenter, _⟩, _⟩ := External.huppert_II_10_12 J (2 ^ n) hEcard hfix hJ
  rw [hRderived] at hRcenter
  have hRp : IsPGroup 2 R := IsPGroup.of_card (hRcard.trans (pow_mul 2 n 3).symm)
  obtain ⟨Q, hRQ⟩ := hRp.exists_le_sylow
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let f : P ≃* Q := (e.subgroupMap (P : Subgroup X)).trans (P'.equiv Q)
  have hQcard : Nat.card Q = 64 := (Nat.card_congr f.toEquiv).symm.trans hPcard
  have hle : (2 ^ n) ^ 3 ≤ 64 := by
    rw [← hRcard, ← hQcard]
    exact Subgroup.card_le_of_le hRQ
  have hn2 : n = 2 := by
    have hh : 2 ^ (n * 3) ≤ 2 ^ 6 := by simpa [pow_mul] using hle
    have := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh
    omega
  subst n
  norm_num at hRcard hRcenter
  have hReq : R = (Q : Subgroup _) :=
    Subgroup.eq_of_le_of_card_ge hRQ (by omega)
  let g : P ≃* R := f.trans (MulEquiv.subgroupCongr hReq).symm
  have hc := Nat.card_congr (Subgroup.centerCongr g).toEquiv
  omega

/-- Within the three concrete Bender families, the residual Sylow and centralizer
geometry selects the actual matrix group Sz(8). -/
theorem suzuki_of_bender_residual_geometry
    (hmodel : IsSimpleBenderGroup X)
    (P : Sylow 2 X) (hPcard : Nat.card P = 64)
    (V : Subgroup X) (hVcard : Nat.card V = 8)
    (hV : ∀ x : X, x ∈ V ↔ x ∈ (P : Subgroup X) ∧ x ^ 2 = 1)
    (hC : ∀ v : X, v ∈ V → v ≠ 1 →
      centralizer ({v} : Set X) = (P : Subgroup X)) :
    Nonempty (X ≃* SuzukiMatrixGroup 1) := by
  cases hmodel with
  | isPSL2 h =>
    obtain ⟨n, hn, ⟨e⟩⟩ := h
    exact (not_psl2_of_residual_geometry P hPcard V hVcard hV n hn e).elim
  | isSuzuki h =>
    obtain ⟨m, hm, ⟨e⟩⟩ := h
    have hc := suzukiSylow_card (by omega : 0 < m) e P
    rw [hPcard] at hc
    have he : 2 ^ 6 = 2 ^ ((2 * m + 1) * 2) := by simpa [pow_mul] using hc
    have hm1 : m = 1 := by
      have := Nat.pow_right_injective (by decide : 2 ≤ 2) he
      omega
    subst m
    exact ⟨e⟩
  | isPSU3 h =>
    obtain ⟨n, hn, E, hEfield, hEfinite, J, hJ, hEcard, hfix, ⟨e⟩⟩ := h
    exact (not_psu3_of_residual_geometry P hPcard
      (residual_center_card_lower_bound P V hVcard hV hC)
      n hn E J hJ hEcard hfix e).elim

end CFSG.Quasithin.ChapterJ.Centralizers.SuzukiRecognition
