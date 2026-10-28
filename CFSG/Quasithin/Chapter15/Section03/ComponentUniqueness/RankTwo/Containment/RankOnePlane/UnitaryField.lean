module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.Definitions
public import CFSG.Quasithin.ChapterF.Section01.SourceDefs
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.SpecialBorel
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.FormTransport
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.RankOnePlane.UnitaryField.RootCoordinates

/-!
# The unitary field restriction and invariant Sylow plane

A four-group in a PSU₃(2ⁿ) Sylow two-subgroup, invariant under its normalizer,
is the full Sylow center and forces n = 2. The coordinate proof places all
involutions in the root center and uses the torus action to fill that center.
Its order is the fixed-field order 2ⁿ; the matrix field has order (2ⁿ)².

Actual matrix conjugation transports an arbitrary Hermitian form to the
antidiagonal form. The image of the special-unitary root Sylow under the
projective quotient is Sylow, and Sylow conjugacy puts the given subgroup in
these coordinates. Injectivity on the root and transport of embedded centers
then recover the claimed equality in the original group. No field bound,
root-center identity, or preferred Sylow coordinates are assumed.

The ambient corollary uses the literal relative Borel N_L(S ∩ L).
Its invariance of W is an input supplied by the source-theorem owner using
15.3.33(1). This module proves the intrinsic model step, not the subsequent
exclusion of PSU₃(4). Positivity of n suffices, so the result applies in
particular to the even n in the source alternatives.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of
15.3.40, printed p.1138. The concrete Sylow and form transport reuse F.1.3.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
open CFSG.Quasithin.ChapterF.Source
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane
open UnitaryField

private theorem sylow_coordinates {H K : Type*} [Group H] [Group K] [Finite K]
    (e : H ≃* K) (P : Sylow 2 H) (Q : Sylow 2 K) :
    ∃ f : H ≃* K, (P : Subgroup H).map f.toMonoidHom = Q := by
  let : Finite H := Finite.of_equiv K e.toEquiv.symm
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P' Q
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  change (P : Subgroup H).map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
  rw [← Subgroup.map_map]
  exact congrArg Sylow.toSubgroup hg

/-- An invariant four-group in any Sylow coordinates is its full center;
the fixed field, rather than the matrix field, has order four. -/
theorem unitary_model_plane_field
    {H F : Type*} [Group H] [Field F] [Finite F]
    (J : HermitianForm 3 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (e : H ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (P : Sylow 2 H) (W : Subgroup H)
    (hW : Nat.card W = 4) (hsq : ∀ w ∈ W, w ^ 2 = 1)
    (hWP : W ≤ P) (hN : normalizer (P : Set H) ≤ normalizer (W : Set H)) :
    n = 2 ∧ W = (center (P : Subgroup H)).map (P : Subgroup H).subtype := by
  classical
  let J0 := Unitary.FormTransport.standardForm J
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J0) :=
    Finite.of_surjective _ (Unitary.suProjection_surjective J0)
  let : CharP F 2 := Unitary.charP_two n hn hcard
  obtain ⟨C, hC⟩ := Unitary.FormTransport.exists_standard_basis J n hn hcard hconj
  let e0 := e.trans (Unitary.FormTransport.projectiveEquiv J C hC)
  obtain ⟨_, _, S, hS, _⟩ := Unitary.standard_su_borel_data J0 n hn hcard hconj rfl
  let Q := S.mapSurjective (Unitary.suProjection_surjective J0)
  have hQ : (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J0)) =
      (hermitianUnipotentPSU J0 rfl).range := by
    change (S : Subgroup J0.specialSubgroup).map (Unitary.suProjection J0) = _
    rw [hS]
    exact Unitary.suRoot_map_projection J0 rfl
  obtain ⟨f, hf⟩ := sylow_coordinates e0 P Q
  have hR : (P : Subgroup H).map f.toMonoidHom =
      (hermitianUnipotentPSU J0 rfl).range := hf.trans hQ
  let W' := W.map f.toMonoidHom
  have hW' : Nat.card W' = 4 := by
    rw [Subgroup.card_map_of_injective f.injective, hW]
  have hsq' (w) (hw : w ∈ W') : w ^ 2 = 1 := by
    obtain ⟨z, hz, rfl⟩ := hw
    rw [← map_pow, hsq z hz, map_one]
  have hWR : W' ≤ (hermitianUnipotentPSU J0 rfl).range :=
    hR ▸ Subgroup.map_mono hWP
  have hNR : normalizer ((hermitianUnipotentPSU J0 rfl).range :
      Set (ProjectiveSpecialUnitaryMatrixGroup J0)) ≤
      normalizer (W' : Set (ProjectiveSpecialUnitaryMatrixGroup J0)) := by
    have hh := Subgroup.map_mono (f := f.toMonoidHom) hN
    change (normalizer ((P : Subgroup H) : Set H)).map f.toMonoidHom ≤
      (normalizer (W : Set H)).map f.toMonoidHom at hh
    rwa [Subgroup.map_equiv_normalizer_eq, Subgroup.map_equiv_normalizer_eq, hR] at hh
  obtain ⟨hfield, hcenter⟩ := projective_plane_eq_center J0 (2 ^ n) hcard
    (Unitary.fixed_card J0 n hn hcard hconj) rfl W' hWR hW' hsq' hNR
  refine ⟨Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) (by omega), ?_⟩
  apply Subgroup.map_injective (f := f.toMonoidHom) f.injective
  rw [map_subgroup_center f.toMonoidHom f.injective, hR]
  exact hcenter

/-- The intrinsic unitary contract used in 15.3.40. Positivity suffices;
no parity restriction on n is needed for this step. -/
theorem unitary_sylow_plane_degree_eq_two
    {H : Type*} [Group H] [Finite H] {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSU H 3 (2 ^ n))
    (P : Sylow 2 H) (W : Subgroup H) (hW : IsKleinFour W)
    (hWP : W ≤ P) (hN : normalizer (P : Set H) ≤ normalizer (W : Set H)) :
    n = 2 ∧ W = (center (P : Subgroup H)).map (P : Subgroup H).subtype := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hm
  let := hW
  apply unitary_model_plane_field J n hn hcard hconj e P W IsKleinFour.card_four
    ?_ hWP hN
  intro w hw
  have hh := Monoid.pow_exponent_eq_one (⟨w, hw⟩ : W)
  rw [IsKleinFour.exponent_two] at hh
  exact congrArg Subtype.val hh

/-- The ambient form: Borel invariance identifies W with the center of S ∩ L
and forces the unitary fixed-field degree to be two. -/
theorem unitary_plane_degree_eq_two
    {G : Type*} [Group G] [Finite G] {L S W : Subgroup G} {n : ℕ}
    (hn : 0 < n) (hm : ClassicalGroup.IsPSU L 3 (2 ^ n))
    (P : Sylow 2 L) (hP : (P : Subgroup L).map L.subtype = S ⊓ L)
    (hWS : W ≤ S) (hWL : W ≤ L) (hW : IsKleinFour W)
    (hN : borel L S ≤ normalizer (W : Set G)) :
    n = 2 ∧ W = (center (S ⊓ L : Subgroup G)).map (S ⊓ L).subtype := by
  have hPi : (S ⊓ L).subgroupOf L = (P : Subgroup L) := by
    rw [← hP]
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  have hWP : W.subgroupOf L ≤ (P : Subgroup L) := by
    rw [← hPi]
    exact Subgroup.subgroupOf_mono L (le_inf hWS hWL)
  have hWi : IsKleinFour (W.subgroupOf L) := by
    let := hW
    let e := subgroupOfEquivOfLe hWL
    exact ⟨(Nat.card_congr e.toEquiv).trans IsKleinFour.card_four,
      (Monoid.exponent_eq_of_mulEquiv e).trans IsKleinFour.exponent_two⟩
  have hNi : normalizer (P : Set L) ≤ normalizer (W.subgroupOf L : Set L) := by
    change normalizer ((P : Subgroup L) : Set L) ≤ _
    rw [← hPi, ← Subgroup.subgroupOf_normalizer_eq inf_le_right,
      ← Subgroup.subgroupOf_normalizer_eq hWL]
    intro x hx
    exact hN ⟨x.property, hx⟩
  obtain ⟨hdegree, hcenter⟩ := unitary_sylow_plane_degree_eq_two hn hm P
    (W.subgroupOf L) hWi hWP hNi
  refine ⟨hdegree, ?_⟩
  have hh := congrArg (Subgroup.map L.subtype) hcenter
  rw [Subgroup.map_subgroupOf_eq_of_le hWL,
    map_subgroup_center L.subtype L.subtype_injective, hP] at hh
  exact hh

end CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane
