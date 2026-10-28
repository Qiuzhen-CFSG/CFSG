module
public import Theory.SpecificGroups.SU3.CartanPanelFixedPoints
public import Theory.SpecificGroups.SU3.FixedFieldTwo
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.SpecialBorel
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.FormTransport
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.CartanFixedPoints.Quotient

/-!
# The unitary Cartan fixed-pair branches

The actual root normalizers in SU₃ and PSU₃ share their coset action via
the special-to-projective map. Its scalar kernel stays in the full torus.
The fixed-field torus calculation gives the sharp element for any supplied
supplement. Basis change and Sylow conjugacy then cover arbitrary forms
and Sylows. Perfectness excludes q = 2 through the genuine solvable
projective quotient of order 72.

Source: Huppert II.10.12 and Aschbacher--Smith F.1.1, printed pp.259--260.
-/

public section
open BenderSuzuki.MatrixGroups BenderSuzuki.External Theory.CartanPanel
namespace CFSG.Quasithin.ChapterF.Source
namespace Unitary.CartanPanel
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)

/-- Perfectness excludes the actual projective group at q = 2. -/
theorem parameter_ge_two [Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J)]
    (n : ℕ) (hn : 0 < n) (hc : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) : 2 ≤ n := by
  by_contra hh
  have hn1 : n = 1 := by omega
  subst n
  have hc' : Nat.card F = 2 ^ 2 := by simpa using hc
  have hconj' : ∀ x, J.conj x = x ^ 2 := by simpa using hconj
  have horder := HermitianForm.FixedFieldTwo.card_projective J hc' hconj'
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ (suProjection_surjective J)
  let : Nontrivial (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [horder]; decide)
  exact Group.IsPerfect.not_isSolvable (ProjectiveSpecialUnitaryMatrixGroup J)
    (HermitianForm.FixedFieldTwo.projective_isSolvable J hc' hconj')

/-- Inverse image of the projective root normalizer, retaining its scalar kernel. -/
theorem root_normalizer_comap (n : ℕ) (hn : 0 < n)
    (hc : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) :
    (Subgroup.normalizer ((hermitianUnipotentPSU J hJ).range : Set _)).comap
      (suProjection J) = Subgroup.normalizer (suRoot J hJ : Set _) := by
  obtain ⟨_, _, _, _, _, _, hsup, hN, _⟩ :=
    standard_projective_matrix_borel J n hn hc hconj hJ
  obtain ⟨_, _, _, _, _, _, _, hNS, _⟩ := standard_su_borel_data J n hn hc hconj hJ
  rw [hN, ← hsup, ← suRoot_map_projection, ← suTorus_map_projection,
    ← Subgroup.map_sup, Subgroup.comap_map_eq, hNS]
  exact sup_eq_left.mpr ((suProjection_ker_le_torus J hJ).trans le_sup_right)

/-- The perfectness-free standard SU₃ calculation for q ≥ 4. -/
theorem standard_su (n : ℕ) (hn : 2 ≤ n)
    (hc : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) (T : Sylow 2 J.specialSubgroup) :
    SylowHasTwoFixedCosets T := by
  let : CharP F 2 := charP_two n (by omega) hc
  obtain ⟨_, _, S, hSR, _⟩ := standard_su_borel_data J n (by omega) hc hconj hJ
  have hpre := root_normalizer_comap J n (by omega) hc hconj hJ
  apply Theory.CartanPanel.all_sylows S ?_ T
  intro D hD _hodd _hdis hsup
  change HasTwoFixedCosets (Subgroup.normalizer ((S : Subgroup J.specialSubgroup) : Set J.specialSubgroup)) D
  change D ≤ Subgroup.normalizer ((S : Subgroup J.specialSubgroup) : Set J.specialSubgroup) at hD
  change (S : Subgroup J.specialSubgroup) ⊔ D = Subgroup.normalizer ((S : Subgroup J.specialSubgroup) : Set J.specialSubgroup) at hsup
  rw [hSR] at hD hsup ⊢
  apply two_fixed_pullback (suProjection J) (suProjection_surjective J) _ _ hpre D
  apply HermitianForm.CartanPanel.projective_root_two_fixed_cosets J hJ hc
    (fixed_card J n (by omega) hc hconj)
    ((by decide : 2 < 2 ^ 2).trans_le (Nat.pow_le_pow_right (by decide) hn))
  · exact Subgroup.map_le_iff_le_comap.mpr (hpre.symm ▸ hD)
  · rw [← suRoot_map_projection, ← Subgroup.map_sup, hsup, ← hpre,
      Subgroup.map_comap_eq_self_of_surjective (suProjection_surjective J),
      suRoot_map_projection]

/-- The standard PSU₃ calculation uses the literal projected root Sylow. -/
theorem standard_psu (n : ℕ) (hn : 2 ≤ n)
    (hc : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    SylowHasTwoFixedCosets T := by
  let : CharP F 2 := charP_two n (by omega) hc
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ (suProjection_surjective J)
  obtain ⟨_, _, S, hSR, _⟩ := standard_su_borel_data J n (by omega) hc hconj hJ
  let P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J) :=
    S.mapSurjective (f := suProjection J) (suProjection_surjective J)
  have hP : (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = (hermitianUnipotentPSU J hJ).range := by
    change (S : Subgroup J.specialSubgroup).map (suProjection J) = _
    rw [hSR, suRoot_map_projection]
  apply Theory.CartanPanel.all_sylows P ?_ T
  intro D hD _hodd _hdis hsup
  change HasTwoFixedCosets (Subgroup.normalizer ((P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Set (ProjectiveSpecialUnitaryMatrixGroup J))) D
  change D ≤ Subgroup.normalizer ((P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Set (ProjectiveSpecialUnitaryMatrixGroup J)) at hD
  change (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ⊔ D = Subgroup.normalizer ((P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Set (ProjectiveSpecialUnitaryMatrixGroup J)) at hsup
  rw [hP] at hD hsup ⊢
  exact HermitianForm.CartanPanel.projective_root_two_fixed_cosets J hJ hc
    (fixed_card J n (by omega) hc hconj)
    ((by decide : 2 < 2 ^ 2).trans_le (Nat.pow_le_pow_right (by decide) hn)) D hD hsup

/-- Arbitrary Hermitian forms and Sylows in the perfect special-unitary case. -/
theorem perfect_su [Group.IsPerfect J.specialSubgroup]
    (n : ℕ) (hn : 0 < n) (hc : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) (T : Sylow 2 J.specialSubgroup) :
    SylowHasTwoFixedCosets T := by
  let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Group.IsPerfect.ofSurjective (f := suProjection J) (suProjection_surjective J)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ (suProjection_surjective J)
  have hn2 := parameter_ge_two J n hn hc hconj
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J n hn hc hconj
  let e := FormTransport.specialEquiv J C hC
  let P := T.mapSurjective (f := e.toMonoidHom) e.surjective
  apply sylow_transport e.symm P T _
    (standard_su (FormTransport.standardForm J) n hn2 hc hconj rfl P)
  exact (Subgroup.map_symm_eq_iff_map_eq _).mpr rfl

/-- Arbitrary Hermitian forms and Sylows in the perfect projective-unitary case. -/
theorem perfect_psu [Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J)]
    (n : ℕ) (hn : 0 < n) (hc : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    SylowHasTwoFixedCosets T := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ (suProjection_surjective J)
  have hn2 := parameter_ge_two J n hn hc hconj
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J n hn hc hconj
  let e := FormTransport.projectiveEquiv J C hC
  let P := T.mapSurjective (f := e.toMonoidHom) e.surjective
  apply sylow_transport e.symm P T _
    (standard_psu (FormTransport.standardForm J) n hn2 hc hconj rfl P)
  exact (Subgroup.map_symm_eq_iff_map_eq _).mpr rfl
end Unitary.CartanPanel

/-- The special-unitary source constructor, with its actual field and form witnesses. -/
theorem perfect_sylow_two_fixed_cosets_su {M : Type*} [Group M] [Group.IsPerfect M]
    (n : ℕ) (hn : 0 < n) (hmodel : IsSU M 3 (2 ^ n))
    (T : Sylow 2 M) : SylowHasTwoFixedCosets T := by
  obtain ⟨F, hF, hf, J, hc, hconj, ⟨e⟩⟩ := hmodel
  let : Finite M := Finite.of_injective e e.injective
  let : Group.IsPerfect J.specialSubgroup :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let P := T.mapSurjective (f := e.toMonoidHom) e.surjective
  apply sylow_transport e.symm P T _ (Unitary.CartanPanel.perfect_su J n hn hc hconj P)
  exact (Subgroup.map_symm_eq_iff_map_eq _).mpr rfl

/-- The projective-unitary constructor keeps the actual cubic scalar quotient. -/
theorem perfect_sylow_two_fixed_cosets_psu {M : Type*} [Group M] [Group.IsPerfect M]
    (n : ℕ) (hn : 0 < n) (hmodel : ClassicalGroup.IsPSU M 3 (2 ^ n))
    (T : Sylow 2 M) : SylowHasTwoFixedCosets T := by
  obtain ⟨F, hF, hf, J, hc, hconj, ⟨e⟩⟩ := hmodel
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ (Unitary.suProjection_surjective J)
  let : Finite M := Finite.of_injective e e.injective
  let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let P := T.mapSurjective (f := e.toMonoidHom) e.surjective
  apply sylow_transport e.symm P T _ (Unitary.CartanPanel.perfect_psu J n hn hc hconj P)
  exact (Subgroup.map_symm_eq_iff_map_eq _).mpr rfl

end CFSG.Quasithin.ChapterF.Source
