module
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.SpecialBorel.Projective

/-!
# The standard SU₃ Borel

The upper unitriangular matrix range is a Sylow two-subgroup of order q³,
and its normalizer is its join with the diagonal torus of order q² − 1.
This normalizer is precisely the inverse image of the natural isotropic-point
stabilizer in PSU₃. It is proper and solvable. The proof uses the genuine
surjection SU₃ → PSU₃ and the containment of its scalar kernel in the torus;
it never identifies the root group with its full projective preimage.

All positive n, including q = 2, are covered. Maximal-overgroup uniqueness
and transport to arbitrary Hermitian forms or Sylow subgroups are separate.
Source: Aschbacher–Smith F.1.3(1), printed pp.259–260; Huppert II.10.12.
-/
noncomputable section
open BenderSuzuki BenderSuzuki.MatrixGroups External
open scoped LinearAlgebra.Projectivization
namespace CFSG.Quasithin.ChapterF.Source.Unitary

private theorem solvable_normalizer
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (D : Subgroup G)
    (hD : D ≤ Subgroup.normalizer ((S : Subgroup G) : Set G))
    (hcyc : IsCyclic D)
    (hsup : (S : Subgroup G) ⊔ D = Subgroup.normalizer ((S : Subgroup G) : Set G)) :
    Group.IsSolvable (Subgroup.normalizer ((S : Subgroup G) : Set G)) := by
  let B := Subgroup.normalizer ((S : Subgroup G) : Set G)
  let : Group.IsNilpotent (S : Subgroup G) := S.isPGroup'.isNilpotent
  let : IsCyclic D := hcyc
  let := IsCyclic.commGroup (α := D)
  let eS := Subgroup.subgroupOfEquivOfLe (S : Subgroup G).le_normalizer
  let eD := Subgroup.subgroupOfEquivOfLe hD
  let : Group.IsSolvable ((S : Subgroup G).subgroupOf B) :=
    Group.isSolvable_of_isSolvable_injective (f := eS.toMonoidHom) eS.injective
  let : Group.IsSolvable (D.subgroupOf B) :=
    Group.isSolvable_of_isSolvable_injective (f := eD.toMonoidHom) eD.injective
  apply Group.isSolvable_of_normal_sup_eq_top
    ((S : Subgroup G).subgroupOf B) (D.subgroupOf B)
  rw [← Subgroup.subgroupOf_sup (S : Subgroup G).le_normalizer hD, hsup]
  exact Subgroup.subgroupOf_self B

/-- The concrete SU₃ root is Sylow and has the standard proper solvable Borel. -/
public theorem standard_su_borel_data
    {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    ∃ (rho : ProjectiveSpecialUnitaryMatrixGroup J →*
        Equiv.Perm (unitaryIsotropicPoints J))
      (pinf : unitaryIsotropicPoints J) (S : Sylow 2 J.specialSubgroup),
      (S : Subgroup J.specialSubgroup) = suRoot J hstandard ∧
      Function.Injective rho ∧
      (∀ (g : J.specialSubgroup) (z : unitaryIsotropicPoints J),
        ((rho (suProjection J g) z : unitaryIsotropicPoints J) : ℙ F (Fin 3 → F)) =
          (Matrix.GeneralLinearGroup.toLin (g : GL (Fin 3) F)).toLinearEquiv •
            (z : ℙ F (Fin 3 → F))) ∧
      Nat.card (suRoot J hstandard) = (2 ^ n) ^ 3 ∧
      Subgroup.normalizer (suRoot J hstandard : Set J.specialSubgroup) =
        suRoot J hstandard ⊔ suTorus J hstandard ∧
      Subgroup.normalizer (suRoot J hstandard : Set J.specialSubgroup) =
        ((MulAction.stabilizer (Equiv.Perm (unitaryIsotropicPoints J)) pinf).comap rho).comap
          (suProjection J) ∧
      Subgroup.normalizer (suRoot J hstandard : Set J.specialSubgroup) < ⊤ ∧
      Group.IsSolvable (Subgroup.normalizer (suRoot J hstandard : Set J.specialSubgroup)) ∧
      Disjoint (suRoot J hstandard) (suTorus J hstandard) ∧
      IsCyclic (suTorus J hstandard) ∧
      Nat.card (suTorus J hstandard) = (2 ^ n) ^ 2 - 1 ∧
      Odd (Nat.card (suTorus J hstandard)) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let R := suRoot J hstandard
  let D := suTorus J hstandard
  let f := suProjection J
  obtain ⟨rho, pinf, hrho, hnatural, hcoordcard, _hRprojcard, hsup, hnormalizer, hproper⟩ :=
    standard_projective_matrix_borel J n hn hcard hconj hstandard
  let U := (MulAction.stabilizer (Equiv.Perm (unitaryIsotropicPoints J)) pinf).comap rho
  have hmap : (R ⊔ D).map f = U := by
    rw [Subgroup.map_sup, suRoot_map_projection, suTorus_map_projection]
    exact hsup
  have hpre : U.comap f = R ⊔ D := by
    rw [← hmap, Subgroup.comap_map_eq]
    exact sup_eq_left.mpr ((suProjection_ker_le_torus J hstandard).trans le_sup_right)
  have hBN : R ⊔ D ≤ Subgroup.normalizer (R : Set J.specialSubgroup) :=
    sup_le R.le_normalizer (suTorus_normalizes_root J hstandard)
  have hNpre : Subgroup.normalizer (R : Set J.specialSubgroup) ≤ U.comap f := by
    have hle := Subgroup.le_normalizer_map (H := R) f
    rw [suRoot_map_projection, hnormalizer] at hle
    exact Subgroup.map_le_iff_le_comap.mp hle
  have hNB : Subgroup.normalizer (R : Set J.specialSubgroup) = R ⊔ D :=
    le_antisymm (hNpre.trans hpre.le) hBN
  have hNU : Subgroup.normalizer (R : Set J.specialSubgroup) = U.comap f :=
    hNB.trans hpre.symm
  have hRcard : Nat.card R = (2 ^ n) ^ 3 :=
    (Nat.card_congr (MonoidHom.ofInjective (suRoot_injective J hstandard)).toEquiv.symm).trans
      hcoordcard
  have hRp : IsPGroup 2 R := IsPGroup.of_card (by
    simpa [pow_mul] using hRcard : Nat.card R = 2 ^ (n * 3))
  have hDodd := suTorus_odd J hstandard n hn hcard
  have hDnot : ¬ 2 ∣ Nat.card D := by
    exact fun h => (Nat.not_even_iff_odd.mpr hDodd) (even_iff_two_dvd.mpr h)
  obtain ⟨P, hP⟩ := exists_sylow_map_eq_of_normal_complement
    (show R ≤ R ⊔ D from le_sup_left) (show D ≤ R ⊔ D from le_sup_right) hBN
    (disjoint_iff.mp (suRoot_disjoint_torus J hstandard)) rfl hRp hDnot
  obtain ⟨S, hS⟩ := exists_sylow_map_eq_of_normalizer_le P (by rw [hP, hNB])
  have hSR : (S : Subgroup J.specialSubgroup) = R := hS.trans hP
  have hNproper : Subgroup.normalizer (R : Set J.specialSubgroup) < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro he
    apply ne_of_lt hproper
    apply top_unique
    intro y _
    obtain ⟨x, rfl⟩ := suProjection_surjective J y
    have hx : x ∈ Subgroup.normalizer (R : Set J.specialSubgroup) := he ▸ Subgroup.mem_top x
    exact hNpre hx
  have hsolv : Group.IsSolvable (Subgroup.normalizer (R : Set J.specialSubgroup)) := by
    have hh := solvable_normalizer S D (by rw [hSR, hNB]; exact le_sup_right)
      (suTorus_cyclic J hstandard) (by rw [hSR, hNB])
    rwa [hSR] at hh
  refine ⟨rho, pinf, S, hSR, hrho, ?_, hRcard, hNB, hNU, hNproper, hsolv,
    suRoot_disjoint_torus J hstandard, suTorus_cyclic J hstandard, ?_, hDodd⟩
  · intro g z
    exact hnatural (f g) z g rfl
  · rw [suTorus_card, hcard]

end CFSG.Quasithin.ChapterF.Source.Unitary
