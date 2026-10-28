module
public import Theory.SpecificGroups.SymplecticFour.RadicalParabolics.Exact
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy

/-!
# Perfect subgroups of symplectic radical normalizers

A nontrivial perfect subgroup normal in a point or plane parabolic is its
literal solvable residual. The residual's quasisimple two-core quotient
supplies C-component minimality. Combining this with radical-normalizer
recognition gives simultaneous symplectic coordinates for the normalizer
and its specified perfect subgroup; solvability excludes the Borel.

Source: Aschbacher–Smith C.4.5 and the symplectic case of C.4.1,
printed pp.151–153; the local matrices are those of F.1.12, pp.262–264.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymplecticFour.RadicalNormalizer
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem isPPerfect_of_perfect {G : Type*} [Group G] [Finite G]
    [Group.IsPerfect G] : IsPPerfect 2 G := by
  intro N hN hp
  let := hN
  have hs : Subsingleton (G ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (G ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

private theorem perfect_normal_eq_residual {G : Type*} [Group G] [Finite G]
    (B P L : Subgroup G) [Group.IsPerfect B] (hne : B ≠ ⊥) (hBP : B ≤ P)
    (hPB : P ≤ normalizer (B : Set G))
    (he : (solvableResidual P).map P.subtype = L)
    [Group.IsPerfect L] [IsQuasisimple (L ⧸ pCore 2 L)] : B = L := by
  have hBL : B ≤ L := he ▸ le_map_solvableResidual_of_isPerfect B P hBP
  have hLP : L ≤ P := he ▸ map_subtype_le (solvableResidual P)
  let : (B.subgroupOf L).Normal :=
    (normal_subgroupOf_iff_le_normalizer hBL).mpr (hLP.trans hPB)
  let : Group.IsPerfect (B.subgroupOf L) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hBL).symm.toMonoidHom)
      (subgroupOfEquivOfLe hBL).symm.surjective
  have hb : B.subgroupOf L ≠ ⊥ := by
    intro hb
    have hh := congrArg (Subgroup.map L.subtype) hb
    rw [map_subgroupOf_eq_of_le hBL,Subgroup.map_bot] at hh
    exact hne hh
  have hc := isCComponent_top_of_isPPerfect_of_quasisimple_quotient
    (pCore 2 L) pCore_isPGroup (isPPerfect_of_perfect (G := L))
  have ht : B.subgroupOf L = ⊤ := top_unique (hc.minimal _ le_top hb inferInstance
    (inferInstance : (B.subgroupOf L).Normal).isSubnormal)
  exact le_antisymm hBL (subgroupOf_eq_top.mp ht)

/-- The nontrivial perfect normal subgroup is the actual point residual. -/
theorem perfect_normal_point_eq {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (B : Subgroup (Sp F)) [Group.IsPerfect B] (hne : B ≠ ⊥)
    (hBP : B ≤ pointParabolic)
    (hPB : pointParabolic ≤ normalizer (B : Set (Sp F))) : B = pointLocal := by
  have hcard : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_eq_of_lt (by decide : 2 = 2^1) (Nat.pow_lt_pow_right (by decide) hn)
  let := pointLocal_perfect hF hn
  let := (pointNaturalExtension hF hn).quotient_quasisimple hcard
  exact perfect_normal_eq_residual B _ _ hne hBP hPB (pointParabolic_solvableResidual_eq hF hn)

/-- The nontrivial perfect normal subgroup is the actual plane residual. -/
theorem perfect_normal_plane_eq {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (B : Subgroup (Sp F)) [Group.IsPerfect B] (hne : B ≠ ⊥)
    (hBP : B ≤ planeParabolic)
    (hPB : planeParabolic ≤ normalizer (B : Set (Sp F))) : B = planeLocal := by
  have hcard : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_eq_of_lt (by decide : 2 = 2^1) (Nat.pow_lt_pow_right (by decide) hn)
  let := planeLocal_perfect hF hn
  let := (planeNaturalExtension hF hn).quotient_quasisimple hcard
  exact perfect_normal_eq_residual B _ _ hne hBP hPB (planeParabolic_solvableResidual_eq hF hn)

/-- One symplectic conjugacy marks both the radical normalizer and its residual. -/
theorem radical_perfect_normal_conjugate
    (R B : Subgroup (Sp F)) (hR : R.IsPRadical 2)
    [Group.IsPerfect B] (hne : B ≠ ⊥)
    (hBN : B ≤ normalizer (R : Set (Sp F)))
    (hNB : normalizer (R : Set (Sp F)) ≤ normalizer (B : Set (Sp F)))
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n) :
    ∃ g : Sp F,
      ((normalizer (R : Set (Sp F))).map (MulAut.conj g).toMonoidHom = pointParabolic ∧
        B.map (MulAut.conj g).toMonoidHom = pointLocal) ∨
      ((normalizer (R : Set (Sp F))).map (MulAut.conj g).toMonoidHom = planeParabolic ∧
        B.map (MulAut.conj g).toMonoidHom = planeLocal) := by
  obtain ⟨g,hg⟩ := radical_normalizer_eq_parabolic_or_borel R hR
  let a := MulAut.conj g
  let C := B.map a.toMonoidHom
  let : Group.IsPerfect C := Group.IsPerfect.map a.toMonoidHom
  have hC : C ≠ ⊥ := fun hc => hne ((B.map_eq_bot_iff_of_injective a.injective).mp hc)
  have hCN : C ≤ (normalizer (R : Set (Sp F))).map a.toMonoidHom := map_mono hBN
  have hNC : (normalizer (R : Set (Sp F))).map a.toMonoidHom ≤ normalizer (C : Set (Sp F)) := by
    rw [←map_equiv_normalizer_eq B a]
    exact map_mono hNB
  refine ⟨g,?_⟩
  rcases hg with he | he | he
  · exact Or.inl ⟨he,perfect_normal_point_eq hF hn C hC (he ▸ hCN) (he ▸ hNC)⟩
  · exact Or.inr ⟨he,perfect_normal_plane_eq hF hn C hC (he ▸ hCN) (he ▸ hNC)⟩
  · have hCB : C ≤ borel := he ▸ hCN
    let : Group.IsSolvable (borel (F := F)) := isSolvable_borel hF
    let : Group.IsSolvable C := Group.isSolvable_of_isSolvable_injective (f := inclusion hCB) (inclusion_injective hCB)
    let : Nontrivial C := C.nontrivial_iff_ne_bot.mpr hC
    exact (Group.IsPerfect.not_isSolvable C inferInstance).elim
end Theory.SpecificGroups.SymplecticFour.RadicalNormalizer
