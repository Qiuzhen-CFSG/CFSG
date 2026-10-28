module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.SeedGeneration
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Action
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Rows
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.EightSylow

/-!
# The original seed marks the orthogonal parabolic

The seed U ∩ ZS generates U. Its image in the nonzero orthogonal quotient
therefore contains a nonzero vector. The actual Sylow subgroup of X fixes
this vector. The alternating-eight Sylow calculation then gives a conjugate
four-block stabilizer using these same quotient coordinates.

Source: Aschbacher--Smith 15.2.23(c), printed p.1117.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open Section01 PlaneUniquenessPreceding ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

/-- A nonzero image of the literal seed marks the full permutation stabilizer. -/
theorem exists_orthogonal_seed_marking
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G))
    (P : Sylow 2 X) (hP : (P : Subgroup X).map X.subtype ≤ planeSylow T ZS) :
    letI := U_elementary d hI hfit hXI
    ∀ (C : Subrepresentation (U_representation d hI hfit hXI hn))
      (e : ActionEquiv C.quotientRepresentation (alternatingNatural 8)),
      ∃ u : Additive (U X ZS), (u.toMul : G) ∈ ZS ∧
        e.linearEquiv (C.toSubmodule.mkQ u) ≠ 0 ∧
        ∃ r : alternatingGroup (Fin 8), ∀ g : Equiv.Perm (Fin 8),
          BinaryPermutation.naturalRepresentation (Fin 8) g
            (e.linearEquiv (C.toSubmodule.mkQ u)) = e.linearEquiv (C.toSubmodule.mkQ u) ↔
            r.val * g * r.val⁻¹ ∈
              Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.fourStabilizer := by
  let := U_elementary d hI hfit hXI
  intro C e
  let σ := U_representation d hI hfit hXI hn
  let Z := AddSubgroup.toZModSubmodule 2 (ZS.subgroupOf (U X ZS)).toAddSubgroup
  have hgen := U_seed_module_generates d hI hfit hXI hn σ
    (U_representation_apply d hI hfit hXI hn)
  obtain ⟨u,hu,hne⟩ : ∃ u ∈ Z, e.linearEquiv (C.toSubmodule.mkQ u) ≠ 0 := by
    by_contra! hz
    have hZC : Z ≤ C.toSubmodule := by
      intro u hu
      apply (Submodule.Quotient.mk_eq_zero _).mp
      apply e.linearEquiv.injective
      change e.linearEquiv (C.toSubmodule.mkQ u) = e.linearEquiv 0
      simpa only [map_zero] using hz u hu
    have hle : (⨆ g : X ⧸ pCore 2 X, Z.map (σ g)) ≤ C.toSubmodule := by
      apply iSup_le
      rintro g _ ⟨u,hu,rfl⟩
      exact C.apply_mem_toSubmodule g (hZC hu)
    rw [hgen] at hle
    have ht := top_unique hle
    have hdim := e.linearEquiv.finrank_eq
    rw [ht] at hdim
    have hmodel := BinaryPermutation.finrank_natural_even (Fin 8) (by decide)
    simp only [Module.finrank_zero_of_subsingleton] at hdim
    simp only [Fintype.card_fin] at hmodel
    omega
  let q := e.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  let Q := P.mapSurjective (f := q)
    (e.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _))
  have hfix : ∀ g ∈ (Q : Subgroup (alternatingGroup (Fin 8))),
      BinaryPermutation.naturalRepresentation (Fin 8) g.val
        (e.linearEquiv (C.toSubmodule.mkQ u)) = e.linearEquiv (C.toSubmodule.mkQ u) := by
    rintro g ⟨x,hx,rfl⟩
    have hxS := hP (mem_map_of_mem X.subtype hx)
    have hxu : σ (QuotientGroup.mk' (pCore 2 X) x) u = u := by
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [U_representation_apply]
      have hc : (u.toMul : G) * (x : G) = (x : G) * (u.toMul : G) :=
        hxS.2 u.toMul (show (u.toMul : G) ∈ ZS from hu)
      rw [← hc,mul_inv_cancel_right]
    change alternatingNatural 8 (e.groupEquiv (QuotientGroup.mk' (pCore 2 X) x))
      (e.linearEquiv (C.toSubmodule.mkQ u)) = _
    rw [← e.intertwines, Subrepresentation.quotientRepresentation_mk, hxu]
  obtain ⟨r,hr⟩ := BinaryPermutation.TerminalOrthogonal.Eight.alternating_exists_conjugate_stabilizer
    Q (e.linearEquiv (C.toSubmodule.mkQ u)) hne hfix
  exact ⟨u,hu,hne,r,hr⟩

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear
