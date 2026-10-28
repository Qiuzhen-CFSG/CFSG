module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.BinaryAutomorphisms.DerivedAction
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.WeylOpposition
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.Disjoint

/-!
# The center of the full binary Ree group

The actual full fixed matrix group `Model 0` has trivial center. Positive-root
matrix exchanges give split Bruhat coverage. Uniqueness of the middle Weyl
representative and the fixed-Weyl generation theorem descend this coverage to
the exceptional fixed group. The proved simple-root coordinate witnesses then
make its positive subgroup self-normalizing, so it contains every central
element.

The explicit sixth Coxeter power is fixed by the exceptional twist and
conjugates the positive root subgroup to the negative root subgroup. A central
positive element is therefore also negative. Their proved matrix intersection
is trivial, completing the center calculation. This last intersection argument
works for every `Model m`.

`FixedGeometry.unipotent_normalizer_eq` discharges all geometric premises of
the binary result. No comparison
of the derived subgroup with the Tits group is needed, and the carrier remains
the exceptional-twist fixed subgroup of the root-generated F₄ matrix group.

Sources: GLS3, Theorem 2.5.15, explicitly stating `Z(L) = 1`, and the
opposition calculation in 2.3.8, `refs/KGroup/GLS3/chapter2.tex`;
Aschbacher–Smith F.1.12, printed pp.263–264 of `refs/quasithin.pdf`, which
identifies the full binary Ree group with the automorphism group of its
Tits derived subgroup. The derived-action bijectivity assembly is separate.
-/

public section

namespace ReeF4.Parabolics.OuterLocal

open Subgroup
open ReeF4.LocalBlockInput.PairNormalization

/-- A central positive element is also negative, by the actual fixed opposition
representative, and is therefore identity. This includes the binary endpoint. -/
theorem center_inf_unipotent_eq_bot (m : ℕ) :
    center (Model m) ⊓ unipotent m = ⊥ := by
  apply le_bot_iff.mp
  intro z hz
  let w : Model m := ⟨splitOpposition m, by
    apply (mem_fixedSubgroup m _).mpr
    simpa only [LocalBlockInput.twist_eq_reeAutomorphism, reeAutomorphism_apply] using
      twist_splitOpposition (canonicalLocalBlockInput m)⟩
  have hcomm : w * z * w⁻¹ = z := by
    rw [(mem_center_iff.mp hz.1) w, mul_assoc, mul_inv_cancel, mul_one]
  have hu : toSplitGroup m z ∈ LargeLocalSeeds.splitUnipotent m := hz.2
  have hn : toSplitGroup m z ∈ LocalBlockInput.splitNegativeUnipotent m := by
    rw [← splitOpposition_map_unipotent m]
    refine ⟨toSplitGroup m z, hu, ?_⟩
    simpa only [map_mul, map_inv, toSplitGroup_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply] using congrArg (toSplitGroup m) hcomm
  apply mem_bot.mpr
  apply toSplitGroup_injective m
  rw [map_one]
  exact (Subgroup.disjoint_def.mp (splitUnipotent_disjoint_negative m)) hu hn

/-- Self-normalization puts every central binary Ree element in the positive
subgroup, where the concrete opposition calculation eliminates it. -/
theorem binary_center_eq_bot_of_unipotent_normalizer
    (hN : normalizer (unipotent 0) = unipotent 0) :
    center (Model 0) = ⊥ := by
  have hc := center_le_normalizer (unipotent 0 : Set (Model 0))
  rw [hN] at hc
  calc
    center (Model 0) = center (Model 0) ⊓ unipotent 0 := (inf_eq_left.mpr hc).symm
    _ = ⊥ := center_inf_unipotent_eq_bot 0

/-- Fixed Bruhat coverage and Weyl separation imply binary centerlessness. -/
theorem binary_center_eq_bot_of_bruhat
    (hcover : ∀ g : Model 0, ∃ u ∈ unipotent 0,
      ∃ n ∈ Binary.FixedGeometry.weylSubgroup 0,
        ∃ v ∈ unipotent 0, g = u * n * v)
    (hsep : ∀ n ∈ Binary.FixedGeometry.weylSubgroup 0,
      n ∈ normalizer (unipotent 0) → n ∈ unipotent 0) :
    center (Model 0) = ⊥ :=
  binary_center_eq_bot_of_unipotent_normalizer
    (Binary.FixedGeometry.unipotent_normalizer_eq_of_bruhat hcover hsep)

/-- The fixed-root coordinate witnesses discharge Weyl separation, reducing
binary centerlessness to the fixed Bruhat coverage contract. -/
theorem binary_center_eq_bot_of_bruhat_coverage
    (hcover : ∀ g : Model 0, ∃ u ∈ unipotent 0,
      ∃ n ∈ Binary.FixedGeometry.weylSubgroup 0,
        ∃ v ∈ unipotent 0, g = u * n * v) :
    center (Model 0) = ⊥ :=
  binary_center_eq_bot_of_bruhat hcover Binary.FixedGeometry.WeylSeparation.weyl_mem_unipotent

/-- The center of the actual full binary Ree fixed matrix group is trivial.
The proved binary Bruhat geometry supplies self-normalization, and the
concrete fixed opposition eliminates every central positive element. -/
theorem binary_center_eq_bot : center (Model 0) = ⊥ :=
  binary_center_eq_bot_of_unipotent_normalizer Binary.FixedGeometry.unipotent_normalizer_eq

end ReeF4.Parabolics.OuterLocal
