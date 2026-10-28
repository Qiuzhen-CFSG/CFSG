module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.SourceSetup
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelCases
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.TorusControl
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection.Transport
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.RankTwoField.ComponentBorels
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.RankTwoField.Symplectic
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.RankTwoField.G2
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage

/-!
# The nonbinary rank-two branches of the source Borel argument

All T-conjugate star components enter the commuting-product construction of
the component Sylow normalizer. The source's Borel control makes that normalizer
prime to three and makes Y₀* act trivially on its torus quotient. The concrete
rank-two torus kernels make the action inner; generation of Y₀* by elements of
order three makes it trivial, contradicting L* = [L*,Y₀*].

Both exclusions use proved perfectness to identify the derived carriers with
the full groups. The symplectic calculation includes graph-field actors; the
G₂ calculation uses the proved coverage of all abstract automorphisms by the
actual inner-field homomorphism. The conditional G₂ interface is retained,
and `g2_exclusion` discharges its coverage premise.

Source: Aschbacher–Smith, `refs/quasithin.pdf`, printed p.1144, proof of
15.3.49(k), with the component alternatives of B.4.2(3–4) and B.5.6.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.RankTwoField

universe u
variable {G : Type u} [Group G] [Finite G]
variable {κ : GroupClass.{u}} {H M Y V Y0 L ZS Z A : Subgroup G}
    {T : Sylow 2 G} [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : SourceSetup κ H M Y V Y0 L ZS Z A T)

include d

/-- The whole conjugate-component product supplies the local Borel embeddings. -/
theorem exclusion_of_torusRigid [Group.IsSolvable (relativeBorel L T)]
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (hout : ¬ Y0 ≤ localSpan L T) (hrigid : TorusRigid (starImage H L)) : False := by
  obtain ⟨c⟩ := exists_componentBorel d hq
  exact exclusion_of_componentBorel d hout c hrigid

/-- No nonbinary derived Sp₄ model satisfies source noncontainment and Borel control. -/
theorem symplectic_exclusion [Group.IsSolvable (relativeBorel L T)]
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (hout : ¬ Y0 ≤ localSpan L T)
    {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (e : starImage H L ≃* commutator (Matrix.symplecticGroup (Fin 2) F)) : False :=
  exclusion_of_torusRigid d hq hout ((derived_symplectic_torusRigid hF hn).of_equiv e)

/-- The G₂ source branch, conditional only on the separately owned inner-field coverage theorem. -/
theorem g2_exclusion_of_coverage [Group.IsSolvable (relativeBorel L T)]
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (hout : ¬ Y0 ≤ localSpan L T)
    {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (e : starImage H L ≃* commutator (Atlas.G2.Model F))
    (hcover : Function.Surjective (Atlas.G2.LieAutomorphismExtensions.semilinearAction
      (F := F))) : False := by
  let _ := Fintype.ofFinite F
  let _ : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hcard : 2 < Nat.card F := by
    rw [hF]
    exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) hn
  exact exclusion_of_torusRigid d hq hout
    ((derived_g2_torusRigid_of_coverage hcard hcover).of_equiv e)

/-- No nonbinary derived G₂ model satisfies source noncontainment and Borel control. -/
theorem g2_exclusion [Group.IsSolvable (relativeBorel L T)]
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (hout : ¬ Y0 ≤ localSpan L T)
    {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (e : starImage H L ≃* commutator (Atlas.G2.Model F)) : False := by
  let _ := Fintype.ofFinite F
  let _ : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hcard : 2 < Nat.card F := by
    rw [hF]
    exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) hn
  exact g2_exclusion_of_coverage d hq hout hF hn e
    (Atlas.G2.LieAutomorphismExtensions.semilinearAction_surjective hcard)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.RankTwoField
