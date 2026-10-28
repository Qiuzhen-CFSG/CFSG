module
public import Theory.GroupTheory.PResidual.NormalizerImage
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual

/-!
# Residuals of Sylow overgroups above an abelian residual

If the p-residual is abelian, the p-residual of a Sylow overgroup is normal:
the ambient residual centralizes it and the Sylow subgroup normalizes it.
The assertion lifts through a p-group kernel, which lies in the given Sylow
and hence normalizes the original residual. In particular this applies to
any two-group extension of S₃ × S₃.

Source application: Aschbacher--Smith, 10.2.9, printed p.753, normalization
of O²(P) by a nonadjacent rank-one parabolic. This concerns the two-residual,
not the two-core.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]

/-- The residual and Sylow supplement normalize the smaller residual. -/
theorem residual_normal_of_abelian_residual {p : ℕ} [Fact p.Prime]
    [IsMulCommutative (pResidual p G)] (S : Sylow p G) (P : Subgroup G)
    (hSP : (S : Subgroup G) ≤ P) : ((pResidual p P).map P.subtype).Normal := by
  let R := (pResidual p P).map P.subtype
  have hR : R ≤ pResidual p G := map_pResidual_le p P.subtype
  have hPR : P ≤ normalizer (R : Set G) :=
    P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pResidual p P))
  have hc : pResidual p G ≤ centralizer (R : Set G) := by
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm (⟨y,hR hy⟩ : pResidual p G) ⟨x,hx⟩)
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← pResidual_sup_sylow_eq_top S]
  exact sup_le (hc.trans (centralizer_le_normalizer _)) (hSP.trans hPR)

/-- A normalizing p-group kernel preserves this relative residual normality. -/
theorem residual_normal_of_p_kernel_abelian_residual {p : ℕ} [Fact p.Prime]
    [IsMulCommutative (pResidual p Q)] (f : G →* Q) (hf : Function.Surjective f)
    (hk : IsPGroup p f.ker) (S : Sylow p G) (P : Subgroup G)
    (hSP : (S : Subgroup G) ≤ P) : ((pResidual p P).map P.subtype).Normal := by
  let R := (pResidual p P).map P.subtype
  have hPR : P ≤ normalizer (R : Set G) :=
    P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pResidual p P))
  have him : (R.map f).Normal := by
    change (((pResidual p P).map P.subtype).map f).Normal
    rw [map_embedded_pResidual]
    exact residual_normal_of_abelian_residual (S.mapSurjective hf) (P.map f) (map_mono hSP)
  have he := comap_normalizer_map_of_pPerfect f R (isPPerfect_embedded_pResidual p P)
    hk ((hk.le_sylow_of_normal S).trans (hSP.trans hPR))
  rw [normalizer_eq_top, comap_top] at he
  exact normalizer_eq_top_iff.mp he.symm

/-- The concrete two-node Levi quotient gives normality in its full preimage. -/
theorem residual_normal_of_symmetricThreePair
    (f : G →* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (S : Sylow 2 G) (P : Subgroup G)
    (hSP : (S : Subgroup G) ≤ P) : ((pResidual 2 P).map P.subtype).Normal := by
  let : IsMulCommutative (pResidual 2 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq
      (p := 3) SymmetricThreeProductResidual.residual_card
  exact residual_normal_of_p_kernel_abelian_residual f hf hk S P hSP
end Subgroup
