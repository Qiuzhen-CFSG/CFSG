module
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups.Covers
public import Theory.SpecificGroups.BinaryLinear.OrderedResidualConjugators.CubicResidual

/-!
# Cubic generation in binary linear Sylow overgroups

Every overgroup of a full binary Sylow two-subgroup is a partial flag
stabilizer. Each omitted cut contributes a minimal parabolic, whose
prime-to-three residual supplements the full flag stabilizer. Applying
flag containment to the join of these residuals and the original Sylow
shows that it is the whole overgroup. Consequently O² and O^{3′} agree.

This calculation uses the literal Sylow and subgroup inclusions. Its
application to the two-core quotient of the selected component excludes
the binary linear rows at prime five in Aschbacher--Smith 15.1.23,
printed p.1100, using the parabolics of 15.1.22, pp.1099--1100.
-/

public section
open Subgroup
namespace BinaryLinear.SylowFlagOvergroups
open OuterCyclic InvariantNodeActions OrderedResidualConjugators
variable {m : ℕ}

/-- The original Sylow supplements the embedded prime-to-three residual. -/
theorem cubic_supplement
    (S : Sylow 2 (LinearGroup (m+1))) (H : Subgroup (LinearGroup (m+1)))
    (hSH : (S : Subgroup _) ≤ H) :
    H = (primeToResidual 3 H).map H.subtype ⊔ (S : Subgroup _) := by
  let : Finite (LinearGroup (m+1)) := Finite.of_injective
    (fun g : LinearGroup (m+1) => (g : Space (m+1) → Space (m+1))) DFunLike.coe_injective
  let R := (primeToResidual 3 H).map H.subtype
  let K := R ⊔ (S : Subgroup _)
  have hKH : K ≤ H := sup_le (map_subtype_le _) hSH
  obtain ⟨b,cuts,hS,hH⟩ := exists_flag_of_sylow_le S H hSH
  obtain ⟨cutsK,hK⟩ := overgroup_eq_cutStabilizer S b hS K le_sup_right
  have he : cutsK = cuts := by
    apply Set.Subset.antisymm _ ((cutStabilizer_le_iff b _ _).mp (hK.symm.le.trans (hKH.trans hH.le)))
    intro i hi
    by_contra hin
    have hPH : minimalParabolic b i ≤ H := by
      rw [hH]
      exact (cutStabilizer_le_iff b _ _).mpr (fun j hj hji => hin (hji ▸ hj))
    have hPK : minimalParabolic b i ≤ K := by
      rw [minimalParabolic_cubic_supplement]
      exact sup_le ((embedded_primeToResidual_mono 3 hPH).trans le_sup_left)
        (hS ▸ le_sup_right)
    have hh := (cutStabilizer_le_iff b _ _).mp (hPK.trans hK.le) hi
    exact hh (Set.mem_singleton i)
  exact hH.trans ((congrArg (cutStabilizer b) he).symm.trans hK.symm)

/-- The two-residual of a binary linear Sylow overgroup is its cubic residual. -/
theorem twoResidual_eq_cubic
    (S : Sylow 2 (LinearGroup (m+1))) (H : Subgroup (LinearGroup (m+1)))
    (hSH : (S : Subgroup _) ≤ H) : pResidual 2 H = primeToResidual 3 H := by
  let : Finite (LinearGroup (m+1)) := Finite.of_injective
    (fun g : LinearGroup (m+1) => (g : Space (m+1) → Space (m+1))) DFunLike.coe_injective
  have hs : primeToResidual 3 H ⊔ (S : Subgroup _).subgroupOf H = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hSH,
      ←MonoidHom.range_eq_map,range_subtype]
    exact (cubic_supplement S H hSH).symm
  have hSp : IsPGroup 2 ((S : Subgroup (LinearGroup (m+1))).subgroupOf H) :=
    S.isPGroup'.comap_subtype
  have hp : IsPGroup 2 (H ⧸ primeToResidual 3 H) :=
    isPGroup_quotient_of_sup_eq_top (primeToResidual 3 H)
      ((S : Subgroup (LinearGroup (m+1))).subgroupOf H) hSp hs
  exact le_antisymm (sInf_le ⟨inferInstance,hp⟩) primeToResidual_three_le_twoResidual
end BinaryLinear.SylowFlagOvergroups
