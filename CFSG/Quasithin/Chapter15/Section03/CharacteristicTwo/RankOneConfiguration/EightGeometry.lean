module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Basic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.ConjugatePair
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Quotient
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.LocalControl
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.CentralInvolution
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.Residual
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.CoreGeneration
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ParabolicCoreAction

/-!
# Degree-eight geometry for the characteristic-two branch

The group-theoretic reductions establish `T`-invariance of the residual
overgroup `XS`, put a compatible component module in `S`, exclude an
invariant local two-core, and deduce core generation from the irreducible
parabolic action. The common quotient has the actual denominator `C_S(W)`.

The six conclusions of 15.3.32 are not yet assembled. The compatible
natural-eight action, the fixed-line and fixed-plane calculations, the
residual-centralizer identification of `L`, and the marked end-node parabolic
remain to be constructed. The concrete four-block stabilizer has irreducible
two-core action, which transports through the marked identification.
The conditional theorems below do not assert the remaining premises.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.32, printed pp.1132–1133.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry

open Subgroup

variable {G : Type*} [Group G]

/-- The conjugate-pair conclusion, with module containment and `XS`
invariance and central-involution avoidance derived from the source definitions,
orthogonal action and line-centralizer result.
The natural action and fixed-plane geometry still need to be supplied. -/
theorem lemma_15_3_32_5_of_fixed_plane [Finite G]
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I)
    (a : NaturalEightAction I (d.componentModule I c.L))
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hZ : Nat.card d.Z = 2)
    (hL : c.L = RankOne.threeResidualIn
      (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)))
    (hfixed : d.ZS ⊓ d.componentModule I c.L = d.ZS ⊓ d.V₂)
    (t : G) (ht : t ∈ (d.T : Subgroup G)) (htS : t ∉ d.S) :
    let U := d.componentModule I c.L
    let N := RankOne.threeResidualIn (centralizer (d.ZS : Set G)) ⊔ d.S
    Disjoint U (U.conjBy t) ∧
      N ≤ normalizer ((U ⊔ U.conjBy t : Subgroup G) : Set G) ∧
      U ≤ centralizer (U.conjBy t : Set G) ∧
      ∃ e : U × U.conjBy t ≃* ↥(U ⊔ U.conjBy t),
        ∀ u v, (e (u, v) : G) = (u : G) * (v : G) :=
  lemma_15_3_32_5_of_geometry d c a (componentModule_le_sylow d hI c a P hP)
    le_sup_right (residual_join_le_of_line_centralizer d hI c hL)
    (residual_join_normalized_by_sylow d hindex) hindex hZ
    (centralInvolutions_not_le_plane d hindex hZ _) hfixed t ht htS

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry

end
