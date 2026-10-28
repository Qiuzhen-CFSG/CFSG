module
public import CFSG.Quasithin.Chapter14.Section02.ExceptionalDiagram.Nonabelian
public import CFSG.Quasithin.Chapter14.Section02.ExceptionalPSL3FourAbelian


/-!
# The exceptional PSL₃(4) source13 branch

For the original selected outside subgroup and component, split on whether
the actual span of V under Mc is abelian. In the abelian case the placed
quadratic actor survives on a component-irreducible section, contradicting
the PSL₃(4) quadratic bound. In the nonabelian case the actual two-core
has elementary inner image, so it lies in the marked parabolic normalizer.

The only additional action data are the preceding source12 PSL₃(4)
action and its normalizer transport for the selected parabolic residual.
The original local module, Sylow subgroup, component quotient and ambient
hypotheses are retained. No FF-module or universal section premise occurs.
Source: Aschbacher–Smith, Lemma 14.2.13, printed p.984.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.ExceptionalDiagram
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The complete exceptional source13 branch on the original local module,
component quotient and marked parabolic action from source12. -/
theorem source_exceptional_twoCore_le_of_marked_action
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K : Subgroup H) (hK : K.IsCComponent) (hn : K.Normal)
    (hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (ρ : Mc →* MulAut Matrix.PSL3Four.PSL)
    (hinner : MulAut.innerSubgroup Matrix.PSL3Four.PSL ≤ ρ.range)
    (hswap : ∃ t : Mc, (t : G) ∈ (T : Subgroup G) ∧
      Matrix.PSL3.LinearThree.OuterExtensions.diagramAction Matrix.PSL3Four.F
        (n := 2) (by decide) (by simpa using Matrix.PSL3Four.card_F) (ρ t) ≠ 1)
    (K₁ : Subgroup G)
    (hplace : (T : Subgroup G) ⊓
        ((MulAut.innerSubgroup Matrix.PSL3Four.PSL).comap ρ).map Mc.subtype ≤
      (T : Subgroup G) ⊓ normalizer (K₁ : Set G)) :
    (sourceResidual M Mc).pCoreIn 2 ≤ (T : Subgroup G) ⊓ normalizer (K₁ : Set G) := by
  by_cases hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc)
  · exact (source_abelian_psl3Four_false hG T hempty hM hu hmany hcard e
      H hH hab K hK hn hgen hm).elim
  · have hTMc : (T : Subgroup G) ≤ Mc := by
      have hc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
        hu ▸ Set.mem_singleton Mc
      exact (le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T)).trans hc.2
    exact source_nonabelian_twoCore_le_of_marked_action hG T hempty hM hu hmany hcard e
      hab hTMc ρ hinner hswap K₁ hplace

end CFSG.Quasithin.Chapter14.Section02.ExceptionalDiagram
