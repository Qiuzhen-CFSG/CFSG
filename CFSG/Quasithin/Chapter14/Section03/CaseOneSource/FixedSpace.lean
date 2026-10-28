module

public import CFSG.Quasithin.Chapter14.Section03.CaseOneSource.Naturality
public import CFSG.Quasithin.Chapter12.Section04
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeFusion

/-!
# The final L₃(2) fixed-space contradiction of 12.4.2

The original fusion branch supplies a fixed involution z, weakly closed in
V, with C_G(z) contained in N_G(V). Independently, 12.4.1 and 12.4.8 supply
a noncommuting conjugate, and B.4.8 supplies the symmetric commutator plane
containing C_V(L). Its invariance under the conjugator puts the conjugate
of z back in V. Fusion therefore forces that conjugator to normalize V,
contradicting the nontrivial commutator.

The two source implications remain explicit and have distinct producers:
qt-d-1242-l3-fusion-source and qt-d-1242-l3-commutator-source. This final
assembly retains their discharge with qt-d-1434-source. Neither implication
assumes the desired fixed-space vanishing or naturality.

Source: Aschbacher–Smith, 12.4.1, 12.4.5–9 and the final proof of 12.4.2,
printed pp.812–816. Only the L₃(2) branch is used here.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section03.CaseOneSource
open Chapter12.Section02 Chapter12.Section04 Chapter12.Section04.SmallFusion
universe u

/-- The source 12.4.7 fixed-involution output for the original L₃(2) row.
Weak closure is asserted in V, not in the whole Sylow subgroup. -/
def SLThreeFusion1247 : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (S : Sylow 2 X) (A W : Subgroup X),
    Hypothesis1223 KnownSimple.IsKnownSimple S A → ChosenModule S A W →
    ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 3 2 → fixedSubgroup A W ≠ ⊥ →
    ∃ z : X, orderOf z = 2 ∧ fixedSubgroup A W = zpowers z ∧
      centralizer ({z} : Set X) ≤ normalizer (W : Set X) ∧
      ∀ g : X, MulAut.conj g z ∈ W → MulAut.conj g z = z

/-- The noncommuting conjugate from 12.4.1/8 and its actual B.4.8
commutator plane. The subgroup and its conjugation map are unchanged. -/
def SLThreeCommutator1242 : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (S : Sylow 2 X) (A W : Subgroup X),
    Hypothesis1223 KnownSimple.IsKnownSimple S A → ChosenModule S A W →
    ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 3 2 → fixedSubgroup A W ≠ ⊥ →
    ∃ g : X,
      W.map (MulAut.conj g).toMonoidHom ≤ normalizer (W : Set X) ∧
      fixedSubgroup A W ≤ ⁅W, W.map (MulAut.conj g).toMonoidHom⁆ ∧
      (⁅W, W.map (MulAut.conj g).toMonoidHom⁆).map (MulAut.conj g).toMonoidHom =
        ⁅W, W.map (MulAut.conj g).toMonoidHom⁆ ∧
      ⁅W, W.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥

/-- The actual final fixed-space contradiction, with the two independent
earlier source branches kept explicit. -/
theorem slThreeFixedSpace1242_of_fusion_and_commutator
    (fusion : SLThreeFusion1247.{u}) (geometry : SLThreeCommutator1242.{u}) :
    SLThreeFixedSpace1242.{u} := by
  intro X _ _ S A W h D hq
  by_contra hne
  let := D.elementary
  obtain ⟨z, _, hz, hc, hf⟩ := fusion X S A W h D hq hne
  obtain ⟨g, hn, hfix, hsymm, hcomm⟩ := geometry X S A W h D hq hne
  have hzf : z ∈ fixedSubgroup A W := hz ▸ mem_zpowers z
  have hA : A ≤ centralizer ({z} : Set X) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (hzf.2 a ha)
  apply hcomm
  apply commutator_eq_bot_of_fusion_and_symmetry hA ?_ hc hn (hfix hzf) hsymm
  intro a ha
  exact ⟨1, A.one_mem, by simpa using hf a ha⟩

/-- The original D naturality input after the final fusion contradiction.
Both independent source branches must still be supplied by their owners. -/
theorem earlier1332CaseOne_of_fusion_sources
    (source1332 : ∀ (X : Type u) [Group X] [Finite X] (S : Sylow 2 X)
      (A : Subgroup X),
      Chapter13.Section08.TransvectionRecognition.Component.ModelExtension.Counterexample S A →
      Chapter13.Section03.Noncentrality.SupercriticalSource.Source1332OneTwo S)
    (marked : SLThreeMarkedQuotient1222.{u})
    (fusion : SLThreeFusion1247.{u}) (geometry : SLThreeCommutator1242.{u}) :
    Earlier1332CaseOne.{u} :=
  earlier1332CaseOne_of_sources source1332 marked
    (slThreeFixedSpace1242_of_fusion_and_commutator fusion geometry)

end CFSG.Quasithin.Chapter14.Section03.CaseOneSource
