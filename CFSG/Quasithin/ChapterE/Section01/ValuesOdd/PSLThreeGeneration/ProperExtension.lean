module

public import CFSG.Quasithin.ChapterE.Section01.Inheritance
public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.Defs
public import Theory.SpecificGroups.PSL3.OddPrimeGraphExtension

/-!
# Proper almost-simple extensions in the linear branch of E.1.14(7)

The intrinsic generalized Fitting subgroup acts faithfully, and the checked
odd-prime automorphism coverage identifies every proper Sylow two-extension
with the actual inner-and-inverse-transpose subgroup of Aut(PSL₃(F)). Thus
there is one concrete graph model to treat, including p=3; no splitting or
chosen outer representative is assumed in the source input.

The assembly below transports strong quasithinness and E-generation along
this genuine equivalence. The two model-generation premises are still proof
obligations. This conditional theorem is not the completed source result.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.14(7), printed p.214, and A.2.3(2), printed p.33; the former cites
Aschbacher, *GF(2)-representations of finite groups* (1982), Lemma 4.11.
-/

public section
open scoped MatrixGroups
open Subgroup Matrix.PSL3.OddPrimeGraphExtension
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension

/-- Source reduction to generation of the literal graph models, separating the
small prime from the remaining prime fields. Both model premises must be
proved before asserting the proper-extension branch of E.1.14(7). -/
theorem isEGenerated_one_of_graph_model_calculations
    (hthree : ∀ (F : Type) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)],
      Nat.card F = 3 → IsStronglyQuasithin (graphExtension F) →
      IsEGenerated 1 (graphExtension F))
    (hlarge : ∀ (F : Type) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]
      (p : ℕ), p.Prime → Odd p → 3 < p → Nat.card F = p →
      IsStronglyQuasithin (graphExtension F) → IsEGenerated 1 (graphExtension F))
    {G : Type*} [Group G] [Finite G] {K : GroupClass} (hG : IsSQTK K G)
    [IsSimpleGroup (Theory.GroupTheory.generalizedFitting G)]
    (T : Sylow 2 G)
    (hgen : Theory.GroupTheory.generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (hproper : Theory.GroupTheory.generalizedFitting G ≠ ⊤)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSL (Theory.GroupTheory.generalizedFitting G) 3 p) :
    IsEGenerated 1 G := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let _ : IsSimpleGroup PSL(3,F) := e.symm.isSimpleGroup
  obtain ⟨f⟩ := exists_mulEquiv_graphExtension T hgen hproper hp ho hF e
  have hs : IsStronglyQuasithin (graphExtension F) := by
    intro r hr hro
    exact (Theory.GroupTheory.primeRank_le_of_injective r f.symm.toMonoidHom
      f.symm.injective).trans (hG.stronglyQuasithin r hr hro)
  apply IsEGenerated.map_equiv (e := f.symm)
  by_cases hp3 : p = 3
  · exact hthree F (hp3 ▸ hF) hs
  · have hgt : 3 < p := by
      have htwo := hp.two_le
      have hp2 : p ≠ 2 := by
        intro h
        exact (by decide : ¬ Odd 2) (h ▸ ho)
      omega
    exact hlarge F p hp ho hgt hF hs

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension
