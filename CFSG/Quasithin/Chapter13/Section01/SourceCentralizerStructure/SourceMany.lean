module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents.LinearThree
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.SourceMany

/-!
# Original centralizer source applications with the standing guard supplied

The actual multiple-overgroup hypothesis supplies every outside-local guard
needed to select the maximal nonquasisimple faithful overgroup. Apply the
existing centralizer-structure theorem to that same selected group, retaining
its literal involution, odd radical, action and full centralizer. The selected
group's normalization also supplies the marked linear-three unipotent
exclusion used in the later component analysis.

These applications require no global unguarded 3.1.8 assertion. The original
orbit and component markings remain explicit for their source producers;
the full 13.1.7 nonquasisimple exclusion is a separate argument.

Source: Aschbacher--Smith 13.1.4, 13.1.12 and the opening of 13.3.2,
printed pp.867--868,873--875,884, under the standing assumption after 2.1.1.
-/

public noncomputable section
open scoped MatrixGroups
open Subgroup Theory.GroupTheory
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions Matrix.PSL3Even.UnipotentGeometry
namespace CFSG.Quasithin.Chapter14.Section03.FaithfulSource
open Chapter1 Chapter1.XiEmbedding Chapter12.Section02 Chapter13.Section01
open Chapter13.Section01.SourceCentralizerComponents
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L₀ : Subgroup G}

/-- The original multiple-overgroup branch supplies the actual maximal
counterexample and its literal centralizer-structure alternative. -/
theorem Hypothesis1331.nonquasisimple_centralizer_structure_of_many
    (h : Hypothesis1331 T L₀)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn0 : ¬ IsQuasisimple (XiQuotient L₀)) :
    ∃ L ∈ LStar G T, L₀ ≤ L ∧ FaithfulMaximalLocal T L ∧
      L ∈ nonquasisimpleFaithful T ∧
      ∀ {p : ℕ} [Fact p.Prime]
        (_ho : Odd p) (_hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
        (u : G) (_hu : orderOf u = 2)
        (_hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
          (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)))
        (_hindex : ((centralizer ({u} : Set G)).subgroupOf (T : Subgroup G)).index ≤ 2)
        (_hcentral : ∀ g : G,
          (T : Subgroup G) ≤ centralizer ({g * u * g⁻¹} : Set G) →
            centralizer ({g * u * g⁻¹} : Set G) ≤ normalizer (L : Set G))
        (_hXMu : XiP p L ≤ normalizer (L : Set G) ⊓ centralizer ({u} : Set G))
        (_hirr : ∀ A : Subgroup (XiFrattiniQuotient (XiP p L)),
          (∀ s : (normalizer (L : Set G) ⊓ centralizer ({u} : Set G) : Subgroup G),
            ∀ a ∈ A, xiFrattiniAction
              (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) (XiP p L)
              (XiP_invariant p inf_le_left) s a ∈ A) → A = ⊥ ∨ A = ⊤)
        (z : G) (_hz : orderOf z = 2) (_hzT : z ∈ (T : Subgroup G))
        (_hzcentral : ∀ t ∈ (T : Subgroup G), t * z = z * t)
        (_hCz : centralizer ({z} : Set G) ≤ normalizer (L : Set G)),
        (twoFittingCore (centralizer ({u} : Set G))).map
            (centralizer ({u} : Set G)).subtype ≤
              normalizer (L : Set G) ⊓ centralizer ({u} : Set G) ∧
          pPrimeCore 2 (centralizer ({u} : Set G)) = ⊥ ∧
          (centralizer ({u} : Set G) ≤ normalizer (L : Set G) ∨
            ∃ K : Subgroup G, K ∈ cComponentsIn (centralizer ({u} : Set G)) ∧
              IsQuasisimple (XiQuotient K) ∧
                ¬ ⁅K,XiP p L⁆ ≤ (centralizer ({u} : Set G)).pCoreIn 2 ∧
                  XiP p L ≤ normalizer (K : Set G) ∧ ⁅K,XiP p L⁆ = K ∧
                    ¬ K ≤ normalizer (XiP p L : Set G)) := by
  obtain ⟨L,hL,hL0,hf,hn,hmax,hjoin,huniq,_⟩ :=
    h.maximal_counterexample_of_many hmany hn0
  refine ⟨L,hL,hL0,hf,hn,?_⟩
  intro p hp ho hd u hu hlocal hindex hcentral hXMu hirr z hz hzT hzcentral hCz
  exact source_centralizer_structure h.qtke T hL hn.2 ho hd u hu
    (le_sup_right.trans hjoin) hlocal hindex hcentral hXMu hirr z hz hzT hzcentral hCz


/-- The same original maximal counterexample excludes the marked PSL₃
full-unipotent row using the guarded source selection above. -/
theorem Hypothesis1331.nonquasisimple_linearThree_unipotent_exclusion_of_many
    (h : Hypothesis1331 T L₀)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn0 : ¬ IsQuasisimple (XiQuotient L₀)) :
    ∃ L ∈ LStar G T, L₀ ≤ L ∧ FaithfulMaximalLocal T L ∧
      L ∈ nonquasisimpleFaithful T ∧
      ∀ {p : ℕ} [Fact p.Prime]
        (_ho : Odd p) (_hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
        (u : G)
        (_hXMu : XiP p L ≤ normalizer (L : Set G) ⊓ centralizer ({u} : Set G))
        (_hirr : ∀ A : Subgroup (XiFrattiniQuotient (XiP p L)),
          (∀ s : (normalizer (L : Set G) ⊓ centralizer ({u} : Set G) : Subgroup G),
            ∀ a ∈ A, xiFrattiniAction
              (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) (XiP p L)
              (XiP_invariant p inf_le_left) s a ∈ A) → A = ⊥ ∨ A = ⊤)
        (F : Type*) [Field F] [Finite F] [CharP F 2]
        {n : ℕ} (_hF : Nat.card F = 2 ^ n)
        (K : Subgroup G) (_hXK : XiP p L ≤ K) (e : K ≃* PSL(3,F)),
        (((XiP p L).pCoreIn 2).subgroupOf K).map e.toMonoidHom ≠ unipotent F := by
  obtain ⟨L,hL,hL0,hf,hn,_⟩ := h.nonquasisimple_centralizer_structure_of_many hmany hn0
  refine ⟨L,hL,hL0,hf,hn,?_⟩
  intro p hp ho hd u hXMu hirr F hField hFinite hChar n hF K hXK e hA
  exact source_centralizer_linearThree_unipotent_row_excluded h.qtke T hL hn.2 ho hd
    u hXMu hirr F hF K hXK e hA


end CFSG.Quasithin.Chapter14.Section03.FaithfulSource
