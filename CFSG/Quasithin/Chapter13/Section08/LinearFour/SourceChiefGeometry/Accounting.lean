module

public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.Quotient
public import Theory.GroupTheory.NoncentralChiefRefinement.FourStrata
public import Theory.GroupTheory.NoncentralChiefRefinement.SingleSmallRestriction

/-!
# Six surrounding factors and the remaining three in 13.8.31

The marked filtrations describe actual normal sections of L₀, allowing
central strata and with total multiplicities 1, 2, 1, 2. Their endpoints are the literal intersections
with V₁, U_H, V_H, H_C and Q_H; R is the preimage of the two-core of L₀*.
The terminal quotient has no two-chief factors. The refinement theorem
constructs the surrounding six factors and compares with a complete series.
Thus the nine-factor lower bound leaves at least three in H_C/V_H.

Constructing these marked restrictions from the natural, dual and orthogonal
modules is an outstanding source input. The cardinalities 1, 2, 1, 2 here
are sums of coordinates in supplied equivariant quotient isomorphisms,
not assumed counts of chief factors.

Source: Aschbacher–Smith, 13.8.31(3), printed p.965.
-/

public section
open Subgroup Representation NoncentralChiefRefinement
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G : Type*} [Group G] [Finite G]

/-- The actual L₀-chief sections surrounding H_C/V_H leave at least three
noncentral factors in that interval. No six-factor numerical premise is used. -/
theorem source_three_factors_of_marked_strata
    {W₁ W₂ W₃ W₄ : Type*}
    [AddCommGroup W₁] [Module (ZMod 2) W₁]
    [AddCommGroup W₂] [Module (ZMod 2) W₂]
    [AddCommGroup W₃] [Module (ZMod 2) W₃]
    [AddCommGroup W₄] [Module (ZMod 2) W₄]
    (L₀ V1 UH VH HC QH : Subgroup G)
    (Z U V C Q R : NormalNode L₀)
    (_hZdef : Z.val = V1.subgroupOf L₀) (_hUdef : U.val = UH.subgroupOf L₀)
    (hVdef : V.val = VH.subgroupOf L₀) (hCdef : C.val = HC.subgroupOf L₀)
    (_hQdef : Q.val = QH.subgroupOf L₀)
    (hZ : IsCentral ⊥ Z) (hterminal : HasNoTwoChiefFactors (L₀ ⧸ R.val))
    (ρ₁ : Representation (ZMod 2) L₀ W₁) [IsIrreducible ρ₁]
    (ρ₂ : Representation (ZMod 2) L₀ W₂) [IsIrreducible ρ₂]
    (ρ₃ : Representation (ZMod 2) L₀ W₃) [IsIrreducible ρ₃]
    (ρ₄ : Representation (ZMod 2) L₀ W₄) [IsIrreducible ρ₄]
    (c₁ : MarkedInterval Z U ρ₁ 1) (c₂ : MarkedInterval U V ρ₂ 2)
    (c₃ : MarkedInterval C Q ρ₃ 1) (c₄ : MarkedInterval Q R ρ₄ 2)
    (hn₁ : ∃ k v, ρ₁ k v ≠ v) (hn₂ : ∃ k v, ρ₂ k v ≠ v)
    (hn₃ : ∃ k v, ρ₃ k v ≠ v) (hn₄ : ∃ k v, ρ₄ k v ≠ v)
    (hnine : ∀ t : ChiefSeries L₀, t.head = ⊥ → t.last = ⊤ →
      9 ≤ t.noncentralTwoCount)
    (s : ChiefSeries L₀)
    (hs0 : s.head.val = VH.subgroupOf L₀) (hs1 : s.last.val = HC.subgroupOf L₀) :
    3 ≤ s.noncentralTwoCount := by
  obtain ⟨t, ht0, ht1⟩ := exists_chiefSeries (⊥ : NormalNode L₀) ⊤ bot_le
  have he := complete_count_of_four_strata Z U V C Q R
    hZ hterminal ρ₁ ρ₂ ρ₃ ρ₄ 1 2 1 2 c₁ c₂ c₃ c₄ hn₁ hn₂ hn₃ hn₄ s
    (Subtype.ext (hs0.trans hVdef.symm)) (Subtype.ext (hs1.trans hCdef.symm)) t ht0 ht1
  have hn := hnine t ht0 ht1
  omega

/-- If the restricted interval has three noncentral factors, the actual
component K cannot centralize H_C/V_H. The subgroup inclusion retains the
original ambient action of L₀. -/
theorem source_component_moves_of_three_factors
    (L₀ K VH HC : Subgroup G) (hLK : L₀ ≤ K)
    (V C : NormalNode L₀)
    (hVdef : V.val = VH.subgroupOf L₀) (hCdef : C.val = HC.subgroupOf L₀)
    (hVC : VH ≤ HC)
    (hthree : ∀ s : ChiefSeries L₀, s.head = V → s.last = C →
      3 ≤ s.noncentralTwoCount) : ¬ ⁅HC, K⁆ ≤ VH := by
  intro hm
  have hVC' : V ≤ C := by
    change V.val ≤ C.val
    rw [hVdef, hCdef]
    exact subgroupOf_mono L₀ hVC
  obtain ⟨s, hs0, hs1⟩ := exists_chiefSeries V C hVC'
  have hc : IsCentral V C := by
    rw [isCentral_iff_commutator_le, commutator_le]
    intro x _ y hy
    rw [hCdef] at hy
    rw [hVdef]
    change ⁅(x : G), (y : G)⁆ ∈ VH
    rw [commutator_comm HC K] at hm
    exact hm (commutator_mem_commutator (hLK x.property) hy)
  have hz := s.noncentralTwoCount_eq_zero_of_central (by rwa [hs0, hs1])
  have hn := hthree s hs0 hs1
  omega

/-- Three factors on the literal intersection with L₀ rule out a unique
noncentral K-factor of binary dimension four. Restricting a section of
order sixteen can contribute at most two noncentral factors, so no further
four-dimensional model classification is needed for this obstruction. -/
theorem source_no_unique_four_of_restricted_three
    (H : Subgroup G) (K L₀ : Subgroup H) (hLK : L₀ ≤ K)
    (V C : NormalNode H)
    (hthree : ∀ t : ChiefSeries L₀,
      t.head = restrictNormalNode L₀ V → t.last = restrictNormalNode L₀ C →
      3 ≤ t.noncentralTwoCount)
    (s : ChiefSeries H) (hs0 : s.head = V) (hs1 : s.last = C)
    (hone : s.restrictedNoncentralCount K = 1) (i : Fin s.length)
    (hi : ¬ ∀ k : K, ∀ x, sectionAction (s i.castSucc) (s i.succ) k x = x) :
    Nat.card (Section (s i.castSucc) (s i.succ)) ≠ 16 := by
  intro hc
  have hVC : V ≤ C := by
    rw [← hs0, ← hs1]
    exact CompositionSeries.head_le _
  obtain ⟨t, ht0, ht1⟩ := exists_chiefSeries (restrictNormalNode L₀ V)
    (restrictNormalNode L₀ C) (restrictNormalNode_monotone L₀ hVC)
  have hb := s.restriction_count_le_two_of_unique K L₀ hLK hone i hi hc t
    (ht0.trans (congrArg (restrictNormalNode L₀) hs0.symm))
    (ht1.trans (congrArg (restrictNormalNode L₀) hs1.symm))
  have hn := hthree t ht0 ht1
  omega

end CFSG.Quasithin.Chapter13.Section08.LinearFour
