module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSetup
public import Theory.GroupTheory.ComponentLocalOrbitEmbedding
public import Theory.GroupTheory.SylowSubnormalIntersection

/-! A characteristic-two subgroup of a component, stable under the relevant
Sylow normalizer, generates a characteristic-two group together with the full
Sylow. When Γ-even-zero is empty, the original 2.5.1 overgroup theorem places
that group in M. Components may be permuted by the Sylow.
Source: Aschbacher--Smith 2.5.1--2.5.2, printed pp.550--551. -/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M H L K : Subgroup G}

/-- Original 2.5.1 forces every Sylow-stable characteristic-two local
subgroup of an actual component into M. The full Sylow may permute components. -/
theorem component_invariant_local_le
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (S : Sylow 2 H) (hSM : (S : Subgroup H).map H.subtype ≤ M)
    (hL : IsComponent H (L.subgroupOf H)) (hLH : L ≤ H)
    (hKL : K ≤ L) (hK : K ∈ Chapter1.He G)
    (hinv : (S : Subgroup H).map H.subtype ⊓ normalizer (L : Set G) ≤
      normalizer (K : Set G)) : K ≤ M := by
  let A := (S : Subgroup H).map H.subtype
  let X := K ⊔ A
  have hXe : X ∈ Chapter1.He G := hL.relative_local_adjoin_centralizer hLH hKL
    (map_subtype_le _) (S.isPGroup'.map _) hinv hK
  have hXcore : twoCore X ≠ ⊥ := by
    intro hb
    have hXB : X = ⊥ := by
      apply bot_unique
      intro x hx
      have hxc : X ⊓ centralizer (twoCore X : Set G) ≤ twoCore X := hXe
      rw [hb] at hxc
      apply hxc
      refine ⟨hx,?_⟩
      intro y hy
      rw [show y = 1 from hy]
      simp
    have hcoreH := (hH.elim (fun h => h.1.1) (fun h => h.1)).1
    exact hcoreH (bot_unique (hXB ▸ (pCoreIn_le_sylow H S).trans
      (show A ≤ X from le_sup_right)))
  obtain ⟨R,hR⟩ := sylow_image_in_inf S hSM
  have hXM : X ≤ M := heOver_le_of_empty hH hempty R
    (hR.symm ▸ (show X ∈ Chapter1.HeOver G (A : Set G) from
      ⟨hXe,hXcore,fun _ hx => (show A ≤ X from le_sup_right) hx⟩))
  exact le_sup_left.trans hXM

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
