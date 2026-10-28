module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Ree.TitsMarked
public import CFSG.Quasithin.Chapter1.Section01
public import Theory.GroupTheory.PCoreOvergroup
public import Theory.Quasithin.EvenCharacteristic

/-!
# The first marked Tits local overgroup belongs to He(S)

A projection-compatible marking puts the first overgroup in H ∩ M.
It contains the supplied Sylow subgroup S, so the self-centralizing-core
property of H ∩ M passes to it. Its core is nontrivial: otherwise the
self-centralizing-core property would make the overgroup trivial, although
it contains the involution z. This proves every clause of HeOver.

No first-parabolic core order or quotient identification is used. The same
argument works when S permutes components. Source: Aschbacher–Smith A.1.6
and the local-overgroup argument for 2.3.9(7), printed p.526.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Ree
open Subgroup
variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

private theorem mem_HeOver_of_intersection
    (h : LocalSetup H L M S z) (K : Subgroup G)
    (hSK : (S : Subgroup H).map H.subtype ≤ K) (hKH : K ≤ H) (hKM : K ≤ M) :
    K ∈ Chapter1.HeOver G (((S : Subgroup H).map H.subtype : Subgroup G) : Set G) := by
  let f : ↥(H ⊓ M) →* H := Subgroup.inclusion inf_le_left
  have hf : (S : Subgroup H) ≤ f.range := by
    intro x hx
    refine ⟨⟨(x : G), x.property, h.sylow_le ⟨x, hx, rfl⟩⟩, ?_⟩
    rfl
  let T : Sylow 2 ↥(H ⊓ M) := S.comapOfInjective f (Subgroup.inclusion_injective _) hf
  have hTK : (T : Subgroup ↥(H ⊓ M)) ≤ K.subgroupOf (H ⊓ M) := by
    intro x hx
    exact hSK ⟨f x, hx, rfl⟩
  have hc := centralizer_pCore_le_of_sylow_le T (K.subgroupOf (H ⊓ M)) hTK
    (Chapter1.mem_He_iff.mp h.local_even)
  have hke : K ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr
    ((Theory.Quasithin.centralizer_pCore_le_iff 2
      (subgroupOfEquivOfLe (le_inf hKH hKM))).mp hc)
  refine ⟨hke, ?_, hSK⟩
  intro hk
  have hzero : K ≤ ⊥ := by
    have he : K ⊓ centralizer (K.pCoreIn 2 : Set G) ≤ K.pCoreIn 2 := hke
    rw [hk] at he
    intro x hx
    apply he
    refine ⟨hx, ?_⟩
    intro y hy
    change y = 1 at hy
    simp only [hy, one_mul, mul_one]
  have hz1 : z = 1 := mem_bot.mp (hzero (hSK h.mem_sylow))
  have hz2 := h.involution
  rw [hz1, orderOf_one] at hz2
  exact (by decide : (1 : ℕ) ≠ 2) hz2

/-- Genuine HeOver membership, including a nontrivial two-core. -/
theorem titsFirstOver_mem_HeOver
    (h : LocalSetup H L M S z) (e : L ≃* Tits.ParrottGroup)
    (hproj : IsConjugationProjection L z ((titsAtlasEquiv e).symm Tits.atlas1600R5)) :
    (titsFirst e).map L.subtype ⊔ (S : Subgroup H).map H.subtype ∈
      Chapter1.HeOver G (((S : Subgroup H).map H.subtype : Subgroup G) : Set G) := by
  apply mem_HeOver_of_intersection h _ le_sup_right
  · exact sup_le ((map_subtype_le _).trans h.component_le) (map_subtype_le _)
  · exact titsFirstOver_le_of_projection h e hproj
end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Ree

end
