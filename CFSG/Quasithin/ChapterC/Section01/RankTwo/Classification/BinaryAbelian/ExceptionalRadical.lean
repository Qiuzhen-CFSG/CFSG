module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.Head
public import Theory.AtlasPort.LinearGroups.G2.Order
/-!
# Excluding the exceptional MS radical for a binary linear-three component

The quotient is a setwise product of the component image and the marked
order-eight radical. Its order is at most 168 times 8, incompatible with
the actual order of G₂(2). The map from the component quotient is the
quotient of its literal inclusion; no ambient model recognition is assumed.

Source: Aschbacher–Smith C.1.31(MS2), C.1.34, printed pp.135–137.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS
variable {G : Type*} [Group G] [Finite G] {L R : Subgroup G}

/-- The G₂(2) exceptional MS radical cannot occur with a binary linear-three component. -/
theorem not_exceptional_radical_of_binary_component
    (hL : L.IsSubnormal)
    (eL : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hprod : ∀ g : G, ∃ l ∈ L, ∃ r ∈ R, l * r = g)
    (eG : (G ⧸ pCore 2 G) ≃* Atlas.G2.Model (ZMod 2))
    (hR : Nat.card (R.map (QuotientGroup.mk' (pCore 2 G))) = 8) : False := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let f : (L ⧸ pCore 2 L) →* (G ⧸ pCore 2 G) :=
    QuotientGroup.map _ _ L.subtype (pCore_subnormal_eq_comap 2 hL).le
  let a : (L ⧸ pCore 2 L) × R.map q → (G ⧸ pCore 2 G) := fun x => f x.1 * x.2
  have ha : Function.Surjective a := by
    intro x
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 G) x
    obtain ⟨l,hl,r,hr,rfl⟩ := hprod g
    refine ⟨(QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩, ⟨q r, mem_map_of_mem q hr⟩), ?_⟩
    exact (map_mul q l r).symm
  have hc := Nat.card_le_card_of_surjective a ha
  rw [Nat.card_prod, Nat.card_congr eL.toEquiv, Matrix.PSL3Two.card_SL, hR,
    Nat.card_congr eG.toEquiv, Atlas.G2.card_Model, Nat.card_zmod] at hc
  norm_num at hc
end CFSG.Quasithin.ChapterC.BinaryMS
