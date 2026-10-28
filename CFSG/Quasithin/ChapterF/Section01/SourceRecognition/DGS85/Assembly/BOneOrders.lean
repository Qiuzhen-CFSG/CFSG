module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.C2Source
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneOrderSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.MarkedRecognition
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderFormulas

/-!
# Weyl order from the actual b=1 natural profile

The product of the two original parabolic two-cores is a common Sylow
inside the reduced endpoints. Both cores lie in S₀=O₂(B), so Sylow
maximality identifies that product with the literal S₀. The full marked
split quotient identifies S₀ with its unipotent subgroup. Equal simple
root orders then give |S₀|=qᵐ for the actual dihedral rotation order m.

DGS (10.5)'s natural-profile calculation gives |S₀|=q³ or q⁴ and, in the
first case, trivial centers of both actual actors. Comparing powers gives
m=3 or m=4, retaining precisely the centerfreeness needed for A₂. Neither
a rotation order nor a centerfree actor is an added input. The natural
actions, actor identities and marked split quotient remain earlier inputs;
S₀ is not identified with the original S.

Source: DGS, Groups and Graphs (1985), (10.5), printed pp.156--157,
and Theorem D, p.224; Fong--Seitz split-root coordinates.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
open SuzukiContainment Reduction NoncommutingProfile Subgroup.CosetGeometry.RankTwo
open OriginalExtension FongSeitzBinary
variable {G X k₀ k₁ W₀ W₁ : Type*} [Group G] [Group X]
  [Field k₀] [Finite k₀] [CharP k₀ 2] [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}

/-- The two original parabolic cores generate exactly the reduced Sylow. -/
theorem core_product_eq_reducedSylow (h : HypothesisF11 L S)
    (p : C2Source.Profile L S k₀ k₁ W₀ W₁) :
    (parabolic L S 0).pCoreIn 2 ⊔ (parabolic L S 1).pCoreIn 2 = reducedSylow L S := by
  obtain ⟨T,hT⟩ := (original_core_product_sylow_reduced h p.left p.right).1
  change (T : Subgroup (P₀ L S 0)).map (P₀ L S 0).subtype = _ at hT
  have hle : (parabolic L S 0).pCoreIn 2 ⊔ (parabolic L S 1).pCoreIn 2 ≤ reducedSylow L S :=
    sup_le (parabolic_core_le_reducedSylow h 0) (parabolic_core_le_reducedSylow h 1)
  have hSP : reducedSylow L S ≤ P₀ L S 0 := by
    rw [P₀_eq_source h]
    exact le_sup_right.trans le_sup_left
  have hTS : (T : Subgroup (P₀ L S 0)) ≤ (reducedSylow L S).subgroupOf (P₀ L S 0) := by
    intro x hx
    exact hle (hT ▸ mem_map_of_mem (P₀ L S 0).subtype hx)
  have he : (reducedSylow L S).subgroupOf (P₀ L S 0) = (T : Subgroup (P₀ L S 0)) :=
    T.is_maximal' (reduced_hypothesis h).S_isP.comap_subtype hTS
  rw [←hT,←he,map_subgroupOf_eq_of_le hSP]

/-- Reindex the full reduced overlap by its proved parabolic intersection. -/
def intersectionMark (h : HypothesisF11 L S) (Q : MarkedQuotient P)
    (e : Iso (reducedAmalgam L S) Q.standardAmalgam) :
    Iso (ofSubgroups (parabolic L (reducedSylow L S) 0)
      (parabolic L (reducedSylow L S) 0 ⊓ parabolic L (reducedSylow L S) 1)
      (parabolic L (reducedSylow L S) 1) inf_le_left inf_le_right) Q.standardAmalgam :=
  (A2Source.intersectionAmalgamIso (reduced_hypothesis h)).trans e

/-- The same marked quotient counts the literal reduced Sylow by qᵐ. -/
theorem reducedSylow_card (h : HypothesisF11 L S)
    (p : C2Source.Profile L S k₀ k₁ W₀ W₁)
    (Q : MarkedQuotient P) (e : Iso (reducedAmalgam L S) Q.standardAmalgam)
    (split : SplitData Q.tits) : Nat.card (reducedSylow L S) = Nat.card k₀ ^ rotationOrder Q := by
  let mark := intersectionMark h Q e
  let hr := reduced_hypothesis h
  obtain ⟨a⟩ := p.reduced h
  have hc (i : Fin 2) : Nat.card (simpleRoot Q split i) = Nat.card k₀ :=
    QuadrangleStructure.marked_bOne_simpleRoot_card Q mark hr a.left a.right
      a.left_actor a.right_actor a.natural split i
  have hi : Function.Injective (MarkedLocal.sylowMap Q mark hr) := by
    exact Q.tits.B.subtype_injective.comp
      (((MulEquiv.subgroupCongr (lemma_F_1_3_6 hr).symm).trans mark.middle).injective.comp
        (inclusion_injective _))
  have hs := Nat.card_congr (MonoidHom.ofInjective hi).toEquiv
  rw [MarkedLocal.sylow_range Q mark hr split] at hs
  rw [hs,unipotent_card_alternating Q split false,
    alternatingOrder_eq_pow Q split ((hc 0).trans (hc 1).symm),hc 0]

/-- The natural profile selects rotation three with centerfree actors, or four. -/
theorem rotation_and_center (h : HypothesisF11 L S)
    (p : C2Source.Profile L S k₀ k₁ W₀ W₁)
    (E₁ : letI : Algebra (ZMod 2) k₁ := ZMod.algebra k₁ 2
      W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (Q : MarkedQuotient P) (e : Iso (reducedAmalgam L S) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    (rotationOrder Q = 3 ∧ centerIn p.left.actor = ⊥ ∧ centerIn p.right.actor = ⊥) ∨
      rotationOrder Q = 4 := by
  have hs := reducedSylow_card h p Q e split
  have hprod := core_product_eq_reducedSylow h p
  have hq : 2 ≤ Nat.card k₀ := by
    simpa using Nat.card_le_card_of_injective (fun b : Bool => if b then (1 : k₀) else 0) (by
      intro b c he
      cases b <;> cases c <;> simp_all)
  rcases (original_center_and_core_product_orders h p.left p.right p.natural E₁
    p.left_actor p.right_actor).2 with ⟨h₀,h₁,_,_,hcard⟩ | ⟨_,_,_,_,hcard⟩
  · rw [hprod,hs] at hcard
    rw [←reduced_actor_center_map, map_eq_bot_iff_of_injective _ (G₀ L S).subtype_injective] at h₀ h₁
    exact Or.inl ⟨Nat.pow_right_injective hq hcard,h₀,h₁⟩
  · rw [hprod,hs] at hcard
    exact Or.inr (Nat.pow_right_injective hq hcard)

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
