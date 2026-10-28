module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NoSmallThreeExtraspecialSupport
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.ExtraspecialFiniteLinear
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.LocalGeneration

/-!
# The extraspecial endpoint of original cyclic D.2.17

The local extraspecial commutator supplies a characteristic central cubic.
Source indecomposability makes its six-dimensional support the whole module.
The faithful action over the field of four elements and determinant one
bound the three-core by order 27. The extraspecial normalizer calculation
then identifies the original group with the three-core and its involution.
Every field of the literal endpoint record is thus discharged on the original
representation. Source: Aschbacher–Smith, proof after D.2.29, printed p.192.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- The extraspecial local alternative completes the original source branch. -/
theorem Hypotheses.extraspecial_local_threeCore_localGeneration
    (h : Hypotheses ρ)
    {H : Type*} [Group H] [Finite H] {K : GroupClass} (hH : IsSQTK K H)
    (f : H →* G) (honto : Function.Surjective f)
    (hq : cubicRatio ρ = 2)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2)
    (t : G) (ht : t ∈ smallSupportInvolutions ρ)
    (hF : IsExtraspecial 3 (⁅pCore 3 G,zpowers t⁆ : Subgroup G))
    (hc : Nat.card (⁅pCore 3 G,zpowers t⁆ : Subgroup G) = 27)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ ⁅pCore 3 G,zpowers t⁆) = 6)
    (_hcent : ⁅(center (⁅pCore 3 G,zpowers t⁆ : Subgroup G)).map
      (⁅pCore 3 G,zpowers t⁆ : Subgroup G).subtype,zpowers t⁆ = ⊥) :
    Nonempty (LocalGeneration ρ) := by
  obtain ⟨_,hZ,_,_,hdim⟩ := h.extraspecial_six_space hH f honto hq hfive hNo t ht hF hc hd
  obtain ⟨heq,hgen⟩ := h.toCoreHypotheses.extraspecial_threeCore_generation t ht hF hc hdim hZ
  refine ⟨{kernel := pCore 3 G
           normal := inferInstance
           prime := 3
           prime_prime := by decide
           prime_odd := by decide
           pgroup := pCore_isPGroup
           nontrivial := ?_
           involution := t
           order_two := ht.1
           generated := ?_
           commutator := heq.symm
           moved := h.threeCore_moved_eq_top hq hfive hNo
           codimension := (h.toCoreHypotheses.smallSupport_starred hq ht).2.le}⟩
  · intro he
    rw [←heq,he,card_bot] at hc
    omega
  · rw [heq]
    exact hgen
end CFSG.Quasithin.ChapterD.CyclicSource
