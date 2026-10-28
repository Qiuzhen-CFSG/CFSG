module
public import Theory.SpecificGroups.Triality.TwoLocalCover
public import Theory.GroupAction.RankTwoCosetGeometry.FixedFusion

/-!
# Fusion through the genuine triality endpoints

A nontrivial involution fixes a tree in the native parabolic hexagon.
Reindexing its two vertex types gives a connected fixed coset graph, so
compatible endpoint maps preserve native conjugacy. No map from the whole
native carrier into the target group is required.

This is the native-to-completion direction of Aschbacher--Smith F.4.30,35,
printed pp.290--292. The original ambient consumer is
Chapter14/Section02/EightLargeParabolic/InvolutionFusion.
-/

@[expose] public noncomputable section
open Subgroup
namespace Triality.Standard.EndpointFusion
open Parabolics TwoLocalGeometry GroupAction.EvenPolygon
variable (n : ℕ) (hn : 0 < n)
local notation "P" => binaryParameters n hn

def node : Bool → Node | false => .arms | true => .central
def family (i : Bool) : Subgroup (Carrier P) := parabolic P (node i)

private def boolVertex : Vertex n hn → CosetGeometry.Vertex (family n hn)
  | ⟨.arms,q⟩ => ⟨false,q⟩
  | ⟨.central,q⟩ => ⟨true,q⟩

private theorem boolVertex_smul (g : Carrier P) (v : Vertex n hn) :
    boolVertex n hn (g • v) = g • boolVertex n hn v := by
  rcases v with ⟨i,q⟩
  cases i <;> rfl

private theorem boolVertex_adj {v w : Vertex n hn}
    (h : (incidenceGraph n hn).Adj v w) :
    (CosetGeometry.RankTwo.graph (family n hn)).Adj (boolVertex n hn v) (boolVertex n hn w) := by
  rcases v with ⟨i,q⟩
  rcases w with ⟨j,r⟩
  rcases h with ⟨hne,g,hg,hh⟩
  cases i <;> cases j
  · exact (hne rfl).elim
  · exact ⟨Bool.false_ne_true,g,hg,hh⟩
  · exact ⟨(by decide : true ≠ false),g,hg,hh⟩
  · exact (hne rfl).elim

/-- Native fixed trees give connected fixed graphs on the two endpoint types. -/
theorem fixed_connected (x : Carrier P) (hx : orderOf x = 2) :
    ((CosetGeometry.RankTwo.graph (family n hn)).induce {v | x • v = v}).Preconnected := by
  let R := zpowers x
  have hR : R ≠ ⊥ := by
    intro hh
    have he := zpowers_eq_bot.mp hh
    rw [he,orderOf_one] at hx
    omega
  have hp : IsPGroup 2 R := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,hx,pow_one])
  have hΓ := (hexagonGeometry n hn).toEvenPolygonAction
    (apartmentTranslates n hn) (standardApartment_fixer_odd n hn)
  have ht := fixed_graph_isTree hΓ R hR hp (exists_fixed_edge n hn R hp)
  let f : ((incidenceGraph n hn).induce (fixedVertices R)) →g
      ((CosetGeometry.RankTwo.graph (family n hn)).induce {v | x • v = v}) :=
    ⟨fun v => ⟨boolVertex n hn v.val,by
      change x • boolVertex n hn v.val = boolVertex n hn v.val
      rw [←boolVertex_smul, v.property x (mem_zpowers x)]⟩,
      fun h => boolVertex_adj n hn h⟩
  apply ht.1.preconnected.map f
  rintro ⟨⟨i,q⟩,hq⟩
  cases i
  · let v : Vertex n hn := ⟨.arms,q⟩
    have hv : v ∈ fixedVertices R := by
      intro g hg
      exact (show R ≤ MulAction.stabilizer (Carrier P) v from zpowers_le.mpr (by
        change x • v = v
        exact congrArg (fun u : CosetGeometry.Vertex (family n hn) =>
          match u with | ⟨false,q⟩ => (⟨.arms,q⟩ : Vertex n hn) | ⟨true,q⟩ => ⟨.central,q⟩) hq)) hg
    exact ⟨⟨v,hv⟩,rfl⟩
  · let v : Vertex n hn := ⟨.central,q⟩
    have hv : v ∈ fixedVertices R := by
      intro g hg
      exact (show R ≤ MulAction.stabilizer (Carrier P) v from zpowers_le.mpr (by
        change x • v = v
        exact congrArg (fun u : CosetGeometry.Vertex (family n hn) =>
          match u with | ⟨false,q⟩ => (⟨.arms,q⟩ : Vertex n hn) | ⟨true,q⟩ => ⟨.central,q⟩) hq)) hg
    exact ⟨⟨v,hv⟩,rfl⟩

def endpointMap {A : Type*} [Group A]
    (l : parabolic P .arms →* A) (r : parabolic P .central →* A) :
    ∀ i, family n hn i →* A
  | false => l
  | true => r

theorem endpoint_fusion {A : Type*} [Group A]
    (l : parabolic P .arms →* A) (r : parabolic P .central →* A)
    (hc : ∀ (z : Carrier P) (hl : z ∈ parabolic P .arms) (hr : z ∈ parabolic P .central),
      l ⟨z,hl⟩ = r ⟨z,hr⟩)
    {i j : Bool} (x : family n hn i) (y : family n hn j)
    (hx : orderOf x.val = 2) (hxy : IsConj x.val y.val) :
    IsConj (endpointMap n hn l r i x) (endpointMap n hn l r j y) := by
  let f := endpointMap n hn l r
  exact CosetGeometry.Fusion.of_fixed_connected (family n hn) f hc x y
    (fixed_connected n hn x.val hx) hxy

end Triality.Standard.EndpointFusion

