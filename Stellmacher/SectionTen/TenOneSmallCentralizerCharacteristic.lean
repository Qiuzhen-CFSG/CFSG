module
public import Stellmacher.SectionTen.TenOneSmallElementaryEscapeBound

/-!
# Characteristicity of the elementary-sixteen middle centralizer

Under the small first-module and SL₂(2) local quotient hypotheses, the
literal centralizer W*=C_Qmiddle(W₀) is characteristic in the middle core
whenever it has order sixteen. Characteristicity is stated for its actual
intrinsic subgroup of Qmiddle.

The established centralizer packet makes W* elementary abelian. Every
automorphic image of its intrinsic subgroup remains elementary of order
sixteen. The native escaping-subgroup bound would force such an image to
have order at most eight if it left W*, so every image is contained in W*.
Equal cardinalities give equality, proving invariance under all automorphisms.
The cubic-action and C₄-square arguments are contained in the imported bound.

Source: Stellmacher (10.1)(a3), printed p.61, the characteristicity step
before normalizer identity (7), in `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

/-- The actual order-sixteen middle centralizer is characteristic in the middle core. -/
public theorem ten_one_small_centralizer_characteristic
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
      GeneratedNeighborhoodV ctx.Γ middle
    let Wstar := QAt ctx.Γ middle ⊓ Subgroup.centralizer (W0 : Set G)
    Nat.card Wstar = 16 → (Wstar.subgroupOf (QAt ctx.Γ middle)).Characteristic := by
  let Q := QAt ctx.Γ middle
  let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
    GeneratedNeighborhoodV ctx.Γ middle
  let Wstar := Q ⊓ Subgroup.centralizer (W0 : Set G)
  let C := Wstar.subgroupOf Q
  change Nat.card Wstar = 16 → C.Characteristic
  intro hcard
  let _ : IsElementaryAbelian 2 Wstar :=
    (ten_one_small_centralizer_elementary ctx middle hpath hsmall hmodel).2.1
  let _ : IsElementaryAbelian 2 C :=
    IsElementaryAbelian.subgroupOf (inf_le_left : Wstar ≤ Q)
  have hCcard : Nat.card C = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Wstar ≤ Q)).toEquiv]
    exact hcard
  rw [Subgroup.characteristic_iff_map_eq]
  intro automorphism
  have himageCard : Nat.card (C.map automorphism.toMonoidHom) = 16 := by
    rw [Subgroup.card_map_of_injective automorphism.injective, hCcard]
  have hle : C.map automorphism.toMonoidHom ≤ C := by
    by_contra hnot
    let _ : IsElementaryAbelian 2 (C.map automorphism.toMonoidHom) :=
      IsElementaryAbelian.map _
    have hbound := ten_one_small_elementary_escape_card_bound
      ctx middle hpath hsmall hmodel (C.map automorphism.toMonoidHom) hnot
    rw [himageCard] at hbound
    omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hCcard, himageCard])

end Stellmacher.SectionTen
