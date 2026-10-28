module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CartanCubicLift
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeCubicChiefs
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CartanField

/-!
# Original M22 chief counts for the constructed Cartan cubic

The two-core cover produces an element with order-three actions on the
whole span and on the reduced Cartan. Its nontrivial restriction to the
original orbit is a cubic in that orbit's full automizer. The actual M22
code marking then gives exactly three noncentral chief factors on the code
and its dual. The original group representative and all action maps remain
unchanged. A separate restriction homomorphism retains every original lift.

If the Cartan is a three-group, the native arithmetic calculation makes
its field F₄ and its order three, discharging the divisibility premise of
the cubic construction. The original source centralization argument must
still establish that three-group condition. No original-group kernel is
identified with O₂(H), and no ambient recognition is used.

The named propositions keep the literal action statements at a stable
elaboration boundary; the construction theorems prove all their clauses.
Source: Aschbacher--Smith, proof of3.1.9(6), printed p.578, used in8.2.2(1),
p.715, refs/quasithin.pdf. The Chapter12 application is M22CodeCartanCubic.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open Chapter3 ChapterD ChapterE MathieuCode
open BinaryLinearThree.ParabolicCyclic.ChiefCounts
variable {G D W : Type*} [Group G] [Group D]
  [AddCommGroup W] [Module (ZMod 2) W]
  {M H V : Subgroup G}
  [hU : IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]

/-- The complete restriction map, named to preserve the original elementary
span instance when used with the large essential-source quotient. -/
@[expose] def SpanOrbitRestriction (B : Subgroup H) : Prop :=
  let τ := normalRepresentation ((conjugateSpan H V).subgroupOf H)
  ∃ r : actionSubgroup τ B →* Automizer V,
    ∀ y : B,
      ∃ hn : ((y : H) : G) ∈ normalizer (V : Set G),
        r ⟨actionHom τ y,mem_map_of_mem _ y.property⟩ =
          V.normalizerMonoidHom.rangeRestrict ⟨((y : H) : G),hn⟩

/-- Whole-span restriction is constructed, with every original element retained. -/
theorem span_orbit_restriction (hVH : V ≤ H) (B : Subgroup H)
    (hB : B.map H.subtype ≤ normalizer (V : Set G)) :
    SpanOrbitRestriction (V := V) B := by
  obtain ⟨r,hr⟩ := exists_span_orbit_restriction hVH B hB
  exact ⟨r,fun y => ⟨hB (mem_map_of_mem _ y.property),hr y⟩⟩

variable [hV : IsElementaryAbelian 2 V]

/-- A constructed cubic on the faithful span, its nontrivial reduced action,
and the same original orbit's code and dual chief counts. -/
@[expose] def CubicOrbitChiefs (B : Subgroup H) (q : H →* D) : Prop :=
  ∃ b : B,
    orderOf (actionHom (normalRepresentation ((conjugateSpan H V).subgroupOf H))
      (b : H)) = 3 ∧ orderOf (q (b : H)) = 3 ∧
    ∃ hn : ((b : H) : G) ∈ normalizer (V : Set G),
      let z := V.normalizerMonoidHom.rangeRestrict ⟨((b : H) : G),hn⟩
      orderOf z = 3 ∧
      HasCount ((automizerRepresentation V).comp (zpowers z).subtype) 3 ∧
      HasCount (Representation.dual ((automizerRepresentation V).comp (zpowers z).subtype)) 3

variable [Finite G] {q : H →* D} {ρ : Representation (ZMod 2) D W} {v : W}

set_option backward.isDefEq.respectTransparency false in
/-- Native M22 markings give three chief factors for the constructed cubic,
on the original orbit and dual, with the full covering kernel retained. -/
theorem marked_cartan_cubic_chiefs
    (c : SeedCartan (M := M) q ρ v) (hVH : V ≤ H)
    (hv : ∀ x : H, (x : G) ∈ centralizer (V : Set G) → ρ (q x) v = v)
    (hN : H ⊓ M ≤ normalizer (V : Set G))
    (hc : c.HasSpanCover (normalRepresentation ((conjugateSpan H V).subgroupOf H)))
    (hthree : 3 ∣ Nat.card c.field.Carrierˣ)
    (f : Automizer V →* m22PairStabilizer) (hf : Function.Injective f)
    (E : Additive V ≃ₗ[ZMod 2] M22Code)
    (hE : ∀ b w, E (automizerRepresentation V b w) = m22OuterCodeRepresentation (f b) (E w)) :
    CubicOrbitChiefs (V := V) c.originalPreimage q := by
  obtain ⟨b,hb,hqb,hn,hz⟩ := SeedCartan.exists_cubic_orbit_action
    (G := G) (D := D) (W := W) (M := M) (H := H) (q := q) (ρ := ρ) (v := v)
    (V := V) (hU := hU) c hVH hv hN hc hthree
  let z := V.normalizerMonoidHom.rangeRestrict ⟨((b : H) : G),hn⟩
  have hZ : Nat.card (zpowers z) = 3 := (Nat.card_zpowers z).trans hz
  have hcounts := marked_m22_code_cubic_chiefs
    ((automizerRepresentation V).comp (zpowers z).subtype)
    (f.comp (zpowers z).subtype) (hf.comp (zpowers z).subtype_injective) E
    (fun x w => hE x.val w) hZ
  exact ⟨b,hb,hqb,hn,hz,hcounts⟩

set_option backward.isDefEq.respectTransparency false in
/-- The source's three-group Cartan condition reduces its field to four and
constructs the moving cubic with both original chief counts. The three-group
condition is kept explicit for the original centralization argument. -/
theorem marked_three_group_cartan_chiefs
    (c : SeedCartan (M := M) q ρ v) (hVH : V ≤ H)
    (hv : ∀ x : H, (x : G) ∈ centralizer (V : Set G) → ρ (q x) v = v)
    (hN : H ⊓ M ≤ normalizer (V : Set G))
    (hc : c.HasSpanCover (normalRepresentation ((conjugateSpan H V).subgroupOf H)))
    (hthree : IsPGroup 3 c.field.Carrierˣ)
    (f : Automizer V →* m22PairStabilizer) (hf : Function.Injective f)
    (E : Additive V ≃ₗ[ZMod 2] M22Code)
    (hE : ∀ b w, E (automizerRepresentation V b w) = m22OuterCodeRepresentation (f b) (E w)) :
    Nat.card c.field.Carrier = 4 ∧ Nat.card c.field.Carrierˣ = 3 ∧
      CubicOrbitChiefs (V := V) c.originalPreimage q := by
  have hfour := NormalizedShadowRows.binary_field_card_four_of_units_three_group
    c.field.Carrier c.large hthree
  have hcard : Nat.card c.field.Carrierˣ = 3 := by rw [Nat.card_units,hfour]
  exact ⟨hfour,hcard,marked_cartan_cubic_chiefs c hVH hv hN hc
    (by rw [hcard]) f hf E hE⟩

end CFSG.Quasithin.Chapter8.MathieuShadowRows
