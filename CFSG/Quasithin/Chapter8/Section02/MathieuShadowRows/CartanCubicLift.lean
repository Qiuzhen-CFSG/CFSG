module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.EssentialCartanCover
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global
public import Theory.GroupTheory.PrimeOrderLift

/-!
# Cubic Cartan actions on the original span and orbit

A Cartan whose order is divisible by three has an actual order-three actor
in the faithful whole-span image: Cauchy's theorem supplies it, and the
proved two-group covering kernel preserves its order in the Cartan. Its
original representative need not have order three. Restricting its action
to the unchanged original orbit gives a genuine cubic in the full automizer;
faithfulness on the essential seed excludes trivial restriction.

The restriction homomorphism retains every original conjugation map. This
supplies the same cyclic actor for the later two-versus-three chief-factor
comparison, without replacing the upstairs kernel by O₂(H). The Cartan's
three-divisibility is retained until the original field-reduction argument.

Source: Aschbacher--Smith, proof of 3.1.9(6), printed p.578, used in8.2.2(1),
p.715, refs/quasithin.pdf. The actual chosen-module application is
NonFFSourceMathieuShadowRows/M22CodeCartanCubic in Chapter12/Section02.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open Chapter3 ChapterD

variable {G D W Z : Type*} [Group G] [Finite G] [Group D]
  [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup Z] [Module (ZMod 2) Z]
  {M H : Subgroup G} {q : H →* D} {ρ : Representation (ZMod 2) D W} {v : W}

/-- The cubic is chosen in the faithful whole-span image, where the covering
kernel is a two-group. Its original representative is retained without claiming
that representative has order three in H. -/
theorem SeedCartan.exists_cubic_span_action
    (c : SeedCartan (M := M) q ρ v) (τ : Representation (ZMod 2) H Z)
    (hc : c.HasSpanCover τ) (hthree : 3 ∣ Nat.card c.field.Carrierˣ) :
    ∃ b : c.originalPreimage,
      orderOf (actionHom τ (b : H)) = 3 ∧ orderOf (q (b : H)) = 3 := by
  obtain ⟨f,hf,he,_,hk⟩ := hc
  let P := actionSubgroup τ c.originalPreimage
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := P) 3
    (hthree.trans (Subgroup.card_dvd_of_surjective f hf))
  have hfx : orderOf (f x) = 3 :=
    (f.orderOf_map_eq_of_coprime_of_isPGroup_ker hk x
      (by rw [hx]; decide)).trans hx
  obtain ⟨b,hb,hbx⟩ := x.property
  have hb' : (⟨actionHom τ b,mem_map_of_mem _ hb⟩ : P) = x := Subtype.ext hbx
  refine ⟨⟨b,hb⟩,?_,?_⟩
  · rw [hbx]
    exact (Subgroup.orderOf_coe x).trans hx
  · rw [← he ⟨b,hb⟩,hb']
    exact (orderOf_injective c.embedding c.injective (f x)).trans hfx

variable {V : Subgroup G}
  [hU : IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]

omit [Finite G] in
/-- Trivial whole-span action centralizes the actual original seed subgroup. -/
theorem span_action_kernel_centralizes (hVH : V ≤ H) (x : H)
    (hx : actionHom (normalRepresentation ((conjugateSpan H V).subgroupOf H)) x = 1) :
    (x : G) ∈ centralizer (V : Set G) := by
  intro y hy
  have he := (actionHom_eq_one_iff _ x).mp hx (spanSeedVector H V hVH ⟨y,hy⟩)
  have he' := congrArg (fun w : Additive ((conjugateSpan H V).subgroupOf H) =>
    ((w.toMul : H) : G)) he
  change (x : G) * y * (x : G)⁻¹ = y at he'
  exact (mul_inv_eq_iff_eq_mul.mp he').symm

omit [Finite G] in
/-- Restrict the faithful whole-span action to the unchanged original orbit.
The resulting homomorphism agrees with every original conjugation map. -/
theorem exists_span_orbit_restriction (hVH : V ≤ H) (B : Subgroup H)
    (hB : B.map H.subtype ≤ normalizer (V : Set G)) :
    ∃ r : actionSubgroup (normalRepresentation ((conjugateSpan H V).subgroupOf H)) B →*
        ChapterE.Automizer V,
      ∀ b : B,
        r ⟨actionHom (normalRepresentation ((conjugateSpan H V).subgroupOf H)) b,
          mem_map_of_mem _ b.property⟩ =
        V.normalizerMonoidHom.rangeRestrict ⟨((b : H) : G),hB (mem_map_of_mem _ b.property)⟩ := by
  let τ := normalRepresentation ((conjugateSpan H V).subgroupOf H)
  let P := actionSubgroup τ B
  let p : B →* P := ((actionHom τ).comp B.subtype).codRestrict P
    (fun b => mem_map_of_mem _ b.property)
  have hp : Function.Surjective p := by
    rintro ⟨_,b,hb,rfl⟩
    exact ⟨⟨b,hb⟩,rfl⟩
  let j : B →* normalizer (V : Set G) := (H.subtype.comp B.subtype).codRestrict _
    (fun b => hB (mem_map_of_mem _ b.property))
  let t := V.normalizerMonoidHom.rangeRestrict.comp j
  have hk : p.ker ≤ t.ker := by
    intro b hb
    have hb' : actionHom τ (b : H) = 1 := congrArg P.subtype hb
    have hc := span_action_kernel_centralizes hVH (b : H) hb'
    change j b ∈ V.normalizerMonoidHom.rangeRestrict.ker
    rw [MonoidHom.ker_rangeRestrict,Subgroup.normalizerMonoidHom_ker]
    exact hc
  let r := p.liftOfSurjective hp ⟨t,hk⟩
  exact ⟨r,fun b => p.liftOfRightInverse_comp_apply _ _ _ b⟩

/-- A cubic on the whole span whose Cartan image is nontrivial gives a
cubic in the full original automizer. The full kernel upstairs is retained. -/
theorem SeedCartan.exists_cubic_orbit_action
    (c : SeedCartan (M := M) q ρ v)
    (hVH : V ≤ H)
    (hv : ∀ x : H, (x : G) ∈ centralizer (V : Set G) → ρ (q x) v = v)
    (hN : H ⊓ M ≤ normalizer (V : Set G))
    (hc : c.HasSpanCover (normalRepresentation ((conjugateSpan H V).subgroupOf H)))
    (hthree : 3 ∣ Nat.card c.field.Carrierˣ) :
    ∃ b : c.originalPreimage,
      orderOf (actionHom (normalRepresentation ((conjugateSpan H V).subgroupOf H)) (b : H)) = 3 ∧
      orderOf (q (b : H)) = 3 ∧
      ∃ hn : ((b : H) : G) ∈ normalizer (V : Set G),
        orderOf (V.normalizerMonoidHom.rangeRestrict ⟨((b : H) : G),hn⟩) = 3 := by
  obtain ⟨b,hb,hqb⟩ := c.exists_cubic_span_action _ hc hthree
  have hn : ((b : H) : G) ∈ normalizer (V : Set G) := hN b.property.1
  let z : normalizer (V : Set G) := ⟨((b : H) : G),hn⟩
  let r := V.normalizerMonoidHom.rangeRestrict
  have hpow : r z ^ 3 = 1 := by
    have hx : (b : H) ^ 3 ∈ (actionHom
        (normalRepresentation ((conjugateSpan H V).subgroupOf H))).ker := by
      change actionHom _ ((b : H) ^ 3) = 1
      rw [map_pow,← hb,pow_orderOf_eq_one]
    have hc' := span_action_kernel_centralizes hVH ((b : H) ^ 3) hx
    rw [← map_pow]
    change z ^ 3 ∈ r.ker
    rw [MonoidHom.ker_rangeRestrict,Subgroup.normalizerMonoidHom_ker]
    exact hc'
  have hne : r z ≠ 1 := by
    intro hz
    have hc' : ((b : H) : G) ∈ centralizer (V : Set G) := by
      have hz' : z ∈ r.ker := hz
      rw [MonoidHom.ker_rangeRestrict,Subgroup.normalizerMonoidHom_ker] at hz'
      exact hz'
    obtain ⟨a,ha⟩ := b.property.2
    have hh := hv b hc'
    rw [←ha] at hh
    have he : q (b : H) = 1 := by rw [←ha,c.seed_free a hh,map_one]
    rw [he,orderOf_one] at hqb
    omega
  exact ⟨b,hb,hqb,hn,orderOf_eq_prime_iff.mpr ⟨hpow,hne⟩⟩

end CFSG.Quasithin.Chapter8.MathieuShadowRows
