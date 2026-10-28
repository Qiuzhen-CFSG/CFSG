module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.TerminalWeights.Generator
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.TerminalWeights.Split
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Marking
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry.Torus
/-!
# The actual generator of X intersect K

The ordered quotient marking sends K to the first SL2 factor and has the
literal P as kernel. Source Sylow placement and the original SL3 Cartan
order give a primitive first-factor actor. Since P is the actual two-core
of K, the full kernel of the second-factor map on X is X intersect K.
The constructed actor generates that entire subgroup, not just a nontrivial
cyclic subgroup. Its diagonal coefficient has order q - 1 in the independent
orthogonal field.

The preceding common-core and ordered-quotient geometry remain explicit,
with producers common-core and common-orthogonal. No generator or full
torus-image hypothesis is imposed. Identifying the two eigenspaces with
V2 and the L2-span of W2, and choosing their transported common-field
weights, remains a separate local step of this terminal-weight task.

Source: Aschbacher--Smith, Proposition 11.3.2, final paragraph, printed p.775.
-/

open Subgroup
open scoped MatrixGroups
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.TerminalWeights
open CFSG.Quasithin.Chapter12.Section02 LocalGeometry
open CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 m)) {P I K X : Subgroup G}
    (E : BinaryField)
    (o : CommonCore.ProductQuotientMarking (f.Li 1 ⊔ I) P K (f.Li 1) E)

/-- The literal first factor contains an actor of the full torus order. -/
theorem source_primitive_actor
    (hcard : Nat.card E.Carrier = Nat.card S.field.Carrier)
    (hPK : P = K.pCoreIn 2) (hPT : P ≤ T)
    (hTY : (T : Subgroup G) ≤ f.Li 1 ⊔ I) (hTL : (T : Subgroup G) ≤ L)
    (hX : IsCartan T L X) (hXY : X ≤ f.Li 1 ⊔ I) :
    ∃ y : (X ⊓ K : Subgroup G), orderOf y = 2^S.field.degree-1 ∧
      (o.projection ⟨y,hXY y.property.1⟩).2 = 1 ∧
      orderOf (o.projection ⟨y,hXY y.property.1⟩).1 = 2^S.field.degree-1 ∧
      ∀ z : (X ⊓ K : Subgroup G), ∃ n : ℤ, y ^ n = z := by
  let Y := f.Li 1 ⊔ I
  let R := T.subtype hTY
  let C := X.subgroupOf Y
  have hk : o.projection.ker ≤ (R : Subgroup Y) := by
    rw [o.kernel]
    exact comap_mono hPT
  have hXT : X ≤ normalizer ((T : Subgroup G) : Set G) := by
    have ht : sourceTL T L = T := inf_eq_left.mpr (hTL.trans le_sup_left)
    simpa only [cartanNormalizer,ht] using hX.1.trans inf_le_right
  have hn : C ≤ normalizer (R : Set Y) := by
    change X.subgroupOf Y ≤ normalizer ((T : Subgroup G).subgroupOf Y : Set Y)
    rw [← subgroupOf_normalizer_eq hTY]
    exact comap_mono hXT
  have hodd : Odd (Nat.card C) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hXY).toEquiv]
    exact hX.odd
  have hc : Nat.card C = (Nat.card E.Carrier-1)^2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hXY).toEquiv,
      (Coordinates.sl3 m).cartan_card hX,hcard,S.field.card_eq]
  obtain ⟨y,hy,hoy,hyorder,hygen⟩ := exists_primitive_first_factor o.projection o.surjective R hk C hn hodd hc
  have hPKle : P ≤ K := hPK ▸ pCoreIn_le 2 K
  have hkerK : o.projection.ker ≤ K.subgroupOf Y := by
    rw [o.kernel]
    exact comap_mono hPKle
  have hyK : (y.val : G) ∈ K := by
    have him : o.projection y.val ∈ (K.subgroupOf Y).map o.projection := by
      rw [o.first_factor]
      exact hy
    have hx : y.val ∈ ((K.subgroupOf Y).map o.projection).comap o.projection := him
    rwa [comap_map_eq_self hkerK] at hx
  let z : (X ⊓ K : Subgroup G) := ⟨y.val, y.property, hyK⟩
  have hoambient : orderOf (y.val : G) = orderOf y :=
    (orderOf_injective Y.subtype Y.subtype_injective y.val).trans
      (orderOf_injective C.subtype C.subtype_injective y)
  refine ⟨z,?_,hy,?_,?_⟩
  · calc
      orderOf z = orderOf (z : G) :=
        (orderOf_injective (X ⊓ K).subtype (X ⊓ K).subtype_injective z).symm
      _ = 2^S.field.degree-1 := by
        change orderOf (y.val : G) = _
        rw [hoambient,hoy,hcard,S.field.card_eq]
  · simpa only [hcard,S.field.card_eq] using hyorder
  · intro w
    let v : C := ⟨⟨w,hXY w.property.1⟩,w.property.1⟩
    have hv : (o.projection v.val).2 = 1 := by
      have hh : o.projection v.val ∈ (K.subgroupOf Y).map o.projection :=
        mem_map_of_mem o.projection w.property.2
      rw [o.first_factor] at hh
      exact hh
    obtain ⟨n,hn⟩ := hygen v hv
    refine ⟨n,Subtype.ext ?_⟩
    exact congrArg (fun u : C => (u.val : G)) hn
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.TerminalWeights

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.TerminalWeights
open Subgroup Matrix Matrix.SpecialLinearGroup
open CFSG.Quasithin.Chapter12.Section02 LocalGeometry
open CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 m)) {P I K X : Subgroup G}
    (E : BinaryField)
    (o : CommonCore.ProductQuotientMarking (f.Li 1 ⊔ I) P K (f.Li 1) E)

/-- The actual first-factor generator has a primitive split eigenvalue in
the independent orthogonal coefficient field. -/
theorem source_split_generator
    (hcard : Nat.card E.Carrier = Nat.card S.field.Carrier)
    (hPK : P = K.pCoreIn 2) (hPT : P ≤ T)
    (hTY : (T : Subgroup G) ≤ f.Li 1 ⊔ I) (hTL : (T : Subgroup G) ≤ L)
    (hX : IsCartan T L X) (hXY : X ≤ f.Li 1 ⊔ I) :
    ∃ y : (X ⊓ K : Subgroup G),
      (∀ z : (X ⊓ K : Subgroup G), ∃ n : ℤ, y ^ n = z) ∧
      (o.projection ⟨y,hXY y.property.1⟩).2 = 1 ∧
      ∃ b : SL(2,E.Carrier), ∃ a : E.Carrier,
        a ≠ 0 ∧ orderOf a = 2^S.field.degree-1 ∧
        (b * (o.projection ⟨y,hXY y.property.1⟩).1 * b⁻¹).val = !![a,0;0,a⁻¹] := by
  obtain ⟨y,_,hy₂,hyorder,hygen⟩ := source_primitive_actor D S m f E o
    hcard hPK hPT hTY hTL hX hXY
  let Y := f.Li 1 ⊔ I
  let R := T.subtype hTY
  let q := (MonoidHom.fst SL(2,E.Carrier) SL(2,E.Carrier)).comp o.projection
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨u,hu⟩ := o.surjective (a,1)
    exact ⟨u,congrArg Prod.fst hu⟩
  let R₁ := R.mapSurjective hq
  let yy : Y := ⟨y,hXY y.property.1⟩
  have hXT : X ≤ normalizer ((T : Subgroup G) : Set G) := by
    have ht : sourceTL T L = T := inf_eq_left.mpr (hTL.trans le_sup_left)
    simpa only [cartanNormalizer,ht] using hX.1.trans inf_le_right
  have hyn : yy ∈ normalizer (R : Set Y) := by
    change yy ∈ normalizer ((T : Subgroup G).subgroupOf Y : Set Y)
    rw [← subgroupOf_normalizer_eq hTY]
    exact hXT y.property.1
  have hqn : q yy ∈ normalizer (R₁ : Set SL(2,E.Carrier)) :=
    (R : Subgroup Y).le_normalizer_map q (mem_map_of_mem q hyn)
  let qX := q.comp (inclusion hXY)
  have ho : Odd (orderOf (q yy)) :=
    hX.odd.of_dvd_nat ((orderOf_map_dvd qX (⟨y,y.property.1⟩ : X)).trans
      (orderOf_dvd_natCard _))
  have hne : q yy ≠ 1 := by
    intro he
    have hpow : 4 ≤ 2^S.field.degree := by
      change (2 : ℕ)^2 ≤ 2^S.field.degree
      exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by have := S.nonbinary; omega)
    have hh : orderOf (q yy) = 2^S.field.degree-1 := hyorder
    rw [he,orderOf_one] at hh
    omega
  obtain ⟨b,a,ha,horder,hdiag⟩ := split_odd_actor R₁ (q yy) hqn ho hne
  exact ⟨y,hygen,hy₂,b,a,ha,horder.trans hyorder,hdiag⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.TerminalWeights
