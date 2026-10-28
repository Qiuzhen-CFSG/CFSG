module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.ModelExclusion.Even.Numerics

/-!
# The even exclusion reduced to faithful action and model centralizer orders

The original component's two-core quotient is a simple even model. Its
marked involution fixes a Sylow two-subgroup, the quotient order is divisible
by 480, and its involution centralizer has order dividing 2304. A faithful
compatible action of the ambient quotient centralizer puts a subgroup of
order divisible by nine into the model automorphism centralizer.

The numerical model bound and the construction of that faithful action are
separate explicit obligations. This module proves their conditional assembly
and applies it to the actual `ModelExclusionSource` consumer. It does not
claim either obligation, or original 14.3.20, is complete.
Source: Aschbacher--Smith, 14.3.20, printed p.998, and 1.1.5(3)(a--b),
printed pp.501--503, `refs/quasithin.pdf`.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section08
open CFSG.Quasithin.Chapter12.Section08.InvariantFlag
open CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}

/-- The precise intrinsic model calculation used by the even exclusion.
This is a specification awaiting proof, not a classification theorem. -/
def EvenModelCentralizerBounds : Prop :=
  ∀ (X : Type u) [Group X] [Finite X], IsSimpleGroup X → LieTypeTwoModel X →
    ∀ x : X, orderOf x = 2 →
      (∃ S : Sylow 2 X, ∀ y : S, MulAut.conj x y = y) →
      480 ∣ Nat.card X → Nat.card (centralizer ({x} : Set X)) ∣ 2304 →
      ¬ 9 ∣ Nat.card (centralizer ({MulAut.conj x} : Set (MulAut X)))

namespace MarkedPoint
variable {F : InvariantFlag T V 2} {L A : Subgroup G} (P : MarkedPoint F L A)

/-- A faithful action of the literal quotient centralizer on the actual
component quotient, with the conjugation equation on its existing embedding. -/
def ComponentCentralizerAction (B : Subgroup G)
    (hB : IsComponent P.globalCentralizer (B.subgroupOf P.globalCentralizer))
    (hcore : P.globalCentralizer.pCoreIn 2 = zpowers P.element)
    (z : P.globalCentralizer) : Prop :=
  ∃ ρ : centralizer ({P.pointQuotientMap z} : Set P.PointQuotient) →*
      MulAut ((B.subgroupOf P.globalCentralizer) ⧸ pCore 2 (B.subgroupOf P.globalCentralizer)),
    Function.Injective ρ ∧ ∀ c x,
      P.componentQuotientMap B hB hcore (ρ c x) =
        (c : P.PointQuotient) * P.componentQuotientMap B hB hcore x * (c : P.PointQuotient)⁻¹

/-- The actual source component is excluded once its faithful action and the
independent intrinsic centralizer calculation have been supplied. -/
theorem evenComponent_false_of_centralizer_inputs
    (hmodels : EvenModelCentralizerBounds.{u})
    (hA : ElementaryFactor F L A) (z : G) (hz : F.Vi 1 = zpowers z)
    (hSylow : CFSG.Quasithin.Chapter1.IsSylowIn 2 P.sylowCentralizer P.globalCentralizer)
    (hcore : P.globalCentralizer.pCoreIn 2 = zpowers P.element)
    (hstructure : P.QuotientCentralizerStructure (P.markedGenerator hA.seed_le z hz))
    (B : Subgroup G) (hBC : B ≤ P.globalCentralizer) (hKB : P.blockCentralizer ≤ B)
    (hB : IsComponent P.globalCentralizer (B.subgroupOf P.globalCentralizer))
    {α : MulAut (B.subgroupOf P.globalCentralizer)}
    (hm : EvenModelAction (B.subgroupOf P.globalCentralizer) α)
    (haction : P.ComponentCentralizerAction B hB hcore (P.markedGenerator hA.seed_le z hz)) :
    False := by
  let K := B.subgroupOf P.globalCentralizer
  let X := K ⧸ pCore 2 K
  let x : X := P.componentQuotientGenerator hA z hz B hKB
  let j : X →* P.PointQuotient := P.componentQuotientMap B hB hcore
  have hj : Function.Injective j := P.componentQuotientMap_injective B hB hcore
  let C := centralizer ({P.pointQuotientMap (P.markedGenerator hA.seed_le z hz)} : Set P.PointQuotient)
  have hxj : j x = P.pointQuotientMap (P.markedGenerator hA.seed_le z hz) := rfl
  let cj : centralizer ({x} : Set X) →* C :=
    (j.comp (centralizer ({x} : Set X)).subtype).codRestrict C (by
      intro y
      apply mem_centralizer_singleton_iff.mpr
      change j (y : X) * P.pointQuotientMap (P.markedGenerator hA.seed_le z hz) =
        P.pointQuotientMap (P.markedGenerator hA.seed_le z hz) * j (y : X)
      rw [← hxj, ← map_mul, ← map_mul]
      exact congrArg j (mem_centralizer_singleton_iff.mp y.property))
  have hcj : Function.Injective cj := by
    intro y v h
    exact Subtype.ext (hj (congrArg Subtype.val h))
  have hc : Nat.card (centralizer ({x} : Set X)) ∣ 2304 :=
    (Subgroup.card_dvd_of_injective cj hcj).trans
      (P.quotientCentralizer_card_dvd _ hstructure)
  obtain ⟨ρ, hρ, hact⟩ := haction
  have hfix (c : C) : ρ c x = x := by
    apply hj
    rw [hact, hxj, mem_centralizer_singleton_iff.mp c.property, mul_inv_cancel_right]
  let a : C →* centralizer ({MulAut.conj x} : Set (MulAut X)) :=
    ρ.codRestrict _ (by
      intro c
      apply mem_centralizer_singleton_iff.mpr
      ext y
      change ρ c (x * y * x⁻¹) = x * ρ c y * x⁻¹
      rw [map_mul, map_mul, map_inv, hfix])
  have ha : Function.Injective a := by
    intro c d h
    exact hρ (congrArg Subtype.val h)
  have hnine : 9 ∣ Nat.card (centralizer ({MulAut.conj x} : Set (MulAut X))) :=
    (P.nine_dvd_quotientCentralizer _ hstructure).trans
      (Subgroup.card_dvd_of_injective a ha)
  let : IsQuasisimple K := hB.2
  obtain ⟨_, hs, hl⟩ := hm.quotient_model
  exact hmodels X hs hl x (P.componentQuotientGenerator_order hA z hz B hKB hB hcore)
    (P.componentQuotientGenerator_fixes_sylow hA z hz B hKB hB hSylow)
    (P.componentQuotient_card_dvd B hBC hKB hB hcore) hc hnine

end MarkedPoint

/-- Source action obligation, retaining all original local and model data.
The numerical model obligation is independent of this construction. -/
def EvenCentralizerActionSource (F : InvariantFlag T V 2) (L : Subgroup G) : Prop :=
  ∀ A : Subgroup G, ∀ hA : ElementaryFactor F L A, A < centralizer (A : Set G) →
    ∀ (P : MarkedPoint F L A) (z : G) (hz : F.Vi 1 = zpowers z),
      P.FourCenterGeometry z → CFSG.Quasithin.Chapter1.IsSylowIn 2 P.sylowCentralizer P.globalCentralizer →
      ∀ hcore : P.globalCentralizer.pCoreIn 2 = zpowers P.element,
      P.QuotientCentralizerStructure (P.markedGenerator hA.seed_le z hz) →
      ∀ B : Subgroup G, B ≤ P.globalCentralizer → P.blockCentralizer ≤ B →
      ∀ hB : IsComponent P.globalCentralizer (B.subgroupOf P.globalCentralizer),
      B = ⁅B, zpowers z⁆ →
      ∀ α : MulAut (B.subgroupOf P.globalCentralizer),
      (∀ x : B.subgroupOf P.globalCentralizer,
        ((α x : P.globalCentralizer) : G) = z * (x : G) * z⁻¹) →
      EvenModelAction (B.subgroupOf P.globalCentralizer) α →
      P.ComponentCentralizerAction B hB hcore (P.markedGenerator hA.seed_le z hz)

/-- Conditional assembly on the same marked point and the same component.
Both premises are still source obligations; neither is assumed as an instance. -/
theorem evenExclusionSource_of_centralizer_inputs
    (F : InvariantFlag T V 2) (L : Subgroup G)
    (hmodels : EvenModelCentralizerBounds.{u}) (haction : EvenCentralizerActionSource F L) :
    EvenExclusionSource F L := by
  intro A hA hlt P z hz hgeom hSylow hcore hstructure hcomp
  obtain ⟨B, hBC, hKB, hB, hcomm, α, hα, hm⟩ := hcomp
  exact P.evenComponent_false_of_centralizer_inputs hmodels hA z hz hSylow hcore hstructure
    B hBC hKB hB hm (haction A hA hlt P z hz hgeom hSylow hcore hstructure
      B hBC hKB hB hcomm α hα hm)

/-- The completed arithmetic reduction feeds the actual marked-model consumer.
The local extension and sporadic branch retain their independent producers. -/
theorem modelExclusionSource_of_even_centralizer_inputs
    (F : InvariantFlag T V 2) (L : Subgroup G)
    (hlocal : QuotientCentralizerSource F L)
    (hsporadic : SporadicExclusionSource F L)
    (hmodels : EvenModelCentralizerBounds.{u}) (haction : EvenCentralizerActionSource F L) :
    ModelExclusionSource F L :=
  modelExclusionSource_of_local_inputs F L hlocal
    (evenExclusionSource_of_centralizer_inputs F L hmodels haction) hsporadic

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
