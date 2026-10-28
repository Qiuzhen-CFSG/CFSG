module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.QuotientGeometry.Descent
public import Theory.SpecificGroups.Alternating.FiveSubgroupCentralizer

/-!
# The root involution's centralizer inside a five-centralizer

Let E have order five and lie in C_G(t). In the given marked isomorphism
C_G(t) ≃ E₄ × A₅, E lies in the A₅ factor. Its projection is injective and
self-centralizing in the concrete A₅. Restricting the same isomorphism therefore
identifies the full C_{C_G(E)}(t) with E₄ × E. In particular this centralizer
has order twenty and every element has tenth power one.

The restriction below uses the literal subtype inclusions on both sides of
C_{C_G(E)}(t) = C_G(E) ∩ C_G(t). The resulting quotient application discharges
`LocalCentralizerBounds`; involution fusion remains an explicit separate input.

Source: Aschbacher, *Sporadic Groups* (1994), 47.2(2), printed p.261,
the calculation U(t)* = C_{M*}(t*) for M = C_G(E) and M* = M/E.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent
open InvolutionGeometry
variable {G : Type*} [Group G] [Finite G]
variable {D : Seed G} {t : G} (C : SecondCentralizer D t)
variable (E : Subgroup G) (hE : Nat.card E = 5) (hEt : E ≤ involutionCentralizer t)

private def fiveProjection : E →* A5 :=
  (MonoidHom.snd E4 A5).comp (C.equiv.toMonoidHom.comp (inclusion hEt))

include hE in
private theorem first_coordinate (x : E) : (C.equiv (inclusion hEt x)).1 = 1 := by
  obtain ⟨y, hy, he⟩ := five_le_fiveFactor C E hE hEt x.property
  have hyx : C.equiv.symm y = inclusion hEt x := Subtype.ext he
  have hcoord : y = C.equiv (inclusion hEt x) := by
    simpa only [C.equiv.apply_symm_apply] using congrArg C.equiv hyx
  exact hcoord ▸ hy.1

include hE in
private theorem fiveProjection_injective : Function.Injective (fiveProjection C E hEt) := by
  intro x y h
  apply inclusion_injective hEt
  apply C.equiv.injective
  exact Prod.ext ((first_coordinate C E hE hEt x).trans
    (first_coordinate C E hE hEt y).symm) h

include hE in
private theorem fiveProjection_card : Nat.card (fiveProjection C E hEt).range = 5 := by
  exact (Nat.card_congr (MonoidHom.ofInjective
    (fiveProjection_injective C E hE hEt)).toEquiv).symm.trans hE

include hE in
private theorem mem_centralizer_iff_second (x : involutionCentralizer t) :
    (x : G) ∈ centralizer (E : Set G) ↔
      (C.equiv x).2 ∈ (fiveProjection C E hEt).range := by
  rw [← Theory.SpecificGroups.Alternating.centralizer_eq_of_card_five
    (fiveProjection C E hEt).range (fiveProjection_card C E hE hEt)]
  constructor
  · intro hx b hb
    obtain ⟨y, rfl⟩ := hb
    have hyx : inclusion hEt y * x = x * inclusion hEt y :=
      Subtype.ext (hx y y.property)
    simpa only [map_mul, Prod.snd_mul, fiveProjection, MonoidHom.comp_apply,
      MonoidHom.coe_snd, MulEquiv.coe_toMonoidHom] using congrArg (fun z => (C.equiv z).2) hyx
  · intro hx y hy
    let yE : E := ⟨y, hy⟩
    have hs := hx (fiveProjection C E hEt yE) ⟨yE, rfl⟩
    have hc : C.equiv (inclusion hEt yE) * C.equiv x =
        C.equiv x * C.equiv (inclusion hEt yE) := by
      apply Prod.ext
      · simp only [Prod.fst_mul, first_coordinate C E hE hEt, one_mul, mul_one]
      · exact hs
    have hh : inclusion hEt yE * x = x * inclusion hEt yE :=
      C.equiv.injective (by simpa only [map_mul] using hc)
    exact congrArg Subtype.val hh

include hE in
private theorem centralizer_model_eq :
    ((centralizer (E : Set G)).subgroupOf (involutionCentralizer t)).map
      C.equiv.toMonoidHom =
      (⊤ : Subgroup E4).prod (fiveProjection C E hEt).range := by
  ext z
  rw [mem_map_equiv]
  change ((C.equiv.symm z : involutionCentralizer t) : G) ∈ centralizer (E : Set G) ↔ _
  rw [mem_centralizer_iff_second C E hE hEt, C.equiv.apply_symm_apply]
  simp only [mem_prod, mem_top, true_and]

private def centralizerSwap :
    centralizer ({rootInCentralizer E t hEt} : Set (centralizer (E : Set G))) ≃*
      (centralizer (E : Set G)).subgroupOf (involutionCentralizer t) where
  toFun x := ⟨⟨x.val.val, mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, mem_centralizer_singleton_iff.mpr
    (Subtype.ext (mem_centralizer_singleton_iff.mp x.val.property))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Restriction of the marked second-centralizer model to the full centralizer
of the root involution in C_G(E), with E retaining its original subtype. -/
noncomputable def rootCentralizerEquiv :
    centralizer ({rootInCentralizer E t hEt} : Set (centralizer (E : Set G))) ≃*
      (E4 × E) :=
  (centralizerSwap E hEt).trans <|
    (C.equiv.subgroupMap _).trans <|
    (MulEquiv.subgroupCongr (centralizer_model_eq C E hE hEt)).trans <|
    (prodEquiv (⊤ : Subgroup E4) (fiveProjection C E hEt).range).trans <|
    MulEquiv.prodCongr Subgroup.topEquiv
      (MonoidHom.ofInjective (fiveProjection_injective C E hE hEt)).symm

/-- The order and exponent bounds required by central-five quotient descent
follow from the selected source geometry. -/
theorem localCentralizerBounds (S : SelectedGeometry D) : LocalCentralizerBounds S.t := by
  intro E hE hEt
  let e := rootCentralizerEquiv S.model E hE hEt
  constructor
  · rw [Nat.card_congr e.toEquiv, Nat.card_prod, card_E4, hE]
  · intro x
    apply e.injective
    rw [map_pow, map_one]
    apply Prod.ext
    · have hs : ∀ a : E4, a ^ 2 = 1 := by decide +kernel
      have h2 := hs (e x).1
      change (e x).1 ^ 10 = 1
      rw [show 10 = 2 * 5 from rfl, pow_mul, h2, one_pow]
    · have h5 : (e x).2 ^ 5 = 1 := by
        simpa only [hE] using pow_card_eq_one' (x := (e x).2)
      change (e x).2 ^ 10 = 1
      rw [show 10 = 5 * 2 from rfl, pow_mul, h5, one_pow]

/-- Apply the concrete centralizer calculation to the literal quotient C_G(E)/E.
The independent local involution-fusion obligation is retained explicitly. -/
theorem quotientInvolutionData_of_selectedGeometry (S : SelectedGeometry D)
    (hF : LocalInvolutionFusion S.t) (E : Subgroup G) (hE : Nat.card E = 5)
    (hEt : E ≤ involutionCentralizer S.t) :
    Nonempty (QuotientInvolutionData E S.t hEt) :=
  quotientInvolutionData_of_local S.t S.other.1 (localCentralizerBounds S) hF E hE hEt

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent
