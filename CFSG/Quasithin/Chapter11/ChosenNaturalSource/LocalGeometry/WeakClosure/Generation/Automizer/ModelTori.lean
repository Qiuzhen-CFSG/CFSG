module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer.Cartan
public import Theory.GroupTheory.PCoreSplitTorus
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.Alignment
public import Theory.AtlasPort.LinearGroups.G2.EvenBorelTorus

/-!
# Odd exponents in the full natural-layer Sylow normalizers

For each literal SL₃, Sp₄ and G₂ marking, the quotient of a Sylow normalizer
by its two-core is the concrete torus Fˣ × Fˣ. Hence its odd elements have
order dividing q−1. Transport through the original quotient/action marking
preserves the Sylow and every element order. The Cartan placement theorem
then bounds n′ of the original component image by the field degree.

The full outer automizer is a further step retained by the weak-closure
owner. These results supply its inner-factor calculation, including the
full center of SL₃ and central attachments to the original module.
Source: Aschbacher--Smith A.3.15(5), E.3.37 and 11.2.1,
printed pp.50--51,239,766--767.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterE.Section06.FixedPointBounds
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

private theorem odd_normalizer_exponent_of_equiv
    {X Y : Type*} [Group X] [Finite X] [Group Y] (e : X ≃* Y) {r : ℕ}
    (hexp : ∀ (P : Sylow 2 Y) (a : Y), a ∈ normalizer (P : Set Y) →
      Odd (orderOf a) → a ^ r = 1)
    (P : Sylow 2 X) (a : X) (ha : a ∈ normalizer (P : Set X))
    (ho : Odd (orderOf a)) : a ^ r = 1 := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hmem : e a ∈ normalizer (Q : Set Y) :=
    (P : Subgroup X).le_normalizer_map e.toMonoidHom
      (mem_map_of_mem e.toMonoidHom ha)
  apply e.injective
  rw [map_pow,map_one]
  exact hexp Q (e a) hmem (by rwa [e.orderOf_eq])

/-- The three concrete model Borels have odd exponent dividing q−1. -/
theorem model_sylow_normalizer_odd_exponent (c : Coordinates D S.field)
    (P : Sylow 2 c.ModelGroup) (a : c.ModelGroup)
    (ha : a ∈ normalizer (P : Set c.ModelGroup)) (ho : Odd (orderOf a)) :
    a ^ (2 ^ S.field.degree - 1) = 1 := by
  have hq := S.field.card_eq
  cases c with
  | sl3 m =>
    let e := (Coordinates.sl3 m).groupEquiv.symm.trans m.groupEquiv
    apply odd_normalizer_exponent_of_equiv e ?_ P a ha ho
    intro Q b hb hodd
    have h := odd_pow_eq_one_of_split_torus_quotient
      (Matrix.PSL3.CartanActions.BorelQuotient.sylowSLNormalizerQuotientEquiv
        S.field.Carrier (by have := S.nonbinary; omega) hq Q)
      ⟨b,hb⟩ (by rwa [Subgroup.orderOf_mk])
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, hq] using congrArg Subtype.val h
  | sp4 m =>
    let e := (Coordinates.sp4 m).groupEquiv.symm.trans m.groupEquiv
    apply odd_normalizer_exponent_of_equiv e ?_ P a ha ho
    intro Q b hb hodd
    have h := odd_pow_eq_one_of_split_torus_quotient
      (Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.borelAtQuotientEquiv
        hq (by have := S.nonbinary; omega) Q)
      ⟨b,hb⟩ (by rwa [Subgroup.orderOf_mk])
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, hq] using congrArg Subtype.val h
  | g2 m =>
    let e := (Coordinates.g2 m).groupEquiv.symm.trans m.groupEquiv
    apply odd_normalizer_exponent_of_equiv e ?_ P a ha ho
    intro Q b hb hodd
    have h := odd_pow_eq_one_of_split_torus_quotient
      (Atlas.G2.EvenBorelTorus.sylowNormalizerQuotientEquiv Q)
      ⟨b,hb⟩ (by rwa [Subgroup.orderOf_mk])
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, hq] using congrArg Subtype.val h

/-- The exponent bound on the literal image of L in Aut_G(V). -/
theorem layer_sylow_normalizer_odd_exponent
    (P : Sylow 2 (inducedAutomizer V L)) (a : inducedAutomizer V L)
    (ha : a ∈ normalizer (P : Set (inducedAutomizer V L))) (ho : Odd (orderOf a)) :
    a ^ (2 ^ S.field.degree - 1) = 1 := by
  let c := coordinates D S
  exact odd_normalizer_exponent_of_equiv (Parameters.FullAutomizer.layerEquiv D S c)
    (model_sylow_normalizer_odd_exponent D S c) P a ha ho

/-- The original inner-layer Cartan parameter is at most the field degree. -/
theorem layer_nPrime_le : nPrime (inducedAutomizer V L) ≤ S.field.degree := by
  have hn : 0 < S.field.degree := by have := S.nonbinary; omega
  apply nPrime_le_of_normalizer_exponent ⊤
    (SolvableSylowControl.of_equiv topEquiv
      (layer_solvable_sylow_control D S (coordinates D S))) hn
  intro P a ha ho
  have ha' : a ∈ normalizer (P : Set (inducedAutomizer V L)) := by
    have hset : ((P : Subgroup (inducedAutomizer V L)) ⊓
        (⊤ : Subgroup (inducedAutomizer V L)) : Set (inducedAutomizer V L)) =
        (P : Set (inducedAutomizer V L)) := by
      ext x
      exact ⟨fun h => h.1, fun h => ⟨h, mem_top x⟩⟩
    exact hset ▸ ha
  rw [Nat.mul_comm, pow_mul, layer_sylow_normalizer_odd_exponent D S P a ha' ho, one_pow]
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer
