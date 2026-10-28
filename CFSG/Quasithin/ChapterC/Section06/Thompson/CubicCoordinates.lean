module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.CubicCentralizer
public import Mathlib.FieldTheory.Finite.GaloisField
/-!
# Binary coordinates for the actual cubic block

The A₃ fixed central kernel is trivial, so its natural-plane projection is
injective. Its module order four forces the marked field to have order two.
Transport along the finite-field isomorphism preserves the original shear
parameter and gives explicit binary equivariance on the full module.

Source: Aschbacher–Smith C.6.1, paired A₃ branch, printed p.165.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R K : Subgroup G} {F : Type*} [Field F]

omit [Finite G] in
theorem Setup.cubic_projection_injective (h : Setup R K F) (hA : IsAlternatingBlock K 3) :
    Function.Injective h.coordinates.projection := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro u hu
  have hC := (h.coordinates.projection_kernel u).mp hu
  obtain ⟨v,hv,hvu⟩ := u.property
  have hvC : v ∈ center K := by
    apply mem_center_iff.mpr
    intro k
    apply Subtype.ext
    have hh := hC k k.property
    simpa only [←hvu,Subgroup.coe_mul,Subgroup.subtype_apply] using hh
  have hvf : (⟨v,hv⟩ : blockU K) ∈ blockFixed K := hvC
  rw [alternatingThreeCoverInput K hA] at hvf
  have hv1 := congrArg (fun z : blockU K => ((z : K) : G)) (mem_bot.mp hvf)
  apply Subtype.ext
  exact hvu.symm.trans hv1

omit [Finite G] in
theorem Setup.cubic_field_card (h : Setup R K F) (hA : IsAlternatingBlock K 3) : Nat.card F = 2 := by
  let e := MulEquiv.ofBijective h.coordinates.projection
    ⟨h.cubic_projection_injective hA,h.coordinates.projection_surjective⟩
  have hc := Nat.card_congr e.toEquiv
  rw [h.cubic_module_card hA,Nat.card_congr Multiplicative.toAdd,Nat.card_fun,Nat.card_fin] at hc
  nlinarith

noncomputable def Setup.cubic_fieldEquiv (h : Setup R K F) (hA : IsAlternatingBlock K 3) :
    F ≃+* ZMod 2 := by
  let : Finite F := Nat.finite_of_card_ne_zero (by rw [h.cubic_field_card hA]; decide)
  let : Fintype F := Fintype.ofFinite F
  exact FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,h.cubic_field_card hA,ZMod.card])

noncomputable def Setup.cubic_coordinates (h : Setup R K F) (hA : IsAlternatingBlock K 3) :
    U K ≃* Multiplicative (Fin 2 → ZMod 2) :=
  (MulEquiv.ofBijective h.coordinates.projection
    ⟨h.cubic_projection_injective hA,h.coordinates.projection_surjective⟩).trans
    (AddEquiv.piCongrRight fun _ : Fin 2 => (h.cubic_fieldEquiv hA).toAddEquiv).toMultiplicative

noncomputable def Setup.cubic_parameter (h : Setup R K F) (hA : IsAlternatingBlock K 3) :
    S R →* Multiplicative (ZMod 2) :=
  (h.cubic_fieldEquiv hA).toAddEquiv.toMultiplicative.toMonoidHom.comp h.coordinates.parameter

omit [Finite G] in
theorem Setup.cubic_parameter_eq_one (h : Setup R K F) (hK : IsAlternatingBlock K 3) (s : S R) :
    h.cubic_parameter hK s = 1 ↔ (s : G) ∈ centralizer (U K : Set G) := by
  change (h.cubic_fieldEquiv hK).toAddEquiv.toMultiplicative (h.coordinates.parameter s) = 1 ↔ _
  rw [map_eq_one_iff _ (h.cubic_fieldEquiv hK).toAddEquiv.toMultiplicative.injective]
  exact h.coordinates.parameter_kernel s

omit [Finite G] in
theorem Setup.cubic_equivariant (h : Setup R K F) (hA : IsAlternatingBlock K 3)
    (s : S R) (u : U K) :
    (h.cubic_coordinates hA (moduleConjugate h.coordinates.normalizes s u)).toAdd =
      ![(h.cubic_coordinates hA u).toAdd 0 + (h.cubic_parameter hA s).toAdd *
        (h.cubic_coordinates hA u).toAdd 1,(h.cubic_coordinates hA u).toAdd 1] := by
  change (fun i => h.cubic_fieldEquiv hA ((h.coordinates.projection (moduleConjugate h.coordinates.normalizes s u)).toAdd i)) = _
  rw [h.coordinates.equivariant]
  ext i
  fin_cases i <;> simp [cubic_coordinates,cubic_parameter,AddEquiv.piCongrRight] <;> rfl
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
