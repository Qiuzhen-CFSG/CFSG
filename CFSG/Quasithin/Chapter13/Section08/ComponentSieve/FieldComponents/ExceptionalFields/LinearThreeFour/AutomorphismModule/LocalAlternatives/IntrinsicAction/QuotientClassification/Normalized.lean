module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.MarkedBorel
public import Theory.SpecificGroups.PSL3.CartanActions.SixCommutators.QuotientActions
public import Theory.SpecificGroups.PSL3.CartanActions.ActorCoverage
public import Theory.FieldTheory.FiniteAutomorphismOrder

/-!
# The full SL₃(4) Borel quotient and its marked eigenspaces

The quotient by the upper unitriangular subgroup is the full two-parameter
multiplicative torus. A Sylow-preserving linear factor acts trivially on this
quotient; the field factor inverts both coordinates, while opposition graph
inverts and interchanges them. A nontrivial fixed marked image and a nontrivial
inverted marked image exclude both cases without a graph factor. The remaining
coordinate equations put the inverted image (graph) or fixed image (graph-field)
on the scalar diagonal. All containments retain the unitriangular kernel.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.955 (PDF p.972),
combined manuscript of 1 March 2004. The matrix calculations use the
CartanActions leaves; no invariance of a chosen torus is assumed.
-/

@[expose] public section

open Subgroup Representation.SL3FourNaturalDual
open Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage
open Matrix.PSL3.CartanActions Matrix.PSL3.CartanActions.BorelQuotient
open Matrix.PSL3.CartanActions.SixCommutators
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.IntrinsicAction.QuotientClassification
/-- The full special-linear Borel quotient; its scalar diagonal is retained. -/
noncomputable def quotientMap : borelSL F →* (Fˣ × Fˣ) :=
  (quotientSLTorusEquiv F sl3Field_card).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 (borelSL F)))

theorem quotientMap_torus (d : Fˣ × Fˣ) :
    quotientMap ⟨torusSL F d, torusSL_mem_borel F d⟩ = d :=
  quotientSLTorusEquiv_mk_torus F sl3Field_card d

theorem quotientMap_eq_one (x : borelSL F) : quotientMap x = 1 ↔ x.val ∈ unipotentSL F := by
  change quotientSLTorusEquiv F sl3Field_card (QuotientGroup.mk x) = 1 ↔ _
  rw [map_eq_one_iff _ (quotientSLTorusEquiv F sl3Field_card).injective,
    QuotientGroup.eq_one_iff, twoCoreSL_eq F sl3Field_card]
  rfl

theorem quotientMap_unipotent (u : SL) (hu : u ∈ unipotentSL F) :
    quotientMap ⟨u, unipotentSL_le_borelSL F hu⟩ = 1 := (quotientMap_eq_one _).mpr hu

theorem quotientMap_factor (x : borelSL F) : ∃ u ∈ unipotentSL F,
    x.val = u * torusSL F (quotientMap x) := by
  obtain ⟨d, u, hu, he⟩ := borelSL_factorization F x.val x.property
  have hx : x = (⟨u, unipotentSL_le_borelSL F hu⟩ : borelSL F) *
      ⟨torusSL F d, torusSL_mem_borel F d⟩ := Subtype.ext he
  have hq : quotientMap x = d := by rw [hx, map_mul, quotientMap_unipotent u hu, quotientMap_torus, one_mul]
  exact ⟨u, hu, hq.symm ▸ he⟩

theorem unit_cube (a : Fˣ) : a ^ 3 = 1 := by
  have h := pow_card_eq_one' (x := a)
  rwa [Nat.card_units, sl3Field_card] at h

theorem field_unit_inverse (σ : F ≃+* F) (hσ : σ ≠ 1) (a : Fˣ) :
    Units.map σ.toMonoidHom a = a⁻¹ := by
  have hf : Representation.SL2FourNatural.fieldFrobenius ≠ 1 := by
    intro h
    have hx := DFunLike.congr_fun h (⟨0, 1⟩ : F)
    change (⟨0, 1⟩ : F) ^ 2 = ⟨0, 1⟩ at hx
    have hn : (⟨0, 1⟩ : F) ^ 2 ≠ ⟨0, 1⟩ := by decide +kernel
    exact hn hx
  have hc : Nat.card (F ≃+* F) = 2 :=
    FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two sl3Field_card
  obtain ⟨τ, _, ht⟩ := (Nat.card_eq_two_iff' (1 : F ≃+* F)).mp hc
  have hs : σ = Representation.SL2FourNatural.fieldFrobenius := (ht σ hσ).trans (ht _ hf).symm
  rw [hs]
  have he : Units.map Representation.SL2FourNatural.fieldFrobenius.toMonoidHom a = a ^ 2 :=
    Units.ext rfl
  rw [he]
  apply eq_inv_of_mul_eq_one_left
  simpa only [← pow_succ] using unit_cube a

theorem quotientMap_central (x : borelSL F) (h : (quotientMap x).1 = (quotientMap x).2) :
    x.val ∈ center SL ⊔ unipotentSL F := by
  obtain ⟨u, hu, he⟩ := quotientMap_factor x
  have hz : torusSL F (quotientMap x) ∈ center SL := by
    rw [← projection_ker, MonoidHom.mem_ker]
    exact (torusMap_eq_one_iff F _).mpr ⟨h, unit_cube _⟩
  rw [he]
  have hU : unipotentSL F ≤ center SL ⊔ unipotentSL F := le_sup_right
  have hZ : center SL ≤ center SL ⊔ unipotentSL F := le_sup_left
  exact (center SL ⊔ unipotentSL F).mul_mem (hU hu) (hZ hz)

theorem quotientMap_linear_torus (m : Matrix.GeneralLinearGroup (Fin 3) F)
    (hm : (unipotent F).map (linearConj F m).toMonoidHom = unipotent F)
    (d : Fˣ × Fˣ) (hb : linearConjSL F m (torusSL F d) ∈ borelSL F) :
    quotientMap ⟨linearConjSL F m (torusSL F d), hb⟩ = d := by
  obtain ⟨u, hu, he⟩ := linearConjSL_torus_factor F m hm d
  have he' : (⟨linearConjSL F m (torusSL F d), hb⟩ : borelSL F) =
      ⟨u, unipotentSL_le_borelSL F hu⟩ * ⟨torusSL F d, torusSL_mem_borel F d⟩ :=
    Subtype.ext he
  rw [he', map_mul, quotientMap_unipotent u hu, quotientMap_torus, one_mul]

def parameters (σ : F ≃+* F) (ε : Bool) (d : Fˣ × Fˣ) : Fˣ × Fˣ :=
  if ε then (Units.map σ.toMonoidHom d.2⁻¹, Units.map σ.toMonoidHom d.1⁻¹)
  else (Units.map σ.toMonoidHom d.1, Units.map σ.toMonoidHom d.2)

theorem actor_torus (m : Matrix.GeneralLinearGroup (Fin 3) F)
    (σ : F ≃+* F) (ε : Bool) (d : Fˣ × Fˣ) :
    specialActor F m σ ε (torusSL F d) = linearConjSL F m (torusSL F (parameters σ ε d)) := by
  cases ε <;> simp [specialActor, parameters, MulAut.mul_apply, oppositionGraphSL_torusSL, field_torusSL]

theorem quotientMap_actor (m : Matrix.GeneralLinearGroup (Fin 3) F)
    (σ : F ≃+* F) (ε : Bool)
    (hs : (unipotentSL F).map (specialActor F m σ ε).toMonoidHom = unipotentSL F)
    (x : borelSL F) (hx : specialActor F m σ ε x.val ∈ borelSL F) :
    quotientMap ⟨specialActor F m σ ε x.val, hx⟩ = parameters σ ε (quotientMap x) := by
  have hm := linear_part_unipotent F m σ ε (by
    rw [← centerAction_specialActor]
    exact centerAction_unipotent F _ hs)
  obtain ⟨u, hu, he⟩ := quotientMap_factor x
  have hau : specialActor F m σ ε u ∈ unipotentSL F := hs.le (mem_map_of_mem _ hu)
  have hbt : linearConjSL F m (torusSL F (parameters σ ε (quotientMap x))) ∈ borelSL F :=
    (linearConjSL_borel F m hm).le (mem_map_of_mem _ (torusSL_mem_borel F _))
  have he' : (⟨specialActor F m σ ε x.val, hx⟩ : borelSL F) =
      ⟨specialActor F m σ ε u, unipotentSL_le_borelSL F hau⟩ *
      ⟨linearConjSL F m (torusSL F (parameters σ ε (quotientMap x))), hbt⟩ := by
    apply Subtype.ext
    change specialActor F m σ ε x.val = _
    exact (congrArg (specialActor F m σ ε) he).trans
      ((map_mul (specialActor F m σ ε) u (torusSL F (quotientMap x))).trans
        (congrArg (specialActor F m σ ε u * ·) (actor_torus m σ ε (quotientMap x))))
  rw [he', map_mul, quotientMap_unipotent _ hau, quotientMap_linear_torus m hm, one_mul]

theorem borel_stable (α : MulAut SL)
    (hs : (unipotentSL F).map α.toMonoidHom = unipotentSL F) :
    (borelSL F).map α.toMonoidHom = borelSL F := by
  rw [← normalizer_unipotentSL, map_equiv_normalizer_eq, hs]

theorem quotientMap_fixed (α : MulAut SL) (x : borelSL F)
    (hx : α x.val ∈ borelSL F) (hf : α x.val * x.val⁻¹ ∈ unipotentSL F) :
    quotientMap ⟨α x.val, hx⟩ = quotientMap x := by
  apply mul_inv_eq_one.mp
  rw [← map_inv, ← map_mul]
  exact (quotientMap_eq_one _).mpr hf

theorem quotientMap_inverted (α : MulAut SL) (x : borelSL F)
    (hx : α x.val ∈ borelSL F) (hi : α x.val * x.val ∈ unipotentSL F) :
    quotientMap ⟨α x.val, hx⟩ = (quotientMap x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul]
  exact (quotientMap_eq_one _).mpr hi

theorem torus_eq_one_of_eq_inv (t : Fˣ × Fˣ) (h : t = t⁻¹) : t = 1 := by
  have h2 : t ^ 2 = 1 := by
    rw [pow_two]
    exact (congrArg (t * ·) h).trans (mul_inv_cancel t)
  have h3 : t ^ 3 = 1 := Prod.ext (unit_cube t.1) (unit_cube t.2)
  calc
    t = t ^ 2 * t := by rw [h2, one_mul]
    _ = t ^ 3 := (pow_succ t 2).symm
    _ = 1 := h3

@[simp] theorem parameters_one_false (t : Fˣ × Fˣ) : parameters 1 false t = t := by
  ext <;> rfl

@[simp] theorem parameters_one_true (t : Fˣ × Fˣ) :
    parameters 1 true t = (t.2⁻¹, t.1⁻¹) := by
  ext <;> rfl

theorem parameters_nontrivial_false (σ : F ≃+* F) (hσ : σ ≠ 1) (t : Fˣ × Fˣ) :
    parameters σ false t = t⁻¹ := by
  exact Prod.ext (field_unit_inverse σ hσ _) (field_unit_inverse σ hσ _)

theorem parameters_nontrivial_true (σ : F ≃+* F) (hσ : σ ≠ 1) (t : Fˣ × Fˣ) :
    parameters σ true t = (t.2, t.1) := by
  simp only [parameters, ↓reduceIte, field_unit_inverse σ hσ, inv_inv]

theorem marked_parameters (m : Matrix.GeneralLinearGroup (Fin 3) F)
    (σ : F ≃+* F) (ε : Bool)
    (hs : (unipotentSL F).map (specialActor F m σ ε).toMonoidHom = unipotentSL F)
    (A₀ Ap : Subgroup SL) (h₀ : A₀ ≤ borelSL F) (hp : Ap ≤ borelSL F)
    (hn₀ : ¬ A₀ ≤ unipotentSL F) (hnp : ¬ Ap ≤ unipotentSL F)
    (hf : ∀ x ∈ A₀, specialActor F m σ ε x * x⁻¹ ∈ unipotentSL F)
    (hi : ∀ x ∈ Ap, specialActor F m σ ε x * x ∈ unipotentSL F) :
    ε = true ∧ (σ = 1 → Ap ≤ center SL ⊔ unipotentSL F) ∧
      (σ ≠ 1 → A₀ ≤ center SL ⊔ unipotentSL F) := by
  have hb := borel_stable _ hs
  have hfix (x : SL) (hx : x ∈ A₀) :
      parameters σ ε (quotientMap ⟨x, h₀ hx⟩) = quotientMap ⟨x, h₀ hx⟩ := by
    have ha := hb.le (mem_map_of_mem _ (h₀ hx))
    exact (quotientMap_actor m σ ε hs ⟨x, h₀ hx⟩ ha).symm.trans
      (quotientMap_fixed _ ⟨x, h₀ hx⟩ ha (hf x hx))
  have hinv (x : SL) (hx : x ∈ Ap) :
      parameters σ ε (quotientMap ⟨x, hp hx⟩) = (quotientMap ⟨x, hp hx⟩)⁻¹ := by
    have ha := hb.le (mem_map_of_mem _ (hp hx))
    exact (quotientMap_actor m σ ε hs ⟨x, hp hx⟩ ha).symm.trans
      (quotientMap_inverted _ ⟨x, hp hx⟩ ha (hi x hx))
  have he : ε = true := by
    cases ε with
    | true => rfl
    | false =>
      exfalso
      by_cases hσ : σ = 1
      · apply hnp
        intro x hx
        apply (quotientMap_eq_one ⟨x, hp hx⟩).mp
        apply torus_eq_one_of_eq_inv
        simpa only [hσ, parameters_one_false] using hinv x hx
      · apply hn₀
        intro x hx
        apply (quotientMap_eq_one ⟨x, h₀ hx⟩).mp
        apply torus_eq_one_of_eq_inv
        exact ((parameters_nontrivial_false σ hσ _).symm.trans (hfix x hx)).symm
  refine ⟨he, ?_, ?_⟩
  · intro hσ x hx
    apply quotientMap_central ⟨x, hp hx⟩
    have ht := hinv x hx
    rw [he, hσ, parameters_one_true] at ht
    exact (inv_inj.mp (congrArg Prod.fst ht)).symm
  · intro hσ x hx
    apply quotientMap_central ⟨x, h₀ hx⟩
    have ht := hfix x hx
    rw [he, parameters_nontrivial_true σ hσ] at ht
    exact (congrArg Prod.fst ht).symm

/-- Classification in upper-unitriangular coordinates, using the two nontrivial
marked quotient images and their prescribed actions. -/
theorem normalized_classification (α : MulAut SL)
    (hs : (unipotentSL F).map α.toMonoidHom = unipotentSL F)
    (A₀ Ap : Subgroup SL) (h₀ : A₀ ≤ borelSL F) (hp : Ap ≤ borelSL F)
    (hn₀ : ¬ A₀ ≤ unipotentSL F) (hnp : ¬ Ap ≤ unipotentSL F)
    (hf : ∀ x ∈ A₀, α x * x⁻¹ ∈ unipotentSL F)
    (hi : ∀ x ∈ Ap, α x * x ∈ unipotentSL F)
    (hcover : standard F = ⊤) :
    ∃ (m : Matrix.GeneralLinearGroup (Fin 3) F) (σ : F ≃+* F),
      α = specialActor F m σ true ∧
        ((σ = 1 ∧ Ap ≤ center SL ⊔ unipotentSL F) ∨
         (σ ≠ 1 ∧ A₀ ≤ center SL ⊔ unipotentSL F)) := by
  obtain ⟨m, σ, ε, rfl⟩ :=
    Matrix.PSL3.CartanActions.ActorCoverage.specialCoverage_of_standard_eq_top F hcover α
  obtain ⟨he, hp, hz⟩ := marked_parameters m σ ε hs A₀ Ap h₀ hp hn₀ hnp hf hi
  refine ⟨m, σ, congrArg (specialActor F m σ) he, ?_⟩
  by_cases hσ : σ = 1
  · exact Or.inl ⟨hσ, hp hσ⟩
  · exact Or.inr ⟨hσ, hz hσ⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.IntrinsicAction.QuotientClassification
