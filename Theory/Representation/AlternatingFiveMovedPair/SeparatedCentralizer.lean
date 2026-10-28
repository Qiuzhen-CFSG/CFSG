module
public import Theory.Representation.ScalarMultiplicity
public import Theory.Representation.AlternatingFiveMovedPair.Mixed.ScalarCommutants
public import Theory.Representation.SL2FourNaturalOrbits.SelfDual
public import Theory.LinearAlgebra.SmallMultiplicityGroups

/-!
# Centralizers of separated homogeneous binary A₅ pairs

The natural binary four-space has scalar commutant F₄, whereas the deleted
five-letter four-space has scalar commutant F₂. Both have zero common fixed
space. Consequently every faithful actor commuting with the literal separate
A₅ factors embeds into two full multiplicity general linear groups. Equal
copies may mix arbitrarily; preservation of the two supports is proved.

The coordinate consumers retain the original module, the marked A₅² action,
and the faithful commuting actor. When an independent argument supplies
multiplicity at most two and order prime to 15, the small general linear
group arithmetic makes that actor a two-group. These are the intrinsic
centralizer steps in Aschbacher--Smith D.3.9, printed pp.199--201, and the
separated case of D.3.21, printed p.206.
-/

@[expose] public noncomputable section
namespace Representation.AlternatingFiveMovedPair.SeparatedCentralizer
open SL2FourNatural SL2FourNatural.SemilinearNormalizer
abbrev Alt := alternatingGroup (Fin 5)
abbrev Natural := SL2FourNatural.V
abbrev Deleted := BinaryPermutation.natural (Fin 5)
abbrev natural : Representation (ZMod 2) Alt Natural :=
  Mixed.naturalAction.comp Alt.subtype
abbrev deleted : Representation (ZMod 2) Alt Deleted :=
  BinaryPermutation.alternatingNaturalRepresentation (Fin 5)

private theorem natural_special (g : SL) (v : Natural) :
    natural (alternatingFiveEquiv g) v = Mixed.ν g v := by
  change Mixed.naturalAction (alternatingFiveEquiv g).val v = action g v
  rw [alternatingFiveEquiv_apply,Mixed.naturalAction_special]
  rfl
private theorem deleted_special (g : SL) (v : Deleted) :
    deleted (alternatingFiveEquiv g) v = Mixed.δ g v := rfl

theorem natural_fixed_eq_zero (v : Natural) (hv : ∀ g, natural g v = v) : v = 0 := by
  apply SL2FourNatural.natural_fixed_eq_zero
  intro g
  change Mixed.ν g v = v
  exact (natural_special g v).symm.trans (hv (alternatingFiveEquiv g))

theorem natural_commuting_scalar (f : Module.End (ZMod 2) Natural)
    (hf : ∀ g v, f (natural g v) = natural g (f v)) :
    ∃ c : F, ∀ v, f v = c • v := by
  apply Mixed.natural_commuting_scalar f
  intro g v
  simpa only [natural_special] using hf (alternatingFiveEquiv g) v

theorem deleted_fixed_eq_zero (v : Deleted) (hv : ∀ g, deleted g v = v) : v = 0 := by
  let e := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
  let c : Equiv.Perm (Fin 5) :=
    Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4
  have hc : c ∈ alternatingGroup (Fin 5) := by
    simp only [Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  have he (w : BinaryPermutation.core (Fin 5)) :
      e (BinaryPermutation.coreRepresentation (Fin 5) c w) = deleted ⟨c,hc⟩ (e w) :=
    BinaryPermutation.coreEquivNatural_equivariant (Fin 5) (by decide) c w
  have hfix : BinaryPermutation.coreRepresentation (Fin 5) c (e.symm v) = e.symm v := by
    apply e.injective
    rw [he,e.apply_symm_apply,hv]
  have hz : e.symm v = 0 := by
    have h : ∀ w : BinaryPermutation.Full (Fin 5), (∑ i, w i) = 0 →
        BinaryPermutation.representation (Fin 5) c w = w → w = 0 := by decide +kernel
    exact Subtype.ext (h _ (e.symm v).property (congrArg Subtype.val hfix))
  have hh := congrArg e hz
  simpa only [e.apply_symm_apply,map_zero] using hh

theorem deleted_commuting_scalar (f : Module.End (ZMod 2) Deleted)
    (hf : ∀ g v, f (deleted g v) = deleted g (f v)) :
    ∃ c : ZMod 2, ∀ v, f v = c • v := by
  apply Mixed.deleted_commuting_scalar f
  intro g v
  simpa only [deleted_special] using hf (alternatingFiveEquiv g) v

local instance : Nontrivial Deleted :=
  Module.nontrivial_of_finrank_pos (by rw [Mixed.finrank_deleted]; decide)

variable {C I W : Type*} [Group C] [Fintype I] [DecidableEq I]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The arbitrary-multiplicity natural A₅² commutant embeds over F₄. -/
theorem natural_injective_unit_pair
    (ρ : Representation (ZMod 2) C ((I → Natural) × (I → Natural)))
    (hfaith : Function.Injective ρ)
    (hc : ∀ a g h x y, ρ a (fun i => natural g (x i), fun i => natural h (y i)) =
      (fun i => natural g ((ρ a (x,y)).1 i), fun i => natural h ((ρ a (x,y)).2 i))) :
    ∃ f : C →* (Module.End F (I → F))ˣ × (Module.End F (I → F))ˣ,
      Function.Injective f :=
  ScalarMultiplicity.exists_injective_unit_pair natural natural_fixed_eq_zero
    natural_commuting_scalar ρ hfaith hc

/-- The arbitrary-multiplicity deleted A₅² commutant embeds over F₂. -/
theorem deleted_injective_unit_pair
    (ρ : Representation (ZMod 2) C ((I → Deleted) × (I → Deleted)))
    (hfaith : Function.Injective ρ)
    (hc : ∀ a g h x y, ρ a (fun i => deleted g (x i), fun i => deleted h (y i)) =
      (fun i => deleted g ((ρ a (x,y)).1 i), fun i => deleted h ((ρ a (x,y)).2 i))) :
    ∃ f : C →* (Module.End (ZMod 2) (I → ZMod 2))ˣ ×
      (Module.End (ZMod 2) (I → ZMod 2))ˣ, Function.Injective f :=
  ScalarMultiplicity.exists_injective_unit_pair deleted deleted_fixed_eq_zero
    deleted_commuting_scalar ρ hfaith hc

/-- Actual marked natural coordinates transport a faithful original commuting
actor into the two multiplicity general linear groups over F₄. -/
theorem natural_injective_unit_pair_of_coordinates
    (α : Representation (ZMod 2) (Alt × Alt) W) (ρ : Representation (ZMod 2) C W)
    (hfaith : Function.Injective ρ)
    (hcomm : ∀ a d v, ρ a (α d v) = α d (ρ a v))
    (e : W ≃ₗ[ZMod 2] ((I → Natural) × (I → Natural)))
    (he : ∀ d v, e (α d v) =
      (fun i => natural d.1 ((e v).1 i), fun i => natural d.2 ((e v).2 i))) :
    ∃ f : C →* (Module.End F (I → F))ˣ × (Module.End F (I → F))ˣ,
      Function.Injective f :=
  ScalarMultiplicity.exists_injective_unit_pair_of_coordinates natural natural_fixed_eq_zero
    natural_commuting_scalar α ρ hfaith hcomm e he

/-- Actual marked deleted coordinates transport a faithful original commuting
actor into the two multiplicity general linear groups over F₂. -/
theorem deleted_injective_unit_pair_of_coordinates
    (α : Representation (ZMod 2) (Alt × Alt) W) (ρ : Representation (ZMod 2) C W)
    (hfaith : Function.Injective ρ)
    (hcomm : ∀ a d v, ρ a (α d v) = α d (ρ a v))
    (e : W ≃ₗ[ZMod 2] ((I → Deleted) × (I → Deleted)))
    (he : ∀ d v, e (α d v) =
      (fun i => deleted d.1 ((e v).1 i), fun i => deleted d.2 ((e v).2 i))) :
    ∃ f : C →* (Module.End (ZMod 2) (I → ZMod 2))ˣ ×
      (Module.End (ZMod 2) (I → ZMod 2))ˣ, Function.Injective f :=
  ScalarMultiplicity.exists_injective_unit_pair_of_coordinates deleted deleted_fixed_eq_zero
    deleted_commuting_scalar α ρ hfaith hcomm e he

/-- The prime-to-15 original centralizer is a two-group once the independently
proved natural multiplicity bound supplies k ≤ 2. -/
theorem natural_isPGroup_two_of_coordinates [Finite C] {k : ℕ} (hk : k ≤ 2)
    (α : Representation (ZMod 2) (Alt × Alt) W) (ρ : Representation (ZMod 2) C W)
    (hfaith : Function.Injective ρ)
    (hcomm : ∀ a d v, ρ a (α d v) = α d (ρ a v))
    (e : W ≃ₗ[ZMod 2] ((Fin k → Natural) × (Fin k → Natural)))
    (he : ∀ d v, e (α d v) =
      (fun i => natural d.1 ((e v).1 i), fun i => natural d.2 ((e v).2 i)))
    (hthree : Nat.Coprime 3 (Nat.card C)) (hfive : Nat.Coprime 5 (Nat.card C)) :
    IsPGroup 2 C := by
  obtain ⟨f,hf⟩ := natural_injective_unit_pair_of_coordinates α ρ hfaith hcomm e he
  have hF : Nat.card F = 2 ∨ Nat.card F = 4 :=
    Or.inr (by simpa only [Nat.card_eq_fintype_card] using SL2FourNatural.card_field)
  exact Theory.LinearAlgebra.SmallMultiplicityGroups.isPGroup_two_of_injective_unit_pair
    hF hF hk hk f hf hthree hfive

/-- The prime-to-15 original centralizer is a two-group once the independently
proved deleted multiplicity bound supplies k ≤ 2. -/
theorem deleted_isPGroup_two_of_coordinates [Finite C] {k : ℕ} (hk : k ≤ 2)
    (α : Representation (ZMod 2) (Alt × Alt) W) (ρ : Representation (ZMod 2) C W)
    (hfaith : Function.Injective ρ)
    (hcomm : ∀ a d v, ρ a (α d v) = α d (ρ a v))
    (e : W ≃ₗ[ZMod 2] ((Fin k → Deleted) × (Fin k → Deleted)))
    (he : ∀ d v, e (α d v) =
      (fun i => deleted d.1 ((e v).1 i), fun i => deleted d.2 ((e v).2 i)))
    (hthree : Nat.Coprime 3 (Nat.card C)) (hfive : Nat.Coprime 5 (Nat.card C)) :
    IsPGroup 2 C := by
  obtain ⟨f,hf⟩ := deleted_injective_unit_pair_of_coordinates α ρ hfaith hcomm e he
  have hF : Nat.card (ZMod 2) = 2 ∨ Nat.card (ZMod 2) = 4 :=
    Or.inl (by simp)
  exact Theory.LinearAlgebra.SmallMultiplicityGroups.isPGroup_two_of_injective_unit_pair
    hF hF hk hk f hf hthree hfive
end Representation.AlternatingFiveMovedPair.SeparatedCentralizer
