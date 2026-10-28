module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment.Conditions
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment.Plane
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment.Transvection

/-!
# The original plane commutator is its marked point

The source intersection line removes every field twist from the elementary
actor. Each resulting involution preserves the actual flag, so its displacement
on the plane lies in the point. Noncentrality gives a nonzero displacement;
linearity and the injective original projection give all its field multiples
as actual commutators. Thus the commutator is exactly V₁, including at q=4.

Source: Aschbacher--Smith, 11.5.3(3), printed pp.779--780.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {E : Geometry D} (F₀ : MarkedFlag E)

private theorem projection_injective (c : Coordinates D E.input.field)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) : Function.Injective c.projection := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro v hv
  apply mem_bot.mpr
  apply Subtype.ext
  apply mem_bot.mp
  rw [← hfixed]
  exact ⟨v.property, (c.projection_eq_one_iff v).mp hv⟩

private theorem projection_commutator (c : Coordinates D E.input.field) (a : T) (v : V) :
    (c.projection (V.normalizerMonoidHom (inclusion E.input.sylow_normalizes a) v * v⁻¹)).toAdd =
      c.conjugationAction D.sylow_normalizes_component E.input.sylow_normalizes a
        (c.projection v).toAdd - (c.projection v).toAdd := by
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv, ← sub_eq_add_neg,
    ← c.conjugationAction_projection]

include F₀ in
theorem plane_movement
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hNV : normalizer (V : Set G) ≤ normalizer (L : Set G)) :
    PlaneMovement (E := E) := by
  intro A hAT hA hnon hline
  obtain ⟨l, hl, hsmall⟩ := hline
  let c := F₀.action.coordinates
  let ρ := c.conjugationAction D.sylow_normalizes_component E.input.sylow_normalizes
  have hp : c.preimage (F₀.flag.space 1) = E.V₂ := by
    change D.centralQuotientPreimage _ = D.centralQuotientPreimage E.plane
    rw [F₀.plane_eq]
  have hq : c.preimage (F₀.flag.space 0) = E.V₁ := by
    change D.centralQuotientPreimage _ = D.centralQuotientPreimage E.point
    rw [F₀.point_eq]
  have hlin (a : A) (t : E.input.field.Carrier) (v : c.Space) :
      ρ (inclusion hAT a) (t • v) = t • ρ (inclusion hAT a) v :=
    sylow_linear_of_small_plane_commutator F₀ hNV A hAT ⟨l, hl⟩ hsmall a t v
  have hinv (i : Fin 3) (a : T) (v : c.Space) (hv : v ∈ F₀.flag.space i) :
      ρ a v ∈ F₀.flag.space i :=
    (c.normalizes_preimage_iff D.sylow_normalizes_component E.input.sylow_normalizes
      (F₀.flag.space i)).mp (F₀.flag.invariant i) a v hv
  have : Finite c.Space := Finite.of_surjective
    (fun v : V => (c.projection v).toAdd) (fun x => by
      obtain ⟨v, hv⟩ := c.projection_surjective (Multiplicative.ofAdd x)
      exact ⟨v, congrArg Multiplicative.toAdd hv⟩)
  have : FiniteDimensional E.input.field.Carrier c.Space := Module.Finite.of_finite
  let := hA
  have hsq (a : A) : a ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) a
  have hpoint (a : A) (x : c.Space) (hx : x ∈ F₀.flag.space 1) :
      ρ (inclusion hAT a) x - x ∈ F₀.flag.space 0 := by
    let e : Module.End E.input.field.Carrier c.Space :=
      { toFun := ρ (inclusion hAT a)
        map_add' := (ρ (inclusion hAT a)).map_add
        map_smul' := hlin a }
    have he (v : c.Space) : e (e v) = v := by
      change ρ (inclusion hAT a) (ρ (inclusion hAT a) v) = v
      rw [← Module.End.mul_apply, ← map_mul, ← map_mul, ← pow_two, hsq, map_one, map_one]
      rfl
    exact PlaneDisplacement.displacement_mem_point e he (F₀.flag.space 1) (F₀.flag.space 0)
      (F₀.flag.dimension 1) (F₀.flag.dimension 0) (F₀.flag.nested (by decide))
      (hinv 1 _) (hinv 0 _) x hx
  have hle : ⁅A, E.V₂⁆ ≤ E.V₁ := by
    apply commutator_le.mpr
    intro a ha v hv
    let v' : V := ⟨v, D.centralQuotientPreimage_le _ hv⟩
    let a' : A := ⟨a, ha⟩
    let z := V.normalizerMonoidHom
      (inclusion E.input.sylow_normalizes (inclusion hAT a')) v' * v'⁻¹
    change (z : G) ∈ E.V₁
    rw [← hq]
    apply (c.mem_preimage _ z).mpr
    change (c.projection z).toAdd ∈ _
    rw [projection_commutator]
    apply hpoint a'
    exact (c.mem_preimage _ v').mp (hp ▸ hv)
  have hne : ⁅A, E.V₂⁆ ≠ ⊥ := by
    intro h
    apply hnon
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h)
  obtain ⟨a, x, hxP, hx⟩ : ∃ a : A, ∃ x ∈ F₀.flag.space 1,
      ρ (inclusion hAT a) x ≠ x := by
    by_contra! h
    apply hne
    apply bot_unique
    apply commutator_le.mpr
    intro a ha v hv
    let v' : V := ⟨v, D.centralQuotientPreimage_le _ hv⟩
    let a' : A := ⟨a, ha⟩
    let z := V.normalizerMonoidHom
      (inclusion E.input.sylow_normalizes (inclusion hAT a')) v' * v'⁻¹
    have hz : z = 1 := by
      apply projection_injective c hfixed
      apply Multiplicative.toAdd.injective
      rw [map_one]
      change (c.projection z).toAdd = 0
      rw [projection_commutator]
      exact sub_eq_zero.mpr (h a' _ ((c.mem_preimage _ v').mp (hp ▸ hv)))
    exact mem_bot.mpr (congrArg Subtype.val hz)
  let w := ρ (inclusion hAT a) x - x
  have hw : w ≠ 0 := sub_ne_zero.mpr hx
  have hspan : F₀.flag.space 0 = Submodule.span E.input.field.Carrier {w} :=
    eq_span_singleton_of_mem_of_finrank_eq_one (F₀.flag.dimension 0) (hpoint a x hxP) hw
  rw [commutator_comm]
  apply le_antisymm hle
  intro v hv
  let v' : V := ⟨v, D.centralQuotientPreimage_le _ hv⟩
  have hv' := (c.mem_preimage _ v').mp (hq ▸ hv)
  rw [hspan] at hv'
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hv'
  obtain ⟨y, hy⟩ := c.projection_surjective (Multiplicative.ofAdd (t • x))
  have hyP : (y : G) ∈ E.V₂ := by
    rw [← hp]
    apply (c.mem_preimage _ y).mpr
    change (c.projection y).toAdd ∈ _
    rw [hy]
    exact (F₀.flag.space 1).smul_mem t hxP
  let z := V.normalizerMonoidHom
    (inclusion E.input.sylow_normalizes (inclusion hAT a)) y * y⁻¹
  have hz : z = v' := by
    apply projection_injective c hfixed
    apply Multiplicative.toAdd.injective
    rw [projection_commutator, hy]
    change ρ (inclusion hAT a) (t • x) - t • x = (c.projection v').toAdd
    rw [hlin, ← smul_sub]
    exact ht
  have hm : (z : G) ∈ ⁅A, E.V₂⁆ := commutator_mem_commutator a.property hyP
  rwa [hz] at hm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment
