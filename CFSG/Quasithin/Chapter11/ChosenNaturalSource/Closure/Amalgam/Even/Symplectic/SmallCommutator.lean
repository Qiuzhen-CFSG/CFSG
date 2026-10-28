module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic.Action
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic.Displacement
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.Cardinalities

/-!
# Small commutators are field lines in the actual natural module

Coordinate displacement is the image of a literal ambient commutator.
If that commutator has order at most q, the involutory actors have no field
twist. A nonzero displacement then supplies all scalar multiples of a
nonzero vector, hence a full field line inside the commutator. The order
bound forces equality. Triviality of C_V(L) is used to reflect equality
through the original quotient, rather than silently dropping its kernel.

Source.lean applies this result in both orientations of the critical pair.
Source: Aschbacher--Smith, 11.5.8, refs/quasithin.pdf, printed p.784.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} {E : Closure.Geometry D}
  (m : ActionEquiv D.centralQuotientAction (restrictScalars (k := ZMod 2) (symplecticNatural (k := E.input.field.Carrier) 2)))

/-- The size of one actual displacement is bounded by the original commutator. -/
theorem displacement_card_le_commutator (A : Subgroup G)
    (hAL : A ≤ normalizer (L : Set G)) (hAV : A ≤ normalizer (V : Set G)) (a : A) :
    Nat.card (((Coordinates.sp4 m).conjugationAction hAL hAV a).toAddMonoidHom -
      AddMonoidHom.id _).range ≤ Nat.card (⁅A, V⁆ : Subgroup G) := by
  let c := Coordinates.sp4 m
  let ρ := c.conjugationAction hAL hAV
  let δ := (ρ a).toAddMonoidHom - AddMonoidHom.id c.Space
  have hC : ⁅A, V⁆ ≤ V := le_normalizer_iff_commutator_le_right.mp hAV
  let p : (⁅A, V⁆ : Subgroup G) →* Multiplicative c.Space :=
    c.projection.comp (inclusion hC)
  let : Finite p.range := Finite.of_surjective p.rangeRestrict p.rangeRestrict_surjective
  have hδ (x : δ.range) : Multiplicative.ofAdd x.val ∈ p.range := by
    obtain ⟨v, hv⟩ := x.property
    obtain ⟨w, hw⟩ := c.projection_surjective (Multiplicative.ofAdd v)
    let z : V := V.normalizerMonoidHom (inclusion hAV a) w * w⁻¹
    have hz : (z : G) ∈ ⁅A, V⁆ := commutator_mem_commutator a.property w.property
    refine ⟨⟨z, hz⟩, ?_⟩
    change c.projection z = Multiplicative.ofAdd x.val
    apply Multiplicative.toAdd.injective
    change (c.projection z).toAdd = x.val
    rw [← hv]
    change (c.projection (V.normalizerMonoidHom (inclusion hAV a) w * w⁻¹)).toAdd =
      ρ a v - v
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
    rw [← c.conjugationAction_projection hAL hAV, hw]
    rfl
  let j : δ.range → p.range := fun x => ⟨Multiplicative.ofAdd x.val, hδ x⟩
  exact (Nat.card_le_card_of_injective j (by
    intro x y h
    exact Subtype.ext (congrArg (fun z : p.range => z.val.toAdd) h))).trans
      (Nat.card_le_card_of_surjective p.rangeRestrict p.rangeRestrict_surjective)

/-- A square-one actor with a commutator of order at most q acts linearly
on the original marked four-space. Semilinearity is proved from the source. -/
theorem linear_of_commutator_card_le (A : Subgroup G)
    (hAL : A ≤ normalizer (L : Set G)) (hAV : A ≤ normalizer (V : Set G))
    (a : A) (ha : a ^ 2 = 1)
    (hcard : Nat.card (⁅A, V⁆ : Subgroup G) ≤ Nat.card E.input.field.Carrier) :
    ∀ (r : E.input.field.Carrier) v,
      (Coordinates.sp4 m).conjugationAction hAL hAV a (r • v) =
        r • (Coordinates.sp4 m).conjugationAction hAL hAV a v := by
  let c := Coordinates.sp4 m
  let ρ := c.conjugationAction hAL hAV
  apply linear_of_small_displacement (ρ a).toAddMonoidHom
  · intro v
    change ρ a (ρ a v) = v
    rw [← Module.End.mul_apply, ← map_mul, ← pow_two, ha, map_one]
    rfl
  · obtain ⟨σ, hσ⟩ := normalizerAction_semilinear m (inclusion hAV a)
    refine ⟨σ, ?_⟩
    intro r v
    change ρ a (r • v) = σ r • ρ a v
    specialize hσ r v
    rw [normalizerAction_restrict m A hAL hAV a (r • v),
      normalizerAction_restrict m A hAL hAV a v] at hσ
    exact hσ
  · exact (displacement_card_le_commutator m A hAL hAV a).trans hcard

private theorem projection_injective
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) :
    Function.Injective (Coordinates.sp4 m).projection := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro v hv
  apply mem_bot.mpr
  apply Subtype.ext
  apply mem_bot.mp
  rw [← hfixed]
  exact ⟨v.property, ((Coordinates.sp4 m).projection_eq_one_iff v).mp hv⟩

private theorem projection_commutator (A : Subgroup G)
    (hAL : A ≤ normalizer (L : Set G)) (hAV : A ≤ normalizer (V : Set G))
    (a : A) (v : V) :
    ((Coordinates.sp4 m).projection
      (V.normalizerMonoidHom (inclusion hAV a) v * v⁻¹)).toAdd =
        (Coordinates.sp4 m).conjugationAction hAL hAV a
          ((Coordinates.sp4 m).projection v).toAdd -
          ((Coordinates.sp4 m).projection v).toAdd := by
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
  rw [← (Coordinates.sp4 m).conjugationAction_projection]

/-- A nontrivial commutator under field-linear actors contains an actual
field line. Its scalar multiples are displacements of scalar multiples
of one moving vector. -/
theorem exists_fieldLine_le_commutator
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (A : Subgroup G) (hAL : A ≤ normalizer (L : Set G))
    (hAV : A ≤ normalizer (V : Set G)) (hne : ⁅A, V⁆ ≠ ⊥)
    (hlinear : ∀ a : A, ∀ (r : E.input.field.Carrier) v,
      (Coordinates.sp4 m).conjugationAction hAL hAV a (r • v) =
        r • (Coordinates.sp4 m).conjugationAction hAL hAV a v) :
    ∃ U : Submodule E.input.field.Carrier (Coordinates.sp4 m).Space,
      Module.finrank E.input.field.Carrier U = 1 ∧
        (Coordinates.sp4 m).preimage U ≤ ⁅A, V⁆ := by
  let c := Coordinates.sp4 m
  let ρ := c.conjugationAction hAL hAV
  obtain ⟨a, x, hx⟩ : ∃ a : A, ∃ x : c.Space, ρ a x ≠ x := by
    by_contra! h
    apply hne
    apply bot_unique
    apply commutator_le.mpr
    intro a ha v hv
    let a' : A := ⟨a, ha⟩
    let v' : V := ⟨v, hv⟩
    let z : V := V.normalizerMonoidHom (inclusion hAV a') v' * v'⁻¹
    have hz : z = 1 := by
      apply projection_injective m hfixed
      apply Multiplicative.toAdd.injective
      rw [map_one]
      change (c.projection z).toAdd = 0
      rw [projection_commutator m A hAL hAV, h, sub_self]
    exact mem_bot.mpr (congrArg Subtype.val hz)
  let w := ρ a x - x
  have hw : w ≠ 0 := sub_ne_zero.mpr hx
  refine ⟨Submodule.span E.input.field.Carrier {w}, finrank_span_singleton hw, ?_⟩
  intro v hv
  let v' : V := ⟨v, D.centralQuotientPreimage_le _ hv⟩
  have hv' := (c.mem_preimage _ v').mp hv
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hv'
  obtain ⟨y, hy⟩ := c.projection_surjective (Multiplicative.ofAdd (r • x))
  let z : V := V.normalizerMonoidHom (inclusion hAV a) y * y⁻¹
  have hz : z = v' := by
    apply projection_injective m hfixed
    apply Multiplicative.toAdd.injective
    change (c.projection z).toAdd = (c.projection v').toAdd
    rw [projection_commutator m A hAL hAV, hy]
    change ρ a (r • x) - r • x = (c.projection v').toAdd
    rw [hlinear, ← smul_sub]
    exact hr
  have hm : (z : G) ∈ ⁅A, V⁆ := commutator_mem_commutator a.property y.property
  rwa [hz] at hm

/-- A nonzero commutator of order at most q with square-one actors is a
genuine field line of the marked natural module. -/
theorem commutator_isFieldLine_of_card_le
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (A : Subgroup G) (hAV : A ≤ normalizer (V : Set G))
    (hsq : ∀ a : A, a ^ 2 = 1) (hne : ⁅A, V⁆ ≠ ⊥)
    (hcard : Nat.card (⁅A, V⁆ : Subgroup G) ≤ Nat.card E.input.field.Carrier) :
    IsFieldLine E (.sp4 m) ⁅A, V⁆ := by
  have hAL := hAV.trans (WeakClosure.seed_normalizer_le D E.input)
  obtain ⟨U, hU, hle⟩ := exists_fieldLine_le_commutator m hfixed A hAL hAV hne
    (fun a => linear_of_commutator_card_le m A hAL hAV a (hsq a) hcard)
  refine ⟨U, hU, Subgroup.eq_of_le_of_card_ge hle ?_⟩
  rw [Nonabelian.card_preimage (.sp4 m) hfixed U, hU, pow_one]
  rwa [E.input.field.card_eq] at hcard

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic
