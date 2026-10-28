module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Coordinates
public import CFSG.Quasithin.Chapter13.Section05.A5Source.Context
public import Theory.Representation.BinaryAlternatingFiveFlag.Borel
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Flags

/-!
# Compatible original coordinates for the terminal A₅ argument

The source flag carries the action of the full normalizer of V. Its proved
Sylow alignment relabels both that action and the module embedding. The
original line becomes the singular point z, and the original invariant
three-space becomes the coordinate hyperplane: the Sylow image contains the
regular four-group, whose invariant hyperplane of order eight is unique.
The nonsingular point is exactly the marked v of the already constructed
source flag, so earlier point-centralizer theorems apply without a new mark.

Source: Aschbacher–Smith, Notation 13.2.1, 13.5.13 and the marking paragraph
before 13.6.4, printed pp.877,919,926. This supplies the coordinate inputs
of the terminal argument without assuming fusion or point-centralizer control.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open CentralizerReduction CentralizerReduction.A5Module
open BinaryPermutation BinaryPermutation.FiveCentralizerGeometry
open A5Module.FlagCoordinates
variable {G : Type*} [Group G] {L V : Subgroup G}

private noncomputable def markingEquiv (s : Marking L V) :
    Multiplicative Space ≃* V :=
  MulEquiv.ofBijective (s.map.codRestrict V (map_mem s))
    ⟨fun _ _ h => s.injective (congrArg Subtype.val h), fun x => by
      obtain ⟨y, hy⟩ := s.range_eq.ge x.property
      exact ⟨y, Subtype.ext hy⟩⟩

private noncomputable def normalizerCoordinates {T : Sylow 2 G} {V₁ V₂ : Subgroup G}
    (f : FlagSource T L V V₁ V₂) : FiveCoordinates V where
  equiv := (markingEquiv f.module).symm
  actor := f.normalizerAction
  equivariant n x := by
    apply Multiplicative.ofAdd.injective
    apply (markingEquiv f.module).injective
    change (markingEquiv f.module) ((markingEquiv f.module).symm
      (V.normalizerMonoidHom n x)) = _
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    change MulAut.conj n.val x.val = _
    have hx : x.val = f.module.map ((markingEquiv f.module).symm x) :=
      (congrArg Subtype.val ((markingEquiv f.module).apply_symm_apply x)).symm
    rw [hx]
    exact f.normalizer_equivariant n ((markingEquiv f.module).symm x).toAdd

/-- The terminal coordinates retain the actual line, three-space and full normalizer action. -/
structure SourceCoordinates (V V₁ V₃ : Subgroup G) where
  coordinates : FiveCoordinates V
  nonsingular : V
  singular : V
  form_nonsingular : FiveGeometry.form (coordinates.equiv nonsingular).toAdd ≠ 0
  singular_ne_one : singular ≠ 1
  line_eq : zpowers singular.val = V₁
  form_singular : FiveGeometry.form (coordinates.equiv singular).toAdd = 0
  alternating_le : alternatingGroup (Fin 5) ≤ coordinates.actor.range
  third_mark : ∀ x : V, x.val ∈ V₃ ↔ (coordinates.equiv x).toAdd.val 4 = 0

variable [Finite G] {T : Sylow 2 G} {V₁ V₂ V₃ : Subgroup G}

private theorem third_preimage (f : FlagSource T L V V₁ V₂)
    (hline : zpowers (markedZ f.module) = V₁)
    (hthird : V₃ ≤ V) (hcard : Nat.card V₃ = 8)
    (hinvariant : (T : Subgroup G) ≤ normalizer (V₃ : Set G)) :
    f.preimage V₃ = AlternatingFiveFlag.three := by
  have hpre : f.preimage V₁ = zpowers (Multiplicative.ofAdd z) := by
    apply Subgroup.map_injective f.module.injective
    rw [f.preimage_map V₁ (f.one_le_two.trans f.two_le_V), MonoidHom.map_zpowers]
    exact hline.symm
  have hfix (p : f.image) (hp : p ∈ f.imageSylow) : rho p.val z = z := by
    have hm := f.preimage_invariant V₁ f.one_invariant p hp (Multiplicative.ofAdd z)
      (hpre.symm ▸ mem_zpowers (Multiplicative.ofAdd z))
    rw [hpre] at hm
    have he : Multiplicative.ofAdd (rho p.val z) = 1 ∨
        Multiplicative.ofAdd (rho p.val z) = Multiplicative.ofAdd z := by
      change Multiplicative.ofAdd (rho p.val z) ∈ AlternatingFiveFlag.line
      rw [AlternatingFiveFlag.line_eq_zpowers]
      exact hm
    rcases he with he | he
    · have hh : coordinateEquiv p.val (Multiplicative.ofAdd z) = coordinateEquiv p.val 1 :=
        he.trans (map_one _).symm
      exact (z_ne_zero ((coordinateEquiv p.val).injective hh)).elim
    · exact he
  have hfour := AlternatingFiveFlag.four_le_sylow f.image f.alternating_le_image
    f.imageSylow hfix
  apply AlternatingFiveFlag.three_eq_of_card_invariant
  · exact (f.preimage_card V₃ hthird).trans hcard
  · intro k hk x hx
    obtain ⟨p, hp, he⟩ := hfour hk
    rw [← he]
    exact f.preimage_invariant V₃ hinvariant p hp x hx

private theorem coordinates_of_flag (f : FlagSource T L V V₁ V₂)
    (hline : zpowers (markedZ f.module) = V₁)
    (hthird : V₃ ≤ V) (hcard : Nat.card V₃ = 8)
    (hinvariant : (T : Subgroup G) ≤ normalizer (V₃ : Set G)) :
    ∃ c : SourceCoordinates V V₁ V₃,
      c.nonsingular.val = markedV f.module ∧ c.singular.val = markedZ f.module ∧
      ∀ l : L, c.coordinates.actor ⟨l.val, f.module.normalizes l.property⟩ =
        (f.module.action l).val := by
  let e := markingEquiv f.module
  let c := normalizerCoordinates f
  let v' : V := e (Multiplicative.ofAdd v)
  let z' : V := e (Multiplicative.ofAdd z)
  have hv : (c.equiv v').toAdd = v := e.symm_apply_apply _
  have hz : (c.equiv z').toAdd = z := e.symm_apply_apply _
  refine ⟨{
    coordinates := c
    nonsingular := v'
    singular := z'
    form_nonsingular := ?_
    singular_ne_one := ?_
    line_eq := hline
    form_singular := ?_
    alternating_le := f.alternating_le_image
    third_mark := ?_ }, rfl, rfl, fun l => f.action_agrees l _⟩
  · rw [hv]
    decide +kernel
  · intro h
    have he : Multiplicative.ofAdd z = 1 := e.injective (h.trans (map_one e).symm)
    exact z_ne_zero he
  · rw [hz]
    decide +kernel
  · intro x
    have hx : f.module.map (c.equiv x) = x.val := congrArg Subtype.val (e.apply_symm_apply x)
    have hpre := third_preimage f hline hthird hcard hinvariant
    change x.val ∈ V₃ ↔ c.equiv x ∈ AlternatingFiveFlag.three
    rw [← hpre]
    change x.val ∈ V₃ ↔ f.module.map (c.equiv x) ∈ V₃
    rw [hx]

/-- The terminal coordinates retain the literal quotient action of the same
aligned source marking. This is the compatibility needed by the source
parameter and component constructions. -/
theorem source_coordinates_with_quotient
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃) :
    ∃ c : SourceCoordinates V V₁ V₃,
      ∃ e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5),
      c.nonsingular.val = markedV d.flag.flag.module ∧
      c.singular.val = markedZ d.flag.flag.module ∧
      ∀ l : L, c.coordinates.actor ⟨l.val, d.chosen.normalizes l.property⟩ =
        (e (QuotientGroup.mk' (pCore 2 L) l)).val := by
  obtain ⟨g, hg⟩ := d.flag.flag_relabel
  have hline : zpowers (markedZ (d.flag.relabel g).module) = V₁ := by
    change zpowers (markedZ (d.flag.module.relabel g)) = V₁
    rw [← hg]
    exact d.flag.flag.line_eq
  obtain ⟨c, hv, hz, ha⟩ := coordinates_of_flag (d.flag.relabel g) hline
    d.third_le d.third_card d.third_invariant
  let d' : Section05.A5Source.Context T L V V₁ V₂ V₃ :=
    { d with flag := d.flag.relabel g }
  exact ⟨c, d'.quotient, hv.trans (congrArg markedV hg).symm,
    hz.trans (congrArg markedZ hg).symm, ha⟩

/-- Construct all terminal coordinate marks at the fixed original flag points. -/
theorem source_coordinates
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃) :
    ∃ c : SourceCoordinates V V₁ V₃,
      c.nonsingular.val = markedV d.flag.flag.module ∧
      c.singular.val = markedZ d.flag.flag.module := by
  obtain ⟨c, _, hv, hz, _⟩ := source_coordinates_with_quotient d
  exact ⟨c, hv, hz⟩

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
