module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.HexadCover.Core
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.HexadCover.Inner
public import Theory.Representation.HexacodeAction.CoverComparison

/-!
# The retained, marked triple cover of A₆

Inside the quotient of the native hexad by its two-core, take the full
inverse image of A₆ under the actual six-point action. Its projection has
central kernel of order three. Transfer in the original perfect component
puts that kernel in the derived group, so this inverse image is perfect
and quasisimple. Schur's marked uniqueness theorem identifies it with the
even hexacode group over the same six-point projection. Perfectness also
rules out a section of that projection.

Source: Aschbacher--Smith 14.4.12, pp.1011--1012, H.12.1(4), pp.393--394;
GLS, volume 3, Theorem 5.2.3 for the marked cover comparison.
-/

@[expose] public section
open Subgroup Sporadic.Mathieu Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.HexadCover
open M22ValueBound.Concrete

noncomputable def evenQuotient {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    Subgroup (hexadPreimage b ⧸ pCore 2 (hexadPreimage b)) :=
  (alternatingGroup (Fin 6)).comap (quotientSixProjection hb)

noncomputable def evenProjection {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    evenQuotient hb →* alternatingGroup (Fin 6) :=
  (quotientSixProjection hb).subgroupComap _

theorem evenProjection_surjective {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    Function.Surjective (evenProjection hb) :=
  (quotientSixProjection hb).subgroupComap_surjective_of_surjective _
    (quotientSixProjection_surjective hb)

noncomputable def innerToEvenQuotient {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    innerPreimage b →* evenQuotient hb :=
  ((QuotientGroup.mk' (pCore 2 (hexadPreimage b))).comp (innerNativeInclusion b)).codRestrict _
    (fun x => by
      change M22OuterHexad.action hb (projection b (innerNativeInclusion b x)) ∈ alternatingGroup (Fin 6)
      have hp : projection b (innerNativeInclusion b x) = innerInclusion b (innerProjection b x) :=
        Subtype.ext (designProjection_component x.val)
      rw [hp, action_inner, ← m22HexadAction_range hb]
      exact ⟨innerProjection b x, rfl⟩)

theorem innerToEvenQuotient_surjective {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    Function.Surjective (innerToEvenQuotient hb) := by
  intro y
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (pCore 2 (hexadPreimage b)) y.val
  have heven : sixProjection hb x ∈ alternatingGroup (Fin 6) := by
    change quotientSixProjection hb (QuotientGroup.mk' _ x) ∈ alternatingGroup (Fin 6)
    rw [hx]
    exact y.property
  have hi := (action_even_iff_inner hb (projection b x)).mp heven
  have hxcomp : x.val ∈ component := by
    change x.val ∈ M22ValueBound.Concrete.inner.comap designProjection at hi
    rwa [component_preimage_designProjection] at hi
  let z : M22TripleCover := ⟨x.val.val, hxcomp⟩
  have hz : z ∈ innerPreimage b := by
    have hh := x.property
    change designProjection (componentInclusion z) ∈ MulAction.stabilizer m22DesignAut b at hh
    rw [designProjection_component] at hh
    exact hh
  exact ⟨⟨z, hz⟩, Subtype.ext hx⟩

theorem evenProjection_inner {b : Finset (Fin 22)} (hb : b ∈ m22Blocks)
    (x : innerPreimage b) :
    evenProjection hb (innerToEvenQuotient hb x) = CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.hexadNativeSixProjection hb (innerProjection b x) := by
  apply Subtype.ext
  change M22OuterHexad.action hb (projection b (innerNativeInclusion b x)) = _
  have hp : projection b (innerNativeInclusion b x) = innerInclusion b (innerProjection b x) :=
    Subtype.ext (designProjection_component x.val)
  rw [hp, action_inner]
  rfl

theorem evenProjection_kernel {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    (evenProjection hb).ker = (innerProjection b).ker.map (innerToEvenQuotient hb) := by
  ext y
  constructor
  · intro hy
    have hy' : y.val ∈ (quotientSixProjection hb).ker :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
    rw [quotientSixProjection_kernel hb] at hy'
    obtain ⟨z, hz, he⟩ := hy'
    rw [projection_kernel] at hz
    change z.val ∈ cubic at hz
    rw [cubic_eq_map_center] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    let w' : innerPreimage b := ⟨w, center_le_innerPreimage b hw⟩
    refine ⟨w', ?_, ?_⟩
    · rw [innerProjection_ker]
      exact hw
    · apply Subtype.ext
      change QuotientGroup.mk' _ (innerNativeInclusion b w') = y.val
      rw [show innerNativeInclusion b w' = z from Subtype.ext hwz]
      exact he
  · rintro ⟨x, hx, rfl⟩
    rw [MonoidHom.mem_ker, evenProjection_inner, MonoidHom.mem_ker.mp hx, map_one]

theorem evenProjection_kernel_central {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    (evenProjection hb).ker ≤ center (evenQuotient hb) := by
  rw [evenProjection_kernel hb]
  rintro x ⟨z, hz, rfl⟩
  apply mem_center_iff.mpr
  intro y
  obtain ⟨w, rfl⟩ := innerToEvenQuotient_surjective hb y
  rw [← map_mul, ← map_mul, mem_center_iff.mp (innerProjection_kernel_central b hz) w]

theorem evenProjection_kernel_card {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    Nat.card (evenProjection hb).ker = 3 := by
  have he : (evenProjection hb).ker =
      (quotientSixProjection hb).ker.subgroupOf (evenQuotient hb) := by
    ext x
    change evenProjection hb x = 1 ↔ _
    rw [Subtype.ext_iff]
    rfl
  have hk : (quotientSixProjection hb).ker ≤ evenQuotient hb := ker_le_comap _ _
  rw [he, Nat.card_congr (subgroupOfEquivOfLe hk).toEquiv,
    quotientSixProjection_kernel_card hb]

theorem evenProjection_kernel_le_derived {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    (evenProjection hb).ker ≤ commutator (evenQuotient hb) := by
  rw [evenProjection_kernel hb]
  have hm : (commutator (innerPreimage b)).map (innerToEvenQuotient hb) =
      commutator (evenQuotient hb) := by
    rw [map_commutator_eq,
      MonoidHom.range_eq_top_of_surjective _ (innerToEvenQuotient_surjective hb)]
    rfl
  rw [← hm]
  exact map_mono (innerProjection_kernel_le_derived hb)

instance evenQuotient_isPerfect {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    Group.IsPerfect (evenQuotient hb) := by
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  constructor
  have hm : (commutator (evenQuotient hb)).map (evenProjection hb) = ⊤ := by
    rw [map_commutator_eq,
      MonoidHom.range_eq_top_of_surjective _ (evenProjection_surjective hb)]
    exact Group.IsPerfect.commutator_eq_top
  have he := congrArg (comap (evenProjection hb)) hm
  rwa [comap_map_eq, sup_eq_left.mpr (evenProjection_kernel_le_derived hb), comap_top] at he

theorem evenProjection_kernel_eq_center {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    (evenProjection hb).ker = center (evenQuotient hb) := by
  apply le_antisymm (evenProjection_kernel_central hb)
  intro x hx
  have hz : evenProjection hb x ∈ center (alternatingGroup (Fin 6)) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨y, rfl⟩ := evenProjection_surjective hb y
    simpa only [map_mul] using congrArg (evenProjection hb) (mem_center_iff.mp hx y)
  rw [alternatingGroup.center_eq_bot (by simp)] at hz
  exact mem_bot.mp hz

noncomputable def evenCentralQuotientEquiv {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    (evenQuotient hb ⧸ center (evenQuotient hb)) ≃* alternatingGroup (Fin 6) :=
  QuotientGroup.liftEquiv _ (evenProjection_surjective hb) (evenProjection_kernel_eq_center hb).symm

instance evenQuotient_isQuasisimple {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    IsQuasisimple (evenQuotient hb) := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  exact { toIsPerfect := inferInstance, simple := (evenCentralQuotientEquiv hb).isSimpleGroup }

/-- The comparison respects the six-point projection, not just the abstract group. -/
theorem exists_hexacode_equiv {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    ∃ e : evenQuotient hb ≃* Atlas.Codes.HexEvenAutomorphisms,
      Atlas.Codes.hexEvenCoordinate.comp e.toMonoidHom = evenProjection hb :=
  Representation.Hexacode.CoverComparison.exists_even_equiv_over_coordinate
    ⟨evenProjection hb, evenProjection_surjective hb⟩ (evenProjection_kernel_card hb)

/-- The triple cover has no homomorphic section of its marked A₆ projection. -/
theorem evenProjection_nonsplit {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    ¬ ∃ s : alternatingGroup (Fin 6) →* evenQuotient hb,
      (evenProjection hb).comp s = MonoidHom.id _ := by
  rintro ⟨s, hs⟩
  have hm : s.range.map (evenProjection hb) = ⊤ := by
    rw [← MonoidHom.range_comp, hs]
    exact MonoidHom.range_eq_top.mpr Function.surjective_id
  have hc := congrArg (comap (evenProjection hb)) hm
  rw [comap_map_eq, evenProjection_kernel_eq_center hb, comap_top] at hc
  have ht : s.range = ⊤ :=
    M22ValueBound.central_supplement_eq_top s.range (by simpa only [sup_comm] using hc)
  have hi : Function.Injective (evenProjection hb) := by
    intro x y he
    obtain ⟨a, rfl⟩ := MonoidHom.range_eq_top.mp ht x
    obtain ⟨c, rfl⟩ := MonoidHom.range_eq_top.mp ht y
    have ha : evenProjection hb (s a) = a := DFunLike.congr_fun hs a
    have hb' : evenProjection hb (s c) = c := DFunLike.congr_fun hs c
    exact congrArg s (ha.symm.trans (he.trans hb'))
  have hk := (evenProjection hb).ker_eq_bot_iff.mpr hi
  have hn := evenProjection_kernel_card hb
  rw [hk, Subgroup.card_bot] at hn
  omega

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.HexadCover
