module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneRThreeClassAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.NaturalCore
public import Theory.Combinatorics.TranslationPlane.FlagElations

/-!
# Affine coordinates and full flag elations on the raw source plane

The actual adjacent-core intersection has order q and acts by elations with
its original center and axis. Conjugacy in the same natural actor makes every
nonidentity axis-core element an elation. Its order q² and the affine-point
count give a regular action and one affine chart using the original natural
coordinates; its action is literal vector addition.

Independently, the geometric bound of q on a flag-elation group shows that
the adjacent-core image is the entire flag-elation group. The raw collineation
homomorphism has exactly the original apartment quotient kernel. Consequently
these elations lift to the original adjacent-core intersection on the SAME
quotient map, and their images belong to the original whole Borel.

This establishes the flag-elation comparison, not yet the comparison for all
class edge stabilizers or the original path-root conjugates. It assumes no
marked BN quotient or Borel-image root-sign conclusion.
Source: DGS, *Groups and Graphs* (1985), (3.6)--(3.7), pp.77--80, and (10.5),
p.156. The affine argument adapts the BN-independent `A2Source/SourcePlane`;
the flag bound is `TranslationPlane/FlagElations`.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam Configuration
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan
universe uF
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {h : HypothesisF11 L S} {c : CompatibleCartans L (reducedSylow L S)}
variable (ds : ∀ j : Bool, FullCartanReflectionProfile.{uF} h c j)
local notation "A" => reducedAmalgam L S
local notation "X" => RankTwoAmalgam.Universal (reducedAmalgam L S)
local notation "U" => fullCartanUniversalCore (L := L) (S := S)
local notation "I" => (U true ⊓ U false : Subgroup X)
local notation "Pt" => fullCartanClassPoint ds
local notation "Ln" => fullCartanClassLine ds
local notation "axis" => fullCartanClassAxis ds
local notation "center" => fullCartanClassCenter ds
local instance {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2

include ds in
theorem fullCartan_original_core_eq_center (i : Bool) :
    Q (reducedFamily L S) (base (reducedFamily L S) i) =
      Z (reducedFamily L S) (base (reducedFamily L S) i) := by
  have hc := paired_cores_eq_centers_of_actions (reduced_triple h) (ds false).data (ds true).data
  cases i
  · exact hc.1
  · exact hc.2

variable (hr : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4)

/-- The original natural coordinates transported through the actual endpoint covering. -/
def fullCartanClassCoreCoordinates (i : Bool) : U i ≃* Multiplicative (Fin 2 → (ds i).F) :=
  (universalBOneCoreEquiv h i).trans
    (FongSeitzBinary.A2Source.coreCoordinates (ds i).data (reduced_triple h)
      (fullCartan_original_core_eq_center ds i)
      (fullCartan_centers_eq_bot_of_source_r_three ds hr i) (ds i).dimension)

theorem fullCartanClassCoreCoordinates_apply (i : Bool) (x : U i) :
    fullCartanClassCoreCoordinates ds hr i x =
      FongSeitzBinary.A2Source.coreCoordinates (ds i).data (reduced_triple h)
        (fullCartan_original_core_eq_center ds i)
        (fullCartan_centers_eq_bot_of_source_r_three ds hr i) (ds i).dimension
        (universalBOneCoreEquiv h i x) := rfl

include hr in
theorem fullCartanClassCore_conjugate (i : Bool)
    (a : universalBOneActor h i (ds i).data) (x : U i) :
    ∃ y : U i, (y : X) = (a : X) * (x : X) * (a : X)⁻¹ ∧
      (fullCartanClassCoreCoordinates ds hr i y).toAdd =
        Matrix.mulVec (universalBOneQuotient h i (ds i).data a).val
          (fullCartanClassCoreCoordinates ds hr i x).toAdd := by
  obtain ⟨z, hz, hc⟩ := FongSeitzBinary.A2Source.coreCoordinates_conjugate
    (ds i).data (reduced_triple h) (fullCartan_original_core_eq_center ds i)
    (fullCartan_centers_eq_bot_of_source_r_three ds hr i) (ds i).dimension
    (universalBOneActorEquiv h i (ds i).data a) (universalBOneCoreEquiv h i x)
  let y := (universalBOneCoreEquiv h i).symm z
  have hy : universalBOneCoreEquiv h i y = z := (universalBOneCoreEquiv h i).apply_symm_apply z
  refine ⟨y, ?_, ?_⟩
  · have he : bOne_tree_map h y = bOne_tree_map h ((a : X) * (x : X) * (a : X)⁻¹) := by
      rw [map_mul, map_mul, map_inv]
      exact (congrArg Subtype.val hy).trans hz
    have hP := (Universal.cosetFamily A i).mul_mem
      ((Universal.cosetFamily A i).mul_mem a.property.2 (pCoreIn_le 2 _ x.property))
      ((Universal.cosetFamily A i).inv_mem a.property.2)
    exact congrArg (fun t : Universal.cosetFamily A i => (t : X))
      ((bOne_tree_cover h).injective i
        (a₁ := ⟨y, pCoreIn_le 2 _ y.property⟩) (a₂ := ⟨_, hP⟩) he)
  · change (FongSeitzBinary.A2Source.coreCoordinates _ _ _ _ _
      (universalBOneCoreEquiv h i y)).toAdd = _
    rw [hy]
    exact hc

include hr in
theorem fullCartanClassCore_nonidentity_conjugate (i : Bool)
    (x y : U i) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ a : universalBOneActor h i (ds i).data,
      (a : X) * (x : X) * (a : X)⁻¹ = (y : X) := by
  let φ := fullCartanClassCoreCoordinates ds hr i
  have hnonzero (z : U i) (hz : z ≠ 1) : (φ z).toAdd ≠ 0 := by
    intro he
    exact hz (φ.injective ((show φ z = 1 from he).trans φ.map_one.symm))
  obtain ⟨g, hg⟩ := Matrix.SL2.exists_mulVec_eq (ds i).F (φ x).toAdd (φ y).toAdd
    (hnonzero x hx) (hnonzero y hy)
  obtain ⟨a, ha⟩ := (ds i).data.onto g
  let a' := (universalBOneActorEquiv h i (ds i).data).symm a
  obtain ⟨z, hz, hφ⟩ := fullCartanClassCore_conjugate ds hr i a' x
  have hπ : universalBOneQuotient h i (ds i).data a' = g := by
    change (ds i).data.quotient (universalBOneActorEquiv h i (ds i).data a') = g
    rw [MulEquiv.apply_symm_apply, ha]
  rw [hπ] at hφ
  have hzy : z = y := φ.injective (show φ z = φ y from hφ.trans hg)
  exact ⟨a', hz.symm.trans (congrArg Subtype.val hzy)⟩

include hr in
theorem fullCartanClassCoreIntersection_card : Nat.card I = Nat.card (ds true).F :=
  (Nat.card_congr (universalBOneCoreIntersectionEquiv h).toEquiv).trans
    (FongSeitzBinary.A2Source.core_intersection_card (ds true).data (reduced_triple h)
      (fullCartan_original_core_eq_center ds true)
      (fullCartan_centers_eq_bot_of_source_r_three ds hr true) (ds true).dimension)

include hr in
theorem fullCartanClassIntersection_isElation (z : X) (hz : z ∈ I) (hne : z ≠ 1) :
    IsElation z center axis := by
  refine ⟨fullCartanClass_incident ds hr, ?_, ?_,
    fullCartanClass_moves ds hr true (pCoreIn_le 2 _ hz.1) hne⟩
  · intro p hp
    exact Subtype.ext (fullCartanClassCore_fixes_neighbor ds hr true hz.1 hp.symm)
  · intro l hl
    exact Subtype.ext (fullCartanClassCore_fixes_neighbor ds hr false hz.2 hl)

include hr in
theorem fullCartanClassCore_isElation (x : U true) (hx : x ≠ 1) :
    ∃ C : Pt, IsElation (x : X) C axis := by
  have hI : I ≠ ⊥ := by
    intro he
    have hc := fullCartanClassCoreIntersection_card ds hr
    rw [he, Subgroup.card_bot] at hc
    exact Finite.one_lt_card.ne hc
  obtain ⟨z, hz, hz1⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI)
  change z ≠ 1 at hz1
  let zU : U true := ⟨z, hz.1⟩
  obtain ⟨a, ha⟩ := fullCartanClassCore_nonidentity_conjugate ds hr true zU x
    (fun he => hz1 (congrArg Subtype.val he)) hx
  have hh := (fullCartanClassIntersection_isElation ds hr z hz hz1).conjugate (a : X)
  rw [ha, fullCartanClassBase_fixed ds true a.property.2] at hh
  exact ⟨(a : X) • center, hh⟩

theorem fullCartanClassCore_fixes_axis (x : U true) : (x : X) • axis = axis :=
  fullCartanClassBase_fixed ds true (pCoreIn_le 2 _ x.property)

include hr in
theorem fullCartanClassCore_card (i : Bool) : Nat.card (U i) = Nat.card (ds i).F ^ 2 := by
  have hc := Nat.card_congr ((fullCartanClassCoreCoordinates ds hr i).toEquiv.trans Multiplicative.toAdd)
  simpa only [Nat.card_fun, Nat.card_fin] using hc

theorem fullCartanClassPlane_order_right :
    let := fullCartanClassPlane ds hr
    ProjectivePlane.order Pt Ln = Nat.card (ds true).F := by
  let := fullCartanClassPlane ds hr
  exact (fullCartanClassPlane_order ds hr).trans
    (paired_field_orders_eq (reduced_triple h) (ds false).data (ds true).data (ds false).dimension)


include hr in
theorem fullCartanClass_exists_affine_origin : ∃ p : Pt, p ∉ axis := by
  let := fullCartanClassPlane ds hr
  have hc := card_affinePoints (P := Pt) axis
  rw [fullCartanClassPlane_order_right ds hr] at hc
  have hpos : 0 < Nat.card {p : Pt // p ∉ axis} := hc ▸ pow_pos Nat.card_pos 2
  obtain ⟨p⟩ := (Nat.card_pos_iff.mp hpos).1
  exact ⟨p, p.property⟩

/-- The actual axis core acts regularly on all affine raw classes. -/
def fullCartanClassAffineChart (o : {p : Pt // p ∉ axis}) :
    (Fin 2 → (ds true).F) ≃ {p : Pt // p ∉ axis} := by
  let := fullCartanClassPlane ds hr
  exact translationChart (U true) axis (fullCartanClassCore_fixes_axis ds) o
    (fullCartanClassCore_isElation ds hr)
    (by rw [fullCartanClassPlane_order_right ds hr]; exact fullCartanClassCore_card ds hr true)
    (fullCartanClassCoreCoordinates ds hr true)

theorem fullCartanClassAffineChart_apply (o : {p : Pt // p ∉ axis}) (t : Fin 2 → (ds true).F) :
    (fullCartanClassAffineChart ds hr o t).val =
      ((fullCartanClassCoreCoordinates ds hr true).symm (.ofAdd t) : X) • o.val := rfl

theorem fullCartanClassAffineChart_add (o : {p : Pt // p ∉ axis})
    (a : U true) (t : Fin 2 → (ds true).F) :
    (fullCartanClassAffineChart ds hr o
      ((fullCartanClassCoreCoordinates ds hr true a).toAdd + t)).val =
        (a : X) • (fullCartanClassAffineChart ds hr o t).val := by
  let := fullCartanClassPlane ds hr
  exact translationChart_add _ _ _ _ _ _ _ a t

/-- The original universal action, on the full point-line incidence structure. -/
def fullCartanClassCollineation : X →* Collineation Pt Ln := Collineation.ofAction X Pt Ln

/-- This geometric action has the SAME kernel as the source quotient. -/
theorem fullCartanClassCollineation_kernel :
    (fullCartanClassCollineation ds).ker =
      kernel A (cartanApartment A (apartmentGroup c (fullCartanPathRoots ds))) (fullCartanPathLength ds) := by
  ext g
  let r := sourceRelation A (cartanApartment A (apartmentGroup c (fullCartanPathRoots ds)))
    (fullCartanPathLength ds)
  let act := quotientAction r (apartmentSetoid_invariant (source_action A))
  constructor
  · intro hg
    apply (mem_quotientKernel r (apartmentSetoid_invariant (source_action A)) g).mpr
    intro v
    apply Quotient.exact
    cases hv : v.type
    · exact congrArg Subtype.val
        (congrArg (fun a => Collineation.pointHom Pt Ln a (⟨Quotient.mk r v, hv⟩ : Pt)) hg)
    · exact congrArg Subtype.val
        (congrArg (fun a => Collineation.lineHom Pt Ln a (⟨Quotient.mk r v, hv⟩ : Ln)) hg)
  · intro hg
    have he : act g = 1 := hg
    apply Collineation.ext
    · intro p
      exact Subtype.ext (DFunLike.congr_fun he p.val)
    · intro l
      exact Subtype.ext (DFunLike.congr_fun he l.val)

theorem fullCartanClassCollineation_eq_iff (g k : X) :
    fullCartanClassCollineation ds g = fullCartanClassCollineation ds k ↔
      quotientMap A (cartanApartment A (apartmentGroup c (fullCartanPathRoots ds)))
        (fullCartanPathLength ds) g =
      quotientMap A (cartanApartment A (apartmentGroup c (fullCartanPathRoots ds)))
        (fullCartanPathLength ds) k := by
  rw [← inv_mul_eq_one, ← map_inv, ← map_mul]
  change g⁻¹*k ∈ (fullCartanClassCollineation ds).ker ↔ _
  rw [fullCartanClassCollineation_kernel]
  exact QuotientGroup.eq.symm

include hr in
theorem fullCartanClassCollineation_injective_endpoint (i : Bool) :
    Function.Injective (fun g : Universal.cosetFamily A i => fullCartanClassCollineation ds g) := by
  intro g k he
  have heq := (fullCartanClassCollineation_eq_iff ds g k).mp he
  have hk := QuotientGroup.eq.mp heq
  have hb : (g : X)⁻¹ * (k : X) ∈
      kernel A (cartanApartment A (apartmentGroup c (fullCartanPathRoots ds)))
        (fullCartanPathLength ds) ⊓ Universal.cosetFamily A i :=
    ⟨hk, (Universal.cosetFamily A i).mul_mem ((Universal.cosetFamily A i).inv_mem g.property) k.property⟩
  rw [fullCartan_kernel_inf_endpoints_of_r_three ds hr i] at hb
  exact Subtype.ext (inv_mul_eq_one.mp hb)

include hr in
/-- The original adjacent cores exhaust the full geometric flag group. -/
theorem fullCartanClassIntersection_eq_flagElations :
    (U true ⊓ U false : Subgroup X).map (fullCartanClassCollineation ds) = TranslationPlane.flagElations center axis := by
  let := fullCartanClassPlane ds hr
  obtain ⟨o, ho⟩ := fullCartanClass_exists_affine_origin ds hr
  apply TranslationPlane.eq_flagElations_of_card center axis (fullCartanClass_incident ds hr) o ho
  · rintro g ⟨x, hx, rfl⟩
    constructor
    · intro p hp
      exact Subtype.ext (fullCartanClassCore_fixes_neighbor ds hr true hx.1 hp.symm)
    · intro l hl
      exact Subtype.ext (fullCartanClassCore_fixes_neighbor ds hr false hx.2 hl)
  · let f := (fullCartanClassCollineation ds).subgroupMap I
    have hf : Function.Injective f := by
      intro x y he
      have hh := fullCartanClassCollineation_injective_endpoint ds hr true
        (a₁ := ⟨x, pCoreIn_le 2 _ x.property.1⟩)
        (a₂ := ⟨y, pCoreIn_le 2 _ y.property.1⟩) (congrArg Subtype.val he)
      exact Subtype.ext (congrArg (fun z : Universal.cosetFamily A true => (z : X)) hh)
    have hc := Nat.card_congr (Equiv.ofBijective f
      ⟨hf, (fullCartanClassCollineation ds).subgroupMap_surjective I⟩)
    rw [← hc, fullCartanClassCoreIntersection_card ds hr, fullCartanClassPlane_order_right ds hr]

include hr in
/-- Every raw base-flag elation has a representative in the original core intersection. -/
theorem fullCartanClass_flagElations_lift (g : X)
    (hg : fullCartanClassCollineation ds g ∈ TranslationPlane.flagElations center axis) :
    ∃ z ∈ I,
      quotientMap A (cartanApartment A (apartmentGroup c (fullCartanPathRoots ds)))
        (fullCartanPathLength ds) z =
      quotientMap A (cartanApartment A (apartmentGroup c (fullCartanPathRoots ds)))
        (fullCartanPathLength ds) g := by
  rw [← fullCartanClassIntersection_eq_flagElations ds hr] at hg
  obtain ⟨z, hz, he⟩ := hg
  exact ⟨z, hz, (fullCartanClassCollineation_eq_iff ds z g).mp he⟩

include hr in
/-- The lift gives membership in the original whole Borel image on the literal quotient. -/
theorem fullCartanClass_flagElations_mem_borel (g : X)
    (hg : fullCartanClassCollineation ds g ∈ TranslationPlane.flagElations center axis) :
    quotientMap A (cartanApartment A (apartmentGroup c (fullCartanPathRoots ds)))
      (fullCartanPathLength ds) g ∈
      (originalMiddle A).map (quotientMap A
        (cartanApartment A (apartmentGroup c (fullCartanPathRoots ds))) (fullCartanPathLength ds)) := by
  obtain ⟨z, hz, he⟩ := fullCartanClass_flagElations_lift ds hr g hg
  refine ⟨z, ?_, he⟩
  exact universal_endpoint_core_le_middle h true hz.1

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
