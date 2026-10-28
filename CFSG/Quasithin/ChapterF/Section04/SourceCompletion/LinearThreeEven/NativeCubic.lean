module
public import Theory.SpecificGroups.PSL3.SmallCompletion.Weyl
public import Theory.SpecificGroups.PSL3.SmallCompletion.TorusAlignment
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.Pair
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.LinearThree
public import Theory.GroupTheory.Amalgam.AutomorphismTransport
public import Theory.GroupTheory.Amalgam.Reversal

/-!
# The common cubic relation for native and twisted linear-three markings

An automorphism of the whole native amalgam preserves its Borel in both
endpoints. One common Borel conjugation aligns its torus image. The native
torus-normalizer calculation then proves the cubic relation on the exact
images of the two coordinate reflections. Cancelling that common conjugation
proves the relation for the original prescribed maps, in both orientations.

The concrete model and its twisted marking therefore give a paired completion
with a literal common cubic word. Both pair projections are actual coset
coverings and preserve the endpoint elements. Small-cover injectivity, and
hence the requested global native lift, are further obligations.

Source: the marked refinement of Aschbacher–Smith F.4.8–9, pp.278–279,
and the compatible native action in 5.3.2, p.659 (`refs/quasithin.pdf`).
The projective scalar kernel is retained throughout, including at q = 4.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
open Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open Matrix.PSL3.SmallCompletion
namespace CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeEven
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
local notation "α" => GreenBook.LieModels.LinearThree.amalgam F

/-- Conjugate all three component maps by the same element of the whole Borel. -/
def borelConjugation (b : borel F) : RankTwoAmalgam.Iso α α where
  left := MulAut.conj (⟨b.val, GreenBook.LieModels.LinearThree.borel_le_point F b.property⟩ : pointParabolic F)
  middle := MulAut.conj b
  right := MulAut.conj (⟨b.val, GreenBook.LieModels.LinearThree.borel_le_line F b.property⟩ : lineParabolic F)
  left_commutes _ := Subtype.ext rfl
  right_commutes _ := Subtype.ext rfl

/-- Endpoint selection, with exactly the point/line convention of the native model. -/
def endpointAut (e : RankTwoAmalgam.Iso α α) (i : Bool) : MulAut (parabolic F i) :=
  match i with
  | false => e.left
  | true => e.right

omit [Finite F] [CharP F 2] in
theorem borel_le_parabolic (i : Bool) : borel F ≤ parabolic F i := by
  cases i
  · exact GreenBook.LieModels.LinearThree.borel_le_point F
  · exact GreenBook.LieModels.LinearThree.borel_le_line F

omit [Finite F] [CharP F 2] in
theorem endpointAut_middle (e : RankTwoAmalgam.Iso α α) (i : Bool) (x : borel F) :
    (endpointAut F e i (inclusion (borel_le_parabolic F i) x)).val = (e.middle x).val := by
  cases i
  · exact congrArg Subtype.val (e.left_commutes x)
  · exact congrArg Subtype.val (e.right_commutes x)

omit [Finite F] [CharP F 2] in
/-- An endpoint automorphism with its compatible middle map preserves the
image of every middle subgroup preserved by that middle map. -/
private theorem endpoint_preserves_subgroup (e : RankTwoAmalgam.Iso α α)
    (i : Bool) (T : Subgroup PSL(3,F)) (hTB : T ≤ borel F)
    (hT : (T.subgroupOf (borel F)).map e.middle.toMonoidHom = T.subgroupOf (borel F)) :
    (T.subgroupOf (parabolic F i)).map (endpointAut F e i).toMonoidHom =
      T.subgroupOf (parabolic F i) := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    let b : borel F := ⟨x.val,hTB hx⟩
    have hb : e.middle b ∈ T.subgroupOf (borel F) := hT.le (mem_map_of_mem _ hx)
    have hh := endpointAut_middle F e i b
    change (endpointAut F e i x).val ∈ T
    rw [show (endpointAut F e i x).val = (e.middle b).val from hh]
    exact hb
  · intro x hx
    let b : borel F := ⟨x.val,hTB hx⟩
    obtain ⟨y,hy,he⟩ := hT.ge (show b ∈ T.subgroupOf (borel F) from hx)
    refine ⟨inclusion (borel_le_parabolic F i) y, hy, ?_⟩
    apply Subtype.ext
    exact (endpointAut_middle F e i y).trans (congrArg Subtype.val he)

omit [Finite F] [CharP F 2] in
private theorem endpoint_preserves_borel (e : RankTwoAmalgam.Iso α α) (i : Bool) :
    ((borel F).subgroupOf (parabolic F i)).map (endpointAut F e i).toMonoidHom =
      (borel F).subgroupOf (parabolic F i) := by
  apply endpoint_preserves_subgroup F e i (borel F) le_rfl
  rw [subgroupOf_self,Subgroup.map_top_of_surjective _ e.middle.surjective]

/-- The two specified native reflection images stay outside the entire Borel. -/
theorem image_reflection_not_mem_borel (e : RankTwoAmalgam.Iso α α) (i : Bool) :
    (endpointAut F e i ⟨reflection F i,reflection_mem F i⟩).val ∉ borel F := by
  intro h
  have hh : endpointAut F e i ⟨reflection F i,reflection_mem F i⟩ ∈
      ((borel F).subgroupOf (parabolic F i)).map (endpointAut F e i).toMonoidHom := by
    rwa [endpoint_preserves_borel F e i]
  have hmem : (⟨reflection F i,reflection_mem F i⟩ : parabolic F i) ∈
      (borel F).subgroupOf (parabolic F i) :=
    (mem_map_iff_mem (endpointAut F e i).injective).mp hh
  exact reflection_not_mem_borel F i hmem

/-- Torus alignment in the middle is enough to put both exact endpoint
reflection images in their native torus-normalizer cosets. -/
theorem image_reflection_normalizes (e : RankTwoAmalgam.Iso α α)
    (hT : ((torus F).subgroupOf (borel F)).map e.middle.toMonoidHom =
      (torus F).subgroupOf (borel F)) (i : Bool) :
    (endpointAut F e i ⟨reflection F i,reflection_mem F i⟩).val ∈
      normalizer (torus F : Set PSL(3,F)) := by
  let P := parabolic F i
  let T := (torus F).subgroupOf P
  let s : P := ⟨reflection F i,reflection_mem F i⟩
  have hs : s ∈ normalizer (T : Set P) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact Subgroup.mem_normalizer_iff.mp (reflection_normalizes_torus F i) x.val
  have hmap : T.map (endpointAut F e i).toMonoidHom = T :=
    endpoint_preserves_subgroup F e i (torus F) (torus_le_borel F) hT
  have hn := T.le_normalizer_map (endpointAut F e i).toMonoidHom (mem_map_of_mem _ hs)
  rw [hmap] at hn
  have hh := T.le_normalizer_map P.subtype (mem_map_of_mem _ hn)
  rw [map_subgroupOf_eq_of_le ((torus_le_borel F).trans (borel_le_parabolic F i))] at hh
  exact hh

/-- Exact endpoint elements, rather than endpoint ranges, satisfy the native
cubic relation after a single compatible torus alignment. -/
theorem aligned_reflection_images_cube (hq : 2 < Nat.card F)
    (e : RankTwoAmalgam.Iso α α)
    (hT : ((torus F).subgroupOf (borel F)).map e.middle.toMonoidHom =
      (torus F).subgroupOf (borel F)) (i : Bool) :
    ((endpointAut F e i ⟨reflection F i,reflection_mem F i⟩).val *
      (endpointAut F e (!i) ⟨reflection F (!i),reflection_mem F (!i)⟩).val)^3 = 1 :=
  normalizer_product_cube F hq i _ _ (Subtype.property _) (Subtype.property _)
    (image_reflection_normalizes F e hT i) (image_reflection_normalizes F e hT (!i))
    (image_reflection_not_mem_borel F e i) (image_reflection_not_mem_borel F e (!i))

/-- Every compatible native amalgam automorphism preserves the literal cubic
word in the prescribed endpoint reflections. The same Borel conjugation is
used on both endpoints and then cancelled in the ambient projective group. -/
theorem reflection_images_cube {n : ℕ} (hF : Nat.card F = 2^n)
    (hn : 1 < n) (e : RankTwoAmalgam.Iso α α) (i : Bool) :
    ((endpointAut F e i ⟨reflection F i,reflection_mem F i⟩).val *
      (endpointAut F e (!i) ⟨reflection F (!i),reflection_mem F (!i)⟩).val)^3 = 1 := by
  obtain ⟨b,hb⟩ := exists_borel_torus_alignment F hF e.middle
  let a := e.trans (borelConjugation F b)
  have hT : ((torus F).subgroupOf (borel F)).map a.middle.toMonoidHom =
      (torus F).subgroupOf (borel F) := by
    change ((torus F).subgroupOf (borel F)).map
      ((MulAut.conj b).toMonoidHom.comp e.middle.toMonoidHom) = _
    rw [←Subgroup.map_map]
    exact hb
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hn
  have hc := aligned_reflection_images_cube F hq a hT i
  have he (j : Bool) (x : parabolic F j) :
      (endpointAut F a j x).val = MulAut.conj b.val (endpointAut F e j x).val := by
    cases j <;> rfl
  rw [he,he,←map_mul,←map_pow] at hc
  exact (MulAut.conj b.val).injective (hc.trans (map_one _).symm)

/-- The same literal relation with the line endpoint first. -/
theorem reverse_reflection_images_cube {n : ℕ} (hF : Nat.card F = 2^n)
    (hn : 1 < n) (e : RankTwoAmalgam.Iso (α).reverse (α).reverse) :
    ((e.left ⟨reflection F true,reflection_mem F true⟩).val *
      (e.right ⟨reflection F false,reflection_mem F false⟩).val)^3 = 1 :=
  reflection_images_cube F hF hn e.reverse true

/-- The native inclusion completion on the already known concrete carrier. -/
def modelCompletion : RankTwoAmalgam.FaithfulCompletion α (G := PSL(3,F)) :=
  RankTwoAmalgam.FaithfulCompletion.ofSubgroups _ _ _
    (GreenBook.LieModels.LinearThree.borel_le_point F)
    (GreenBook.LieModels.LinearThree.borel_le_line F) (parabolics_sup_eq_top F)

omit [CharP F 2] in
theorem model_overlap :
    (modelCompletion F).left.range ⊓ (modelCompletion F).right.range =
      (modelCompletion F).middle.range := by
  have hm : (modelCompletion F).middle.range = borel F :=
    RankTwoAmalgam.FaithfulCompletion.ofSubgroups_middle_range _ _ _ _ _ _
  rw [hm]
  simpa only [modelCompletion,RankTwoAmalgam.FaithfulCompletion.ofSubgroups_left_range,
    RankTwoAmalgam.FaithfulCompletion.ofSubgroups_right_range] using
    GreenBook.LieModels.LinearThree.parabolic_intersection F

omit [CharP F 2] in
/-- The original and twisted native markings have exactly the same whole Borel. -/
theorem twisted_model_overlap (e : RankTwoAmalgam.Iso α α) :
    ((modelCompletion F).comapIso e).left.range ⊓ ((modelCompletion F).comapIso e).right.range =
      ((modelCompletion F).comapIso e).middle.range := by
  simpa only [RankTwoAmalgam.FaithfulCompletion.comapIso_left_range,
    RankTwoAmalgam.FaithfulCompletion.comapIso_right_range,
    RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range] using model_overlap F

omit [CharP F 2] in
/-- The pair has the whole overlap, as detected by its faithful first marking. -/
theorem paired_overlap (e : RankTwoAmalgam.Iso α α) :
    let c := (modelCompletion F).pairCompletion ((modelCompletion F).comapIso e)
    c.left.range ⊓ c.right.range = c.middle.range := by
  let c := modelCompletion F
  let d := c.comapIso e
  let z := c.pairCompletion d
  apply le_antisymm _ (le_inf z.middle_le_left z.middle_le_right)
  rintro a ⟨⟨x,hx⟩,⟨y,hy⟩⟩
  have hxy : c.left x=c.right y := by
    have he := congrArg (c.pairFst d) (hx.trans hy.symm)
    simpa only [z,RankTwoAmalgam.FaithfulCompletion.pairFst_left,
      RankTwoAmalgam.FaithfulCompletion.pairFst_right] using he
  obtain ⟨b,hb⟩ := (model_overlap F).le
    (show c.left x ∈ c.left.range ⊓ c.right.range from ⟨⟨x,rfl⟩,⟨y,hxy.symm⟩⟩)
  have hbx : (GreenBook.LieModels.LinearThree.amalgam F).left b = x := c.left_injective hb
  refine ⟨b,?_⟩
  change z.left _ = a
  rw [hbx]
  exact hx

omit [CharP F 2] in
/-- The first pair projection is a literal covering of the native coset graph. -/
theorem paired_first_cover (e : RankTwoAmalgam.Iso α α) :
    Subgroup.CosetGeometry.RankTwo.CoverData
      ((modelCompletion F).pairCompletion ((modelCompletion F).comapIso e)).cosetFamily
      (modelCompletion F).cosetFamily
      ((modelCompletion F).pairFst ((modelCompletion F).comapIso e)) := by
  apply RankTwoAmalgam.FaithfulCompletion.coverData_of_hom
  · ext x; exact (modelCompletion F).pairFst_left ((modelCompletion F).comapIso e) x
  · ext x; exact (modelCompletion F).pairFst_right ((modelCompletion F).comapIso e) x
  · exact paired_overlap F e
  · exact model_overlap F

omit [CharP F 2] in
/-- The second covering retains the given endpoint automorphisms pointwise. -/
theorem paired_second_cover (e : RankTwoAmalgam.Iso α α) :
    Subgroup.CosetGeometry.RankTwo.CoverData
      ((modelCompletion F).pairCompletion ((modelCompletion F).comapIso e)).cosetFamily
      ((modelCompletion F).comapIso e).cosetFamily
      ((modelCompletion F).pairSnd ((modelCompletion F).comapIso e)) := by
  apply RankTwoAmalgam.FaithfulCompletion.coverData_of_hom
  · ext x; exact (modelCompletion F).pairSnd_left ((modelCompletion F).comapIso e) x
  · ext x; exact (modelCompletion F).pairSnd_right ((modelCompletion F).comapIso e) x
  · exact paired_overlap F e
  · exact twisted_model_overlap F e

/-- The paired native/twisted-native completion satisfies a COMMON literal
cubic word. Cube membership in a source middle would not suffice here. -/
theorem paired_reflections_cube {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : RankTwoAmalgam.Iso α α) :
    let c := (modelCompletion F).pairCompletion ((modelCompletion F).comapIso e)
    (c.left ⟨reflection F false,reflection_mem F false⟩ *
      c.right ⟨reflection F true,reflection_mem F true⟩)^3 = 1 := by
  dsimp only
  let c := modelCompletion F
  let d := c.comapIso e
  let z := c.pairCompletion d
  let s : pointParabolic F := ⟨reflection F false,reflection_mem F false⟩
  let t : lineParabolic F := ⟨reflection F true,reflection_mem F true⟩
  apply Subtype.ext
  apply Prod.ext
  · have h : c.pairFst d ((z.left s*z.right t)^3) = c.pairFst d 1 := by
      rw [map_pow,map_mul,RankTwoAmalgam.FaithfulCompletion.pairFst_left,
        RankTwoAmalgam.FaithfulCompletion.pairFst_right,map_one]
      change (reflection F false * reflection F true)^3 = 1
      have hh := twisted_reflections_cube F false 1 1
      simpa only [map_one,one_mul,Bool.not_false] using hh
    exact h
  · have h : c.pairSnd d ((z.left s*z.right t)^3) = c.pairSnd d 1 := by
      rw [map_pow,map_mul,RankTwoAmalgam.FaithfulCompletion.pairSnd_left,
        RankTwoAmalgam.FaithfulCompletion.pairSnd_right,map_one]
      exact reflection_images_cube F hF hn e false
    exact h

end CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeEven
