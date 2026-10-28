module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Restriction

/-!
# Integral coordinates and polynomial geometry of the octad restriction

Restriction to the marked eight coordinates is an actual integral linear
isomorphism. In these coordinates the lattice consists of the vectors whose
entries are all 0 modulo 4 or all 2 modulo 4, with coordinate sum 0 modulo 8.
This is the usual coordinate description of the scaled E₈ lattice. The Golay
minimum proves that a codeword supported on the octad is zero or that octad;
eight times each coordinate vector gives the rank-eight lower bound.

The source's central involution is the sign on the complementary sixteen
coordinates, namely `negationIsometry * sign`. We prove that it is nonidentity,
central in the actual centralizer, and belongs to the actual restriction kernel.
Finally the whole-Leech polynomial implies the octad polynomial and the A₂
pairing identity for its minimal vectors. These facts do not classify cubic
images or replace the whole-Leech lift condition by an octad-only condition.

Source: Aschbacher, *Sporadic Groups* (1994), §25, pp.132–134, especially
25.1–25.5. The underlying Golay and Leech constructions are the existing ports
of Gerald Höhn and ATLAS contributors, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`; see `LICENSES/ATLAS.txt` and
`LICENSES/ATLAS-CITATION.cff`.
-/

@[expose] public noncomputable section

open Atlas.Codes Atlas.Lattices Atlas.Conway
open scoped BigOperators
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction

abbrev Coordinate := {i : Omega // (golayBasis 0).val i ≠ 0}

theorem coordinate_card : Fintype.card Coordinate = 8 := by
  classical
  change Fintype.card {i : Omega // (golayBasis 0 : BinaryWord) i ≠ 0} = 8
  rw [Fintype.card_subtype]
  exact ambientOctad_weight

def coordinates : lattice →ₗ[ℤ] (Coordinate → ℤ) where
  toFun x i := x.val.val i.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coordinates_injective : Function.Injective coordinates := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  funext i
  by_cases hi : (golayBasis 0).val i = 0
  · rw [(mem_lattice_iff_support x.val).mp x.prop i hi,
      (mem_lattice_iff_support y.val).mp y.prop i hi]
  · exact congrFun h ⟨i, hi⟩

def extendCoordinates : (Coordinate → ℤ) →ₗ[ℤ] IntegerCoordinates where
  toFun x i := if hi : (golayBasis 0).val i ≠ 0 then x ⟨i, hi⟩ else 0
  map_add' x y := by ext i; dsimp; split_ifs <;> rfl
  map_smul' n x := by ext i; dsimp; split_ifs <;> simp

def scaledCoordinates : (Coordinate → ℤ) →ₗ[ℤ] lattice where
  toFun x := ⟨eightIntoLeech (extendCoordinates x), by
    rw [mem_lattice_iff_support]
    intro i hi
    simp [eightIntoLeech, extendCoordinates, hi]⟩
  map_add' x y := by apply Subtype.ext; simp
  map_smul' n x := by
    apply Subtype.ext
    change eightIntoLeech (extendCoordinates (n • x)) = n • eightIntoLeech (extendCoordinates x)
    rw [map_smul, map_smul]

theorem coordinates_scaled (x : Coordinate → ℤ) :
    coordinates (scaledCoordinates x) = 8 • x := by
  funext i
  simp [coordinates, scaledCoordinates, eightIntoLeech, extendCoordinates, i.prop]

theorem scaledCoordinates_injective : Function.Injective scaledCoordinates := by
  intro x y h
  have hh := congrArg coordinates h
  rw [coordinates_scaled, coordinates_scaled] at hh
  funext i
  have hi := congrFun hh i
  change (8 : ℤ) * x i = 8 * y i at hi
  omega

theorem lattice_finrank : Module.finrank ℤ lattice = 8 := by
  have hu := LinearMap.finrank_le_finrank_of_injective coordinates_injective
  have hl := LinearMap.finrank_le_finrank_of_injective scaledCoordinates_injective
  have hd : Module.finrank ℤ (Coordinate → ℤ) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, coordinate_card]
  rw [hd] at hu hl
  omega

theorem supported_code (c : golay)
    (hc : ∀ i : Omega, (golayBasis 0).val i = 0 → c.val i = 0) :
    c = 0 ∨ c = golayBasis 0 := by
  classical
  by_cases hz : c = 0
  · exact Or.inl hz
  right
  have hs : support c.val ⊆ support (golayBasis 0).val := by
    intro i hi
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact fun h => hi (hc i h)
  have hn : c.val ≠ 0 := fun h => hz (Subtype.ext h)
  have hl := golay_minimum c.val c.prop hn
  have he : support c.val = support (golayBasis 0).val := by
    apply Finset.eq_of_subset_of_card_le hs
    change hammingNorm (golayBasis 0).val ≤ hammingNorm c.val
    rw [ambientOctad_weight]
    exact hl
  exact Subtype.ext (support_injective he)

theorem lattice_coordinates_even (x : lattice) (i : Omega) : x.val.val i % 2 = 0 := by
  obtain ⟨m, _, hp, _, _⟩ := (mem_leech x.val.val).mp x.val.prop
  have hzero : (golayBasis 0).val ((0,0),0) = 0 := by
    rw [golayBasis_coe]
    decide +kernel
  have hx := (mem_lattice_iff_support x.val).mp x.prop ((0,0),0) hzero
  have hm := hp ((0,0),0)
  rw [hx] at hm
  simpa only [← hm, Int.zero_emod] using hp i

theorem lattice_halfResidue (x : lattice) :
    halfResidue x.val.val 0 = 0 ∨
      halfResidue x.val.val 0 = (golayBasis 0).val := by
  obtain ⟨m, _, hp, hc, _⟩ := (mem_leech x.val.val).mp x.val.prop
  have hm : m = 0 := (hp ((0,0),0)).symm.trans (lattice_coordinates_even x _)
  subst m
  have hh := supported_code ⟨halfResidue x.val.val 0, hc⟩ (by
    intro i hi
    have hx := (mem_lattice_iff_support x.val).mp x.prop i hi
    simp [halfResidue, integerReduction, hx])
  exact hh.imp (congrArg Subtype.val) (congrArg Subtype.val)

theorem lattice_coordinate_congruences (x : lattice) :
    (∀ i, x.val.val i % 2 = 0) ∧
      (halfResidue x.val.val 0 = 0 ∨ halfResidue x.val.val 0 = (golayBasis 0).val) ∧
      (∑ i, x.val.val i) % 8 = 0 := by
  refine ⟨lattice_coordinates_even x, lattice_halfResidue x, ?_⟩
  obtain ⟨m, _, hp, _, hs⟩ := (mem_leech x.val.val).mp x.val.prop
  have hm : m = 0 := (hp ((0,0),0)).symm.trans (lattice_coordinates_even x _)
  simpa only [hm, mul_zero] using hs

/-- The integral coordinates are the usual `4 E₈` coordinates on the marked octad. -/
theorem supported_mem_leech_iff (x : IntegerCoordinates)
    (hx : ∀ i : Omega, (golayBasis 0).val i = 0 → x i = 0) :
    x ∈ leech ↔
      ((∀ i : Coordinate, x i.val % 4 = 0) ∨ (∀ i : Coordinate, x i.val % 4 = 2)) ∧
        (∑ i, x i) % 8 = 0 := by
  constructor
  · intro hxl
    let y : lattice := ⟨⟨x, hxl⟩, (mem_lattice_iff_support _).mpr hx⟩
    obtain ⟨he, hr, hs⟩ := lattice_coordinate_congruences y
    refine ⟨?_, hs⟩
    rcases hr with hr | hr
    · left
      intro i
      have hi := congrFun hr i.val
      simp only [halfResidue, integerReduction, sub_zero, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
        Pi.zero_apply] at hi
      change ((x i.val / 2 : ℤ) : Bit) = 0 at hi
      have hm := (ZMod.intCast_zmod_eq_zero_iff_dvd (x i.val / 2) 2).mp hi
      have hp := he i.val
      change x i.val % 2 = 0 at hp
      omega
    · right
      intro i
      have hi := congrFun hr i.val
      simp only [halfResidue, integerReduction, sub_zero, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hi
      have hone : (golayBasis 0).val i.val = 1 := by
        have hb : ∀ b : Bit, b ≠ 0 → b = 1 := by decide
        exact hb _ i.prop
      change ((x i.val / 2 : ℤ) : Bit) = (golayBasis 0).val i.val at hi
      rw [hone] at hi
      have hm := (ZMod.intCast_eq_intCast_iff' (x i.val / 2) 1 2).mp hi
      have hp := he i.val
      change x i.val % 2 = 0 at hp
      omega
  · rintro ⟨hr, hs⟩
    have he (i : Omega) : x i % 2 = 0 := by
      by_cases hi : (golayBasis 0).val i = 0
      · rw [hx i hi]; decide
      · rcases hr with hr | hr
        · have hh : x i % 4 = 0 := hr ⟨i, hi⟩
          omega
        · have hh : x i % 4 = 2 := hr ⟨i, hi⟩
          omega
    apply (mem_leech x).mpr
    refine ⟨0, Or.inl rfl, he, ?_, by simpa only [mul_zero] using hs⟩
    rcases hr with hr | hr
    · have hz : halfResidue x 0 = 0 := by
        funext i
        simp only [halfResidue, integerReduction, sub_zero, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
          Pi.zero_apply]
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr
        by_cases hi : (golayBasis 0).val i = 0
        · rw [hx i hi]; simp
        · have hh : x i % 4 = 0 := hr ⟨i, hi⟩
          exact Int.dvd_of_emod_eq_zero (by omega)
      rw [hz]
      exact golay.zero_mem
    · have hz : halfResidue x 0 = (golayBasis 0).val := by
        funext i
        simp only [halfResidue, integerReduction, sub_zero, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
        by_cases hi : (golayBasis 0).val i = 0
        · rw [hi, hx i hi]; norm_num
        · have hone : (golayBasis 0).val i = 1 := by
            have hb : ∀ b : Bit, b ≠ 0 → b = 1 := by decide
            exact hb _ hi
          rw [hone]
          apply (ZMod.intCast_eq_intCast_iff' (x i / 2) 1 2).mpr
          have hh : x i % 4 = 2 := hr ⟨i, hi⟩
          omega
      rw [hz]
      exact (golayBasis 0).prop

/-- Zero extension realizes the concrete eight-coordinate lattice inside Leech. -/
def coordinateModel : Submodule ℤ (Coordinate → ℤ) := leech.comap extendCoordinates

def coordinateEquiv : lattice ≃ₗ[ℤ] coordinateModel where
  toFun x := ⟨coordinates x, by
    change extendCoordinates (coordinates x) ∈ leech
    have he : extendCoordinates (coordinates x) = x.val.val := by
      funext i
      by_cases hi : (golayBasis 0).val i = 0
      · simp [extendCoordinates, hi, (mem_lattice_iff_support x.val).mp x.prop i hi]
      · simp [extendCoordinates, coordinates, hi]
    rw [he]
    exact x.val.prop⟩
  invFun x := ⟨⟨extendCoordinates x.val, x.prop⟩, by
    rw [mem_lattice_iff_support]
    intro i hi
    simp [extendCoordinates, hi]⟩
  left_inv x := by
    apply coordinates_injective
    funext i
    simp [coordinates, extendCoordinates, i.prop]
  right_inv x := by
    apply Subtype.ext
    funext i
    simp [coordinates, extendCoordinates, i.prop]
  map_add' x y := rfl
  map_smul' n x := rfl

theorem coordinateEquiv_apply (x : lattice) (i : Coordinate) :
    (coordinateEquiv x).val i = x.val.val i.val := rfl

theorem mem_coordinateModel (x : Coordinate → ℤ) :
    x ∈ coordinateModel ↔
      ((∀ i, x i % 4 = 0) ∨ (∀ i, x i % 4 = 2)) ∧ (∑ i, x i) % 8 = 0 := by
  change extendCoordinates x ∈ leech ↔ _
  rw [supported_mem_leech_iff _ (by intro i hi; simp [extendCoordinates, hi])]
  have hs : (∑ i : Omega, extendCoordinates x i) = ∑ i : Coordinate, x i := by
    symm
    apply Fintype.sum_of_injective (fun i : Coordinate => i.val) Subtype.val_injective
    · intro i hi
      have hn : ¬(golayBasis 0).val i ≠ 0 := fun h => hi ⟨⟨i, h⟩, rfl⟩
      simp [extendCoordinates, hn]
    · intro i
      simp [extendCoordinates, i.prop]
  have hv (i : Coordinate) : extendCoordinates x i.val = x i := by
    simp [extendCoordinates, i.prop]
  simp only [hv, hs]

def complementSign : centralizer :=
  ⟨negationIsometry * sign, by
    rw [mem_centralizer]
    exact (show Commute negationIsometry sign from
      (Subgroup.mem_center_iff.mp negation_mem_center sign).symm).mul_left
      (Commute.refl sign)⟩

theorem complementSign_apply (x : leech) :
    complementSign.val.val x = -(sign.val x) := negationIsometry_apply _

theorem complementSign_mem_kernel : complementSign ∈ action.ker := by
  rw [mem_action_ker]
  intro x
  rw [complementSign_apply]
  have hx : sign.val x.val = -x.val := x.prop
  rw [hx, neg_neg]

theorem complementSign_mem_center : complementSign ∈ Subgroup.center centralizer := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  change g.val * (negationIsometry * sign) = (negationIsometry * sign) * g.val
  exact ((show Commute g.val negationIsometry from
    Subgroup.mem_center_iff.mp negation_mem_center g.val).mul_right
      (mem_centralizer.mp g.prop)).eq

theorem complementSign_ne_one : complementSign ≠ 1 := by
  intro h
  have he := congrArg (fun g : centralizer => g.val.val (coordinateEight ((0,0),0))) h
  rw [complementSign_apply] at he
  have hi := congrArg (fun x : leech => x.val ((0,0),0)) he
  change -(if (golayBasis 0).val ((0,0),0) = 0 then (8 : ℤ) else -8) = 8 at hi
  have hzero : (golayBasis 0).val ((0,0),0) = 0 := by
    rw [golayBasis_coe]
    decide +kernel
  rw [if_pos hzero] at hi
  norm_num at hi

theorem image_preserves_form (u : Image) (x y : lattice) :
    integerDot (u.val x).val.val (u.val y).val.val = integerDot x.val.val y.val.val := by
  obtain ⟨g, hg⟩ := u.prop
  rw [← hg]
  exact action_preserves_form g x y

theorem polynomial_image {u : Image} (hu : HasPolynomialLift u) (x : lattice) :
    u.val (u.val x) + u.val x + x = 0 := by
  obtain ⟨r, hr, _, hp⟩ := hu
  rw [← hr]
  exact polynomial_on_lattice hp x

theorem polynomial_image_fixed {u : Image} (hu : HasPolynomialLift u)
    {x : lattice} (hx : u.val x = x) : x = 0 := by
  have hp := polynomial_image hu x
  rw [hx, hx] at hp
  apply Subtype.ext
  apply Subtype.ext
  funext i
  have hi := congrArg (fun y : lattice => y.val.val i) hp
  change x.val.val i + x.val.val i + x.val.val i = 0 at hi
  change x.val.val i = 0
  omega

theorem polynomial_image_pairing {u : Image} (hu : HasPolynomialLift u) (x : lattice) :
    2 * integerDot x.val.val (u.val x).val.val = -integerDot x.val.val x.val.val := by
  have hp := polynomial_image hu x
  have he := congrArg (fun y : lattice => integerDot y.val.val (u.val x).val.val) hp
  change integerDot ((u.val (u.val x)).val.val + (u.val x).val.val + x.val.val)
    (u.val x).val.val = integerDot 0 (u.val x).val.val at he
  rw [integerDot_add_left, integerDot_add_left,
    image_preserves_form u (u.val x) x, image_preserves_form u x x,
    integerDot_comm (u.val x).val.val x.val.val] at he
  simp only [integerDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at he
  change 2 * (∑ i, x.val.val i * (u.val x).val.val i) = -(∑ i, x.val.val i * x.val.val i)
  omega

theorem polynomial_image_root_pairing {u : Image} (hu : HasPolynomialLift u)
    (x : lattice) (hx : integerDot x.val.val x.val.val = 32) :
    integerDot x.val.val (u.val x).val.val = -16 := by
  have hp := polynomial_image_pairing hu x
  omega

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
