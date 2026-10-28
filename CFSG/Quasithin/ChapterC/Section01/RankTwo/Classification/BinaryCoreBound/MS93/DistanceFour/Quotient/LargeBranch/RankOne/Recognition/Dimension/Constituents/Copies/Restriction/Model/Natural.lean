module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Copies.Restriction.Model.Transport
public import Theory.SpecificGroups.PSL3Two.Parabolics.LineCore

/-!
# The doubled-natural standard parabolic calculation

For the natural binary SL₃-module, the point parabolic fixes only the e₀ line,
while the plane parabolic has no fixed vectors. On two natural copies, a
point-fixed seed whose full group orbit spans the module must therefore be the
whole pair of e₀ lines: projection onto these lines takes each translate of a
seed vector to a scalar multiple of that same vector.

The adjacent plane parabolic spans exactly the pair of planes v₂ = 0, using
the identity and the swap of coordinates 0 and 1. Reading the first two
coordinates in each copy gives the required linear equivalence. The upper-left
block is a surjection to SL₂(2), its kernel is the shear two-core, and the
coordinates intertwine every element of the parabolic.

This supplies the natural-model input to the homogeneous restriction transport
for Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two* (1993),
(4.6.12)(5), printed pp.911--912, in particular the doubled natural SL₂
restriction at the start of p.912.
-/

@[expose] public section
open Subgroup Matrix Representation Matrix.PSL3Two
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension.Restriction
namespace NaturalCalculation

private theorem binary_unit (a b : ZMod 2) (h : a * b = 1) : a = 1 ∧ b = 1 := by
  have hfinite : ∀ a b : ZMod 2, a * b = 1 → a = 1 ∧ b = 1 := by decide
  exact hfinite a b h

private theorem line_det (g : lineParabolicSL) :
    (g.val.val 0 0 * g.val.val 1 1 - g.val.val 0 1 * g.val.val 1 0) = 1 ∧
      g.val.val 2 2 = 1 := by
  obtain ⟨h20, h21⟩ := (mem_lineParabolicSL_iff _).mp g.property
  have hd := g.val.property
  rw [det_fin_three] at hd
  simp only [h20, h21, mul_zero, add_zero, sub_zero] at hd
  apply binary_unit _ _
  calc
    _ = g.val.val 0 0 * g.val.val 1 1 * g.val.val 2 2 -
        g.val.val 0 1 * g.val.val 1 0 * g.val.val 2 2 := by ring
    _ = 1 := hd

private def quotient : lineParabolicSL →* SL2 where
  toFun g := ⟨!![g.val.val 0 0, g.val.val 0 1; g.val.val 1 0, g.val.val 1 1], by
    simpa only [det_fin_two, of_apply, cons_val_zero, cons_val_one, head_cons] using
      (line_det g).1⟩
  map_one' := by apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_mul' g h := by
    obtain ⟨h20, h21⟩ := (mem_lineParabolicSL_iff _).mp h.property
    apply Subtype.ext
    change !![(g.val.val * h.val.val) 0 0, (g.val.val * h.val.val) 0 1;
        (g.val.val * h.val.val) 1 0, (g.val.val * h.val.val) 1 1] =
      !![g.val.val 0 0, g.val.val 0 1; g.val.val 1 0, g.val.val 1 1] *
        !![h.val.val 0 0, h.val.val 0 1; h.val.val 1 0, h.val.val 1 1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, h20, h21]

private theorem quotient_surjective : Function.Surjective quotient := by
  intro a
  let g : SL := ⟨!![a.val 0 0, a.val 0 1, 0; a.val 1 0, a.val 1 1, 0; 0,0,1], by
    have hd := a.property
    rw [det_fin_two] at hd
    simpa [det_fin_three] using hd⟩
  refine ⟨⟨g, (mem_lineParabolicSL_iff _).mpr ⟨rfl, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem quotient_ker : quotient.ker = pCore 2 lineParabolicSL := by
  have hcore : (pCore 2 lineParabolicSL).map lineParabolicSL.subtype = BinaryLinearThree.R :=
    lineParabolicSL_pCoreIn_two_eq_R
  ext g
  have hg : g ∈ pCore 2 lineParabolicSL ↔ g.val ∈ BinaryLinearThree.R := by
    rw [← hcore]
    constructor
    · exact Subgroup.mem_map_of_mem _
    · rintro ⟨x, hx, he⟩
      exact (Subtype.ext he : x = g) ▸ hx
  rw [hg]
  constructor
  · intro hk
    have he : (quotient g).val = (1 : SL2).val := congrArg Subtype.val hk
    have h00 := congrArg (fun m : Matrix (Fin 2) (Fin 2) (ZMod 2) => m 0 0) he
    have h01 := congrArg (fun m : Matrix (Fin 2) (Fin 2) (ZMod 2) => m 0 1) he
    have h10 := congrArg (fun m : Matrix (Fin 2) (Fin 2) (ZMod 2) => m 1 0) he
    have h11 := congrArg (fun m : Matrix (Fin 2) (Fin 2) (ZMod 2) => m 1 1) he
    change g.val.val 0 0 = 1 at h00
    change g.val.val 0 1 = 0 at h01
    change g.val.val 1 0 = 0 at h10
    change g.val.val 1 1 = 1 at h11
    obtain ⟨h20, h21⟩ := (mem_lineParabolicSL_iff _).mp g.property
    have h22 := (line_det g).2
    refine ⟨Multiplicative.ofAdd (g.val.val 0 2, g.val.val 1 2), ?_⟩
    apply Subtype.ext
    change !![1,0,g.val.val 0 2; 0,1,g.val.val 1 2; 0,0,1] = g.val.val
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11, h20, h21, h22]
  · rintro ⟨c, hc⟩
    change quotient g = 1
    apply Subtype.ext
    have hm := congrArg Subtype.val hc
    change !![1,0,c.toAdd.1; 0,1,c.toAdd.2; 0,0,1] = g.val.val at hm
    change !![g.val.val 0 0, g.val.val 0 1; g.val.val 1 0, g.val.val 1 1] = 1
    rw [← hm]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

private abbrev Vector := BinaryLinearThree.Vector
private noncomputable abbrev sigma := BinaryLinearThree.W.prod BinaryLinearThree.W

private def t01 : SL := ⟨!![1,1,0; 0,1,0; 0,0,1], by decide⟩
private def t02 : SL := ⟨!![1,0,1; 0,1,0; 0,0,1], by decide⟩
private def t10 : SL := ⟨!![1,0,0; 1,1,0; 0,0,1], by decide⟩
private def swap01 : SL := ⟨!![0,1,0; 1,0,0; 0,0,1], by decide⟩

private theorem fixed_point_coordinates (v : Vector)
    (h : ∀ g : pointParabolicSL, BinaryLinearThree.W g.val v = v) :
    v 1 = 0 ∧ v 2 = 0 := by
  have h1 := congrFun (h ⟨t01, (mem_pointParabolicSL_iff _).mpr ⟨rfl, rfl⟩⟩) 0
  have h2 := congrFun (h ⟨t02, (mem_pointParabolicSL_iff _).mpr ⟨rfl, rfl⟩⟩) 0
  change (!![1,1,0; 0,1,0; 0,0,1].mulVec v) 0 = v 0 at h1
  change (!![1,0,1; 0,1,0; 0,0,1].mulVec v) 0 = v 0 at h2
  simpa [mulVec, dotProduct, Fin.sum_univ_three] using And.intro h1 h2

private theorem fixed_line_zero (v : Vector)
    (h : ∀ g : lineParabolicSL, BinaryLinearThree.W g.val v = v) : v = 0 := by
  have h1 := congrFun (h ⟨t01, (mem_lineParabolicSL_iff _).mpr ⟨rfl, rfl⟩⟩) 0
  have h2 := congrFun (h ⟨t02, (mem_lineParabolicSL_iff _).mpr ⟨rfl, rfl⟩⟩) 0
  have h0 := congrFun (h ⟨t10, (mem_lineParabolicSL_iff _).mpr ⟨rfl, rfl⟩⟩) 1
  change (!![1,1,0; 0,1,0; 0,0,1].mulVec v) 0 = v 0 at h1
  change (!![1,0,1; 0,1,0; 0,0,1].mulVec v) 0 = v 0 at h2
  change (!![1,0,0; 1,1,0; 0,0,1].mulVec v) 1 = v 1 at h0
  simp [mulVec, dotProduct, Fin.sum_univ_three] at h0 h1 h2
  ext k
  fin_cases k <;> simp [h0, h1, h2]

private def axis : Submodule (ZMod 2) Vector where
  carrier := {v | v 1 = 0 ∧ v 2 = 0}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := by rintro v w ⟨h1, h2⟩ ⟨k1, k2⟩; exact ⟨by simp [h1, k1], by simp [h2, k2]⟩
  smul_mem' := by rintro c v ⟨h1, h2⟩; exact ⟨by simp [h1], by simp [h2]⟩

private def plane : Submodule (ZMod 2) Vector where
  carrier := {v | v 2 = 0}
  zero_mem' := rfl
  add_mem' := by intro v w hv hw; simp_all
  smul_mem' := by intro c v hv; simp_all

private def projection : Vector →ₗ[ZMod 2] Vector where
  toFun v := ![v 0,0,0]
  map_add' v w := by ext k; fin_cases k <;> simp
  map_smul' c v := by ext k; fin_cases k <;> simp

private theorem projection_axis (v : Vector) (hv : v ∈ axis) : projection v = v := by
  obtain ⟨h1, h2⟩ := hv
  ext k
  fin_cases k <;> simp [projection, h1, h2]

private theorem projection_action (g : SL) (v : Vector) (hv : v ∈ axis) :
    projection (BinaryLinearThree.W g v) = g.val 0 0 • v := by
  obtain ⟨h1, h2⟩ := hv
  ext k
  fin_cases k <;>
    simp [projection, BinaryLinearThree.W, specialLinearNatural_apply,
      mulVec, dotProduct, Fin.sum_univ_three, h1, h2]

-- Full-group generation recovers both multiplicity coordinates without choosing
-- a basis of the unknown seed submodule.
private theorem seed_eq (E : Submodule (ZMod 2) (Vector × Vector))
    (hfix : E ≤ BinaryOffender.fixedSpace sigma pointParabolicSL)
    (hgen : Seed.orbitSpace sigma ⊤ E = ⊤) : E = axis.prod axis := by
  have haxis : E ≤ axis.prod axis := by
    intro v hv
    exact ⟨fixed_point_coordinates v.1 (fun g => congrArg Prod.fst (hfix hv g)),
      fixed_point_coordinates v.2 (fun g => congrArg Prod.snd (hfix hv g))⟩
  have hproj : Seed.orbitSpace sigma ⊤ E ≤ E.comap (projection.prodMap projection) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, _, v, hv, rfl⟩
    change (projection (BinaryLinearThree.W g v.1),
      projection (BinaryLinearThree.W g v.2)) ∈ E
    rw [projection_action g v.1 (haxis hv).1, projection_action g v.2 (haxis hv).2]
    exact E.smul_mem (g.val 0 0) hv
  apply le_antisymm haxis
  intro v hv
  have he := hproj (show v ∈ Seed.orbitSpace sigma ⊤ E by rw [hgen]; trivial)
  change (projection v.1, projection v.2) ∈ E at he
  rwa [projection_axis v.1 hv.1, projection_axis v.2 hv.2] at he

private theorem line_orbit_eq :
    Seed.orbitSpace sigma lineParabolicSL (axis.prod axis) = plane.prod plane := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, v, hv, rfl⟩
    obtain ⟨h20, h21⟩ := (mem_lineParabolicSL_iff _).mp hg
    have h12 := hv.1.2
    have h22 := hv.2.2
    change (g.val.mulVec v.1) 2 = 0 ∧ (g.val.mulVec v.2) 2 = 0
    simp [mulVec, dotProduct, Fin.sum_univ_three, h20, h21, h12, h22]
  · intro v hv
    let v0 : Vector × Vector := (![v.1 0,0,0], ![v.2 0,0,0])
    let v1 : Vector × Vector := (![v.1 1,0,0], ![v.2 1,0,0])
    have h0 : v0 ∈ Seed.orbitSpace sigma lineParabolicSL (axis.prod axis) := by
      exact Submodule.subset_span ⟨1, one_mem _, v0, ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩, by simp⟩
    have h1 : sigma swap01 v1 ∈ Seed.orbitSpace sigma lineParabolicSL (axis.prod axis) :=
      Submodule.subset_span ⟨swap01, (mem_lineParabolicSL_iff _).mpr ⟨rfl, rfl⟩,
        v1, ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩, rfl⟩
    have he : v0 + sigma swap01 v1 = v := by
      have h12 : v.1 2 = 0 := hv.1
      have h22 : v.2 2 = 0 := hv.2
      apply Prod.ext
      · change ![v.1 0,0,0] + !![0,1,0; 1,0,0; 0,0,1].mulVec ![v.1 1,0,0] = v.1
        ext k
        fin_cases k <;> simp [h12]
      · change ![v.2 0,0,0] + !![0,1,0; 1,0,0; 0,0,1].mulVec ![v.2 1,0,0] = v.2
        ext k
        fin_cases k <;> simp [h22]
    rw [← he]
    exact Submodule.add_mem _ h0 h1

-- These coordinates read the actual orbit vectors, so the action equation
-- below uses the full upper-left block of each parabolic element.
private def coordinates :
    Seed.orbitSpace sigma lineParabolicSL (axis.prod axis) ≃ₗ[ZMod 2]
      (Fin 2 → Fin 2 → ZMod 2) where
  toFun v := ![![v.val.1 0, v.val.1 1], ![v.val.2 0, v.val.2 1]]
  invFun f := ⟨(![f 0 0, f 0 1, 0], ![f 1 0, f 1 1, 0]), by
    rw [line_orbit_eq]
    exact ⟨rfl, rfl⟩⟩
  left_inv v := by
    have hv : v.val ∈ plane.prod plane := line_orbit_eq ▸ v.property
    have h12 : v.val.1 2 = 0 := hv.1
    have h22 : v.val.2 2 = 0 := hv.2
    apply Subtype.ext
    apply Prod.ext
    · ext k; fin_cases k <;> simp [h12]
    · ext k; fin_cases k <;> simp [h22]
  right_inv f := by ext j k; fin_cases j <;> fin_cases k <;> rfl
  map_add' v w := by ext j k; fin_cases j <;> fin_cases k <;> rfl
  map_smul' c v := by ext j k; fin_cases j <;> fin_cases k <;> rfl

private theorem coordinates_action (a : lineParabolicSL)
    (v w : Seed.orbitSpace sigma lineParabolicSL (axis.prod axis))
    (hw : (w : Vector × Vector) = sigma a.val (v : Vector × Vector)) (j : Fin 2) :
    coordinates w j = (quotient a).val.mulVec (coordinates v j) := by
  have hv : v.val ∈ plane.prod plane := line_orbit_eq ▸ v.property
  have h12 : v.val.1 2 = 0 := hv.1
  have h22 : v.val.2 2 = 0 := hv.2
  have hw0 := congrArg Prod.fst hw
  have hw1 := congrArg Prod.snd hw
  change w.val.1 = a.val.val.mulVec v.val.1 at hw0
  change w.val.2 = a.val.val.mulVec v.val.2 at hw1
  fin_cases j
  · change ![w.val.1 0, w.val.1 1] =
      !![a.val.val 0 0, a.val.val 0 1; a.val.val 1 0, a.val.val 1 1].mulVec
        ![v.val.1 0, v.val.1 1]
    rw [hw0]
    ext k
    fin_cases k <;> simp [mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two, h12]
  · change ![w.val.2 0, w.val.2 1] =
      !![a.val.val 0 0, a.val.val 0 1; a.val.val 1 0, a.val.val 1 1].mulVec
        ![v.val.2 0, v.val.2 1]
    rw [hw1]
    ext k
    fin_cases k <;> simp [mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two, h22]

private theorem line_not_generates (E : Submodule (ZMod 2) (Vector × Vector))
    (hfix : E ≤ BinaryOffender.fixedSpace sigma lineParabolicSL)
    (hgen : Seed.orbitSpace sigma ⊤ E = ⊤) : False := by
  have hzero : Seed.orbitSpace sigma ⊤ E ≤ ⊥ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, _, v, hv, rfl⟩
    have he : v = 0 := Prod.ext
      (fixed_line_zero v.1 (fun a => congrArg Prod.fst (hfix hv a)))
      (fixed_line_zero v.2 (fun a => congrArg Prod.snd (hfix hv a)))
    simp [he]
  rw [hgen] at hzero
  exact top_ne_bot (le_antisymm hzero bot_le)

end NaturalCalculation

/-- The standard doubled-natural restriction, with its full parabolic action
and the intrinsic two-core as kernel of the actual rank-one quotient. -/
theorem natural_standard_orbit_calculation :
    StandardOrbitCalculation (BinaryLinearThree.W.prod BinaryLinearThree.W) := by
  intro i E hfix hgen
  cases i with
  | false =>
    refine ⟨NaturalCalculation.quotient, NaturalCalculation.quotient_surjective,
      NaturalCalculation.quotient_ker, ?_⟩
    rw [NaturalCalculation.seed_eq E hfix hgen]
    exact ⟨NaturalCalculation.coordinates, NaturalCalculation.coordinates_action⟩
  | true => exact (NaturalCalculation.line_not_generates E hfix hgen).elim

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension.Restriction
