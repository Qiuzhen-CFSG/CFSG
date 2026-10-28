module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Interface

/-!
# Excluding a single natural starred factor

The natural binary three-space is transitive on nonzero vectors; its graph
twist has the same property. The large-intersection midpoint supplies a
nonzero involution lift in the actual starred group. Transitivity transports
this lift to every nonzero quotient vector. The central elementary kernel
Z_alpha then makes every element of the starred group an involution.

This would make the starred group abelian. The established decomposition
V_alpha = B_alpha V_alpha-star, with B_alpha central, contradicts the
noncentral radius-derived subgroup. No dimension-six or seed recognition
premise enters the argument.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.9)--(4.6.10) and the constituent inference in (4.6.12)(5),
printed pp.908 and 911. This supplies the exclusion of one natural factor.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
open AbelianCore.QuotientRecognition.ExtensionControl

private theorem natural_transitive {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) SL W} (hn : NaturalOrDual ρ)
    (v w : W) (hv : v ≠ 0) (hw : w ≠ 0) : ∃ g, ρ g v = w := by
  classical
  obtain ⟨a, ⟨e⟩⟩ := hn.marked
  have hev : e v ≠ 0 := fun h => hv (e.injective (h.trans e.map_zero.symm))
  have hew : e w ≠ 0 := fun h => hw (e.injective (h.trans e.map_zero.symm))
  let p : Matrix.PSL3Two.Fano.Point := ⟨e v, hev⟩
  let q : Matrix.PSL3Two.Fano.Point := ⟨e w, hew⟩
  obtain ⟨l, hl⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card
      {l : Matrix.PSL3Two.Fano.Line // Matrix.PSL3Two.Fano.Incident p l} by
    rw [Matrix.PSL3Two.Fano.lines_through_point]; decide)
  obtain ⟨k, hk⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card
      {l : Matrix.PSL3Two.Fano.Line // Matrix.PSL3Two.Fano.Incident q l} by
    rw [Matrix.PSL3Two.Fano.lines_through_point]; decide)
  let x : BinaryLinearThree.FanoDecomposition.Flag := ⟨(p,l),hl⟩
  let y : BinaryLinearThree.FanoDecomposition.Flag := ⟨(q,k),hk⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL x y
  refine ⟨a.symm g, e.injective ?_⟩
  have he := LinearMap.congr_fun (e.isIntertwining' (a.symm g)) v
  change e (ρ (a.symm g) v) = BinaryLinearThree.W (a (a.symm g)) (e v) at he
  rw [a.apply_symm_apply] at he
  exact he.trans (BinaryLinearThree.FanoDecomposition.flagPerm_eq_iff g x y |>.mp hg).1

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem natural_star_impossible (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hs : ¬ s.SmallIntersection)
    (d : LayerModule source (VStar R geometry (alpha R) (beta R)))
    (hn : NaturalOrDual d.representation) : False := by
  have hstar := Flags.star_le_radius geometry (alpha R) (beta R)
  have hQ := hstar.trans (Flags.V_le_Q geometry common.large_distance _ rfl)
  have hZstar := Flags.Z_le_star geometry radius.toEarlyFacts common.large_distance
    (alpha R) (beta R) rfl (base_adjacent R)
  have hZcstar : Z R s.middle ≤ VStar R geometry (alpha R) (beta R) :=
    (Z_le_orbitSpan s.middle).trans
      (orbitSpan_le_star geometry radius.toEarlyFacts _ _ (base_adjacent R)
        (midpoint_nu common radius hb s))
  have hZc : ¬ Z R s.middle ≤ Z R (alpha R) :=
    large_intersection_not_le_Z radius s hs
  obtain ⟨x, hx, hxZ⟩ := SetLike.not_le_iff_exists.mp hZc
  let xS : VStar R geometry (alpha R) (beta R) := ⟨x,hZcstar hx⟩
  have hv : (d.projection xS).toAdd ≠ 0 := by
    intro hz
    have hk : xS ∈ d.projection.ker := hz
    rw [d.kernel] at hk
    exact hxZ hk
  let : IsElementaryAbelian 2 (Z R s.middle) :=
    geometry.Z_elementary (by omega) _ s.middle_color
  let : IsElementaryAbelian 2 (Z R (alpha R)) :=
    geometry.Z_elementary (by omega) _ rfl
  have hx2 : x ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian x hx
  have hcentral : Z R (alpha R) ≤ centralizer
      (VStar R geometry (alpha R) (beta R) : Set (FreeAmalgam R)) := by
    rw [← common.X_eq_Z (alpha R) rfl]
    exact le_centralizer_iff.mp (hQ.trans (Q_le_centralizer_X R _))
  have hsquare (y : VStar R geometry (alpha R) (beta R)) : y ^ 2 = 1 := by
    by_cases hy : (d.projection y).toAdd = 0
    · apply Subtype.ext
      have hk : y ∈ d.projection.ker := hy
      rw [d.kernel] at hk
      exact elemPow_eq_one_of_isElementaryAbelian (A := Z R (alpha R)) (y : FreeAmalgam R) hk
    obtain ⟨g, hg⟩ := natural_transitive hn (d.projection xS).toAdd
      (d.projection y).toAdd hv hy
    obtain ⟨m, hm⟩ := source.projection_surjective g
    have hmM : embedM R m ∈ stabilizer R (alpha R) := by
      rw [alpha, stabilizer_m_base]
      exact ⟨m,rfl⟩
    let z : VStar R geometry (alpha R) (beta R) :=
      ⟨embedM R m * x * (embedM R m)⁻¹,
        (mem_normalizer_iff.mp (Flags.star_normalized geometry _ _ hmM) x).mp xS.property⟩
    have hzproj : d.projection z = d.projection y := by
      have hh := d.action m xS z rfl
      rw [hm, hg] at hh
      exact hh
    have hk : (z⁻¹ * y : VStar R geometry (alpha R) (beta R)) ∈ d.projection.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hzproj, inv_mul_cancel]
    rw [d.kernel] at hk
    have hk2 : ((z⁻¹ * y : VStar R geometry (alpha R) (beta R)) : FreeAmalgam R) ^ 2 = 1 :=
      elemPow_eq_one_of_isElementaryAbelian (A := Z R (alpha R)) _ hk
    have hz2 : z ^ 2 = 1 := by
      apply Subtype.ext
      change (embedM R m * x * (embedM R m)⁻¹) ^ 2 = 1
      change (MulAut.conj (embedM R m) x) ^ 2 = 1
      rw [← map_pow, hx2, map_one]
    have hc : Commute z (z⁻¹ * y) := by
      apply Subtype.ext
      exact hcentral hk z z.property
    have hk2' : (z⁻¹ * y) ^ 2 = 1 := Subtype.ext hk2
    have hh := hc.mul_pow 2
    simpa only [mul_inv_cancel_left, hz2, hk2', one_mul] using hh
  have hcomm : IsMulCommutative (VStar R geometry (alpha R) (beta R)) := by
    refine ⟨⟨fun x y => ?_⟩⟩
    have hinv (x : VStar R geometry (alpha R) (beta R)) : x⁻¹ = x := by
      exact inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hsquare x)
    rw [← hinv (x * y), mul_inv_rev, hinv x, hinv y]
  have hstarC : VStar R geometry (alpha R) (beta R) ≤ centralizer
      (VStar R geometry (alpha R) (beta R) : Set (FreeAmalgam R)) :=
    le_centralizer_iff_isMulCommutative.mpr hcomm
  have hBC : B R (alpha R) (geometry.Z_normal _) ≤
      centralizer (V R (alpha R) : Set (FreeAmalgam R)) := by
    rw [radius.B_eq_center (alpha R) rfl]
    rintro x ⟨z,hz,rfl⟩ y hy
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨y,hy⟩)
  have hVS : V R (alpha R) ≤ centralizer
      (VStar R geometry (alpha R) (beta R) : Set (FreeAmalgam R)) := by
    rw [Flags.radius_eq_B_sup_star geometry radius.toEarlyFacts common.large_distance
      (alpha R) (beta R) rfl (base_adjacent R)]
    exact sup_le (hBC.trans (centralizer_le hstar)) hstarC
  have hVC : V R (alpha R) ≤ centralizer
      (V R (alpha R) : Set (FreeAmalgam R)) := by
    conv_lhs => rw [Flags.radius_eq_B_sup_star geometry radius.toEarlyFacts common.large_distance
      (alpha R) (beta R) rfl (base_adjacent R)]
    exact sup_le hBC (le_centralizer_iff.mp hVS)
  apply radius.derived_noncentral (alpha R) rfl
  rw [commutator_eq_bot_iff_le_centralizer.mpr hVC]
  exact bot_le
/-- The actual starred action cannot consist of a single natural factor,
in either orientation, before any starred index or canonical seed is known. -/
theorem star_not_naturalOrDual (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hs : ¬ s.SmallIntersection)
    (d : LayerModule source (V R (alpha R))) :
    ¬ NaturalOrDual (starRepresentation (geometry := geometry) d).toRepresentation :=
  natural_star_impossible common radius hb s hs (starLayer d)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
