module
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineCore.Parabolic.Blocks.Torus
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.Flag.Center.LineRadical
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourRadicalCentralizers
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourFormTransport

/-!
# The long-root center and its cubic orbit in PSU₅(4)

The centralizer bound for the full unipotent radical puts the center of the
line residual in that radical. Faithful radical coordinates identify it with
the scalar subgroup, of order four. For two nonzero fixed scalars their ratio
is a cube root of unity. The existing literal cubic torus scales by that ratio,
proving transitivity under actual projective line-parabolic conjugation.

Source: Aschbacher--Smith F.4.27(4), F.4.34 and 5.3.3(b), printed pp.288,
291 and659. The ChapterF/6 companions transport this calculation through
the original parabolic marking and prove the ambient long-root bound.
-/

public noncomputable section
open BenderSuzuki.MatrixGroups Matrix Subgroup
namespace Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic
open Blocks
variable {F : Type*} [Field F] [CharP F 2] [Finite F]
  (J : HermitianForm 5 F) (hJ : J.form = 1)
  (hconj : ∀ a, J.conj a = a ^ 4) (hcard : Nat.card F = 16)
  (c : F) (hc : c + J.conj c = 1)

include hconj hcard c hc in
theorem center_image_eq :
    (center (radicalLeviSubgroup J hJ)).map (radicalLeviSubgroup J hJ).subtype =
      (center (Coord J)).map (toParabolic J hJ) := by
  apply le_antisymm
  · rintro x ⟨x,hx,rfl⟩
    have hcomm : x.val ∈ centralizer (projectiveUnipotent J hJ : Set (lineParabolic J)) := by
      intro u hu
      exact congrArg Subtype.val (mem_center_iff.mp hx
        ⟨u,projectiveUnipotent_le_radicalLeviSubgroup J hJ hu⟩)
    obtain ⟨u,hu⟩ := RadicalCentralizers.line_centralizer_le J hJ hconj hcard hcomm
    refine ⟨u,?_,hu⟩
    apply mem_center_iff.mpr
    intro v
    apply toParabolic_injective J hJ
    rw [map_mul,map_mul,hu]
    exact mem_centralizer_iff.mp hcomm _ ⟨v,rfl⟩
  · rintro _ ⟨u,hu,rfl⟩
    have huR : toParabolic J hJ u ∈ radicalLeviSubgroup J hJ :=
      projectiveUnipotent_le_radicalLeviSubgroup J hJ ⟨u,rfl⟩
    refine ⟨⟨toParabolic J hJ u,huR⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro g
    apply Subtype.ext
    apply Flag.Center.commute_of_centralizes_projectiveUnipotent J c hc hJ huR g.property
    rintro _ ⟨v,rfl⟩
    simpa only [map_mul] using congrArg (toParabolic J hJ) (mem_center_iff.mp hu v)

omit [Finite F] in
include c hc in
private theorem scalar_fixed {u : Coord J} (hu : u ∈ center (Coord J)) :
    J.conj u.scalar = u.scalar := by
  have hh := u.trace_eq
  rw [(Coord.mem_center_iff_vector_eq_zero c hc u).mp hu,pairing_zero_left] at hh
  exact add_left_cancel (hh.trans (CharTwo.add_self_eq_zero u.scalar).symm)

omit [Finite F] in
include c hc in
private theorem scalar_ne_zero {u : Coord J} (hu : u ∈ center (Coord J)) (hne : u ≠ 1) :
    u.scalar ≠ 0 := by
  intro he
  apply hne
  exact Coord.ext ((Coord.mem_center_iff_vector_eq_zero c hc u).mp hu) he

omit [Finite F] in
include c hc in
theorem center_cubic_transitive (u v : Coord J)
    (hu : u ∈ center (Coord J)) (hv : v ∈ center (Coord J))
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    ∃ b : Cubic (F := F), cubicAction J hconj b u = v := by
  have hus := scalar_ne_zero J c hc hu hu1
  have hvs := scalar_ne_zero J c hc hv hv1
  let a : F := v.scalar / u.scalar
  have ha : a ≠ 0 := div_ne_zero hvs hus
  have hfix : J.conj a = a := by
    dsimp only [a]
    rw [_root_.map_div₀,scalar_fixed J c hc hv,scalar_fixed J c hc hu]
  have ha3 : a ^ 3 = 1 := by
    apply mul_right_cancel₀ ha
    rw [←pow_succ,one_mul,←hconj,hfix]
  let b : Cubic (F := F) := ⟨Units.mk0 a ha, (mem_rootsOfUnity' 3 _).mpr ha3⟩
  refine ⟨b,?_⟩
  apply Coord.ext
  · ext i
    simp only [cubicAction_apply,cubicScale_vector,
      (Coord.mem_center_iff_vector_eq_zero c hc u).mp hu,
      (Coord.mem_center_iff_vector_eq_zero c hc v).mp hv,Pi.zero_apply,mul_zero]
  · change (v.scalar / u.scalar) * u.scalar = v.scalar
    exact div_mul_cancel₀ _ hus

include hconj hcard c hc in
theorem center_orbit :
    ∀ x ∈ (center (radicalLeviSubgroup J hJ)).map (radicalLeviSubgroup J hJ).subtype,
      x ≠ 1 →
      ∀ y ∈ (center (radicalLeviSubgroup J hJ)).map (radicalLeviSubgroup J hJ).subtype,
        y ≠ 1 → ∃ g : lineParabolic J, y = g*x*g⁻¹ := by
  rw [center_image_eq J hJ hconj hcard c hc]
  rintro _ ⟨u,hu,rfl⟩ hu1 _ ⟨v,hv,rfl⟩ hv1
  have hune : u ≠ 1 := fun he => hu1 (by rw [he,map_one])
  have hvne : v ≠ 1 := fun he => hv1 (by rw [he,map_one])
  obtain ⟨b,hb⟩ := center_cubic_transitive J hconj c hc u v hu hv hune hvne
  refine ⟨cubicParabolic J hconj c hc hJ b,?_⟩
  rw [←toParabolic_cubicAction J hconj c hc hJ b u,hb]

include hconj hcard c hc in
theorem center_card : Nat.card (center (radicalLeviSubgroup J hJ)) = 4 := by
  rw [←Subgroup.card_map_of_injective (K := center (radicalLeviSubgroup J hJ))
    (f := (radicalLeviSubgroup J hJ).subtype) Subtype.val_injective,
    center_image_eq J hJ hconj hcard c hc,
    Subgroup.card_map_of_injective (toParabolic_injective J hJ),
    Coord.card_center c hc]
  exact Theory.SpecificGroups.UnitaryFive.fixed_card_four J hcard hconj

end Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic
