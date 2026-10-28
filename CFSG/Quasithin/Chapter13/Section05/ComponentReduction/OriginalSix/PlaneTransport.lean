module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SeedTransitivity
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction.Representation
public import Theory.GroupAction.MaximalCosetOrbit

/-!
# Original A₆ point-residual plane transport

The natural point residual acts transitively on the three nonzero vectors
of the literal section V₃/V₁. A vector of a subgroup strictly above V₁
can therefore be carried onto a nonzero vector of V₂/V₁. Lifting that
equality through U_H/V₁, and adjoining the fixed point, proves the actual
plane containment required by the F.9.5 application in13.5.20.

The source point residual is identified with the F.9 residual before the
action is used. No normality of L₁ in H or plane-fusion conclusion is an
input. Source: Aschbacher–Smith13.5.13(1), printed p.919.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
open Section08.SourceCompletion Section08.TransvectionRecognition
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionParabolic.Marking
open Fitting.SourceAction
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz) (h : D.Hypothesis)
include d h

theorem residual_eq_sourceOne : D.L₁ = sourceOne D.L D.T D.V₁ := by
  have hh := Section08.TransvectionQuotients.FiveSeed.BarMarking.normalizer_residual_eq D.L D.V₁ (D.T : Subgroup G)
    D.T.isPGroup' d.normalizes_L
  change sourceOne D.L D.T D.V₁ =
    (pResidual 2 (D.L ⊓ normalizer (D.V₁ : Set G) : Subgroup G)).map
      (D.L ⊓ normalizer (D.V₁ : Set G)).subtype at hh
  rw [h.normalizer_point_eq] at hh
  exact hh.symm

theorem plane_transport (W : Subgroup G) (hW : D.V₁ < W) (hWU : W ≤ D.Vplus) :
    ∃ l ∈ D.L₁, V₂ ≤ W.map (MulAut.conj l).toMonoidHom := by
  classical
  let : (D.V₁.subgroupOf D.UH).Normal := point_normal_in_UH h
  let : IsElementaryAbelian 2 (Quotient (D := D)) := quotient_elementary h
  let : (D.V₁.subgroupOf (Section08.Source.UH D.H D.Vplus)).Normal := point_normal_in_UH h
  let : IsElementaryAbelian 2 (Section08.Source.Utilde D.H D.Vplus D.V₁) := quotient_elementary h
  let ρ : Representation (ZMod 2) (Section08.Source.Hstar D.H)
      (Additive (Section08.Source.Utilde D.H D.Vplus D.V₁)) := representation h
  have hρ : IsConjugation D.H D.Vplus D.V₁ ρ := representation_apply h
  have hLH : sourceOne D.L D.T D.V₁ ≤ D.H :=
    (residual_eq_sourceOne d h).symm ▸ (le_sup_left.trans h.local_le)
  obtain ⟨w,hw,hwP⟩ := SetLike.exists_of_lt hW
  have hPE : D.V₁ < V₂ := lt_of_le_of_ne d.line_le_plane (by
    intro he
    have hh := congrArg (fun A : Subgroup G => Nat.card A) he
    rw [d.line_card,d.plane_card] at hh
    omega)
  obtain ⟨v,hv,hvP⟩ := SetLike.exists_of_lt hPE
  let u : Section08.Source.UH D.H D.Vplus := ⟨w,le_conjugateSpanBy D.Vplus D.H (hWU hw)⟩
  let t : Section08.Source.UH D.H D.Vplus := ⟨v,le_conjugateSpanBy D.Vplus D.H (d.plane_le_seed hv)⟩
  have hu : vector D.H D.Vplus D.V₁ u ∈ sectionImage D.H D.Vplus D.V₁ D.Vplus :=
    ⟨u,hWU hw,rfl⟩
  have ht : vector D.H D.Vplus D.V₁ t ∈ sectionImage D.H D.Vplus D.V₁ D.Vplus :=
    ⟨t,d.plane_le_seed hv,rfl⟩
  have hu0 : vector D.H D.Vplus D.V₁ u ≠ 0 := by
    intro he
    exact hwP ((QuotientGroup.eq_one_iff (N := D.V₁.subgroupOf (Section08.Source.UH D.H D.Vplus)) u).mp he)
  have ht0 : vector D.H D.Vplus D.V₁ t ≠ 0 := by
    intro he
    exact hvP ((QuotientGroup.eq_one_iff (N := D.V₁.subgroupOf (Section08.Source.UH D.H D.Vplus)) t).mp he)
  obtain ⟨l,hl⟩ := Section07.ModelExclusions.seed_section_nonzero_orbit d hLH ρ hρ
    _ hu hu0 _ ht ht0
  have hlL : (l : G) ∈ D.L₁ := (residual_eq_sourceOne d h).symm ▸ l.property
  let W' := W.map (MulAut.conj (l : G)).toMonoidHom
  have hPW' : D.V₁ ≤ W' := by
    have he := mem_normalizer_iff_map_conj_eq.mp
      ((h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) (hLH l.property))
    exact he ▸ map_mono (f := (MulAut.conj (l : G)).toMonoidHom) hW.le
  have hvW' : v ∈ W' := by
    have hl' := hρ (inclusion hLH l) u
    rw [hl'] at hl
    have hq := QuotientGroup.eq_iff_div_mem.mp (congrArg Additive.toMul hl)
    have hdiff : (l : G) * w * (l : G)⁻¹ / v ∈ D.V₁ := hq
    have hw' : (l : G) * w * (l : G)⁻¹ ∈ W' := mem_map_of_mem _ hw
    have hmul := W'.mul_mem (W'.inv_mem (hPW' hdiff)) hw'
    simpa only [inv_div,div_mul_cancel] using hmul
  have hi : D.V₁.relIndex V₂ = 2 := by
    have hh := (D.V₁.subgroupOf V₂).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe d.line_le_plane).toEquiv,
      d.line_card,d.plane_card] at hh
    change 2 * D.V₁.relIndex V₂ = 4 at hh
    omega
  refine ⟨l,hlL,?_⟩
  rw [←sup_zpowers_eq_of_relIndex_prime d.line_le_plane Nat.prime_two hi hv hvP]
  exact sup_le hPW' (zpowers_le.mpr hvW')
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
