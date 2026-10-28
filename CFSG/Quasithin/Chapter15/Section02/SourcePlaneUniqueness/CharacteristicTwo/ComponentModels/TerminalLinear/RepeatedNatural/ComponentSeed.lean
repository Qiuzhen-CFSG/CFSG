module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.RepeatedNatural.MinimalParabolic
public import Theory.GroupTheory.PCoreSylowCoverIntersection

/-!
# The minimal parabolic inside the original component

The marked quotient of XS restricts surjectively to X. Since its kernel
is a two-group, intersecting the constructed Sylow cover with X preserves
the cover. The quotient XS/X is a two-group, so this intersection also
preserves the embedded two-residual. Thus the source parabolic lies in
X itself, is normalized by S, and supplies the same corrected seed.

Source: Aschbacher--Smith, 15.2.23(a), printed p.1117. This is consumed
by RepeatedNatural.Source on the literal binary branch.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open Section01 BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The minimal parabolic lies in the original X. Intersecting the XS
construction with X preserves the Sylow cover and its embedded two-residual. -/
theorem component_minimalParabolic_seed_of_point_image
    (hI : PlaneEscapes Mc ZS I) (hXI : X ≤ I)
    (hn : I ≤ normalizer (X : Set G))
    (hX : X = (primeToResidual 3 I).map I.subtype)
    (hescape : ¬ (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype ≤ Mc ⊓ I)
    (e : (X ⧸ pCore 2 X) ≃* SL(5,ZMod 2))
    (v : Fin 5 → ZMod 2) (hv : v ≠ 0)
    (hm : (((M1 X ZS).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
      e.toMonoidHom = MulAction.stabilizer SL(5,ZMod 2) v) :
    ∃ P : Subgroup G, smallActionS T ZS ⊓ X ⋖ P ∧ P ≤ X ∧ P ≤ M ⊓ I ∧
      smallActionS T ZS ≤ normalizer (P : Set G) ∧
      SmallActionsSource.Seed M I (smallActionS T ZS) ((pResidual 2 P).map P.subtype) ∧
      ¬ (pResidual 2 P).map P.subtype ≤ Mc ⊓ I := by
  obtain ⟨P0,hcov0,hP0NI,hP0J,hseed,hout⟩ :=
    minimalParabolic_seed_of_point_image d hI hXI hn hX hescape e v hv hm
  let S := smallActionS T ZS
  let J := X ⊔ S
  let NX := X.subgroupOf J
  let P := P0.subgroupOf J
  have hXJ : X ≤ J := le_sup_left
  have hSJ : S ≤ J := le_sup_right
  have hSI : S ≤ I := (le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
  have hSX : S ≤ normalizer (X : Set G) := hSI.trans hn
  let : NX.Normal := normal_subgroupOf_of_le_normalizer (sup_le X.le_normalizer hSX)
  obtain ⟨SP,hSP⟩ := (show Chapter1.IsSylowIn 2 S I from d.sylow_in_escape hI).restrict
    hSJ (sup_le hXI hSI)
  have hSP' : (SP : Subgroup J) = S.subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [hSP,map_subgroupOf_eq_of_le hSJ]
  have hcov : (SP : Subgroup J) ⋖ P := by
    apply (covBy_map_subtype_iff J _ _).mp
    rw [hSP,map_subgroupOf_eq_of_le hP0J]
    exact hcov0
  obtain ⟨f,hf,hk,he⟩ := point_image_extension d hI hn e v hv hm
  have hNX : Function.Surjective (f.comp NX.subtype) := by
    intro z
    obtain ⟨x,hx⟩ := ((e.trans (slEquivLinear 5)).surjective.comp
      (QuotientGroup.mk'_surjective (pCore 2 X))) z
    refine ⟨⟨⟨x,hXJ x.property⟩,x.property⟩,?_⟩
    change f (inclusion hXJ x) = z
    exact (he x).trans hx
  have hcovQ := sylow_cover_inf_of_surjective_restriction f hk NX hNX SP P hcov
  have hcovG := (covBy_map_subtype_iff J _ _).mpr hcovQ
  rw [map_inf _ _ _ J.subtype_injective,map_inf _ _ _ J.subtype_injective,
    hSP,map_subgroupOf_eq_of_le hXJ,map_subgroupOf_eq_of_le hP0J] at hcovG
  have hgen : NX ⊔ S.subgroupOf J = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hXJ,map_subgroupOf_eq_of_le hSJ,
      ←MonoidHom.range_eq_map,range_subtype]
  have hresle : pResidual 2 J ≤ NX := sInf_le ⟨inferInstance,
    isPGroup_quotient_of_sup_eq_top NX (S.subgroupOf J)
      (T.isPGroup'.to_le (show S ≤ (T : Subgroup G) from inf_le_left)).comap_subtype hgen⟩
  have hres := congrArg (Subgroup.map J.subtype)
    (embedded_twoResidual_inf_eq_of_residual_le NX P hresle)
  rw [map_embedded_pResidual,map_embedded_pResidual,
    map_inf _ _ _ J.subtype_injective,map_subgroupOf_eq_of_le hP0J,
    map_subgroupOf_eq_of_le hXJ] at hres
  refine ⟨P0 ⊓ X,hcovG,inf_le_right,inf_le_left.trans hP0NI,?_,?_,?_⟩
  · exact (le_inf (hcov0.le.trans P0.le_normalizer) hSX).trans inf_normalizer_le_normalizer_inf
  · rwa [hres]
  · rwa [hres]

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear
