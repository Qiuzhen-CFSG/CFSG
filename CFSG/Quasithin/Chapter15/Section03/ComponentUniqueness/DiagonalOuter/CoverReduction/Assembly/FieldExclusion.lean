module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.FieldBalance
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Terminal
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.RankOne
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.Setup

/-!
# Consuming the diagonal-outer reduction at the field-centralizer terminal

The literal graph-field residual supplies the transfer subgroup. Fusion
transports the extraspecial Sylow subgroup into C_G(f); the complete rank-one
exclusion and ordinary balance then select its normal rank-two component.
The component-center rank bound and the three model actions give False.

The local residual, fusion and index rows remain explicit for their source
producers, as does the selected-component three-model sieve. The full genuine
KnownSimple A/C inputs are used. This theorem does not assert unconditional
15.3.38 and does not require a cover classification.

Source: Aschbacher–Smith, proof of 15.3.38, printed pp.1136–1137.
-/

public section

open Subgroup Theory.GroupTheory MulAut
open CFSG.Quasithin.ChapterA.Section02
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open FieldExclusion
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal mixed fixed residual embedded in the ambient group. -/
@[expose] def Reduction.graphFieldResidual {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    (r : Reduction d I L) : Subgroup G :=
  (pResidual 2 (L ⊓ centralizer
    ({(r.sylow.lift.dihedral.firstReflection : G) *
      (r.sylow.lift.dihedral.halfTurn : G)} : Set G) : Subgroup G)).map
    (L ⊓ centralizer ({(r.sylow.lift.dihedral.firstReflection : G) *
      (r.sylow.lift.dihedral.halfTurn : G)} : Set G)).subtype

/-- Consume the actual reduction, local residual and fusion rows, and the selected
component sieve. Rank-one exclusion, field balance, all three terminal actions,
and the final center-rank contradiction are discharged here. -/
theorem Reduction.field_exclusion {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    (r : Reduction d I L)
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      TheoremA CFSG.KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      TheoremC CFSG.KnownSimple.IsKnownSimple X)
    (hperfect : IsPPerfect 2 G) (z : G)
    (hsmall : ¬ 4 ∣ Nat.card (((centralizer (r.graphFieldResidual : Set G)).subgroupOf
      (normalizer (L : Set G))).map L.normalizerMonoidHom))
    (hz : generalizedFitting (centralizer ({z} : Set G)) =
      pCore 2 (centralizer ({z} : Set G)))
    (hinside : ∀ x : G, x ∈ L → orderOf x = 2 →
      IsConj x r.representative.v ∨ IsConj x z)
    (hcoset : ∀ x : G, orderOf x = 2 → x * (r.sylow.lift.dihedral.halfTurn : G)⁻¹ ∈ L →
      IsConj x (r.sylow.lift.dihedral.halfTurn : G))
    (hindex : L.relIndex (centralizer (r.coverData.cover.borel.W₁ : Set G)) = 2)
    (eW : pResidual 2 (L ⊓ centralizer
      ({(r.sylow.lift.dihedral.firstReflection : G) *
        (r.sylow.lift.dihedral.halfTurn : G)} : Set G) : Subgroup G) ≃* ElementaryNine)
    (eO : pPrimeCore 2 (I ⊓ centralizer
      ({(r.sylow.lift.dihedral.firstReflection : G) *
        (r.sylow.lift.dihedral.halfTurn : G)} : Set G) : Subgroup G) ≃* ElementaryNine)
    (eF : pResidual 2 (L ⊓ centralizer
      ({(r.sylow.lift.dihedral.halfTurn : G)} : Set G) : Subgroup G) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
    (hH : IsSQTK CFSG.KnownSimple.IsKnownSimple
      (centralizer ({(r.sylow.lift.dihedral.halfTurn : G)} : Set G)))
    (P : Sylow 3 (I ⊓ centralizer
      ({(r.sylow.lift.dihedral.firstReflection : G) *
        (r.sylow.lift.dihedral.halfTurn : G)} : Set G) : Subgroup G))
    [IsExtraspecial 3 P] (hc : Nat.card P = 27) (he : ∀ x : P, x ^ 3 = 1)
    (hsieve : ∀ K : Subgroup G,
      Identification.Input (centralizer ({(r.sylow.lift.dihedral.halfTurn : G)} : Set G))
        K r.representative.v → FieldComponentQuotient K) : False := by
  let V := r.coverData.cover.borel.W₁
  let f : G := r.sylow.lift.dihedral.halfTurn
  let w : G := (r.sylow.lift.dihedral.firstReflection : G) * f
  obtain ⟨i, hi⟩ := r.coverData.plane
  have hV : V = d.action.plane i := hi
  let : IsElementaryAbelian 2 V := d.action.elementary_of_le (hV ▸ d.action.plane_le i)
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hV, d.action.card_plane]; decide)
  let : IsKleinFour V := ⟨hV ▸ d.action.card_plane i, IsElementaryAbelian.exponent_eq_prime⟩
  let F := r.graphFieldResidual
  have hF : IsPPerfect 2 F :=
    (isPPerfect_pResidual 2).of_surjective
      ((L ⊓ centralizer ({w} : Set G)).subtype.subgroupMap _)
      ((L ⊓ centralizer ({w} : Set G)).subtype.subgroupMap_surjective _)
  have hfixedF : w ∈ centralizer (F : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_centralizer_singleton_iff.mp x.property.2
  obtain ⟨hTI, _, hfusion⟩ := r.field_fusion hperfect F z hF hsmall hfixedF hz hinside hcoset
  obtain ⟨B, hB, hBc, hBe⟩ := extraspecial_subgroup_in_fieldCentralizer I hfusion P hc he
  let := hB
  have hv : r.representative.v ∈ V :=
    (r.representative.generator ▸ mem_zpowers r.representative.v).2
  have hvf : r.representative.v ∈ centralizer ({f} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp
      (r.representative.sylow_centralizes r.sylow.lift.halfTurn_mem)).symm
  have hbalance := fieldResidual_balance_of_marked_center I L V f r.representative.v
    r.normalizes r.representative.centralizer_le r.coverData.cover.center_plane hv hvf
    r.representative.order eF
  have hno := fun J hJ => FieldExclusion.RankOne.component_rank_ne_one
    (hA _) hC hH B hBc hBe J hJ
  obtain ⟨hvH, K, hKH, hK, hKn, hKr, hFK, hAC, hAN, hAcomp, ⟨eA⟩⟩ :=
    selected_component_with_representative_of_fusion_and_rank_exclusion V d.ZS d.S I L
      r.representative hTI r.normalizer_eq r.normalizes r.coverData.cover.center_plane
      r.sylow.lift.halfTurn_mem r.sylow.fixes hfusion eO eF hbalance hH hno
  let s : Identification.Input (centralizer ({f} : Set G)) K r.representative.v := {
    le := hKH
    sqtk := hH
    component := hK
    normal := hKn
    rank := hKr
    involution_mem := hvH
    involution_order := r.representative.order
    centralizerComponent := ((fieldResidual L f).map (centralizer ({f} : Set G)).subtype).subgroupOf
      (K ⊓ centralizer ({r.representative.v} : Set G))
    centralizerComponent_isComponent := hAcomp
    centralizerComponent_equiv := eA }
  let : IsQuasisimple K := s.quasisimple
  have hmodel := hsieve K s
  have hrank := hH.stronglyQuasithin 3 (by decide) (by decide)
  obtain ⟨ι, hι⟩ := centralizer_oddCore_embeds_of_fusion V I hTI r.normalizer_eq
    r.sylow.fixes hfusion eO
  let : IsSimpleGroup (fieldResidual L f) := (MulEquiv.isSimpleGroup_congr
    (fieldResidualEquivModel L f eF)).mpr (Atlas.psl_simple_high_rank 3 (by decide))
  let := fieldResidual_perfect L f eF
  have hOr := oddCore_rank_le_one_of_simple_subgroup (fieldResidual L f)
    (fieldResidual_card L f eF) hrank ι hι
  have hZ := component_center_rank_le_one_of_oddCore hOr hK
  have hLC : L ≤ centralizer (V : Set G) := by
    intro x hx v hv
    have hv' : v ∈ (center L).map L.subtype := by
      have he : (center L).map L.subtype = V := r.coverData.cover.center_plane
      exact he.symm ▸ hv
    obtain ⟨c, hc, rfl⟩ := hv'
    exact (congrArg Subtype.val (mem_center_iff.mp hc ⟨x, hx⟩)).symm
  obtain ⟨g, _, hfour, hU, eR, _, hUf, _, hUN, hinj⟩ :=
    faithful_conjugate_plane V L K hTI hLC hindex r.sylow.fixes hfusion eW hKH hKn
  let U := V.map (MulAut.conj g).toMonoidHom
  let : IsKleinFour U := hfour
  exact contradiction_of_component_quotient U K f hU hKH hKn hUf eR hmodel hrank hKr.ge hZ

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
