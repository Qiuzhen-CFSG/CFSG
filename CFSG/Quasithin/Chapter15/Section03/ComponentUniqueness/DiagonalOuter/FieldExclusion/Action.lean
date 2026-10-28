module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.JointCentralizer
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The conjugate plane acts faithfully on the field component

Fusion and the index-two plane-centralizer geometry construct the actual E₉
joint residual. If the plane centralized a quasisimple component of `C_G(f)`,
that perfect component would lie in the joint two-residual and hence in E₉,
which is impossible. The TI property then gives a faithful conjugation action.
Normality is relative to `C_G(f)`, never ambient normality in `G`.

This repairs the action step of Aschbacher--Smith 15.3.38, printed p.1137
(1 March 2004 manuscript), using the corrected E₉ residual rather than the
incompatible printed extraspecial order-27 group. Component existence and the
model-specific centralizer calculation are separate proof obligations.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion
variable {G : Type*} [Group G] [Finite G]

private theorem perfect_isPPerfect {H : Type*} [Group H] [Finite H]
    [Group.IsPerfect H] : IsPPerfect 2 H := by
  intro N hN hp
  let := hN
  have hsub : Subsingleton (H ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (H ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

/-- A quasisimple component cannot be contained in an E₉ joint residual. -/
theorem nontrivial_action_of_jointResidual_model (U K : Subgroup G) (f : G)
    [IsQuasisimple K] (hK : K ≤ centralizer ({f} : Set G))
    (e : jointResidual U f ≃* ElementaryNine) :
    ¬ U ≤ centralizer (K : Set G) := by
  intro hUK
  let J := jointCentralizer U f
  have hKJ : K ≤ J := le_inf (le_centralizer_iff.mp hUK) hK
  have hp : IsPPerfect 2 (K.subgroupOf J) :=
    perfect_isPPerfect.of_surjective (subgroupOfEquivOfLe hKJ).symm.toMonoidHom
      (subgroupOfEquivOfLe hKJ).symm.surjective
  have hKR : K ≤ jointResidual U f := by
    simpa only [map_subgroupOf_eq_of_le hKJ, jointResidual, J] using
      (map_mono (f := J.subtype) (le_pResidual_of_isPPerfect (K.subgroupOf J) hp))
  let φ := e.toMonoidHom.comp (inclusion hKR)
  let : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective
    (f := φ) (e.injective.comp (inclusion_injective hKR))
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  exact Group.IsPerfect.not_isSolvable K inferInstance

/-- The actual conjugation homomorphism is injective by the TI action lemma. -/
theorem faithful_action_of_jointResidual_model (U K : Subgroup G) (f : G)
    [IsKleinFour U] [IsQuasisimple K]
    (hU : CFSG.Quasithin.ChapterI.Section06To08.IsTISubgroup U)
    (hK : K ≤ centralizer ({f} : Set G)) (hUN : U ≤ normalizer (K : Set G))
    (e : jointResidual U f ≃* ElementaryNine) :
    Function.Injective (K.normalizerMonoidHom.comp (inclusion hUN)) := by
  exact conjugation_injective_of_twoPerfect_nontrivial U K hU perfect_isPPerfect hUN
    (nontrivial_action_of_jointResidual_model U K f hK e)

/-- Fusion constructs a TI four-group, its joint odd core and a faithful action. -/
theorem faithful_conjugate_plane (V L K : Subgroup G) [IsKleinFour V]
    [IsQuasisimple K]
    (hV : CFSG.Quasithin.ChapterI.Section06To08.IsTISubgroup V)
    (hLC : L ≤ centralizer (V : Set G))
    (hindex : L.relIndex (centralizer (V : Set G)) = 2)
    {w f : G} (hw : w ∈ centralizer (V : Set G)) (hfusion : IsConj w f)
    (eF : pResidual 2 (L ⊓ centralizer ({w} : Set G) : Subgroup G) ≃* ElementaryNine)
    (hK : K ≤ centralizer ({f} : Set G))
    (hn : (K.subgroupOf (centralizer ({f} : Set G))).Normal) :
    ∃ g : G, (MulAut.conj g) w = f ∧
      let U := V.map (MulAut.conj g).toMonoidHom
      IsKleinFour U ∧
      CFSG.Quasithin.ChapterI.Section06To08.IsTISubgroup U ∧
      ∃ _e : jointResidual U f ≃* ElementaryNine,
        jointResidual U f = (pPrimeCore 2 (jointCentralizer U f)).map
          (jointCentralizer U f).subtype ∧
        U ≤ centralizer ({f} : Set G) ∧
        ¬ U ≤ centralizer (K : Set G) ∧
        ∃ hUN : U ≤ normalizer (K : Set G),
          Function.Injective (K.normalizerMonoidHom.comp (inclusion hUN)) := by
  obtain ⟨g, hg, ⟨e⟩⟩ := jointResidual_model_of_fusion V L hLC hindex hfusion eF
  let U := V.map (MulAut.conj g).toMonoidHom
  have hUC : U ≤ centralizer ({f} : Set G) := by
    rintro _ ⟨v, hv, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg (MulAut.conj g) (hw v hv)
    simpa only [map_mul, hg, MulEquiv.coe_toMonoidHom] using he
  have hUN : U ≤ normalizer (K : Set G) :=
    hUC.trans ((normal_subgroupOf_iff_le_normalizer hK).mp hn)
  let eU : V ≃* U := V.equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective
  let : IsKleinFour U := {
    card_four := (Nat.card_congr eU.toEquiv).symm.trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eU).symm.trans
      IsKleinFour.exponent_two }
  exact ⟨g, hg, inferInstance, ti_map V hV (MulAut.conj g), e,
    jointResidual_eq_oddCore_of_model U f e, hUC,
    nontrivial_action_of_jointResidual_model U K f hK e, hUN,
    faithful_action_of_jointResidual_model U K f (ti_map V hV (MulAut.conj g)) hK hUN e⟩
/-- For each nonidentity element of the TI plane, the whole plane fixes the
actual two-residual of its centralizer in K. This constraint remains available
to the model calculation in addition to faithfulness of the full action. -/
theorem plane_centralizes_involution_residual (U K : Subgroup G) [IsKleinFour U]
    (hU : CFSG.Quasithin.ChapterI.Section06To08.IsTISubgroup U)
    {u : G} (hu : u ∈ U) (hu1 : u ≠ 1) :
    U ≤ centralizer
      ((pResidual 2 (K ⊓ centralizer ({u} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({u} : Set G)).subtype : Set G) := by
  let C := K ⊓ centralizer ({u} : Set G)
  let R := (pResidual 2 C).map C.subtype
  have hp : IsPPerfect 2 R := (isPPerfect_pResidual 2).of_surjective
    (C.subtype.subgroupMap (pResidual 2 C)) (C.subtype.subgroupMap_surjective _)
  apply centralizes_of_twoPerfect_fixed U R hU hp hu hu1
  intro r hr
  have hrC : r ∈ centralizer ({u} : Set G) :=
    ((map_subtype_le (pResidual 2 C)).trans inf_le_right) hr
  exact mem_centralizer_singleton_iff.mp hrC


end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion
