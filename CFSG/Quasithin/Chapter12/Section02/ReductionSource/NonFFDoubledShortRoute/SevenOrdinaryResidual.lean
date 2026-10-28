module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SevenOrdinaryCatalogue
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SevenOrdinaryLie
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# The same A7 reciprocal component has central quotient J4

The original quotient of the intersection residual maps onto A7 after
retaining its covering center. Its solvable kernel and the full moved orbit
exclude every characteristic-two rank-two model of the actual component.
The only remaining ordinary central quotient is J4.
Source: Aschbacher--Smith C.3.2--5 and 4.4.6, printed pp.149--150,620.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter4.Section04.NormalizedRankOneOddControl
open Chapter4.Section02.RankOneReciprocalEscape
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original intersection residual maps onto A7 through its full two-core
quotient and its actual central covering kernel. -/
theorem sourceOrbit_seven_witness_residual_quotient
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 4 → ZMod 2))
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    {A J H W : Subgroup G} (hw : Witness L V A J H W) :
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ∃ π : F →* alternatingGroup (Fin 7), Function.Surjective π ∧ Group.IsSolvable π.ker := by
  obtain ⟨m⟩ := hmodel
  let e := (D.componentCentralQuotientEquiv h.quasisimple).trans
    ((centerQuotientCongr m.groupEquiv).trans
      ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot
        (by simp))).trans QuotientGroup.quotientBot))
  rcases hw with ⟨_,_,_,_,_,_,_,_,_,_,_,⟨c,_⟩,_⟩
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let r : F →* (L ⧸ pCore 2 L) := c.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F))
  have hrk : r.ker = pCore 2 F := by
    rw [MonoidHom.ker_comp_of_injective _ _ c.injective,QuotientGroup.ker_mk']
  let : Group.IsNilpotent (pCore 2 F) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable r.ker := hrk.symm ▸ inferInstanceAs (Group.IsSolvable (pCore 2 F))
  let π : F →* alternatingGroup (Fin 7) := e.toMonoidHom.comp
    ((QuotientGroup.mk' (center (L ⧸ pCore 2 L))).comp r)
  have hπ : Function.Surjective π := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (c.surjective.comp (QuotientGroup.mk'_surjective _)))
  refine ⟨π,hπ,?_⟩
  have he : π.ker = (center (L ⧸ pCore 2 L)).comap r := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,
      ←MonoidHom.comap_ker,QuotientGroup.ker_mk']
  rw [he]
  exact isSolvable_comap_of_solvable_ker r _

/-- The ordinary component supplied by this original reciprocal witness has
central quotient J4; every rank-two row is excluded on its literal residual. -/
theorem sourceOrbit_seven_witness_ordinary_janko
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ Representation.BinaryOffender.IsFFModule D.sourceOrbitNormalizerRepresentation)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 4 → ZMod 2))
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    {A J H W : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K) :
    Nonempty ((K ⧸ center K) ≃* Janko4.Model) := by
  obtain ⟨hn,_,hUF,hcomm,hfix⟩ :=
    D.sourceOrbit_whole_pushingUp_residual_data h hmany hnon hA ho hw
  obtain ⟨_,hc⟩ := D.sourceOrbit_seven_ordinary_component_catalogue
    h hd σ hmodel hw hUF hcomm hfix K hK
  rcases hc with ⟨n,hrank⟩ | hj
  · let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let K₀ := K.map H.subtype
    have hC := hw.2.2.2.2.2.2.1
    let : Group.IsPerfect F := by
      change Group.IsPerfect ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      exact (hC.normalized_span_eq hn) ▸ hC.span_perfect
    have hFK : F ≤ K₀ := by
      intro f hf
      exact ⟨⟨f,hC.component_le.trans hC.local_le hf⟩,
        hC.ordinary_component_contains_original K hK hf,rfl⟩
    let e := (K.equivMapOfInjective H.subtype H.subtype_injective).symm
    let z := QuotientGroup.congr (center K₀) (center K) e
      (Theory.GroupTheory.FixedElementary.map_center e)
    obtain ⟨π,hπ,_⟩ := D.sourceOrbit_seven_witness_residual_quotient h σ hmodel hw
    exact (no_CrankTwo_of_seven_residual_module F K₀ D.sourceOrbit hFK hUF
      D.sourceOrbit_weakClosure_setup.nontrivial hcomm π hπ (hrank.of_mulEquiv z)).elim
  · exact hj

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
