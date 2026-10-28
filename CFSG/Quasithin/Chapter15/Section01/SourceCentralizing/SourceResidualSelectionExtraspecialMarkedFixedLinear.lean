module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialModelSource
public import Theory.Representation.ExtraspecialBinarySix.FixedPlanes
public import Theory.Representation.CyclicFixedRank

/-!
# The original marked plane complements the Thompson moved plane

The pointwise kernel of the marked fixed plane has the marked cubic as
its two-residual. Thus the small Thompson involution normalizes that
cubic. Its displacement lies in the cubic's moved space, which is
disjoint from the marked fixed plane by odd-order averaging. The two
planes therefore sum to the Thompson fixed four-space.

Source: Aschbacher--Smith, Notation 15.1.16(c), printed p.1092.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

private theorem moved_le_cubic_moved
    {D A : Type*} [Group D] [AddCommGroup A] [Module (ZMod 2) A]
    (ρ : Representation (ZMod 2) D A) (X : Subgroup D) (t : D)
    (hc : IsCompl (fixedSpace ρ X) (subspaceCommutator ρ ⊤ X))
    (hn : t ∈ normalizer (X : Set D))
    (hf : fixedSpace ρ X ≤ fixedSpace ρ (zpowers t)) :
    subspaceCommutator ρ ⊤ (zpowers t) ≤ subspaceCommutator ρ ⊤ X := by
  have hs := subspaceCommutator_invariant_normalizer ρ
    (show normalizer (X : Set D) ≤ subspaceStabilizer ρ ⊤ from
      le_subspaceStabilizer ρ ⊤ (by intros; trivial)) le_rfl
  rw [CyclicFixedRank.commutator_eq_range]
  rintro _ ⟨v,rfl⟩
  have hv : v ∈ fixedSpace ρ X ⊔ subspaceCommutator ρ ⊤ X := by
    rw [hc.sup_eq_top]
    trivial
  obtain ⟨w,hw,y,hy,rfl⟩ := Submodule.mem_sup.mp hv
  have hwf := hf hw ⟨t,mem_zpowers t⟩
  change ρ t w = w at hwf
  have hyf := (hs hn y).2 hy
  have he : (ρ t - (LinearMap.id : A →ₗ[ZMod 2] A)) (w+y) = ρ t y-y := by
    simp only [LinearMap.sub_apply,LinearMap.id_apply,map_add,hwf]
    abel
  rw [he]
  exact (subspaceCommutator ρ ⊤ X).sub_mem hyf hy

/-- The selected original cubic fixed plane and the original Thompson moved
plane are disjoint and sum to the original Thompson fixed space. -/
theorem PreparedChosenModule.extraspecial_marked_fixed_direct_sum
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    letI := h.elementary
    ∀ c : ExtraspecialMarker.ImageMarking T M V h.normalized,
      let ρ := imageRepresentation M V h.normalized
      let P := pResidual 2 (internalActionImage M V h.normalized)
      let R := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V h.normalized).rangeRestrict
      let W := fixedSpace ρ (c.X.map P.subtype)
      let U := subspaceCommutator ρ ⊤ R
      Disjoint W U ∧ fixedSpace ρ R = W ⊔ U := by
  let := h.elementary
  intro c
  let D := internalActionImage M V h.normalized
  let ρ := imageRepresentation M V h.normalized
  let P := pResidual 2 D
  let R := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
    (actionHom M V h.normalized).rangeRestrict
  let X := c.X.map P.subtype
  let W := fixedSpace ρ X
  let U := subspaceCommutator ρ ⊤ R
  let K := subspaceKernel ρ W ⊤
  change Disjoint W U ∧ fixedSpace ρ R = W ⊔ U
  obtain ⟨t,ht,htR,hr⟩ := h.extraspecial_small_thompson_image
    hG T hempty hM hmany hJ hfull hex
  change zpowers t = R at htR
  change fixedCodim ρ R = 2 at hr
  have hRK : R ≤ K := by
    intro r hr
    exact ⟨mem_top _,fun w hw => c.fixed_thompson hw ⟨r,hr⟩⟩
  have hKN : K ≤ normalizer (X : Set D) := by
    have hn := K.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image K (pResidual 2 K))
    simpa only [show (pResidual 2 K).map K.subtype = X from c.residual] using hn
  have htN : t ∈ normalizer (X : Set D) :=
    hKN (hRK (htR ▸ mem_zpowers t))
  obtain ⟨_,_,_,hP,hPc,_,h6,_⟩ := hex
  let : IsExtraspecial 3 P := hP
  obtain ⟨hW,_,hc⟩ := ExtraspecialBinarySix.noncentral_cubic_planes
    ρ (imageRepresentation_injective M V h.normalized) P hPc h6 c.X c.card_X c.noncentral
  change Module.finrank (ZMod 2) W = 2 at hW
  have hUY : U ≤ subspaceCommutator ρ ⊤ X := by
    rw [show U = subspaceCommutator ρ ⊤ R from rfl,←htR]
    exact moved_le_cubic_moved ρ X t hc htN (by rw [htR]; exact c.fixed_thompson)
  have hd : Disjoint W U := hc.disjoint.mono_right hUY
  refine ⟨hd,?_⟩
  have hq : IsQuadratic ρ R := by
    rw [←htR]
    exact (involution_actor_rank_and_fixedCodim ρ t ht).2.2.1
  have hUE : U ≤ fixedSpace ρ R := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,v,_,rfl⟩ b
    exact hq b b.property a ha v
  have hU : Module.finrank (ZMod 2) U = 2 := by
    rw [show U = subspaceCommutator ρ ⊤ R from rfl,←htR,
      CyclicFixedRank.commutator_eq_range,←fixedCodim_zpowers_eq_displacement_rank,htR]
    exact hr
  have hE : Module.finrank (ZMod 2) (fixedSpace ρ R) = 4 := by
    have hh := fixedCodim_add_finrank ρ R
    rw [hr,h6] at hh
    omega
  have hsum : Module.finrank (ZMod 2) (W ⊔ U : Submodule (ZMod 2) (Additive V)) = 4 := by
    have hh := Submodule.finrank_sup_add_finrank_inf_eq W U
    rw [hd.eq_bot,finrank_bot,hW,hU] at hh
    omega
  exact (Submodule.eq_of_le_of_finrank_eq (sup_le c.fixed_thompson hUE)
    (hsum.trans hE.symm)).symm

end CFSG.Quasithin.Chapter15.Section01
