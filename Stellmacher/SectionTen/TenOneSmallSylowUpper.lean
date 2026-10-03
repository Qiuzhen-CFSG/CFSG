module

public import Stellmacher.SectionTen.TenOneMiddleResidualModel
public import Stellmacher.SectionTen.TenOneSmallSylowLower
public import Stellmacher.SectionEight.GeneratedEightSixSL2ResidualOdd
public import Stellmacher.TwoResidualSylowSupplement
public import Theory.GroupTheory.CenterFreeC4SquareCoreBound

/-!
# The upper Sylow bound in the small case of (10.1)

For an order-eight first neighbor module with SL2(2) local quotient, the
actual distinguished Sylow subgroup T has order at most 128.

Inside the middle stabilizer, its normal two-residual and two-core intersect
in the proved C4-times-C4 residual core. The literal SL2(2) quotient makes
the residual image have order three. Transporting the initial stabilizer's
trivial center along the opening conjugator lets the generic center-free
C4-square theorem bound the middle two-core by 64. The same conjugator
identifies its order with the initial core order. The initial edge is the
supplied T and has twice that core's order, giving the asserted bound.
No auxiliary model, faithful action, or cardinal bound is assumed.
The native middle-stabilizer input packet is exported for the subsequent
small-case central-quotient arguments, retaining the actual residual and core.

Source: Stellmacher (10.1)(a1), printed pp.60-61,
`refs/files/stellmacher-n-group.pdf`. Together with TenOneSmallSylowLower,
this supplies both Sylow bounds in alternative (a).
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_middle_bound_inputs
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    let M := GAt ctx.Γ middle
    let E := twoResidualAmbient (⊤ : Subgroup M)
    let Q := pCore 2 M
    Subgroup.center M = ⊥ ∧
      IsModel (E ⊓ Q : Subgroup M) (C4 × C4) ∧
      Nat.card (E.map (QuotientGroup.mk' Q)) = 3 := by
  let M := GAt ctx.Γ middle
  let E := twoResidualAmbient (⊤ : Subgroup M)
  let Q := pCore 2 M
  let D := twoCoreIn (EAt ctx.Γ middle)
  have hEmap : E.map M.subtype = EAt ctx.Γ middle := by
    have hm := map_twoResidualAmbient_of_subgroup_image (⊤ : Subgroup M) M.subtype M
      (by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype])
    exact hm.trans (ctx.Γ.twoResidualAt_def middle).symm
  have hQmap : Q.map M.subtype = QAt ctx.Γ middle :=
    (ctx.Γ.twoCoreAt_def middle).symm
  have hRmap : (E ⊓ Q : Subgroup M).map M.subtype = D := by
    rw [Subgroup.map_inf E Q M.subtype M.subtype_injective,hEmap,hQmap]
    change ctx.Γ.twoResidualAt middle ⊓ ctx.Γ.twoCoreAt middle =
      twoCoreIn (ctx.Γ.twoResidualAt middle)
    rw [ctx.Γ.twoResidualAt_def, ctx.Γ.twoCoreAt_def, residual_core_eq_inter_core]
  have hRmodel : IsModel (E ⊓ Q : Subgroup M) (C4 × C4) := by
    obtain ⟨model⟩ := ten_one_middle_residual_c4_square ctx middle hpath hsmall hmodel
    exact ⟨((Subgroup.equivMapOfInjective (E ⊓ Q) M.subtype M.subtype_injective).trans
      (MulEquiv.subgroupCongr hRmap)).trans model⟩
  obtain ⟨⟨actor,hactor⟩,_,_,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  let Pa := GAt ctx.Γ ctx.criticalPath.a
  have hPmap : Pa.map (MulAut.conj actor⁻¹).toMonoidHom = M :=
    (stabilizer_act ctx.Γ actor ctx.criticalPath.a).symm.trans (congrArg _ hactor)
  let eP : Pa ≃* M := ((MulAut.conj actor⁻¹).subgroupMap Pa).trans
    (MulEquiv.subgroupCongr hPmap)
  have hcenterM : Subgroup.center M = ⊥ := by
    apply Subgroup.card_eq_one.mp
    calc
      Nat.card (Subgroup.center M) = Nat.card (Subgroup.center Pa) :=
        (Nat.card_congr (Subgroup.centerCongr eP).toEquiv).symm
      _ = 1 := by
        rw [(lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).start_center_trivial,
          Subgroup.card_bot]
  obtain ⟨projection, hsurj, hker⟩ := (sectionTenOpeningData ctx middle hpath).quotient_model
  have hkerQ : projection.ker = Q := by
    rw [hker, ← hQmap]
    exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  have hEimage : E.map projection = commutator SL2Two := by
    rw [map_twoResidualAmbient_of_subgroup_image (⊤ : Subgroup M) projection ⊤
      (Subgroup.map_top_of_surjective _ hsurj),SectionEight.eight_six_sl2_residual_eq_commutator]
  have hcard : Nat.card (E.map (QuotientGroup.mk' Q)) = 3 := by
    rw [← Subgroup.relIndex_ker,QuotientGroup.ker_mk',← hkerQ,Subgroup.relIndex_ker,hEimage]
    exact isSL2Two_commutator_card ⟨MulEquiv.refl _⟩
  exact ⟨hcenterM,hRmodel,hcard⟩

private theorem sylow_upper_of_middle_core_bound
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hbound : Nat.card (pCore 2 (GAt ctx.Γ middle)) ≤ 64) :
    Nat.card T ≤ 128 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hmiddle : Nat.card (QAt Γ middle) ≤ 64 := by
    change Nat.card (Γ.twoCoreAt middle) ≤ 64
    rw [Γ.twoCoreAt_def]
    change Nat.card ((pCore 2 (GAt Γ middle)).map (GAt Γ middle).subtype) ≤ 64
    rw [Subgroup.card_map_of_injective (GAt Γ middle).subtype_injective]
    exact hbound
  obtain ⟨⟨actor,hactor⟩,_,_,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hQa : Nat.card (QAt Γ cp.a) ≤ 64 := by
    have hq : (QAt Γ cp.a).map (MulAut.conj actor⁻¹).toMonoidHom = QAt Γ middle := by
      change (q Γ cp.a).map _ = q Γ middle
      rw [← q_act,hactor]
    rw [← hq,Subgroup.card_map_of_injective (MulAut.conj actor⁻¹).injective] at hmiddle
    exact hmiddle
  have hb : 1 < cp.length := by have := ctx.critical_length; change 1 < ctx.criticalPath.length; omega
  have hjoin := (nine_initial_edge_core_product ctx.toAmbientSectionNineContext hb).1
  have hcores := local_cores_le_edge_sylow ctx.sectionSeven Γ cp
  have hTedge : T = GAt Γ cp.a ⊓ GAt Γ cp.firstStep :=
    le_antisymm cp.S_le_edge_stabilizers (hjoin ▸ sup_le hcores.1 hcores.2)
  have hcard : Nat.card T = 2 * Nat.card (QAt Γ cp.a) := by
    exact (congrArg (fun U : Subgroup G => Nat.card U) hTedge).trans
      (nine_initial_edge_core_product ctx.toAmbientSectionNineContext hb).2
  rw [hcard]
  omega

public theorem ten_one_small_sylow_card_upper
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) : Nat.card T ≤ 128 := by
  let M := GAt ctx.Γ middle
  let E := twoResidualAmbient (⊤ : Subgroup M)
  let Q := pCore 2 M
  let _ : E.Normal := by
    dsimp only [E]
    rw [SectionThree.twoResidualAmbient_top_eq_hktPResidual]
    exact BenderSuzuki.External.hktPResidual_normal
  obtain ⟨hcenter,hc4,himage⟩ := ten_one_small_middle_bound_inputs ctx middle hpath hsmall hmodel
  have hQ : Nat.card Q ≤ 64 := card_le_sixtyfour_of_centerfree_c4_square_residual (default : Sylow 2 M) E Q
    (twoResidualAmbient_top_sup_sylow _) (pCore_isPGroup (p := 2) (G := M))
    hcenter hc4 himage
  exact sylow_upper_of_middle_core_bound ctx middle hpath hQ

end Stellmacher.SectionTen
