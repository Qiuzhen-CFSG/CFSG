module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.FaithfulModels
public import Theory.Representation.HexacodeAction.SmallInvolution.Descent
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.FourSpace

/-!
# Completion of the faithful exceptional exhaustion branch

The original vertex projection contains the actual even hexacode cover: its
component has the same order, is perfect, and embeds under the given map.
The literal moving central quotient has full residual movement, zero fixed
space, and a critical actor of displacement at most two. The small-involution
budget makes its even restriction irreducible before descending through the
two-group kernel. Actual natural-four or hexacode coordinates then contradict
the previously proved derived-order and invariant-form obstructions.

Thus the faithful initial-action kernel forces critical distance two and
exhausts the entire intrinsic block, including its central attachment. The
whole-core clauses and the literal small-MS rank-two consumer follow. The
unconditional alternatives below retain only the cubic initial kernel at
larger distance. That branch and final natural/exceptional assembly remain
with qt-e-ms-small-a6-reconstruction.

Source: Meierfrankenfeld--Stellmacher (1993), (3.8), printed pp.878--879;
Aschbacher--Smith C.1.31--32, printed pp.135--136. The imported concrete
hexacode and finite recognition retain their documented ATLAS attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Atlas.Codes
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance
open NaturalStructure.Exclusion
private theorem even_le_image_of_perfect {H : Type*} [Group H]
    (C : Subgroup H) [Group.IsPerfect C]
    (f : H →* HexAutomorphisms) (hf : Function.Injective f)
    (hc : Nat.card C = Nat.card hexSign.ker) : hexSign.ker ≤ C.map f := by
  have hCe : C.map f ≤ hexSign.ker := by
    let sign : C →* ℤˣ := hexSign.comp (f.comp C.subtype)
    have hh : _root_.commutator C ≤ sign.ker := Abelianization.commutator_subset_ker sign
    rw [Group.IsPerfect.commutator_eq_top] at hh
    rintro x ⟨y,hy,rfl⟩
    have he : (⟨y,hy⟩ : C) ∈ sign.ker := hh (mem_top _)
    change sign ⟨y,hy⟩ = 1 at he
    change hexSign (f y) = 1
    exact he
  have he : Nat.card (C.map f) = Nat.card hexSign.ker :=
    (card_map_of_injective hf).trans hc
  exact (eq_of_le_of_card_ge hCe he.ge).ge

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
local notation "T" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)
variable (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = pCore 2 (L ⊔ R : Subgroup G))
include h e hz hk

/-- Every original projection with kernel Q contains the full even cubic cover. -/
theorem original_projection_contains_even (π : M →* HexAutomorphisms)
    (hπ : π.ker = pCore 2 M) : hexSign.ker ≤ π.range := by
  let q := QuotientGroup.mk' (layerKernel L R)
  let b : LayerActor L R ≃* M ⧸ π.ker := QuotientGroup.quotientMulEquivOfEq (hk.trans hπ.symm)
  let f := (QuotientGroup.kerLift π).comp b.toMonoidHom
  have hf : Function.Injective f := (QuotientGroup.kerLift_injective π).comp b.injective
  have hfq (g : M) : f (q g) = π g := rfl
  let C := layerComponent L R
  let := layerComponent_quasisimple h e hz
  obtain ⟨d⟩ := layerComponent_equiv_hexEven h e hz hk
  have hCe := even_le_image_of_perfect C f hf (Nat.card_congr d.toEquiv)
  intro x hx
  obtain ⟨y,hy,rfl⟩ := hCe hx
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (layerKernel L R) y
  exact ⟨g,hfq g⟩

/-- The actual coordinates at each vertex retain the even cover in their image. -/
theorem HexacodeChart.even_le_range
    {a : Vertex T} (c : HexacodeChart (L := L) (R := R) a)
    (ha : color T a = false) : hexSign.ker ≤ c.projection.range := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color T ha
  let H := stabilizer T (mVertex T g)
  let H0 := stabilizer T (alpha T)
  let b : M ≃* H0 := (MonoidHom.ofInjective (embedM_injective T)).trans
    (MulEquiv.subgroupCongr (stabilizer_m_base T).symm)
  have hG : H0.map (MulAut.conj g⁻¹).toMonoidHom = H := by
    simpa only [H0,H,alpha,act_mVertex,one_mul] using (stabilizer_act T g (alpha T)).symm
  let a : M ≃* H := b.trans (((MulAut.conj g⁻¹).subgroupMap H0).trans
    (MulEquiv.subgroupCongr hG))
  have hQ : (pCore 2 M).map a.toMonoidHom = (Q T (mVertex T g)).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le (show Q T (mVertex T g) ≤ H from fun _ hx => hx.1)]
    change (pCore 2 M).map ((MulAut.conj g⁻¹).toMonoidHom.comp (embedM T)) = _
    rw [←map_map,←Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    simpa only [alpha,act_mVertex,one_mul] using (Q_act T g (alpha T)).symm
  let π := c.projection.comp a.toMonoidHom
  have hπ : π.ker = pCore 2 M := by
    change c.projection.ker.comap a.toMonoidHom = pCore 2 M
    rw [c.kernel,←hQ,comap_map_eq_self_of_injective a.injective]
  have hh := original_projection_contains_even h e hz hk π hπ
  intro x hx
  obtain ⟨m,hm⟩ := hh hx
  exact ⟨a m,hm⟩

/-- Both recognized moving central quotients are excluded in the faithful branch. -/
theorem faithful_largeDistance_false (hb : 2 < sourceDistance h) : False := by
  let a := alpha T
  have ha : color T a = false := rfl
  let := moving_central_quotient_elementary (sourceGeometry h) (sourceDistance_pos h)
    a ha (faithful_radius_derived_le_fixed h e hz hk hb a ha)
  let := finite_moving (sourceGeometry h) hb a ha
  let := finite_stabilizer T a
  let ρ := Offenders.linearize (movingQuotientAction a)
  obtain ⟨b,hcrit⟩ := criticalPair_exists T a ((sourceGeometry h).exists_critical a ha)
  let p := DistanceEight.PathCentrality.CriticalPath.ofPair (geometry := sourceGeometry h) ha hcrit
  have hl : p.walk.length = 4 := p.length_eq_b.trans (faithful_distance_eq_four h e hz hk hb)
  have hle : 2 ≤ p.walk.length := by omega
  let d := p.walk.getVert 2
  have hd : color T d = false := (p.vertex_color hle).mpr (by decide)
  have had : (cosetGraph T).dist a d = 2 := p.dist_start hle
  have hdb : (cosetGraph T).dist d b = 2 := by rw [p.dist_end,hl]
  obtain ⟨c⟩ := hexacodeChart_nonempty h e hz hk a ha
  let A := (X T b).subgroupOf (stabilizer T a)
  have hbest : IsBestOffender Hexacode.action (A.map c.projection) :=
    c.critical_best h e hz hk ha b hcrit
  have hAE := Hexacode.bestOffender_le_even _ hbest
  have hex : ∃ x, x ∈ A.map c.projection ∧ x ≠ 1 := by
    by_contra! hn
    exact hbest.1.1 (le_bot_iff.mp (fun x hx => hn x hx))
  obtain ⟨x,hx,hxn⟩ := hex
  let t : HexEvenAutomorphisms := ⟨x,hAE hx⟩
  have ht : orderOf t = 2 := by
    rw [Subgroup.orderOf_mk]
    let := hbest.1.2
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian x hx) hxn
  have hfull := movingQuotientAction_full_original h (sourceGeometry h) hb a ha
    (faithful_radius_derived_le_fixed h e hz hk hb a ha)
  have hn : Nontrivial (Additive ((Vcirc T a) ⧸ center (Vcirc T a))) := by
    by_contra! hh
    let := hh
    have hcomm : IsMulCommutative (Vcirc T a) := ⟨⟨fun x y => by
      have hx : QuotientGroup.mk' (center (Vcirc T a)) x = 1 :=
        Additive.ofMul.injective (Subsingleton.elim _ _)
      exact (mem_center_iff.mp ((QuotientGroup.eq_one_iff x).mp hx) y).symm⟩⟩
    let := hcomm
    have hfour := faithful_moving_derived_card_lower h e hz hk hb a ha
    rw [commutator_eq_bot,card_bot] at hfour
    omega
  let := hn
  obtain ⟨q,hq,σ,hσ,hnσ,hσρ,hdegree⟩ := Hexacode.SmallInvolution.exists_residual_model
    c.projection (c.even_le_range h e hz hk ha)
    (by rw [c.kernel]; exact (Q_isPGroup T h.relative_radical.isPGroup
      h.relative_radical.twoCore_le a ha).comap_subtype)
    ρ hfull (faithful_moving_fixedSpace_eq_bot h e hz hk hb a ha)
    A hAE t ht hx
    (faithful_moving_fixedCodim_le_two h e hz hk hb a ha b hcrit d hd had hdb)
  let := hσ
  rcases hdegree with ⟨hcenter,hdim⟩ | ⟨hfσ,hdim⟩
  · let τ := (quotientOfLEKer σ (center HexEvenAutomorphisms) hcenter).comp
      Hexacode.even_quotient_center_equiv.symm.toMonoidHom
    have hτσ (g : HexEvenAutomorphisms) : τ (hexEvenCoordinate g) = σ g := by
      change quotientOfLEKer σ (center HexEvenAutomorphisms) hcenter
        (Hexacode.even_quotient_center_equiv.symm (hexEvenCoordinate g)) = _
      have hh : Hexacode.even_quotient_center_equiv.symm (hexEvenCoordinate g) =
          QuotientGroup.mk' (center HexEvenAutomorphisms) g :=
        Hexacode.even_quotient_center_equiv.symm_apply_eq.mpr rfl
      rw [hh]
      rfl
    have hfτ : Function.Injective τ := by
      let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
      rcases (MonoidHom.normal_ker τ).eq_bot_or_eq_top with hker | hker
      · exact τ.ker_eq_bot_iff.mp hker
      · exfalso
        apply hnσ
        ext g v
        rw [←hτσ]
        have hh : hexEvenCoordinate g ∈ τ.ker := hker.symm ▸ mem_top _
        exact LinearMap.congr_fun hh v
    obtain ⟨E⟩ := CFSG.Quasithin.ChapterK.Alternating.RecognitionInputs.Six.actionEquiv_of_faithful_fourSpace τ hfτ hdim
    let f := E.groupEquiv.toMonoidHom.comp (hexEvenCoordinate.comp q)
    have hfs : Function.Surjective f := E.groupEquiv.surjective.comp (hexEvenCoordinate_surjective.comp hq)
    have hm : HasNaturalMovingQuotient (L := L) (R := R) a := by
      refine ⟨inferInstance,(alternatingGroup (Fin 6)).subtype.comp f,?_,E.linearEquiv,?_⟩
      · intro x hx
        obtain ⟨g,hg⟩ := hfs ⟨x,hx⟩
        exact ⟨g,congrArg Subtype.val hg⟩
      · intro g v
        rw [←hσρ g v,←hτσ]
        exact E.intertwines _ _
    exact faithful_moving_not_natural h e hz hk hb a ha hm
  · obtain ⟨E,F,hF⟩ := Hexacode.EvenBinaryRecognition.exists_equivariant σ hfσ hσ hdim
    let f := E.toMonoidHom.comp q
    have hfs : Function.Surjective f := E.surjective.comp hq
    have hm : HasHexacodeMovingQuotient (L := L) (R := R) a := by
      refine ⟨inferInstance,hexSign.ker.subtype.comp f,?_,F,?_⟩
      · intro x hx
        obtain ⟨g,hg⟩ := hfs ⟨x,hx⟩
        exact ⟨g,congrArg Subtype.val hg⟩
      · intro g v
        rw [←hσρ g v]
        exact hF _ _
    exact faithful_moving_not_hexacode h e hz hk hb a ha hm

/-- The faithful initial-kernel branch has critical distance exactly two. -/
theorem faithful_distance_eq_two : sourceDistance h = 2 := by
  apply sourceDistance_eq_two h
  exact Nat.le_of_not_gt (faithful_largeDistance_false h e hz hk)

/-- Exhaustion of the entire intrinsic core for the faithful initial action. -/
theorem coreExhaustion_of_faithful : CoreExhaustion L R :=
  coreExhaustion_of_distanceTwo h e hz (faithful_distance_eq_two h e hz hk)

open ChapterC in
/-- All exceptional block clauses retain the whole core and its central attachment. -/
theorem core_facts_of_faithful :
    IsElementaryAbelian 2 (blockU L) ∧
      blockU L ≤ centralizer (pCore 2 L : Set L) ∧
      BlockModuleIrreducible L ∧ Nat.card (blockU L) = 2 ^ 6 ∧
      centralizer (blockU L : Set L) = pCore 2 L :=
  core_facts_of_exhaustion h e hz (coreExhaustion_of_faithful h e hz hk)

/-- The literal small-MS rank-two consumer in the faithful initial-kernel branch. -/
theorem rankTwo_of_faithful : RankTwoAlternatives L R :=
  rankTwo_of_exhaustion h e hz (coreExhaustion_of_faithful h e hz hk)

omit hk in
/-- The only remaining exceptional obstruction has cubic initial kernel and larger distance. -/
theorem coreExhaustion_or_cubic_largeDistance :
    CoreExhaustion L R ∨ layerKernel L R = extensionKernel h ∧ 2 < sourceDistance h := by
  rcases centralOmega_centralizer_cases h e hz with hf | hc
  · exact Or.inl (coreExhaustion_of_faithful h e hz hf)
  · refine Or.inr ⟨hc,?_⟩
    by_contra! hb
    exact cubic_distanceTwo_impossible h e hz hc (sourceDistance_eq_two h hb)

omit hk in
/-- The same remaining branch is retained in the original C.1.32 consumer. -/
theorem rankTwo_or_cubic_largeDistance :
    RankTwoAlternatives L R ∨ layerKernel L R = extensionKernel h ∧ 2 < sourceDistance h :=
  (coreExhaustion_or_cubic_largeDistance h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
