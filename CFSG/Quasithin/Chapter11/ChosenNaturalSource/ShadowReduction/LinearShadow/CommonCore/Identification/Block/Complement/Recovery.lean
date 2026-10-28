module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.Block.Complement.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.FieldFour.PlaneComplement
public import Theory.SpecificGroups.PSL3.LinearThreeFieldTransport

/-!
# Recovering the original component core, including field order four

An actual coefficient-field equivalence transports the full SL₃ cover,
its plane radical and its original Sylow into the field-four model.
The invariant complement makes the projective kernel odd, so the original
quotient two-core vanishes. Together with the ordinary multiplier branch
this proves V=O₂(L)=C_L(V), and pulling back the radical image gives
R₂∩L=PV. The original counterexample application discharges all local
complement premises. The remaining P=J(PV)=O₂(L₂) argument stays with this
identification task; earlier-source final discharge belongs to
qt-d-1222-shadow-common-core.

Source: Aschbacher--Smith, refs/quasithin.pdf, printed p.774,
first three paragraphs. The exceptional model calculation uses I.2.2(3b).
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Matrix
open scoped IsMulCommutative commutatorElement MatrixGroups
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
namespace OriginalBlock
open Matrix.PSL3.LinearThree
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G} {h : G}
    (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

private theorem field_lineRadical_image {F K : Type*} [Field F] [Field K]
    [Finite F] [Finite K] [CharP F 2] [CharP K 2] (e : F ≃+* K) :
    ((lineRadicalSL F).map (lineLocalSL F).subtype).map (Atlas.fieldEquivSL 3 e).toMonoidHom =
      (lineRadicalSL K).map (lineLocalSL K).subtype := by
  rw [←lineLocalSL_twoCore_eq,←lineLocalSL_twoCore_eq,
    ←pCore_map_iso 2 (lineLocalSLFieldEquiv e),Subgroup.map_map,Subgroup.map_map]
  rfl

private theorem field_lineParabolic {F K : Type*} [Field F] [Field K] [Finite F] [Finite K]
    (e : F ≃+* K) (g : SL(3,F)) (hg : g ∈ lineParabolicSL F) :
    Atlas.fieldEquivSL 3 e g ∈ lineParabolicSL K := by
  obtain ⟨h20,h21⟩ := (mem_lineParabolicSL_iff F g).mp hg
  rw [mem_lineParabolicSL_iff]
  change e (g.val 2 0) = 0 ∧ e (g.val 2 1) = 0
  simp only [h20,h21,map_zero,and_self]

include D S a in
private theorem aligned_inner_sylow_parabolic (l : L) (hl : (l : G) ∈ (T : Subgroup G)) :
    SL3.PlaneAction.alignedQuotient D S a l ∈ lineParabolicSL S.field.Carrier := by
  apply (SL3.PlaneAction.aligned_stabilizer (SL3.alignment D S a)
    ((SL3.coordinates D S a).quotientMap l) 1).mp
  exact ((SL3.coordinates D S a).mem_normalizer_preimage_iff ((SL3.flag D S a).space 1) l).mp
    ((SL3.flag D S a).invariant 1 hl)

include D S a in
/-- The actual invariant complement kills the exceptional quotient two-core.
The full special-linear cover is retained throughout the field transport. -/
theorem seedQuotient_core_eq_bot_of_complement
    (hcomm : ⁅L.pCoreIn 2,L⁆ = V)
    (h4 : 2 ^ S.field.degree = 4)
    (hd : Disjoint (seedQuotientModel D S a).ker (pairImage D H h))
    (hE : IsElementaryAbelian 2 (pairImage D H h))
    (him : (pairImage D H h).map (alignedSeedModel D S a) =
      (lineRadicalSL S.field.Carrier).map (lineLocalSL S.field.Carrier).subtype)
    (hT : (T : Subgroup G) ≤ normalizer (pairCore V H h : Set G)) :
    pCore 2 (SeedQuotient D) = ⊥ := by
  let : Fintype S.field.Carrier := Fintype.ofFinite _
  let : Fintype Matrix.PSL3Four.F := Fintype.ofFinite _
  let e : S.field.Carrier ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,S.field.card_eq,h4,Matrix.PSL3Four.card_F])
  let b := (MulAut.conj (SL3.alignment D S a)⁻¹).trans (Atlas.fieldEquivSL 3 e)
  let f : PerfectCentralCovering.Cover (SeedQuotient D) SL(3,Matrix.PSL3Four.F) := {
    toMonoidHom := b.toMonoidHom.comp (seedQuotientModel D S a)
    surjective := b.surjective.comp (seedQuotientModel_surjective D S a)
    isPerfect := (seedCover D S a hcomm).isPerfect
    ker_le_center := by
      rw [MonoidHom.ker_comp_of_injective _ _ b.injective]
      exact (seedCover D S a hcomm).ker_le_center }
  have hker : f.toMonoidHom.ker = (seedQuotientModel D S a).ker :=
    MonoidHom.ker_comp_of_injective _ _ b.injective
  obtain ⟨R,hR,hn⟩ := pairImage_sylow_normalizer D hT
  have hRP : (R : Subgroup (SeedQuotient D)).map f.toMonoidHom ≤
      lineParabolicSL Matrix.PSL3Four.F := by
    rintro _ ⟨x,hx,rfl⟩
    rw [hR] at hx
    obtain ⟨l,hl,rfl⟩ := hx
    exact field_lineParabolic e _ (aligned_inner_sylow_parabolic D S a l hl)
  have him' : (pairImage D H h).map f.toMonoidHom =
      (lineRadicalSL Matrix.PSL3Four.F).map (lineLocalSL Matrix.PSL3Four.F).subtype := by
    change (pairImage D H h).map
      ((Atlas.fieldEquivSL 3 e).toMonoidHom.comp (alignedSeedModel D S a)) = _
    rw [←Subgroup.map_map,him,field_lineRadical_image]
  let := hE
  have ho := FieldFour.full_cover_projective_kernel_odd f R hRP (pairImage D H h)
    (hker.symm ▸ hd) him' hn
  have hz : ((Matrix.PSL3.projection Matrix.PSL3Four.F).comp f.toMonoidHom).ker =
      center (SeedQuotient D) := by
    rw [←MonoidHom.comap_ker,Matrix.PSL3.projection_ker]
    exact f.comap_center
  rw [hz] at ho
  let := seedQuotient_quasisimple D S a hcomm
  obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := SeedQuotient D)).exists_card_eq
  have hdvd := card_dvd_of_le (IsQuasisimple.pCore_le_center (G := SeedQuotient D) 2)
  have hk0 : k = 0 := by
    by_contra hne
    exact ho ((dvd_pow_self 2 hne).trans (hk ▸ hdvd))
  exact (pCore 2 (SeedQuotient D)).eq_bot_of_card_eq (by simpa [hk0] using hk)

include D S a in
/-- After core recovery, the full original plane radical inside L is exactly PV. -/
theorem plane_radical_inter_component_eq_pairJoin
    (hcore : L.pCoreIn 2 = V) (hPL : pairCore V H h ≤ L)
    (hgen : planeRadicalImage D S a = (seedQuotientModel D S a).ker ⊔ pairImage D H h) :
    (SL3.flag D S a).Ri 1 ⊓ L = pairCore V H h ⊔ V := by
  let : (V.subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer D.normalizes
  have hzero : (seedQuotientModel D S a).ker = ⊥ := by
    rw [seedQuotientModel_ker]
    apply bot_unique
    rintro _ ⟨l,hl,rfl⟩
    exact (QuotientGroup.eq_one_iff (N := V.subgroupOf L) l).mpr
      (hcore ▸ mem_map_of_mem L.subtype hl)
  rw [hzero,bot_sup_eq] at hgen
  change (((SL3.flag D S a).Ri 1).subgroupOf L).map (seedProjection D) =
    ((pairCore V H h).subgroupOf L).map (seedProjection D) at hgen
  have hqker : (seedProjection D).ker = V.subgroupOf L := QuotientGroup.ker_mk' _
  have hVR : V.subgroupOf L ≤ ((SL3.flag D S a).Ri 1).subgroupOf L :=
    comap_mono (D.le_componentCore.trans (component_core_le_plane_radical D S a))
  have he := congrArg (comap (seedProjection D)) hgen
  rw [comap_map_eq,comap_map_eq,hqker,sup_eq_left.mpr hVR,
    ←subgroupOf_sup hPL D.le_component] at he
  have hm := congrArg (map L.subtype) he
  simpa only [subgroupOf_map_subtype,
    inf_eq_left.mpr (sup_le hPL D.le_component)] using hm

end OriginalBlock

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {h : G}

theorem source_pair_component_core_recovery
    (cL : Coordinates D S.field) (flag : InvariantFlag cL)
    (s : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H) (hh : h ∈ H)
    (hm : h ∉ normalizer (L : Set G))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    (hnot : ¬ V ≤ H.pCoreIn 2)
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree))
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (R : Sylow 2 (residualStar T H))
    (hR : (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      (V.subgroupOf H).map (starProjection T H))
    (cK : NaturalQuotientMarking T H S.field)
    (A X : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hX : IsCartan T L X) (hAX : oddCartanPart A ≤ X) :
    L.pCoreIn 2 = V ∧ L ⊓ centralizer (V : Set G) = V ∧
      ∃ a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3),
        (SL3.flag D S a).Ri 1 ⊓ L = pairCore V H h ⊔ V := by
  obtain ⟨a,hPL,hB,hPV,hcard,hT,hcomp,cover,hcover⟩ :=
    source_pair_invariant_complement cL flag s p hc hh hm hfixed hf hnot hmodel hG2
      R hR cK A X hA hHall hX hAX
  obtain ⟨hd,hgen,hE,hCcard,him,hfull,hRnorm⟩ := hcomp
  obtain ⟨hgenL,hLT,hL⟩ := source_pair_core_centralization a (SL3.flag D S a)
    (SL3.flag_inner_unique D S a) s p hc hh hm hfixed hf hnot hmodel R hR cK
      A X hA hHall hX hAX
  have hcore : L.pCoreIn 2 = V ∧ L ⊓ centralizer (V : Set G) = V := by
    rcases OriginalBlock.core_alternative D S a hL with hcore | ⟨h4,hbad⟩
    · exact hcore
    · exact (hbad (OriginalBlock.seedQuotient_core_eq_bot_of_complement D S a hL h4
        hd hE him hT)).elim
  exact ⟨hcore.1,hcore.2,a,OriginalBlock.plane_radical_inter_component_eq_pairJoin D S a
    hcore.1 hPL hgen⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
