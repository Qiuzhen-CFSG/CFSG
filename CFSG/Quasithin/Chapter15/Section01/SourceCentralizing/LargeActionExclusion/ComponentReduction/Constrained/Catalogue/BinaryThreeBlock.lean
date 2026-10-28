module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryThreePlacement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.AbelianSourceDouble
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.NonabelianRadical

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.CentralSylow
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.LinearThree.Exclusion
public import Theory.Representation.PSL3Two.OrbitStabilizers
public import Theory.Representation.PSL3Two.NaturalSylowFixed
public import Theory.Representation.SpecialLinearFieldTransport
import all CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.G2Geometry
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.SourceGeometry.Source

/-!
# Whole binary-three blocks and their source centralizers

The actual MS pair has either a natural L₃(2) block or an omega-center
centralizer that fails to normalize Q₁. The doubled natural module and
nonabelian MS alternatives supply this movement directly. In the original
ambient group, the central involutions lie in Q₁ and in the omega-center
of S_L Q₁. Their singleton centralizer overgroup forces that centralizer
into M_Z, where it normalizes Q₁. Thus the whole original L is a natural
block, including the possible central attachment of its intrinsic layer.

A faithful automorphism fixing S_L modulo the center is inner by a fixed
natural vector. The binary fixed line bounds the faithful omega-center
by two; the original seed supplies its nonidentity element. Its point
stabilizer is maximal. The existing central-kernel lifting theorem then
identifies M_L with the literal centralizer of the original seed. The
opposite parabolic's already proved O^{3′} escape gives the S-centralizer
identity. Together these prove the full ConstrainedL3Alternative and
apply the independently proved exchanged-source exclusion.

Both original primes, the same core-to-FF quotient marking, and the actual
marker hypotheses are retained. Only the later exclusion uses the original
cubic source together with an exchanged selection. The earlier 15.1.14
premise remains explicit for its existing producer and assembly owner.
The A₆ branches, general local-family Borel placement and full seven-row
assembly remain separate mathematical obligations of this catalogue.

This internal continuation uses the hidden actor body and the existing
faithful plus action from AutomorphismAction, G2Geometry and
SourceGeometry.Source only in proofs. Their public boundaries are unchanged.

Source: Aschbacher--Smith 15.1.20(2b), 15.1.22(**),(2), printed
pp.1094--1100; C.1.34's binary MS movement and A.1.39.
The concrete binary model retains its ATLAS attribution in LICENSES/ATLAS.txt.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open CFSG.Quasithin
open ChapterC
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
variable {G : Type*} [Group G] [Finite G]
variable {L R S : Subgroup G}
open Representation Representation.BinaryOffender
open BinaryLinearThree BinaryLinearThree.DoubledOffenders

omit [Finite G] in
private theorem doubled_normalizer_escape (a : DoubledSourceAction L R S) (hRS : R ≤ S)
    (hlift : L ⊓ centralizer ((msQ L R ⊓ centralizer (S : Set G) : Subgroup G) : Set G) ≤
      centralizer (FullSieve.SourceInterface.omegaCenterIn S : Set G)) :
    ¬ L ⊓ centralizer (FullSieve.SourceInterface.omegaCenterIn S : Set G) ≤ normalizer (R : Set G) := by
  intro hnorm
  obtain ⟨c, hcfix, hcmove⟩ := exists_point_fixer_moving_axis a.frame
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (a.marking.symm c)
  have hlc : a.marking (QuotientGroup.mk' (pCore 2 L) l) = c := by
    rw [hl, MulEquiv.apply_symm_apply]
  let j : (L ⊔ R : Subgroup G) := ⟨l, (show L ≤ L ⊔ R from le_sup_left) l.property⟩
  have hj : a.actor j = δ c := (a.component l).trans (congrArg δ hlc)
  have hlfix : (l : G) ∈ centralizer
      ((msQ L R ⊓ centralizer (S : Set G) : Subgroup G) : Set G) := by
    intro x hx
    let xQ : msQ L R := ⟨x, hx.1⟩
    have hfixed : (a.coordinates xQ).toAdd ∈ fixedSpace τ
        ((Matrix.PSL3Two.borelSL.map (MulAut.conj a.frame).toMonoidHom).map δ) := by
      rw [← a.componentSylow]
      rintro ⟨_, s, hs, rfl⟩
      exact (a.equivariant s xQ xQ (by
        change x = (s : G) * x * (s : G)⁻¹
        rw [hx.2 s hs.1, mul_inv_cancel_right])).symm
    let y : msQ L R := ⟨(l : G) * x * (l : G)⁻¹,
      (mem_normalizer_iff.mp (a.normalized j.property) x).mp hx.1⟩
    have hy : y = xQ := a.coordinates.injective (Multiplicative.toAdd.injective (by
      rw [a.equivariant j xQ y rfl, hj]
      exact hcfix _ hfixed))
    have hv := congrArg (fun z : msQ L R => (z : G)) hy
    exact (mul_inv_eq_iff_eq_mul.mp hv).symm
  have hlZ := hlift ⟨l.property, hlfix⟩
  have hlN : (l : G) ∈ normalizer R := hnorm ⟨l.property,hlZ⟩
  have hjN : j ∈ normalizer (R.subgroupOf (L ⊔ R) : Set (L ⊔ R : Subgroup G)) :=
    (Subgroup.le_normalizer_comap (L ⊔ R).subtype) hlN
  have himage : a.actor j ∈ normalizer ((R.subgroupOf (L ⊔ R)).map a.actor : Set D) :=
    (R.subgroupOf (L ⊔ R)).le_normalizer_map a.actor (mem_map_of_mem a.actor hjN)
  have hnorm := normalizes_unique_offender τ
    (normalizer ((R.subgroupOf (L ⊔ R)).map a.actor : Set D))
    ((R.subgroupOf (L ⊔ R)).map a.actor) ((S.subgroupOf (L ⊔ R)).map a.actor)
    ((BinaryLinearThree.R.map (MulAut.conj a.frame).toMonoidHom).map δ)
    le_rfl a.offender_le (map_mono (comap_mono hRS)) (axis_isOffender a.frame)
    a.unique_offender
  exact hcmove (hj ▸ hnorm himage)


private theorem nonabelian_normalizer_escape
    (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (hc : ¬ IsMulCommutative (msQ L R))
    (hS : Chapter1.IsSylowIn 2 S (L ⊔ R)) (hRS : R ≤ S) :
    ¬ L ⊓ centralizer (FullSieve.SourceInterface.omegaCenterIn S : Set G) ≤ normalizer (R : Set G) := by
  have hc' : ¬ IsMulCommutative (BinaryMS.commutatorCore (L.subgroupOf (L ⊔ R))) := by
    intro hh
    apply hc
    apply isMulCommutative_iff.mpr
    intro x y
    apply (binaryCoreEquiv L R).symm.injective
    simpa only [map_mul] using isMulCommutative_iff.mp hh
      ((binaryCoreEquiv L R).symm x) ((binaryCoreEquiv L R).symm y)
  obtain ⟨t⟩ := BinaryMS.MS93.exists_setup (h.binaryInput e) hc'
  obtain ⟨common⟩ := t.commonFacts hc'
  intro hnorm
  by_cases hb : t.geometry.b t.reduction.radical = 4
  · apply h.distance_four_replacement_movement e t common hb hS hRS
    intro l hl
    have hlC := h.distance_four_centralizer_omega_le e t common hb hS hl
    have hlN := hnorm ⟨hl.1,hlC⟩
    let j : (L ⊔ R : Subgroup G) := ⟨l,(show L ≤ L ⊔ R from le_sup_left) hl.1⟩
    have hjN : j ∈ normalizer (R.subgroupOf (L ⊔ R) : Set (L ⊔ R : Subgroup G)) :=
      (Subgroup.le_normalizer_comap (L ⊔ R).subtype) hlN
    let := t.reduction.characteristic
    have hjT : j ∈ normalizer (t.reduction.ambient : Set (L ⊔ R : Subgroup G)) :=
      normalizer_le_normalizer_characteristic_image (R.subgroupOf (L ⊔ R))
        t.reduction.subgroup hjN
    exact t.reduction.ambient.le_normalizer_map (L ⊔ R).subtype
      (mem_map_of_mem (L ⊔ R).subtype hjT)
  · have hb' : 4 < t.geometry.b t.reduction.radical := by
      have he := t.geometry.even (BinaryMS.MS93.alpha t.reduction.radical) rfl
      change Even (t.geometry.b t.reduction.radical) at he
      obtain ⟨n,hn⟩ := he
      have hl := common.large_distance
      omega
    let J := L ⊔ R
    obtain ⟨P,hP⟩ := hS
    have hSP : S.subgroupOf J = (P : Subgroup J) := by
      rw [←hP]
      exact comap_map_eq_self_of_injective J.subtype_injective _
    have hRP : R.subgroupOf J ≤ (P : Subgroup J) := hSP ▸ comap_mono hRS
    have hSJ : S ≤ J := hP ▸ map_subtype_le (P : Subgroup J)
    apply t.distance_eight_replacement_movement common hb' P hRP
    intro l hl
    have hlC : (l : G) ∈ centralizer (FullSieve.SourceInterface.omegaCenterIn S : Set G) := by
      intro z hz
      have hzS : z ∈ S := map_subtype_le _ hz
      have hzC : z ∈ centralizer (S : Set G) := by
        obtain ⟨a,⟨b,hb,rfl⟩,rfl⟩ := hz
        intro s hs
        exact congrArg S.subtype (mem_center_iff.mp b.property ⟨s,hs⟩)
      let zJ : J := ⟨z,hSJ hzS⟩
      have hzP : zJ ∈ centralizer (P : Set J) := by
        intro p hp
        exact Subtype.ext (hzC p (hP ▸ mem_map_of_mem J.subtype hp))
      exact congrArg Subtype.val (hl.2 zJ hzP)
    have hlN := hnorm ⟨hl.1,hlC⟩
    have hjN : l ∈ normalizer (R.subgroupOf J : Set J) :=
      (Subgroup.le_normalizer_comap J.subtype) hlN
    let := t.reduction.characteristic
    exact normalizer_le_normalizer_characteristic_image (R.subgroupOf J)
      t.reduction.subgroup hjN

private theorem binaryThree_block_or_normalizer_escape
    (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (hS : Chapter1.IsSylowIn 2 S (L ⊔ R)) (hRS : R ≤ S) :
    IsSL3EvenBlock L 1 ∨
      ¬ L ⊓ centralizer (FullSieve.SourceInterface.omegaCenterIn S : Set G) ≤ normalizer (R : Set G) := by
  by_cases hc : IsMulCommutative (msQ L R)
  · obtain ⟨m,q,hm,_,_,hC,hcard,hblock⟩ := h.abelian_source_quotient e hc
    rcases hm with rfl | rfl
    · exact Or.inl (hblock rfl).2
    · have h64 : Nat.card (msQ L R) = 64 := by
        rw [hcard,hC rfl]
        norm_num
      obtain ⟨a⟩ := h.exists_doubledSourceAction e hc h64 hS hRS
      exact Or.inr (doubled_normalizer_escape a hRS
        (centralizer_omega_le_of_double_split
          (h.abelian_source_double_split e hc h64 hS)))
  · exact Or.inr (nonabelian_normalizer_escape h e hc hS hRS)

variable {T : Sylow 2 G} {M Mc V : Subgroup G}
open Section03 Section03.InitialSource ChapterA.Section05To06

private theorem central_seed_le_radical (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hQne : d.Q1 ≠ ⊥)
    (hn : (T : Subgroup G) ≤ normalizer (d.MZ : Set G)) :
    centralInvolutions T ≤ d.Q1 := by
  let J := d.MZ ⊔ (T : Subgroup G)
  have hJnorm : J ≤ normalizer (d.MZ : Set G) := sup_le d.MZ.le_normalizer hn
  have hJQ : J ≤ normalizer (d.Q1 : Set G) := hJnorm.trans
    (normalizer_le_normalizer_characteristic_image d.MZ (pCore 2 d.MZ))
  have hQJ : d.Q1 ≤ J := d.Q1_le_MZ.trans le_sup_left
  have hH : J ∈ Chapter1.HOver G (T : Set G) := by
    refine ⟨?_,(show (T : Subgroup G) ≤ J from le_sup_right)⟩
    intro hb
    exact hQne (bot_unique ((le_pCoreIn_of_normalizes
      (isPGroup_pCoreIn 2 d.MZ) hQJ hJQ).trans_eq hb))
  have hZJ : centralInvolutions T ≤ J.pCoreIn 2 :=
    (centralInvolutions_le_omegaCore hG T hH).trans
      (map_mono (show omegaOneCenterAmbient (pCore 2 J) ≤ pCore 2 J from
        fun x hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1))
  have hZM : centralInvolutions T ≤ d.MZ := by
    refine le_inf ?_ (centralizer_le_partner T hu |>.trans' ?_)
    · exact centralInvolutions_le_centralizer_sylow T |>.trans
        (centralizer_le (d.marked_le_sylow h hTM))
    · exact (centralInvolutions_le_centralizer_sylow T).trans
        (centralizer_le (centralInvolutions_le_sylow T))
  have hnorm : d.MZ ≤ normalizer (J.pCoreIn 2 : Set G) :=
    (show d.MZ ≤ J from le_sup_left).trans (J.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
  exact (le_inf hZJ hZM).trans (le_pCoreIn_of_normalizes
    ((isPGroup_pCoreIn 2 J).to_le (show J.pCoreIn 2 ⊓ d.MZ ≤ J.pCoreIn 2 from inf_le_left))
    inf_le_right ((le_inf hnorm d.MZ.le_normalizer).trans inf_normalizer_le_normalizer_inf))

private theorem binaryThree_block_from_original
    (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hQne : d.Q1 ≠ ⊥) (hnM : (T : Subgroup G) ≤ normalizer (d.MZ : Set G))
    (hs : Chapter1.IsSylowIn 2 d.S d.G1)
    (hSL : Chapter1.IsSylowIn 2 d.SL d.L)
    (hn : d.Q1 ≤ normalizer (d.L : Set G))
    (hm : SmallMSPair KnownSimple.IsKnownSimple d.L d.Q1)
    (e : (d.L ⧸ pCore 2 d.L) ≃* Matrix.PSL3Two.SL) :
    IsSL3EvenBlock d.L 1 := by
  let S0 := d.SL ⊔ d.Q1
  have hQS := d.catalogue_radical_le_sylow hs hu
  have hS0S : S0 ≤ d.S := sup_le inf_le_left hQS
  have hS0N : S0 ≤ normalizer (d.L : Set G) :=
    sup_le (inf_le_right.trans d.L.le_normalizer) hn
  have hgen : d.L ⊔ S0 = d.L ⊔ d.Q1 := by
    rw [←sup_assoc,sup_eq_left.mpr (show d.SL ≤ d.L from inf_le_right)]
  obtain ⟨P,hP⟩ := hSL
  have hSyl : Chapter1.IsSylowIn 2 S0 (d.L ⊔ d.Q1) := by
    rw [←hgen]
    exact (T.isPGroup'.to_le (hS0S.trans d.S_le_T)).exists_sylow_sup_of_coprime_index
      d.L S0 hS0N (P : Subgroup d.L) P.not_dvd_index (hP ▸ le_sup_left)
  have hZQ := d.central_seed_le_radical hG h hTM hu hQne hnM
  have hZomega : centralInvolutions T ≤ FullSieve.SourceInterface.omegaCenterIn S0 := by
    intro z hz
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    exact ⟨mem_sup_right (hZQ hz),
      ((mem_omegaOneCenterAmbient_iff (T : Subgroup G) z).mp hz).2.1,
      fun x hx => centralInvolutions_le_centralizer_sylow T hz x (d.S_le_T (hS0S hx))⟩
  apply (binaryThree_block_or_normalizer_escape hm e hSyl le_sup_right).resolve_right
  intro hesc
  apply hesc
  intro l hl
  have hMc : l ∈ Mc := centralizer_le_partner T hu (centralizer_le hZomega hl.2)
  exact (d.MZ.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image d.MZ (pCore 2 d.MZ)))
      ⟨d.L_component.1 hl.1,hMc⟩

/-- The original binary-three FF row reconstructs the whole natural block,
retaining the literal quotient marking and either source prime. -/
theorem PreExclusionSource.constrained_binaryThree_block
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* Matrix.PSL3Two.SL) :
    IsSL3EvenBlock d.L 1 ∧
      ∃ t : (d.L ⧸ pCore 2 d.L) ≃* Matrix.PSL3Two.SL,
        ∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k) := by
  obtain ⟨hi,hm,t,ht,_⟩ := s.constrained_binaryThree_inputs (h := h)
    hG hempty hM hJ hu hf e
  exact ⟨d.binaryThree_block_from_original hG h hM.1.2 hu s.core_nontrivial
    s.sylow_normalizes_MZ s.centralizer_sylow s.component_sylow hi.normalizes hm t,t,ht⟩

/-- Later exchanged selection retains the original natural block and its FF marking. -/
theorem ExchangedSource.constrained_binaryThree_block
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (h : PreparedChosenModule T M V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* Matrix.PSL3Two.SL) :
    IsSL3EvenBlock d.L 1 ∧
      ∃ t : (d.L ⧸ pCore 2 d.L) ≃* Matrix.PSL3Two.SL,
        ∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k) := by
  obtain ⟨hi,hm,t,ht,_⟩ := s.constrained_binaryThree_inputs h hG hempty hM hJ hu hf e
  exact ⟨d.binaryThree_block_from_original hG h hM.1.2 hu s.core_nontrivial
    s.sylow_normalizes_MZ s.centralizer_sylow s.component_sylow hi.normalizes hm t,t,ht⟩

private theorem binaryThree_sylow_fixers
    {A : Type*} [_root_.Group A] [Finite A] (hb : IsSL3EvenBlock A 1)
    (P : Sylow 2 A) (B : Subgroup (MulAut A))
    (hB : ∀ a ∈ B, ∀ x ∈ P, a x * x⁻¹ ∈ center A) : Nat.card B ≤ 2 := by
  obtain ⟨F,_,_,hF,ρ,⟨m⟩,hρ⟩ := hb.2.2
  have hfield : Nat.card F = 2 := by simpa using hF
  let _ := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hfield)).symm
  let e := Atlas.fieldEquivSL 3 eF
  let v := Representation.SpecialLinearFieldTransport.natural 3 eF
  have hρi : Function.Injective ρ := by
    intro g j he
    apply Matrix.SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.ext
    intro w
    have hh := congrArg (fun k : MulAut (Multiplicative (Fin 3 → F)) =>
      (k (Multiplicative.ofAdd w)).toAdd) he
    simp only [hρ] at hh
    exact hh
  have hk : IsPGroup 2 m.actor.ker := by
    rw [BlockModuleModel.actor,MonoidHom.ker_comp_of_injective _ _ m.quotientIso.injective,
      QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) F) :=
    Atlas.sl_perfect 3 (by decide)
  let : Group.IsPerfect A := hb.2.1.twoPerfect.isPerfect_of_surjective_pGroup_kernel
    m.actor m.actor_surjective hk
  let q := e.toMonoidHom.comp m.actor
  have hq : Function.Surjective q := e.surjective.comp m.actor_surjective
  let Q := P.mapSurjective hq
  let W := {w : Multiplicative (Fin 3 → F) // ∀ x ∈ P, ρ (m.actor x) w = w}
  let f : W → Representation.BinaryOffender.fixedSpace BinaryLinearThree.W (Q : Subgroup _) :=
    fun w => ⟨v w.val.toAdd,by
      rintro ⟨g,x,hx,rfl⟩
      change Representation.specialLinearNatural 3 (e (m.actor x)) (v w.val.toAdd) = _
      rw [←Representation.SpecialLinearFieldTransport.natural_action 3 eF]
      exact congrArg v ((hρ _ _).symm.trans
        (congrArg Multiplicative.toAdd (w.property x hx)))⟩
  have hfi : Function.Injective f := by
    intro x y hh
    apply Subtype.ext
    exact Multiplicative.toAdd.injective (v.injective (congrArg Subtype.val hh))
  exact (hb.2.1.central_sylow_fixers_card_le m hρi P B hB).trans
    ((Nat.card_le_card_of_injective f hfi).trans
      (BinaryLinearThree.card_sylow_natural_fixed_le_two Q))

/-- The faithful normalizer omega-center of the original natural L₃ block
has order at most two, retaining the possible central attachment of U(L). -/
theorem constrained_binaryThree_plusOmega_bound (d : CaseIComponentData T M Mc V)
    (hb : IsSL3EvenBlock d.L 1) (hs : Chapter1.IsSylowIn 2 d.SL d.L) :
    Nat.card d.plusOmega ≤ 2 := by
  obtain ⟨P,hP⟩ := hs
  let B := d.plusOmega.map d.plusAction
  have hB : ∀ a ∈ B, ∀ y ∈ P, a y * y⁻¹ ∈ center d.L := by
    rintro a ⟨x,hx,rfl⟩ y hy
    have hyS : (y : G) ∈ d.S := (hP ▸ mem_map_of_mem d.L.subtype hy).1
    have hyN : (y : G) ∈ d.sylowNormalizer := ⟨hyS,d.L.le_normalizer y.property⟩
    have hyplus : d.componentPlusHom y ∈ d.plus d.sylowNormalizer :=
      mem_map_of_mem d.plusMap hyN
    have hc := (mem_omegaOneCenterAmbient_iff _ _).mp hx |>.2.2
    have he : d.componentPlusHom (d.plusAction x y * y⁻¹) = 1 := by
      rw [map_mul,map_inv,d.plusAction_component,←hc _ hyplus,mul_inv_cancel_right,mul_inv_cancel]
    have hh : d.plusAction x y * y⁻¹ ∈ d.componentPlusHom.ker := he
    rwa [d.componentPlusHom_ker] at hh
  have hh := binaryThree_sylow_fixers hb P B hB
  rwa [card_map_of_injective d.plusAction_injective] at hh

/-- The original seed is nontrivial in the same faithful omega-center. -/
theorem PreExclusionSource.constrained_binaryThree_plusOmega_card
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* Matrix.PSL3Two.SL) : Nat.card d.plusOmega = 2 := by
  have hb := (s.constrained_binaryThree_block (h := h) hG hempty hM hJ hu hf e).1
  obtain ⟨hi,_,_⟩ := s.constrained_binaryThree_inputs (h := h) hG hempty hM hJ hu hf e
  have hnZ := (d.central_seed_le_radical hG h hM.1.2 hu
    s.core_nontrivial s.sylow_normalizes_MZ).trans hi.normalizes
  have hZ1T := d.marked_le_sylow h hM.1.2
  have hZne := d.central_seed_plus_ne_bot hu hZ1T hnZ
  have hne : d.plusOmega ≠ ⊥ := by
    intro he
    exact hZne (bot_unique (he ▸ d.central_seed_plus_le_omega hZ1T hnZ))
  have hlo := (one_lt_card_iff_ne_bot _).mpr hne
  have hhi := d.constrained_binaryThree_plusOmega_bound hb s.component_sylow
  omega

/-- The literal cubic residual of the opposite parabolic has exactly C_S(L)
as its S-centralizer. No block or omega-center premise remains. -/
theorem PreExclusionSource.constrained_binaryThree_residual_centralizer
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* Matrix.PSL3Two.SL) :
    d.ConstrainedCentralizerIdentity := by
  have hc := s.constrained_binaryThree_plusOmega_card (h := h) hG hempty hM hJ hu hf e
  have hout := (s.constrained_binaryThree_parabolic_geometry (h := h)
    hG hempty hM hJ hu hf e).2.2.2
  exact s.source_residual_centralizer (h := h) hG hfull hM.1.2 hu hc hout

private theorem binaryThree_fixer_parabolic
    {A : Type*} [_root_.Group A] [Finite A] (hb : IsSL3EvenBlock A 1)
    (P : Sylow 2 A) (a : MulAut A) (ha : a ≠ 1)
    (hP : ∀ x ∈ P, a x * x⁻¹ ∈ center A) :
    ∃ J : Subgroup A, IsCoatom J ∧ ∀ x ∈ J, a x * x⁻¹ ∈ center A := by
  obtain ⟨F,_,_,hF,ρ,⟨m⟩,hρ⟩ := hb.2.2
  have hfield : Nat.card F = 2 := by simpa using hF
  let _ := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hfield)).symm
  let e := Atlas.fieldEquivSL 3 eF
  let v := Representation.SpecialLinearFieldTransport.natural 3 eF
  have hρi : Function.Injective ρ := by
    intro g j he
    apply Matrix.SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.ext
    intro w
    have hh := congrArg (fun k : MulAut (Multiplicative (Fin 3 → F)) =>
      (k (Multiplicative.ofAdd w)).toAdd) he
    simp only [hρ] at hh
    exact hh
  have hk : IsPGroup 2 m.actor.ker := by
    rw [BlockModuleModel.actor,MonoidHom.ker_comp_of_injective _ _ m.quotientIso.injective,
      QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let : _root_.Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) F) :=
    Atlas.sl_perfect 3 (by decide)
  let : _root_.Group.IsPerfect A := hb.2.1.twoPerfect.isPerfect_of_surjective_pGroup_kernel
    m.actor m.actor_surjective hk
  obtain ⟨u,hu,_⟩ := hb.2.1.automorphism_eq_conj_of_central_sylow m hρi P a hP
  let w := m.moduleIso (QuotientGroup.mk' (blockFixed A) u)
  have hw : w ≠ 1 := by
    intro hh
    have hz : (u : A) ∈ center A := (QuotientGroup.eq_one_iff u).mp
      (m.moduleIso.map_eq_one_iff.mp hh)
    apply ha
    rw [hu]
    ext x
    change (u : A) * x * (u : A)⁻¹ = x
    rw [←mem_center_iff.mp hz x,mul_inv_cancel_right]
  have hw0 : v w.toAdd ≠ 0 := by
    intro hh
    apply hw
    exact Multiplicative.toAdd.injective (v.injective (hh.trans v.map_zero.symm))
  let B := MulAction.stabilizer Matrix.PSL3Two.SL (v w.toAdd)
  have hmax : IsCoatom B := by
    obtain ⟨g,hg⟩ := BinaryLinearThree.natural_transitive_nonzero ![1,0,0]
      (v w.toAdd) (by decide) hw0
    have hstd : MulAction.stabilizer Matrix.PSL3Two.SL
        (![1,0,0] : BinaryLinearThree.Vector) = Matrix.PSL3Two.pointParabolicSL := by
      rw [←Matrix.PSL3Two.Fano.stabilizer_flagPoint_SL]
      ext k
      change k • (![1,0,0] : BinaryLinearThree.Vector) = ![1,0,0] ↔
        k • Matrix.PSL3Two.flagPoint = Matrix.PSL3Two.flagPoint
      exact ⟨fun hh => Subtype.ext hh,fun hh => congrArg Subtype.val hh⟩
    change IsCoatom (MulAction.stabilizer Matrix.PSL3Two.SL (v w.toAdd))
    change g • (![1,0,0] : BinaryLinearThree.Vector) = v w.toAdd at hg
    rw [←hg,MulAction.stabilizer_smul_eq_stabilizer_map_conj,hstd]
    exact ((MulAut.conj g).mapSubgroup.isCoatom_iff _).mpr
      Matrix.PSL3Two.isCoatom_pointParabolicSL
  let q := e.toMonoidHom.comp m.actor
  refine ⟨B.comap q,isCoatom_comap_of_surjective
    (e.surjective.comp m.actor_surjective) hmax,?_⟩
  intro x hx
  have hfix : ρ (m.actor x) w = w := by
    apply Multiplicative.toAdd.injective
    apply v.injective
    change BinaryLinearThree.W (e (m.actor x)) (v w.toAdd) = v w.toAdd at hx
    rw [←Representation.SpecialLinearFieldTransport.natural_action 3 eF] at hx
    exact (congrArg v (hρ _ _)).trans hx
  have hh : QuotientGroup.mk' (blockFixed A) (blockConjugate A x u) =
      QuotientGroup.mk' (blockFixed A) u :=
    m.moduleIso.injective ((m.intertwining x u).trans hfix)
  have hz : x * (u : A) * x⁻¹ * (u : A)⁻¹ ∈ center A := by
    have hh' := QuotientGroup.eq_iff_div_mem.mp hh
    simp only [div_eq_mul_inv] at hh'
    change (x * (u : A) * x⁻¹) * (u : A)⁻¹ ∈ center A at hh'
    exact hh'
  have hz' := (center A).inv_mem hz
  rw [hu]
  simpa only [MulAut.conj_apply,mul_inv_rev,inv_inv,mul_assoc] using hz'

/-- The marked intersection is the literal centralizer of the original seed,
including the central attachment allowed by the natural block definition. -/
theorem PreExclusionSource.constrained_binaryThree_centralizing
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* Matrix.PSL3Two.SL) :
    d.ML = d.L ⊓ centralizer (centralInvolutions T : Set G) := by
  have hb := (s.constrained_binaryThree_block (h := h) hG hempty hM hJ hu hf e).1
  have hc := s.constrained_binaryThree_plusOmega_card (h := h) hG hempty hM hJ hu hf e
  obtain ⟨w,hw,hunique⟩ := (Nat.card_eq_two_iff' (1 : d.plusOmega)).mp hc
  have hw' : (w : d.ComponentPlus) ≠ 1 := fun hh => hw (Subtype.ext hh)
  have ha : d.plusAction w ≠ 1 := fun hh => hw'
    (d.plusAction_injective (hh.trans (map_one d.plusAction).symm))
  obtain ⟨P,hP⟩ := s.component_sylow
  have hfix : ∀ x ∈ P, d.plusAction w x * x⁻¹ ∈ center d.L := by
    intro x hx
    have hxS : (x : G) ∈ d.S := (hP ▸ mem_map_of_mem d.L.subtype hx).1
    have hxplus : d.componentPlusHom x ∈ d.plus d.sylowNormalizer :=
      mem_map_of_mem d.plusMap ⟨hxS,d.L.le_normalizer x.property⟩
    have hc := (mem_omegaOneCenterAmbient_iff _ _).mp w.property |>.2.2
    have he : d.componentPlusHom (d.plusAction w x * x⁻¹) = 1 := by
      rw [map_mul,map_inv,d.plusAction_component,←hc _ hxplus,mul_inv_cancel_right,mul_inv_cancel]
    have hh : d.plusAction w x * x⁻¹ ∈ d.componentPlusHom.ker := he
    rwa [d.componentPlusHom_ker] at hh
  obtain ⟨J,hJmax,hJfix⟩ := binaryThree_fixer_parabolic hb P _ ha hfix
  have hJC : J ≤ (centralizer (centralInvolutions T : Set G)).comap d.L.subtype := by
    intro x hx
    apply s.source_plus_centralizer_lifts (h := h) hfull hM.1.2
    intro z hz
    have hz' : z ∈ d.plusOmega :=
      (s.source_central_seed_plus (h := h) hfull hM.1.2 hu hc) ▸ hz
    by_cases hz1 : z = 1
    · rw [hz1,one_mul,mul_one]
    · have he : (⟨z,hz'⟩ : d.plusOmega) = w :=
        hunique _ (fun he => hz1 (congrArg Subtype.val he))
      have hzW : z = w := congrArg Subtype.val he
      rw [hzW]
      have hh : d.componentPlusHom (d.plusAction w x * x⁻¹) = 1 := by
        change d.plusAction w x * x⁻¹ ∈ d.componentPlusHom.ker
        rw [d.componentPlusHom_ker]
        exact hJfix x hx
      rw [map_mul,map_inv,mul_inv_eq_one] at hh
      rw [d.plusAction_component] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
  have hloc := s.local_intersections (h := h) hG hu hM.1.2
  have hnot : d.ML.subgroupOf d.L ≠ ⊤ := by
    intro he
    apply hloc.2.2.1.ne
    have hh := congrArg (Subgroup.map d.L.subtype) he
    rw [map_subgroupOf_eq_of_le (show d.ML ≤ d.L from inf_le_right),
      ←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hJM : J ≤ d.ML.subgroupOf d.L := fun x hx =>
    hloc.2.2.2.2.2 ⟨x.property,hJC hx⟩
  have he : d.ML.subgroupOf d.L = J := (hJmax.le_iff_eq hnot).mp hJM
  apply le_antisymm _ hloc.2.2.2.2.2
  intro x hx
  exact ⟨hx.2,hJC (he ▸ (show (⟨x,hx.2⟩ : d.L) ∈ d.ML.subgroupOf d.L from hx))⟩

/-- The original binary-three FF row supplies the entire L₃ alternative,
with both parabolics under the same literal quotient marking. -/
theorem PreExclusionSource.constrained_binaryThree
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* Matrix.PSL3Two.SL) :
    ∃ t : (d.L ⧸ pCore 2 d.L) ≃* Matrix.PSL3Two.SL,
      (∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k)) ∧
      d.ConstrainedLinearParabolic t d.ML ∧
      d.ConstrainedLinearParabolic t (M ⊓ d.L) ∧
      Nat.card d.plusOmega = 2 ∧ d.ConstrainedL3Alternative ∧ d.ConstrainedAlternatives := by
  obtain ⟨t,ht,hML,hM',_⟩ := s.constrained_binaryThree_source_parabolics (h := h)
    hG hempty hM hJ hu hf e
  obtain ⟨hmarked,hselected,hgen,_⟩ := s.constrained_binaryThree_parabolic_geometry (h := h)
    hG hempty hM hJ hu hf e
  have hd : d.ML ≠ M ⊓ d.L := by
    intro hh
    rw [←hh,sup_idem] at hgen
    exact (s.local_intersections (h := h) hG hu hM.1.2).2.2.1.ne hgen
  have ha : d.ConstrainedL3Alternative := {
    block := (s.constrained_binaryThree_block (h := h) hG hempty hM hJ hu hf e).1
    marked_parabolic := hmarked
    selected_parabolic := hselected
    distinct := hd
    centralizing := s.constrained_binaryThree_centralizing (h := h)
      hG hempty hM hJ hu hfull hf e
    centralizers := s.constrained_binaryThree_residual_centralizer (h := h)
      hG hempty hM hJ hu hfull hf e }
  exact ⟨t,ht,hML,hM',s.constrained_binaryThree_plusOmega_card (h := h)
    hG hempty hM hJ hu hf e,ha,.linearThree ha⟩

/-- The later exchanged selection retains the faithful omega-center order. -/
theorem ExchangedSource.constrained_binaryThree_plusOmega_card
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (h : PreparedChosenModule T M V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* Matrix.PSL3Two.SL) : Nat.card d.plusOmega = 2 := by
  have hb := (s.constrained_binaryThree_block h hG hempty hM hJ hu hf e).1
  obtain ⟨hi,_,_⟩ := s.constrained_binaryThree_inputs h hG hempty hM hJ hu hf e
  have hnZ := (d.central_seed_le_radical hG h hM.1.2 hu
    s.core_nontrivial s.sylow_normalizes_MZ).trans hi.normalizes
  have hZ1T := d.marked_le_sylow h hM.1.2
  have hZne := d.central_seed_plus_ne_bot hu hZ1T hnZ
  have hne : d.plusOmega ≠ ⊥ := by
    intro he
    exact hZne (bot_unique (he ▸ d.central_seed_plus_le_omega hZ1T hnZ))
  have hlo := (one_lt_card_iff_ne_bot _).mpr hne
  have hhi := d.constrained_binaryThree_plusOmega_bound hb s.component_sylow
  omega

/-- The proved later L₃ obstruction excludes the original FF row when the
same component has the original cubic source and exchanged selection. -/
theorem ExchangedSource.not_constrained_binaryThree_of_preExclusion
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (x : d.ExchangedSource) (s : d.PreExclusionSource h.normalized 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    (hf : generalizedFitting d.L = pCore 2 d.L) :
    ¬ Nonempty (d.normalizerImage d.L ≃* Matrix.PSL3Two.SL) := by
  rintro ⟨e⟩
  obtain ⟨_,_,_,_,_,ha,_⟩ := s.constrained_binaryThree (h := h)
    hG hempty hM hJ hu hfull hf e
  exact x.no_constrained_l3 (h := h) s hG hempty hM.1.2 hu ha

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Whole L₃ block reconstruction at the actual original marker, with both
source primes, the original quotient marking and the earlier residual premise. -/
theorem PreparedChosenModule.source_preExclusion_constrained_binaryThree_block
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (generalizedFitting d.L = pCore 2 d.L →
        ∀ e : d.normalizerImage d.L ≃* Matrix.PSL3Two.SL,
          IsSL3EvenBlock d.L 1 ∧
            ∃ t : (d.L ⧸ pCore 2 d.L) ≃* Matrix.PSL3Two.SL,
              ∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) =
                e (d.toNormalizerImage d.L k)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hf e =>
    s.constrained_binaryThree_block (h := h) hG hempty hM hJ hu hf e⟩
/-- Full original L₃ catalogue row at the actual marker, retaining both
source primes, all ambient hypotheses, and the original 15.1.14 premise. -/
theorem PreparedChosenModule.source_preExclusion_constrained_binaryThree
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (generalizedFitting d.L = pCore 2 d.L →
        ∀ e : d.normalizerImage d.L ≃* Matrix.PSL3Two.SL,
          ∃ t : (d.L ⧸ pCore 2 d.L) ≃* Matrix.PSL3Two.SL,
            (∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k)) ∧
            d.ConstrainedLinearParabolic t d.ML ∧
            d.ConstrainedLinearParabolic t (M ⊓ d.L) ∧
            Nat.card d.plusOmega = 2 ∧ d.ConstrainedL3Alternative ∧ d.ConstrainedAlternatives) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hf e =>
    s.constrained_binaryThree (h := h) hG hempty hM hJ hu hfull hf e⟩

end CFSG.Quasithin.Chapter15.Section01
