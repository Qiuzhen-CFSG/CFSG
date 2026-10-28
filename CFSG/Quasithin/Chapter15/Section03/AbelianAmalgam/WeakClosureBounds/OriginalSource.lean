module
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl.Selected
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.ChapterE.Section03.OddCore.SolvableApplication
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.Basic
public import CFSG.Quasithin.ChapterE.Section03.SourceContainment
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.HypothesisVerification.OriginalSource
/-!
# Original weak-closure bounds in the abelian-span case

The original natural action identifies the automizer of V and gives localA(V)=1.
The actual centralizer normalizer is unique, so the original fusion and
abelian-span conclusions imply 15.3.63: rank at least three forces w>1 and
excludes generation one in every outside subgroup. Thus a single generation-one
witness proves globalR(V)=2. Finite descent selects a minimal outside subgroup
inside the centralizer partner, on which the following source module applies.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.62–65, printed pp.1151–1152.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.OriginalSource
open ChapterA.Section05To06 ChapterE
variable {G : Type*} [Group G] [Finite G]

private noncomputable def sourceAutomizerEquiv
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G) (hM : IsOrderingMaximal d.T d.M) :
    LocalActionQuotient d.Z d.M ≃* Automizer d.V := by
  let f : d.M →* Automizer d.V :=
    d.V.normalizerMonoidHom.rangeRestrict.comp (Subgroup.inclusion d.action.normalizes)
  have hs : Function.Surjective f := by
    intro a
    obtain ⟨n,hn⟩ := d.V.normalizerMonoidHom.rangeRestrict_surjective a
    have hnM : (n : G) ∈ d.M := by
      rw [InitialSource.UniformControl.source_local_eq_normalizer hG d.T hM.1]
      exact n.property
    exact ⟨⟨n,hnM⟩,hn⟩
  have hk : f.ker = localActionKernel d.Z d.M := by
    ext m
    change f m = 1 ↔ _
    rw [Subtype.ext_iff]
    change d.V.normalizerMonoidHom ⟨m,d.action.normalizes m.property⟩ = 1 ↔ _
    rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
    rfl
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hs)

theorem localA_eq_one_from_original
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M) [IsElementaryAbelian 2 d.V] :
    localA d.V = 1 := by
  let e := sourceAutomizerEquiv hG d hM
  have hHM : d.M ∈ Chapter1.HOver G (d.T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let : Group.IsSolvable (LocalActionQuotient d.Z d.M) :=
    InitialSource.localActionQuotient_isSolvable
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hG d.T hempty hHM
  have hsolv : Group.IsSolvable (Automizer d.V) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  have hcore : pCore 2 (Automizer d.V) = ⊥ := by
    rw [← pCore_map_iso 2 e,
      InitialSource.localActionQuotient_twoReduced_from_source hG d.T hHM,Subgroup.map_bot]
  have hk : d.action.actor.ker = localActionKernel d.Z d.M := d.action.ker_actor
  let a := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective d.action.actor d.action.onto)
  have hc : Nat.card (Automizer d.V) = 72 := by
    rw [← Nat.card_congr e.toEquiv,Nat.card_congr a.toEquiv,RegularWreathProduct.card]
    have hp : Nat.card OrthogonalPlaneActor = 6 := by
      rw [Nat.card_eq_fintype_card]
      decide +kernel
    rw [hp]
    norm_num [OrthogonalPlaneIndex,Nat.card_eq_fintype_card]
  exact OddCore.moduleA_eq_one_of_solvable_of_even (automizerRepresentation d.V)
    (automizerRepresentation_injective d.V) hsolv hcore (by rw [hc]; decide)


/-- A.5.7 on the actual centralizer, upgraded from its relative normalizer. -/
theorem normalizer_sylow_centralizer_unique_from_original
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G) (hM : IsOrderingMaximal d.T d.M) :
    maximalTwoLocalOvergroups (normalizer
      (((d.T : Subgroup G) ⊓ centralizer (d.V : Set G) : Subgroup G) : Set G)) = {d.M} := by
  have hHM : d.M ∈ Chapter1.HOver G (d.T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let : IsElementaryAbelian 2 d.V := InitialSource.localModule_elementary_from_source hG d.T hHM
  let := (InitialSource.localModule_reduced_from_source hG d.T hHM).normal
  have hVM : d.V ≤ d.M := localModule_le d.T d.sylow_le
  have hu := InitialSource.UniformControl.source_unique_overgroup_sylow_centralizer
    hG d.T hM d.V le_rfl hVM
  let R := (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)
  have hVT : d.V ≤ (d.T : Subgroup G) :=
    (d.action.le_planeStabilizer d.T d.sylow_le hVM 1).trans inf_le_left
  have hVR : d.V ≤ R := le_inf hVT (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hR : R ≠ ⊥ := by
    intro he
    have hv : d.V = ⊥ := bot_unique (hVR.trans_eq he)
    have hc : Nat.card d.V = 16 := d.action.card_vector
    rw [hv] at hc
    simp at hc
  have hn : IsTwoLocal (normalizer (R : Set G)) :=
    ⟨R,hR,d.T.isPGroup'.to_le inf_le_left,rfl⟩
  obtain ⟨N,hRN,hN⟩ := Finite.exists_le_maximal hn
  have hNM : N = d.M := by
    have hmem : N ∈ maximalTwoLocalOvergroups (d.M ⊓ normalizer (R : Set G)) :=
      ⟨hN,inf_le_right.trans hRN⟩
    rw [hu] at hmem
    exact Set.mem_singleton_iff.mp hmem
  have hRM : normalizer (R : Set G) ≤ d.M := hRN.trans_eq hNM
  ext N
  constructor
  · intro hN
    have hm : N ∈ maximalTwoLocalOvergroups (d.M ⊓ normalizer (R : Set G)) :=
      ⟨hN.1,inf_le_right.trans hN.2⟩
    rw [hu] at hm
    exact hm
  · rintro rfl
    exact ⟨hM.1.1,hRM⟩

/-- Source E.3.35 on the prescribed Sylow of the actual outside group.
This form needs an actual E-generation witness and no infimum-attainment assumption. -/
theorem outside_not_eGenerated_one_of_bounds
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G) (hM : IsOrderingMaximal d.T d.M)
    [IsElementaryAbelian 2 d.V]
    (hr : (1 : ℕ∞) < globalR d.V) (hw : (1 : ℕ∞) < globalW d.V d.T)
    {H : Subgroup G} (hH : H ∈ sylowOutsideFamily d.T d.M) :
    ¬ IsEGenerated 1 H := by
  intro hgen
  have hVM : d.V ≤ d.M := localModule_le d.T d.sylow_le
  have hVT : d.V ≤ (d.T : Subgroup G) :=
    (d.action.le_planeStabilizer d.T d.sylow_le hVM 1).trans inf_le_left
  have hVne : d.V ≠ ⊥ := by
    intro he
    have hc : Nat.card d.V = 16 := d.action.card_vector
    rw [he] at hc
    simp at hc
  have hT : HypothesisE322 d.V d.T := ⟨hVne,hVT,d.sylow_le.trans d.action.normalizes⟩
  apply hH.2
  apply SourceContainment.le_of_isEGenerated hT (d.T.subtype hH.1.2) (hgen _) 
    (normalizer_sylow_centralizer_unique_from_original hG d hM) _ _ hw hr
  · exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
      (InitialSource.UniformControl.source_local_eq_normalizer hG d.T hM.1).symm.le)
  · change _ ≤ ((d.T : Subgroup G).subgroupOf H).map H.subtype
    rw [map_subgroupOf_eq_of_le hH.1.2]
    exact inf_le_left


/-- Original15.3.62(2), with only the independent45 and50 conclusions remaining. -/
theorem intersecting_conjugates_commute_from_original
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M)
    [IsElementaryAbelian 2 d.V]
    [IsMulCommutative (conjugateSpanBy d.V d.Mc)] :
    ∀ g : G, d.V ⊓ d.V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅d.V,d.V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  let q := FusionCore.OriginalCoordinates.quadraticAction d.action
  let a := FusionCore.OriginalCoordinates.standardAction d.action
  have hf := FusionCore.CosetSetup.OriginalSource.source_fusion_inputs hG d hM hfixed
  have hp := FusionCore.OriginalCoordinates.plane_definite d.action 1
  have h46 := FusionCore.lemma_15_3_46_of_earlier_inputs q hf hp
  obtain ⟨k,c⟩ := FusionCore.orthogonalCoordinateModel_and_fusionCalculations q hf hp
  have hz : (c.z : G) ≠ 1 := fun he => c.z_ne_one (Subtype.ext he)
  have hZ : d.Z = zpowers (c.z : G) := by
    let z : d.Z := ⟨c.z,c.z_central⟩
    have hz' : z ≠ 1 := fun he => hz (congrArg Subtype.val he)
    have he : zpowers z = ⊤ := zpowers_eq_top_of_prime_card hf.central_order hz'
    have hm := congrArg (fun K : Subgroup d.Z => K.map d.Z.subtype) he
    rw [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,range_subtype] at hm
    exact hm.symm
  apply lemma_15_3_62_2 (Mc := d.Mc) a c.z.property hz
  · exact (FusionCore.OriginalCoordinates.quadraticAction_singular d.action c.z).mp c.z_singular
  · rw [←hZ]
    exact FusionCore.CosetSetup.OriginalSource.source_partner_eq hG d hempty hM hu hmany
  · exact fun g hg => h46.1 c.z c.z.property g hg
  · intro g hg x
    apply (FusionCore.OriginalCoordinates.quadraticAction_singular d.action _).mp
    exact (h46.2.1.1 g hg).2 ⟨x,x.property.1⟩ x.property


/-- The actual original47 normalizing-conjugate alternative used in64. -/
theorem commutator_alternative_from_original
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hM : IsOrderingMaximal d.T d.M)
    (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M)
    [IsElementaryAbelian 2 d.V] :
    ∀ x ∈ centralizer (d.ZS : Set G), ⁅d.V,zpowers x⁆ = ⊥ ∨
      ∀ g : G, d.V.map (MulAut.conj g).toMonoidHom ≤
        normalizer ((⁅d.V,zpowers x⁆ : Subgroup G) : Set G) →
        d.V.map (MulAut.conj g).toMonoidHom ≤ centralizer (d.V : Set G) := by
  exact FusionCore.lemma_15_3_47_of_earlier_inputs
    (FusionCore.OriginalCoordinates.quadraticAction d.action)
    (FusionCore.CosetSetup.OriginalSource.source_fusion_inputs hG d hM hfixed)
    (FusionCore.OriginalCoordinates.plane_definite d.action 1)

/-- Original15.3.63(1): the local parameter and earlier fusion data are produced,
while the independent source45 and50 conclusions retain their original shapes. -/
theorem weakClosure_one_from_original
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M)
    [IsElementaryAbelian 2 d.V]
    [IsMulCommutative (conjugateSpanBy d.V d.Mc)]
    (hr : (3 : ℕ∞) ≤ globalR d.V) :
    indexedWeakClosure d.V d.T 1 ≤ (d.T : Subgroup G) ⊓ centralizer (d.V : Set G) ∧
      1 < globalW d.V d.T := by
  have hf := FusionCore.CosetSetup.OriginalSource.source_fusion_inputs hG d hM hfixed
  have hzero := FusionCore.weakClosure_zero_le_centralizer_of_earlier_inputs
    (FusionCore.OriginalCoordinates.quadraticAction d.action) hf
    (FusionCore.OriginalCoordinates.plane_definite d.action 1)
  exact lemma_15_3_63_1_of_localA (localA_eq_one_from_original hG d hempty hM) hr
    (d.sylow_le.trans d.action.normalizes) hzero
    (intersecting_conjugates_commute_from_original hG d hempty hM hu hmany hfixed)

/-- The actual generation-one witness is precisely what the final65 assembly
must construct. All of the63 arithmetic and local normalizer inputs are discharged. -/
theorem globalR_eq_two_of_original_generation_one
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M)
    [IsElementaryAbelian 2 d.V]
    [IsMulCommutative (conjugateSpanBy d.V d.Mc)]
    (hgen : ∃ H ∈ sylowOutsideFamily d.T d.M, IsEGenerated 1 H) : globalR d.V = 2 := by
  have hf := FusionCore.CosetSetup.OriginalSource.source_fusion_inputs hG d hM hfixed
  have hr := (FusionCore.lemma_15_3_46_of_earlier_inputs
    (FusionCore.OriginalCoordinates.quadraticAction d.action) hf
    (FusionCore.OriginalCoordinates.plane_definite d.action 1)).2.2.1
  have hlo : (2 : ℕ∞) ≤ globalR d.V := (ENat.add_one_le_iff (by norm_num)).mpr hr
  have hhi : globalR d.V ≤ 2 := by
    by_contra hnot
    have h3 : (3 : ℕ∞) ≤ globalR d.V :=
      (ENat.add_one_le_iff (by norm_num)).mpr (lt_of_not_ge hnot)
    have hw := (weakClosure_one_from_original hG d hempty hM hu hmany hfixed h3).2
    obtain ⟨H,hH,he⟩ := hgen
    exact outside_not_eGenerated_one_of_bounds hG d hM hr hw hH he
  exact le_antisymm hhi hlo


/-- Finite descent selects one original minimal outside group inside Mc.
This is sufficient for the final rank contradiction. -/
theorem exists_minimal_outside_le_partner_from_original
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard) :
    ∃ H : Subgroup G, H ≤ d.Mc ∧ H ∈ minimalSylowOutsideFamily d.T d.M := by
  have hne := (InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)).1
  have hMc : d.Mc ∈ maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) := by
    rw [hu]
    exact Set.mem_singleton d.Mc
  have hTMc : (d.T : Subgroup G) ≤ d.Mc :=
    (le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow d.T)).trans hMc.2
  have ho : d.Mc ∈ sylowOutsideFamily d.T d.M := by
    refine ⟨⟨Chapter1.mem_H_of_isTwoLocal hMc.1.1,hTMc⟩,?_⟩
    intro hle
    exact hne (le_antisymm hle (hMc.1.2 hM.1.1.1 hle))
  exact Finite.exists_le_minimal (p := fun H : Subgroup G => H ∈ sylowOutsideFamily d.T d.M) ho

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.OriginalSource
