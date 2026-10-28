module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFiveSpace
public import Theory.Representation.HigherFieldBorelFixedSpaces.Sylow
public import Theory.Representation.BinaryConjugationSection.FixedMoving

/-!
# The escaping A5 Sylow-normalizer residual in source 6.2.7

A natural SL2(4) moved space has zero fixed space under every Sylow
normalizer, and that normalizer is two-perfect. Its direct fixed complement
therefore identifies the normalizer fixed space with the full component
fixed space. Surjective Sylow-normalizer transport and residual transport
apply this to the genuine C-component lift in C_G(U).

If the embedded residual lay in M, the field-plane centralizer calculation
would make it fix the image of the original natural layer in the original
closure quotient. The fixed-space identity would then make the original
four-group offender fix that image, killing its nonzero moved plane.
Thus the actual residual escapes M, with the original quotient maps retained.

The Chapter12 companion supplies every premise from the chosen module and
the checked natural-component section. This proves the first paragraph of
the final A5 contradiction; the remaining cubic/field-automorphism argument
and 6.2.8--11 are not asserted here.
Source: Aschbacher--Smith, 6.2.7, printed pp.683--684.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open Representation.SL2NaturalOffenders.FixedField ConjugateFixedSpaces
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem field_centralizer_commutator
    {L M B U : Subgroup G} {n : ℕ} [IsElementaryAbelian 2 B]
    (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUne : U ≠ ⊥)
    (P : Subgroup G) (hPL : P ≤ normalizer (L : Set G))
    (hPB : P ≤ normalizer (B : Set G)) :
    ⁅P ⊓ centralizer (U : Set G), B⁆ ≤ U := by
  have hnat := hnatural
  obtain ⟨F, _, _, _, _, e, f, hf⟩ := hnatural
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨t, htM, htB, hU, K, _, _, _, hK, a, σ, hσ, hσsq, hσact⟩ := hfield
  obtain ⟨hasq, _⟩ := field_quotientActor e a t σ hσ hσsq hσact
  have hi : Function.Involutive (vectorActor f ⟨t, htB⟩) := by
    apply intertwiner_involutive_of_fixed (quotientActor e t) _
      (vectorActor_intertwines e f hf t htB) hasq
    obtain ⟨u, hune⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
    let v : B := ⟨u, (hU.le u.property).1⟩
    refine ⟨(f v).toAdd, ?_, ?_⟩
    · intro hz
      have hv : v = 1 := f.injective (by simpa using congrArg Multiplicative.ofAdd hz)
      exact hune (Subtype.ext (congrArg (fun b : B => (b : G)) hv))
    · apply (vectorActor_fixed_iff f ⟨t, htB⟩ _).mpr
      simpa [v] using (hU.le u.property).2
  have hsquare (b : B) : B.normalizerMonoidHom ⟨t, htB⟩
      (B.normalizerMonoidHom ⟨t, htB⟩ b) = b := by
    apply Subtype.ext
    have hh := congrArg (fun v => (f.symm (Multiplicative.ofAdd v) : G)) (hi (f b).toAdd)
    rw [vectorActor_coe, vectorActor_coe] at hh
    change (t : G) * ((t : G) * (b : G) * (t : G)⁻¹) * (t : G)⁻¹ = b
    simpa only [ofAdd_toAdd, f.symm_apply_apply] using hh
  apply commutator_le.mpr
  intro r hr b hb
  rcases field_fixedSpace_actor_dichotomy hnat t htB hU hUne
      ⟨K, inferInstance, inferInstance, inferInstance, hK, a, σ, hσ, hσsq, hσact⟩
      ⟨r, hPL hr.1⟩ (hPB hr.1) hr.2 with he | he
  · have hc := congrArg (fun E : MulAut B => (E ⟨b,hb⟩ : G)) he
    have hc' : r * b * r⁻¹ = b := hc
    rw [commutatorElement_def, hc', mul_inv_cancel]
    exact U.one_mem
  · have hc := congrArg (fun E : MulAut B => (E ⟨b,hb⟩ : G)) he
    have hc' : r * b * r⁻¹ = (t : G) * b * (t : G)⁻¹ := hc
    rw [commutatorElement_def, hc']
    let E := B.normalizerMonoidHom ⟨t, htB⟩
    let v : B := E ⟨b,hb⟩ * (⟨b,hb⟩ : B)⁻¹
    have hv : E v = v := by
      change E (E ⟨b,hb⟩ * (⟨b,hb⟩ : B)⁻¹) = E ⟨b,hb⟩ * (⟨b,hb⟩ : B)⁻¹
      rw [map_mul, map_inv, hsquare]
      have hpow (x : B) : x⁻¹ = x := by
        apply inv_eq_of_mul_eq_one_left
        apply Subtype.ext
        change (x : G) * (x : G) = 1
        simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : G) x.property
      rw [hpow, hpow]
      exact mul_comm _ _
    have hvU : (v : G) ∈ U := by
      rw [hU]
      refine ⟨v.property, mem_centralizer_singleton_iff.mpr ?_⟩
      have hv' : (t : G) * (v : G) * (t : G)⁻¹ = v := congrArg Subtype.val hv
      exact (mul_inv_eq_iff_eq_mul.mp hv').symm
    exact hvU


namespace LocalFieldQuotientAction

private theorem natural_normalizer_fixed
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (K : Subgroup D)
    (F : BinaryField) (hF : F.degree = 2)
    (hn : IsLinearNatural ((invariantSubspace ρ K (moved ρ K)
      (subspaceCommutator_invariant ρ ⊤ K)).toRepresentation) F 2)
    (hc : IsCompl (moved ρ K) (fixedSpace ρ K)) (S : Sylow 2 K) :
    IsPPerfect 2 (normalizer (S : Set K)) ∧
      fixedSpace ρ ((normalizer (S : Set K)).map K.subtype) = fixedSpace ρ K := by
  obtain ⟨e⟩ := hn
  let V := invariantSubspace ρ K (moved ρ K) (subspaceCommutator_invariant ρ ⊤ K)
  have hcard : 4 ≤ Nat.card F.Carrier := by rw [F.card_eq,hF]; decide
  obtain ⟨hperfect,hzero⟩ := HigherFieldBorelFixedSpaces.natural_sylowNormalizer hcard S
    V.toRepresentation e.groupEquiv e.linearEquiv.toLinearMap e.intertwines
  refine ⟨hperfect,le_antisymm ?_ (fixedSpace_antitone ρ (map_subtype_le _))⟩
  intro v hv
  obtain ⟨w,hw,z,hz,rfl⟩ := Submodule.mem_sup.mp (show v ∈ moved ρ K ⊔ fixedSpace ρ K from
    hc.sup_eq_top.symm ▸ Submodule.mem_top)
  have hwfix : (⟨w,hw⟩ : V) ∈ fixedSpace V.toRepresentation (normalizer (S : Set K)) := by
    intro a
    apply Subtype.ext
    have hh := hv ⟨a,mem_map_of_mem K.subtype a.property⟩
    change ρ (a : D) (w+z) = w+z at hh
    have hzfix : ρ (a : D) z = z := hz (a : K)
    rw [map_add,hzfix] at hh
    exact add_right_cancel hh
  have hwzero : w = 0 := congrArg Subtype.val
    (e.linearEquiv.injective ((hzero ⟨w,hw⟩ hwfix).trans e.linearEquiv.map_zero.symm))
  simpa only [hwzero,zero_add] using hz

private theorem lifted_normalizer_residual_fixed
    {D E W : Type*} [Group D] [Finite D] [Group E] [Finite E]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (K : Subgroup D)
    (F : BinaryField) (hF : F.degree = 2)
    (hn : IsLinearNatural ((invariantSubspace ρ K (moved ρ K)
      (subspaceCommutator_invariant ρ ⊤ K)).toRepresentation) F 2)
    (hc : IsCompl (moved ρ K) (fixedSpace ρ K))
    (q : E →* K) (hq : Function.Surjective q) (S : Sylow 2 E) :
    fixedSpace ρ (((pResidual 2 (normalizer (S : Set E))).map
      (normalizer (S : Set E)).subtype).map (K.subtype.comp q)) = fixedSpace ρ K := by
  let S' := S.mapSurjective hq
  let N := normalizer (S : Set E)
  let N' := normalizer (S' : Set K)
  obtain ⟨hp,hfix⟩ := natural_normalizer_fixed ρ K F hF hn hc S'
  have hN : N.map q = N' := S.normalizer_map_surjective q hq
  rw [←map_map,
    map_embedded_pResidual,hN,(pResidual_eq_top_iff 2 N').mpr hp,
    ←MonoidHom.range_eq_map,range_subtype]
  exact hfix


/-- On the literal field-plane quotient, the residual of a lifted component
Sylow normalizer cannot lie in the original maximal subgroup. -/
theorem field_component_normalizer_escape
    {T : Sylow 2 G} {L M R A U : Subgroup G} {n : ℕ}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfield : IsInvolutoryFieldFixedSpace L M (layer L R) U n) (hUne : U ≠ ⊥)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (action (layer L R) U).range W)
    (c : BinaryConjugationSection (Centralizer U)
      (conjugateSpanBy (layer L R) (Centralizer U)) U
      (ρ.comp (action (layer L R) U).rangeRestrict))
    (hAH : A ≤ Centralizer U)
    (hmove : c.imageSpace ⁅A,layer L R⁆ ≠ ⊥)
    (J : Subgroup (action (layer L R) U).range)
    (hIJ : (A.subgroupOf (Centralizer U)).map (action (layer L R) U).rangeRestrict ≤ J)
    (F : BinaryField) (hF : F.degree = 2)
    (hn : IsLinearNatural ((invariantSubspace ρ J (moved ρ J)
      (subspaceCommutator_invariant ρ ⊤ J)).toRepresentation) F 2)
    (hc : IsCompl (moved ρ J) (fixedSpace ρ J))
    (K : Subgroup (Centralizer U))
    (hK : K.map (action (layer L R) U).rangeRestrict = J) (S : Sylow 2 K) :
    ¬ ((((pResidual 2 (normalizer (S : Set K))).map
      (normalizer (S : Set K)).subtype).map K.subtype).map
        (Centralizer U).subtype) ≤ M := by
  let := h.layer_elementary
  let B := layer L R
  let H := Centralizer U
  let π := (action B U).rangeRestrict
  let q : K →* J := (π.comp K.subtype).codRestrict J (by
    intro k
    exact hK ▸ mem_map_of_mem π k.property)
  have hq : Function.Surjective q := by
    intro j
    obtain ⟨k,hk,he⟩ := (show (j : (action B U).range) ∈ K.map π from hK.symm ▸ j.property)
    exact ⟨⟨k,hk⟩,Subtype.ext he⟩
  have hfixed := lifted_normalizer_residual_fixed ρ J F hF hn hc q hq S
  let N := normalizer (S : Set K)
  let D := (pResidual 2 N).map N.subtype
  let P := M ⊓ H
  intro hDM
  have hnat : IsNaturalModule L B n := hnatural.1 ▸ hnatural.2.1
  have hUB : U ≤ B := hfield.choose_spec.2.2.1.le.trans inf_le_left
  have hPL : P ≤ normalizer (L : Set G) :=
    inf_le_left.trans ((normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal)
  have hPB : P ≤ normalizer (B : Set G) := hE.localCentralizer_le_normalizer hUne hUB
  have hcomm := field_centralizer_commutator hnat hfield hUne P hPL hPB
  have hfix : c.imageSpace B ≤ fixedSpace ρ J := by
    rw [←hfixed]
    intro w hw a
    obtain ⟨k,hk,he⟩ := a.property
    obtain ⟨b,hb,rfl⟩ := (c.mem_imageSpace_iff B w).mp hw
    change ρ (a : (action B U).range) (c.coordinates b).toAdd = _
    rw [←he]
    change (ρ.comp π) (k : H) (c.coordinates b).toAdd = _
    apply (c.fixed_coordinate_iff_commutator_mem (k : H) b).mpr
    have hkH : ((k : H) : G) ∈ H := (k : H).property
    have hkM : ((k : H) : G) ∈ M := hDM
      (mem_map_of_mem H.subtype (mem_map_of_mem K.subtype hk))
    have hh := hcomm (commutator_mem_commutator (show ((k : H) : G) ∈ P ⊓ H from
      ⟨⟨hkM,hkH⟩,hkH⟩) hb)
    simpa only [commutatorElement_inv] using U.inv_mem hh
  apply hmove
  rw [c.imageSpace_commutator A B hAH (le_conjugateSpanBy B H),
    subspaceCommutator_comp_map]
  exact (subspaceCommutator_eq_bot_iff ρ (c.imageSpace B) _).mpr
    (hfix.trans (fixedSpace_antitone ρ hIJ))


/-- The actual A5 component and its lift have escaping Sylow-normalizer
residuals. The quotient equivalence agrees with the original action map. -/
theorem plane_natural_component_escape
    {T : Sylow 2 G} {L M R A U : Subgroup G} {n : ℕ}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N → N = M)
    (hfield : IsInvolutoryFieldFixedSpace L M (layer L R) U n) (hUc : Nat.card U = 4)
    (hout : ¬ Centralizer U ≤ normalizer (layer L R : Set G))
    (hAH : A ≤ Centralizer U)
    [IsElementaryAbelian 2 (space (layer L R) U)]
    (hs : PlaneNaturalSection (layer L R) A U) :
    let H := Centralizer U
    let π := (action (layer L R) U).rangeRestrict
    let I := (A.subgroupOf H).map π
    ∃ J : Subgroup (action (layer L R) U).range,
      IsComponent _ J ∧ ⁅J,I⁆ = J ∧ Nonempty (J ≃* alternatingGroup (Fin 5)) ∧
      ∃ K : Subgroup H, K.IsCComponent ∧ K.map π = J ∧
        (∃ e : (K ⧸ pCore 2 K) ≃* J, ∀ k : K,
          ((e (QuotientGroup.mk' (pCore 2 K) k) : J) : (action (layer L R) U).range) = π k) ∧
        ∀ S : Sylow 2 K, ¬ ((((pResidual 2 (normalizer (S : Set K))).map
          (normalizer (S : Set K)).subtype).map K.subtype).map H.subtype) ≤ M := by
  let H := Centralizer U
  let π := (action (layer L R) U).rangeRestrict
  obtain ⟨ρ,c,hf,hI,hq,hIc,hm,hd,hcodim,hfam,hmin,hmodels,⟨J,hJ,hJI,_⟩,hmark⟩ := hs
  obtain ⟨hirr,he,⟨F,hF,hn⟩,⟨S,hS⟩,hc⟩ := hmodels J hJ hJI
  obtain ⟨K,hK,hKJ,e,hke⟩ := action_component_lift h hnatural hE hfactor hu hfield hUc hout J hJ
  refine ⟨J,hJ,hJI,he,K,hK,hKJ,⟨e,hke⟩,?_⟩
  intro P
  have hUne : U ≠ ⊥ := by intro he; rw [he,card_bot] at hUc; contradiction
  apply field_component_normalizer_escape h hnatural hE hfield hUne ρ c hAH
    (fun hz => ?_) J (by rw [hS]; exact map_subtype_le _) F hF hn hc K hKJ P
  rw [hm,hz,finrank_bot] at hd
  contradiction

end LocalFieldQuotientAction
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
