module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.LocalThompson
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.CoreMarking
public import Theory.Representation.BinaryPermutation.AlternatingEightSylowFixed
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerOmegaSplitting

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ReducedChosenMovement

/-!
# The original Sylow fixed space and central omega

When C_V(L) is nontrivial, the original augmentation cover identifies V
with the seven-dimensional A8 core. A Sylow two-subgroup of A8 is transitive
on the eight letters, so its fixed core vectors are constant. Consequently
C_V(T) is contained in C_V(L), with equality when T normalizes V.

Thompson generation L=[L,J(T)] forces J(T) to move V. B.5.1(2), on the
original faithful reduced action, then gives [R₂(LT),L]=V. The normal
closure of Ω₁Z(T) is reduced and splits into its moved part and its central
part by B.2.14. Its moved part lies in V; the fixed-space calculation
therefore makes Ω₁Z(T) centralize L. This proves source 12.6.1(6).
NormalizerConjugacy applies the result at the original preferred point.

Source: Aschbacher--Smith 12.6.1(2,6), printed p.823, and B.2.14/B.5.1(2),
printed pp.78,99, combined manuscript of 1 March 2004.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory BinaryPermutation
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

omit [IsElementaryAbelian 2 V] in
private theorem sylow_in_component (D : Section02.ChosenModule T L V) :
    ∃ P : Sylow 2 L, ∀ l ∈ (P : Subgroup L), (l : G) ∈ (T : Subgroup G) := by
  let H := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf H
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  let S : Sylow 2 H := T.subtype le_sup_right
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal A
  let e : A ≃* L := subgroupOfEquivOfLe (le_sup_left : L ≤ H)
  refine ⟨R.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  rintro l ⟨r,hr,rfl⟩
  rw [hR] at hr
  exact hr

/-- In the original nonsplit core, a T-fixed vector is already L-fixed. -/
theorem OrthogonalMarking.sylow_fixed_le_global_fixed
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) (hz : ZV L V ≠ ⊥) :
    V ⊓ centralizer (T : Set G) ≤ ZV L V := by
  obtain ⟨E,hE,_⟩ := D.core_marking_of_fixed_ne_bot chosen hz
  obtain ⟨P,hP⟩ := sylow_in_component chosen
  let S := P.mapSurjective D.actorMap_surjective
  intro x hx
  let u : Additive V := Additive.ofMul ⟨x,hx.1⟩
  have hf : ∀ a ∈ (S : Subgroup (alternatingGroup (Fin 8))),
      alternatingCoreRepresentation (Fin 8) a (E u) = E u := by
    rintro a ⟨l,hl,rfl⟩
    rw [←hE]
    apply congrArg E
    apply Additive.toMul.injective
    apply Subtype.ext
    change (l : G) * x * (l : G)⁻¹ = x
    rw [mem_centralizer_iff.mp hx.2 l (hP l hl),mul_inv_cancel_right]
  have hc := alternatingEight_core_sylow_fixed_constant S (E u) hf
  have hfix := (core_fixed_iff_constant (by simp : 3 ≤ Nat.card (Fin 8)) (E u)).mpr hc
  apply (mem_fixedSeed_iff L V chosen.normalizes u).mp
  change ∀ l : L, seedRepresentation L V chosen.normalizes l u = u
  intro l
  apply E.injective
  rw [hE]
  exact hfix (D.actorMap l)

/-- The fixed-subgroup equality in source 12.6.1(2), with the original T. -/
theorem OrthogonalMarking.sylow_fixed_eq_global_fixed
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) (hz : ZV L V ≠ ⊥)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    V ⊓ centralizer (T : Set G) = ZV L V := by
  apply le_antisymm (D.sylow_fixed_le_global_fixed chosen hz)
  exact le_inf inf_le_left (le_centralizer_iff.mp
    (le_sup_right.trans (D.join_centralizes_fixed chosen hTV)))

open Section02.RecognitionSource.FusionReducibleNormalizer

/-- The B.2.14 omega splitting reduces the earlier centralization input to
its precise original moved-module bound. -/
theorem SourceHypothesis.component_centralizes_Z_of_reduced_movement
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (hz : ZV L V ≠ ⊥)
    (hm : ⁅(reducedTwoSubgroup (LT T L)).map (LT T L).subtype,L⁆ ≤ V) :
    L ≤ centralizer (Z T : Set G) := by
  let J := LT T L
  let P : Sylow 2 J := T.subtype le_sup_right
  let E := Stellmacher.omegaOneCenterAmbient (P : Subgroup J)
  let W := normalClosure (E : Set J)
  have hWR : blockOmegaModule T L ≤ (reducedTwoSubgroup J).map J.subtype :=
    map_mono (omegaCenter_normalClosure_reduced P (join_characteristicTwo H.source)).le_reducedPSubgroup
  have hmov : ⁅blockOmegaModule T L,J⁆ ≤ V := by
    change ⁅blockOmegaModule T L,L ⊔ (T : Subgroup G)⁆ ≤ V
    rw [blockOmegaModule_commutator_join H.chosen]
    exact (commutator_mono hWR le_rfl).trans hm
  let C := (W ⊓ center J).map J.subtype
  have hc : C ≤ centralizer (J : Set G) := by
    rintro _ ⟨c,⟨_,hcc⟩,rfl⟩ a ha
    exact congrArg Subtype.val (mem_center_iff.mp hcc ⟨a,ha⟩)
  have hs : blockOmegaModule T L ≤ V ⊔ C := by
    have hh := congrArg (Subgroup.map J.subtype)
      (omegaCenter_subgroup_normalClosure_split P (join_characteristicTwo H.source) E le_rfl)
    rw [Subgroup.map_sup,map_commutator,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh.le.trans (sup_le_sup hmov le_rfl)
  have hVC : V ≤ normalizer (C : Set G) :=
    (le_centralizer_iff.mp (hc.trans (centralizer_le
      (H.chosen.le_sylow.trans (show (T : Subgroup G) ≤ J from le_sup_right))))).trans
        (Subgroup.centralizer_le_normalizer _)
  apply le_centralizer_iff.mpr
  intro z hzZ
  have hzE : z ∈ omegaCenterIn (T : Subgroup G) := by
    rwa [omegaCenterIn_eq_omegaOneAmbient]
  have hzsup := hs (omegaCenter_le_blockOmegaModule hzE)
  have hzprod : z ∈ (V : Set G) * (C : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right V C hVC]
    exact hzsup
  obtain ⟨v,hv,c,hcC,rfl⟩ := hzprod
  have hcT := centralizer_le (show (T : Subgroup G) ≤ J from le_sup_right) (hc hcC)
  have hvT : v ∈ centralizer (T : Set G) := by
    have hh := (centralizer (T : Set G)).mul_mem
      ((mem_omegaCenterIn_iff _ _).mp hzE).2.1
      ((centralizer (T : Set G)).inv_mem hcT)
    simpa only [mul_inv_cancel_right] using hh
  exact (centralizer (L : Set G)).mul_mem
    (D.sylow_fixed_le_global_fixed H.chosen hz ⟨hv,hvT⟩).2
    (centralizer_le (show L ≤ J from le_sup_left) (hc hcC))

omit [IsElementaryAbelian 2 V] in
/-- Thompson generation supplies the faithful FF premise on the actual reduced
module. Nontrivial C_V(L) makes its moved space the original Irr⁺ choice. -/
theorem SourceHypothesis.reduced_commutator_eq_of_thompson_generation
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (hz : ZV L V ≠ ⊥)
    (hgen : L = ⁅L,Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆) :
    ⁅(reducedTwoSubgroup (LT T L)).map (LT T L).subtype,L⁆ = V := by
  have hmove : ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (V : Set G) := by
    intro hc
    have hLC : L ≤ centralizer (V : Set G) := hgen.le.trans
      ((commutator_mono le_rfl hc).trans
        (le_normalizer_iff_commutator_le_right.mp
          (H.chosen.normalizes.trans (normalizer_le_normalizer_centralizer V))))
    exact H.chosen.ne_bot (H.chosen.eq_commutator.trans
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hLC)))
  apply le_antisymm
  · exact Section02.RecognitionSource.ReducedChosenMovement.reduced_commutator_le_chosen_of_thompson_movement
      H.source H.chosen hz hmove
  · exact H.chosen.eq_commutator.le.trans (commutator_mono H.chosen.le_reduced le_rfl)

/-- Source 12.6.1(6), on the original module and original Sylow central omega. -/
theorem SourceHypothesis.component_centralizes_Z_of_thompson_generation
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (hz : ZV L V ≠ ⊥)
    (hgen : L = ⁅L,Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆) :
    L ≤ centralizer (Z T : Set G) :=
  H.component_centralizes_Z_of_reduced_movement D hz
    (H.reduced_commutator_eq_of_thompson_generation hz hgen).le

end CFSG.Quasithin.Chapter12.Section06
