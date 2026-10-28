module
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.FourBlockRecognition
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.ThompsonFusion
public import Theory.GroupTheory.SylowIndexTwoOvergroup

/-!
# Odd point-centralizer indices and the original fixed line

For the selected weight-four vector, a two-subgroup properly above T₄ is
an ambient Sylow subgroup, since |T:T₄|=2. In the large Thompson branch,
conjugation into the original central omega contradicts the completed
four-block lifting theorem. Thus T₄ is Sylow in its full centralizer.
The small Thompson branch uses the already proved Thompson fusion theorem.
Transport within the actual L-orbit gives 12.6.19(2) at every weight-four
vector, with no extra placement or permutation-containment premise.

The other nonidentity weights have their full centralizer in M when the
original fixed space is nontrivial. Consequently every original vector has
odd relative centralizer index. Weight-four vectors are not two-central;
together with the existing nonsingular exclusion, this identifies the
two-central vectors of V with C_V(L). The same original quotient marking
then makes every transporter of its nonidentity fixed vector back into V
fix that vector and belong to M.

The final source application constructs the compatible core marking and
supplies these conclusions on the original V, C_V(L), and projection.
Full element fusion, the remaining fixed-free HS/J₄ centralizer exclusions,
weak closure and fixed-space elimination still remain with this source
owner. Neither full 12.6.2 nor 12.6.23 is asserted. Earlier invariance/TI
retain qt-d-1222-source, and final discharge retains qt-d-12634-source.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
12.6.19(2) and the fixed-line fusion step, printed p.828.
-/

public section
open Subgroup Theory.GroupTheory BinaryPermutation Stellmacher
open Theory.GroupTheory.DoubleCoverCentralizer
open BinaryPermutation.TerminalOrthogonal
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

omit [Finite G] in
/-- Equal weights give an actual L-conjugator on the original marked core. -/
theorem OrthogonalMarking.core_orbit_of_same_weight
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l u, E (seedRepresentation L V chosen.normalizes l u) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E u))
    (v w : V) (hw : wordWeight (E (Additive.ofMul v)).val =
      wordWeight (E (Additive.ofMul w)).val) :
    ∃ l : L, conjugation L V chosen.normalizes l v = w := by
  obtain ⟨a,ha⟩ := exists_even_permutation_of_weight
    (by decide : 3 ≤ Fintype.card (Fin 8)) _ _ hw
  obtain ⟨l,rfl⟩ := D.actorMap_surjective a
  refine ⟨l,Additive.ofMul.injective (E.injective ?_)⟩
  exact (hE l (Additive.ofMul v)).trans (Subtype.ext ha)

private theorem odd_index_of_sylow_le
    {S C B : Subgroup G} (hs : Chapter1.IsSylowIn 2 S C) (hSB : S ≤ B) :
    Odd (B.relIndex C) := by
  obtain ⟨P,hP⟩ := hs
  have hp : (P : Subgroup C) ≤ B.subgroupOf C := by
    intro p hp
    exact hSB (hP ▸ mem_map_of_mem C.subtype hp)
  exact Nat.not_even_iff_odd.mp (fun he => P.not_dvd_index
    ((even_iff_two_dvd.mp he).trans (index_dvd_of_le hp)))

private theorem selected_weight_four_not_twoCentral
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hz : ZV L V ≠ ⊥)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ Q T L)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l u, E (seedRepresentation L V H.chosen.normalizes l u) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E u))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point)
    (l : L) (w : V) (hw : (w : G) = (l : G)*(v : G)*(l : G)⁻¹) :
    ¬ TwoCentral (w : G) := by
  intro hc
  obtain ⟨P,hP⟩ := hc.exists_sylow_le_centralizer
  have hw2 : (w : G)^2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ w.property
  obtain ⟨a,_,ha⟩ := exists_sylow_conjugator_into_Z P T (w : G) hw2 hP
  have hw1 : (w : G) ≠ 1 := by
    intro he
    have hv1 : v = 1 := Subtype.ext ((MulAut.conj (l : G)).injective
      (hw.symm.trans (he.trans (map_one _).symm)))
    have hp : FourBlockPoint.point = 0 := by rw [←hv,hv1]; exact E.map_zero
    exact one_ne_zero (congrArg (fun x : core (Fin 8) => x.val 0) hp)
  have ha1 : MulAut.conj a (w : G) ≠ 1 := fun he => hw1
    ((MulAut.conj a).injective (he.trans (map_one _).symm))
  have hLZ := H.component_centralizes_Z_of_thompson_generation D hz
    (H.eq_commutator_thompson_of_not_le_core hJ)
  have hcM := H.central_omega_point_control hLZ _ ha ha1
  have hnot := (H.weight_four_conjugator_mem D hTV E hE v hv l w hw a _ rfl hcM).2
  exact hnot (le_centralizer_iff.mp hLZ ha)

/-- Source 12.6.19(2), for every original marked weight-four vector. -/
theorem SourceHypothesis.weight_four_centralizer_odd_index
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (hz : ZV L V ≠ ⊥)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l u, E (seedRepresentation L V H.chosen.normalizes l u) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E u))
    (u : V) (hu : wordWeight (E (Additive.ofMul u)).val = 4) :
    Odd ((Mv L (u : G)).relIndex (Gv (u : G))) := by
  by_cases hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ Q T L
  · exact H.centralizer_odd_index_of_thompson_le_core hJ u
  let v : V := (E.symm FourBlockPoint.point).toMul
  have hv : E (Additive.ofMul v) = FourBlockPoint.point := E.apply_symm_apply _
  obtain ⟨l,hs,hi⟩ := D.exists_weight_four_sylow_position H.chosen hTV hTI E hE v hv
  let w := conjugation L V H.chosen.normalizes l v
  have hn := selected_weight_four_not_twoCentral H D hTV hz hJ E hE v hv l w rfl
  have hsG : Chapter1.IsSylowIn 2 (Tv T (w : G)) (Gv (w : G)) := by
    apply Chapter1.isSylowIn_iff.mpr
    refine ⟨T.isPGroup'.to_le inf_le_left,inf_le_right,?_⟩
    intro P hp hTP hPG
    rcases (two_group_over_index_two_sylow T (Tv T (w : G)) P inf_le_left hi hp hTP).2 with he | ⟨S,hS⟩
    · exact he
    · exfalso
      apply hn
      have hSC : (S : Subgroup G) ≤ Gv (w : G) := hS ▸ hPG
      have hwT : (w : G) ∈ (S : Subgroup G) :=
        (show V ≤ Tv T (w : G) from le_inf H.chosen.le_sylow (V_le_Gv w)).trans
          (hTP.trans hS.ge) w.property
      refine ⟨S,hwT,mem_center_iff.mpr ?_⟩
      intro s
      exact Subtype.ext (mem_centralizer_singleton_iff.mp (hSC s.property))
  have hwgt : wordWeight (E (Additive.ofMul w)).val = 4 := by
    rw [show Additive.ofMul w = seedRepresentation L V H.chosen.normalizes l
      (Additive.ofMul v) from rfl,hE]
    change wordWeight (representation (Fin 8) (D.actorMap l).val (E (Additive.ofMul v)).val) = 4
    rw [wordWeight_permute,hv]
    decide
  obtain ⟨b,hb⟩ := D.core_orbit_of_same_weight H.chosen E hE w u (hwgt.trans hu.symm)
  have hb' : MulAut.conj (b : G) (w : G) = (u : G) := congrArg Subtype.val hb
  have hC : (Gv (w : G)).map (MulAut.conj (b : G)).toMonoidHom = Gv (u : G) := by
    rw [Gv,map_pointCentralizer,hb']; rfl
  have hsU := (Chapter1.IsSylowIn.map_iff (MulAut.conj (b : G)).toMonoidHom
    (MulAut.conj (b : G)).injective).mpr hsG
  rw [hC] at hsU
  apply odd_index_of_sylow_le hsU
  apply le_inf
  · have hTM : Tv T (w : G) ≤ M L := inf_le_left.trans H.chosen.sylow_normalizes_component
    have hh := map_mono (f := (MulAut.conj (b : G)).toMonoidHom) hTM
    exact hh.trans_eq (mem_normalizer_iff_map_conj_eq.mp
      ((M L).le_normalizer (L.le_normalizer b.property)))
  · exact (map_mono (show Tv T (w : G) ≤ Gv (w : G) from inf_le_right)).trans_eq hC
/-- Clause 12.6.19(2) also gives an odd local index at every original vector:
nonsingular and fixed vectors already have their whole centralizer in M. -/
theorem SourceHypothesis.fixed_space_centralizer_odd_index
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    (u : V) : Odd ((Mv L (u : G)).relIndex (Gv (u : G))) := by
  by_cases hu1 : u = 1
  · subst u
    have hT : (T : Subgroup G) ≤ Gv (1 : G) := by
      intro t _
      exact mem_centralizer_singleton_iff.mpr (by simp)
    apply odd_index_of_sylow_le (S := (T : Subgroup G))
    · exact ⟨T.subtype hT,map_subgroupOf_eq_of_le hT⟩
    · exact le_inf H.chosen.sylow_normalizes_component hT
  obtain ⟨E,hE,hproj⟩ := D.core_marking_of_fixed_ne_bot H.chosen hz
  by_cases hu4 : wordWeight (E (Additive.ofMul u)).val = 4
  · exact H.weight_four_centralizer_odd_index D hTV hTI hz E hE u hu4
  have hC : Gv (u : G) ≤ M L := by
    by_cases hq : (Submodule.Quotient.mk (Additive.ofMul u) : Vhat L V H.chosen.normalizes) = 0
    · exact H.fixed_vector_centralizer_le D hTV u
        ((mem_fixedSeed_iff L V H.chosen.normalizes _).mp
          ((Submodule.Quotient.mk_eq_zero _).mp hq))
        (fun he => hu1 (Subtype.ext he))
    · apply H.nonsingular_centralizer_le_of_fixed D hTV hTI hz u
      intro hs
      have hn : coreToNatural (Fin 8) (E (Additive.ofMul u)) ≠ 0 := by
        rw [hproj]
        exact fun hh => hq (D.coordinates.injective (hh.trans (map_zero _).symm))
      apply hu4
      exact (EightGeometry.nonzero_singular_core_iff _).mp ⟨hn,by rw [hproj]; exact hs⟩
  have he : Mv L (u : G) = Gv (u : G) := inf_eq_right.mpr hC
  rw [he,relIndex_self]
  decide

private theorem sylow_odd_relIndex (S C : Subgroup G)
    (hs : Chapter1.IsSylowIn 2 S C) : Odd (S.relIndex C) :=
  odd_index_of_sylow_le hs le_rfl

/-- Every weight-four vector in the original seven-space fails to be two-central. -/
theorem SourceHypothesis.weight_four_not_twoCentral
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l u, E (seedRepresentation L V H.chosen.normalizes l u) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E u))
    (u : V) (hu : wordWeight (E (Additive.ofMul u)).val = 4) :
    ¬ TwoCentral (u : G) := by
  let v : V := (E.symm FourBlockPoint.point).toMul
  have hv : E (Additive.ofMul v) = FourBlockPoint.point := E.apply_symm_apply _
  obtain ⟨l,hs,hi⟩ := D.exists_weight_four_sylow_position H.chosen hTV hTI E hE v hv
  let w := conjugation L V H.chosen.normalizes l v
  have hwgt : wordWeight (E (Additive.ofMul w)).val = 4 := by
    rw [show Additive.ofMul w = seedRepresentation L V H.chosen.normalizes l
      (Additive.ofMul v) from rfl,hE]
    change wordWeight (representation (Fin 8) (D.actorMap l).val (E (Additive.ofMul v)).val) = 4
    rw [wordWeight_permute,hv]
    decide
  obtain ⟨b,hb⟩ := D.core_orbit_of_same_weight H.chosen E hE u w (hu.trans hwgt.symm)
  intro hc
  have hwc : TwoCentral (w : G) := by
    have hh := hc.map (MulAut.conj (b : G))
    rwa [show MulAut.conj (b : G) (u : G) = (w : G) from congrArg Subtype.val hb] at hh
  have hodd := (sylow_odd_relIndex _ _ hs).mul
    (H.weight_four_centralizer_odd_index D hTV hTI hz E hE w hwgt)
  rw [relIndex_mul_relIndex (Tv T (w : G)) (Mv L (w : G)) (Gv (w : G))
    (le_inf (inf_le_left.trans H.chosen.sylow_normalizes_component) inf_le_right) inf_le_right] at hodd
  have hgOdd := Nat.not_even_iff_odd.mp (fun he =>
    hwc.not_dvd_centralizer_index (even_iff_two_dvd.mp he))
  have hh : Odd ((Tv T (w : G)).relIndex (Gv (w : G)) * (Gv (w : G)).index) := hodd.mul hgOdd
  rw [relIndex_mul_index (H := Tv T (w : G)) (K := Gv (w : G)) inf_le_right,←relIndex_mul_index
    (show Tv T (w : G) ≤ (T : Subgroup G) from inf_le_left),hi] at hh
  exact (Nat.not_even_iff_odd.mpr hh) (even_iff_two_dvd.mpr (dvd_mul_right 2 _))

/-- In the original seven-space the two-central vectors are exactly C_V(L),
including the identity. This uses the original quotient projection. -/
theorem SourceHypothesis.fixed_space_twoCentral_iff_fixed
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    (u : V) : TwoCentral (u : G) ↔ (u : G) ∈ ZV L V := by
  constructor
  · intro hc
    obtain ⟨E,hE,hproj⟩ := D.core_marking_of_fixed_ne_bot H.chosen hz
    by_cases hq : (Submodule.Quotient.mk (Additive.ofMul u) : Vhat L V H.chosen.normalizes) = 0
    · exact (mem_fixedSeed_iff L V H.chosen.normalizes _).mp
        ((Submodule.Quotient.mk_eq_zero _).mp hq)
    have hns : ¬ D.Nonsingular u := by
      intro hu
      obtain ⟨P,hP⟩ := hc.exists_sylow_le_centralizer
      exact H.nonsingular_no_ambient_sylow D hTV hTI u hu P hP
    have hn : coreToNatural (Fin 8) (E (Additive.ofMul u)) ≠ 0 := by
      rw [hproj]
      exact fun hh => hq (D.coordinates.injective (hh.trans (map_zero _).symm))
    have hw : wordWeight (E (Additive.ofMul u)).val = 4 :=
      (EightGeometry.nonzero_singular_core_iff _).mp
        ⟨hn,by rw [hproj]; exact not_ne_iff.mp hns⟩
    exact (H.weight_four_not_twoCentral D hTV hTI hz E hE u hw hc).elim
  · intro hu
    have hc := le_centralizer_iff.mp (le_sup_right.trans
      (D.join_centralizes_fixed H.chosen hTV)) hu
    refine ⟨T,H.chosen.le_sylow u.property,mem_center_iff.mpr ?_⟩
    intro t
    exact Subtype.ext (mem_centralizer_iff.mp hc t t.property)

omit [Finite G] in
private theorem fixed_word
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hproj : ∀ u, coreToNatural (Fin 8) (E u) = D.coordinates (Submodule.Quotient.mk u))
    (v : V) (hv : v ≠ 1) (hfix : (v : G) ∈ ZV L V) :
    E (Additive.ofMul v) = EightCore.oneWord := by
  have hq : (Submodule.Quotient.mk (Additive.ofMul v) : Vhat L V chosen.normalizes) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ((mem_fixedSeed_iff L V chosen.normalizes _).mpr hfix)
  have he : coreToNatural (Fin 8) (E (Additive.ofMul v)) = 0 := by rw [hproj,hq,map_zero]
  rcases (EightGeometry.coreToNatural_eq_zero _).mp he with he | he
  · have hh : E (Additive.ofMul v) = 0 := Subtype.ext he
    exact (hv (Additive.ofMul.injective (E.injective (hh.trans E.map_zero.symm)))).elim
  · exact Subtype.ext he

/-- The original nonidentity fixed vector is weakly closed in V. Every
transporter taking it back into V actually belongs to M and fixes it. -/
theorem SourceHypothesis.fixed_vector_fusion_conjugator
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    (v : V) (hv : v ≠ 1) (hfix : (v : G) ∈ ZV L V)
    (g : G) (hg : MulAut.conj g (v : G) ∈ V) :
    MulAut.conj g (v : G) = v ∧ g ∈ M L := by
  let w : V := ⟨MulAut.conj g (v : G),hg⟩
  have hw : (w : G) ∈ ZV L V :=
    (H.fixed_space_twoCentral_iff_fixed D hTV hTI hz w).mp
      (((H.fixed_space_twoCentral_iff_fixed D hTV hTI hz v).mpr hfix).map (MulAut.conj g))
  have hw1 : w ≠ 1 := fun he => hv (Subtype.ext ((MulAut.conj g).injective
    ((congrArg Subtype.val he).trans (map_one _).symm)))
  obtain ⟨E,_,hproj⟩ := D.core_marking_of_fixed_ne_bot H.chosen hz
  have he : w = v := Additive.ofMul.injective (E.injective
    ((fixed_word H.chosen D E hproj w hw1 hw).trans
      (fixed_word H.chosen D E hproj v hv hfix).symm))
  have hf : MulAut.conj g (v : G) = v := congrArg Subtype.val he
  exact ⟨hf,H.fixed_vector_centralizer_le D hTV v hfix
    (fun he => hv (Subtype.ext he))
    (mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hf))⟩

/-- The same compatible original marking now supplies every odd-index
assertion and separates its fixed line from all other ambient fusion classes. -/
theorem SourceHypothesis.exists_core_marking_centralizer_control
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥) :
    ∃ E : Additive V ≃ₗ[ZMod 2] core (Fin 8),
      (∀ l u, E (seedRepresentation L V H.chosen.normalizes l u) =
        alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E u)) ∧
      (∀ u, coreToNatural (Fin 8) (E u) = D.coordinates (Submodule.Quotient.mk u)) ∧
      (∀ u : V, Odd ((Mv L (u : G)).relIndex (Gv (u : G)))) ∧
      (∀ u : V, TwoCentral (u : G) ↔ (u : G) ∈ ZV L V) ∧
      ∀ (u : V) (g : G), wordWeight (E (Additive.ofMul u)).val = 8 →
        MulAut.conj g (u : G) ∈ V → MulAut.conj g (u : G) = u ∧ g ∈ M L := by
  obtain ⟨E,hE,hproj⟩ := D.core_marking_of_fixed_ne_bot H.chosen hz
  refine ⟨E,hE,hproj,H.fixed_space_centralizer_odd_index D hTV hTI hz,
    H.fixed_space_twoCentral_iff_fixed D hTV hTI hz,?_⟩
  intro u g hu hg
  have he := (EightCore.weight_eight_iff _).mp hu
  have hu1 : u ≠ 1 := by
    intro h1
    have hh : E (Additive.ofMul u) = 0 := by rw [h1]; exact E.map_zero
    exact EightCore.oneWord_ne_zero (he.symm.trans hh)
  have hq : (Submodule.Quotient.mk (Additive.ofMul u) : Vhat L V H.chosen.normalizes) = 0 := by
    apply D.coordinates.injective
    rw [map_zero,←hproj]
    exact (EightGeometry.coreToNatural_eq_zero _).mpr (Or.inr (congrArg Subtype.val he))
  exact H.fixed_vector_fusion_conjugator D hTV hTI hz u hu1
    ((mem_fixedSeed_iff L V H.chosen.normalizes _).mp ((Submodule.Quotient.mk_eq_zero _).mp hq)) g hg

end CFSG.Quasithin.Chapter12.Section06
