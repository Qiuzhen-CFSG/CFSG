module
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.FixedSpaceCentralizers

/-!
# Fusion of the original weight-four orbit

The two-part of the full point-centralizer index is four on the nonsingular
orbits and two on the weight-four orbit. These values follow from the actual
Sylow positions, the completed odd-index theorem and conjugacy invariance.
Together with the fixed-line fusion theorem, they show that every ambient
conjugate of a weight-four vector lying in V has weight four. An actual
L-conjugator realizes that fusion. The 12.6.20(2) application supplies the
correcting centralizer conjugator on the original V, with coordinates
compatible with the unchanged quotient V/C_V(L).

The remaining fusion problem is reduced to weights two and six. Their
complementary representatives have equal full centralizers: TI makes each
controlled centralizer normalize V, and its action fixes the original
constant word. Any fusion failure therefore gives an element outside M
normalizing this full centralizer and carrying the weight-two point to its
product with the original fixed vector. Centralizer containment alone does
not discharge this normalizer case, and full 12.6.19(1) is not asserted here.

The two/six case, fixed-free HS/J4 centralizer exclusions, weak closure and
fixed-space elimination remain with this source owner. Neither full 12.6.2
nor 12.6.23 is asserted. Earlier invariance/TI retain qt-d-1222-source, and
final discharge retains qt-d-12634-source.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
12.6.19(1) and 12.6.20(2), printed pp.828--829.
-/

public section
open Subgroup Theory.GroupTheory BinaryPermutation
open BinaryPermutation.TerminalOrthogonal
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

private theorem odd_sylow_index {S C : Subgroup G}
    (hs : Chapter1.IsSylowIn 2 S C) : Odd (S.relIndex C) := by
  obtain ⟨P,rfl⟩ := hs
  have he : ((P : Subgroup C).map C.subtype).subgroupOf C = P :=
    comap_map_eq_self_of_injective C.subtype_injective _
  change Odd (((P : Subgroup C).map C.subtype).subgroupOf C).index
  rw [he]
  exact Nat.not_even_iff_odd.mp (fun h => P.not_dvd_index (even_iff_two_dvd.mp h))

omit [IsElementaryAbelian 2 V] in
private theorem point_index_two_part (u : V)
    (hs : Chapter1.IsSylowIn 2 (Tv T (u : G)) (Mv L (u : G)))
    (hi : Odd ((Mv L (u : G)).relIndex (Gv (u : G)))) :
    2 ^ (Gv (u : G)).index.factorization 2 =
      (Tv T (u : G)).relIndex (T : Subgroup G) := by
  have ho := (odd_sylow_index hs).mul hi
  rw [relIndex_mul_relIndex (Tv T (u : G)) (Mv L (u : G)) (Gv (u : G))
    (Chapter1.isSylowIn_iff.mp hs).2.1 inf_le_right] at ho
  have ht : ¬ 2 ∣ (T : Subgroup G).relIndex (Gv (u : G)) := by
    rw [←inf_relIndex_right]
    exact fun h => (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr h)
  have hh := (T.relIndex_eq_pow_factorization (Gv (u : G)) ht).symm
  simpa only [Tv,inf_relIndex_left] using hh

omit [Finite G] [IsElementaryAbelian 2 V] in
private theorem point_index_conj (u : G) (g : G) :
    (Gv (MulAut.conj g u)).index = (Gv u).index := by
  rw [Gv,←map_pointCentralizer]
  exact index_map_of_bijective (MulAut.conj g).bijective _

/-- The two-part of the full centralizer index is four at every original
nonsingular vector when the original fixed space is nontrivial. -/
theorem SourceHypothesis.fixed_space_nonsingular_centralizer_two_part
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    (u : V) (hu : D.Nonsingular u) :
    2 ^ (Gv (u : G)).index.factorization 2 = 4 := by
  obtain ⟨l,hw,hs,hi⟩ := D.exists_nonsingular_sylow_position H.chosen hTV hTI u hu
  have hh := (point_index_two_part _ hs
    (H.fixed_space_centralizer_odd_index D hTV hTI hz _)).trans hi
  change 2 ^ (Gv (MulAut.conj (l : G) (u : G))).index.factorization 2 = 4 at hh
  rwa [point_index_conj] at hh

/-- The two-part of the full centralizer index is two at every original
weight-four vector, retaining the same seven-dimensional core marking. -/
theorem SourceHypothesis.fixed_space_weight_four_centralizer_two_part
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l u, E (seedRepresentation L V H.chosen.normalizes l u) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E u))
    (u : V) (hu : wordWeight (E (Additive.ofMul u)).val = 4) :
    2 ^ (Gv (u : G)).index.factorization 2 = 2 := by
  let v : V := (E.symm FourBlockPoint.point).toMul
  have hv : E (Additive.ofMul v) = FourBlockPoint.point := E.apply_symm_apply _
  obtain ⟨l,hs,hi⟩ := D.exists_weight_four_sylow_position H.chosen hTV hTI E hE v hv
  have hh := (point_index_two_part _ hs
    (H.fixed_space_centralizer_odd_index D hTV hTI hz _)).trans hi
  change 2 ^ (Gv (MulAut.conj (l : G) (v : G))).index.factorization 2 = 2 at hh
  rw [point_index_conj] at hh
  obtain ⟨b,hb⟩ := D.core_orbit_of_same_weight H.chosen E hE v u (by
    rw [hv,hu]; decide)
  have he : MulAut.conj (b : G) (v : G) = (u : G) := congrArg Subtype.val hb
  rwa [←point_index_conj (v : G) (b : G),he] at hh

omit [Finite G] in
private theorem nonsingular_of_core_weight
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hproj : ∀ u, coreToNatural (Fin 8) (E u) = D.coordinates (Submodule.Quotient.mk u))
    (u : V) (hu : wordWeight (E (Additive.ofMul u)).val = 2 ∨
      wordWeight (E (Additive.ofMul u)).val = 6) : D.Nonsingular u := by
  have hf := (EightGeometry.nonsingular_core_iff (E (Additive.ofMul u))).mpr hu
  rw [hproj] at hf
  change Eight.form (D.coordinates (Submodule.Quotient.mk (Additive.ofMul u))) ≠ 0
  rw [hf]
  exact one_ne_zero

omit [Finite G] in
private theorem fixed_of_core_weight_eight
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hproj : ∀ u, coreToNatural (Fin 8) (E u) = D.coordinates (Submodule.Quotient.mk u))
    (u : V) (hu : wordWeight (E (Additive.ofMul u)).val = 8) :
    (u : G) ∈ ZV L V := by
  have he := (EightCore.weight_eight_iff _).mp hu
  have hq : (Submodule.Quotient.mk (Additive.ofMul u) : Vhat L V chosen.normalizes) = 0 := by
    apply D.coordinates.injective
    rw [map_zero,←hproj,he]
    exact (EightGeometry.coreToNatural_eq_zero _).mpr (Or.inr rfl)
  exact (mem_fixedSeed_iff L V chosen.normalizes _).mp ((Submodule.Quotient.mk_eq_zero _).mp hq)

/-- No ambient fusion takes an original weight-four vector into another
weight. This retains the quotient-compatible original coordinates. -/
theorem SourceHypothesis.fixed_space_weight_four_fusion
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l u, E (seedRepresentation L V H.chosen.normalizes l u) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E u))
    (hproj : ∀ u, coreToNatural (Fin 8) (E u) = D.coordinates (Submodule.Quotient.mk u))
    (u w : V) (hu : wordWeight (E (Additive.ofMul u)).val = 4)
    (hc : IsConj (u : G) (w : G)) :
    wordWeight (E (Additive.ofMul w)).val = 4 := by
  obtain ⟨g,hg⟩ := isConj_iff.mp hc
  have hidx : (Gv (w : G)).index = (Gv (u : G)).index := by
    rw [←hg]
    exact point_index_conj _ _
  have hu1 : u ≠ 1 := by
    intro hh
    subst u
    have hzero : E (Additive.ofMul (1 : V)) = 0 := E.map_zero
    rw [hzero,(EightCore.weight_zero_iff _).mpr rfl] at hu
    omega
  have hw1 : w ≠ 1 := fun he => hu1 (Subtype.ext ((MulAut.conj g).injective
    (hg.trans ((congrArg Subtype.val he).trans (map_one _).symm))))
  have hnonsingular : ¬ D.Nonsingular w := by
    intro hw
    have hi := H.fixed_space_nonsingular_centralizer_two_part D hTV hTI hz w hw
    rw [hidx,H.fixed_space_weight_four_centralizer_two_part D hTV hTI hz E hE u hu] at hi
    omega
  rcases EightCore.weights (E (Additive.ofMul w)) with hw | hw | hw | hw | hw
  · exact (hw1 (Additive.ofMul.injective (E.injective
      (((EightCore.weight_zero_iff _).mp hw).trans E.map_zero.symm)))).elim
  · exact (hnonsingular (nonsingular_of_core_weight H.chosen D E hproj w (Or.inl hw))).elim
  · exact hw
  · exact (hnonsingular (nonsingular_of_core_weight H.chosen D E hproj w (Or.inr hw))).elim
  · have hfix := fixed_of_core_weight_eight H.chosen D E hproj w hw
    have hcw := (H.fixed_space_twoCentral_iff_fixed D hTV hTI hz w).mpr hfix
    have hcu := hcw.map (MulAut.conj g).symm
    have he : (MulAut.conj g).symm (w : G) = (u : G) := by
      rw [←hg]
      exact (MulAut.conj g).symm_apply_apply _
    rw [he] at hcu
    exact (H.weight_four_not_twoCentral D hTV hTI hz E hE u hu hcu).elim

/-- L realizes every ambient fusion of an original weight-four point. -/
theorem SourceHypothesis.fixed_space_weight_four_orbit_control
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l u, E (seedRepresentation L V H.chosen.normalizes l u) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E u))
    (hproj : ∀ u, coreToNatural (Fin 8) (E u) = D.coordinates (Submodule.Quotient.mk u))
    (u : V) (hu : wordWeight (E (Additive.ofMul u)).val = 4)
    (g : G) (hg : MulAut.conj g (u : G) ∈ V) :
    ∃ l : L, MulAut.conj (l : G) (u : G) = MulAut.conj g (u : G) := by
  let w : V := ⟨MulAut.conj g (u : G),hg⟩
  have hw := H.fixed_space_weight_four_fusion D hTV hTI hz E hE hproj u w hu
    (isConj_iff.mpr ⟨g,rfl⟩)
  obtain ⟨l,hl⟩ := D.core_orbit_of_same_weight H.chosen E hE u w (hu.trans hw.symm)
  exact ⟨l,congrArg Subtype.val hl⟩

/-- The actual 12.6.20(2) correcting conjugator at every original
weight-four intersection point; its fusion premise is discharged. -/
theorem SourceHypothesis.fixed_space_weight_four_centralizer_conjugator
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l u, E (seedRepresentation L V H.chosen.normalizes l u) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E u))
    (hproj : ∀ u, coreToNatural (Fin 8) (E u) = D.coordinates (Submodule.Quotient.mk u))
    (u : V) (hu : wordWeight (E (Additive.ofMul u)).val = 4)
    (g : G) (hg : (u : G) ∈ V.map (MulAut.conj g).toMonoidHom) :
    ∃ c : Gv (u : G), V.map (MulAut.conj (c : G)).toMonoidHom =
      V.map (MulAut.conj g).toMonoidHom := by
  apply exists_centralizer_conjugator_of_element_fusion _ hg
  intro a ha
  obtain ⟨l,hl⟩ := H.fixed_space_weight_four_orbit_control D hTV hTI hz E hE hproj u hu a ha
  exact ⟨l,H.chosen.normalizes l.property,hl⟩

/-- In the original seven-space every possible failure of orbit preservation
is confined to interchange of weights two and six. The fixed line and the
weight-four orbit are already separated without further source premises. -/
theorem SourceHypothesis.fixed_space_fusion_weights
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l u, E (seedRepresentation L V H.chosen.normalizes l u) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E u))
    (hproj : ∀ u, coreToNatural (Fin 8) (E u) = D.coordinates (Submodule.Quotient.mk u))
    (u w : V) (hc : IsConj (u : G) (w : G)) :
    wordWeight (E (Additive.ofMul u)).val = wordWeight (E (Additive.ofMul w)).val ∨
      (wordWeight (E (Additive.ofMul u)).val = 2 ∧ wordWeight (E (Additive.ofMul w)).val = 6) ∨
      (wordWeight (E (Additive.ofMul u)).val = 6 ∧ wordWeight (E (Additive.ofMul w)).val = 2) := by
  have hz0 (a : V) : wordWeight (E (Additive.ofMul a)).val = 0 ↔ a = 1 := by
    rw [EightCore.weight_zero_iff]
    exact ⟨fun h => Additive.ofMul.injective (E.injective (h.trans E.map_zero.symm)),
      fun h => by rw [h]; exact E.map_zero⟩
  have h0 : wordWeight (E (Additive.ofMul u)).val = 0 ↔
      wordWeight (E (Additive.ofMul w)).val = 0 := by
    rw [hz0,hz0]
    obtain ⟨g,hg⟩ := isConj_iff.mp hc
    constructor
    · intro hu
      apply Subtype.ext
      rw [←hg,hu]
      simp
    · intro hw
      apply Subtype.ext
      apply (MulAut.conj g).injective
      exact hg.trans ((congrArg Subtype.val hw).trans (map_one _).symm)
  have h4 : wordWeight (E (Additive.ofMul u)).val = 4 ↔
      wordWeight (E (Additive.ofMul w)).val = 4 :=
    ⟨fun h => H.fixed_space_weight_four_fusion D hTV hTI hz E hE hproj u w h hc,
      fun h => H.fixed_space_weight_four_fusion D hTV hTI hz E hE hproj w u h hc.symm⟩
  have fixed_eq (a b : V) (hab : IsConj (a : G) (b : G))
      (ha : wordWeight (E (Additive.ofMul a)).val = 8) : a = b := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hab
    have ha1 : a ≠ 1 := fun h => by have hh := (hz0 a).mpr h; omega
    have hh := (H.fixed_vector_fusion_conjugator D hTV hTI hz a ha1
      (fixed_of_core_weight_eight H.chosen D E hproj a ha) g (by change g * (a : G) * g⁻¹ ∈ V; rw [hg]; exact b.property)).1
    exact Subtype.ext (hh.symm.trans hg)
  have h8 : wordWeight (E (Additive.ofMul u)).val = 8 ↔
      wordWeight (E (Additive.ofMul w)).val = 8 := by
    constructor
    · intro h
      rwa [←fixed_eq u w hc h]
    · intro h
      rwa [←fixed_eq w u hc.symm h]
  have hu := EightCore.weights (E (Additive.ofMul u))
  have hw := EightCore.weights (E (Additive.ofMul w))
  omega

/-- The 12.6.19 fusion problem is now precisely the two/six interchange,
with a witness in the original V and the original compatible marking. -/
theorem SourceHypothesis.fusion_failure_has_weight_two_six
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (hf : ¬ CentralLine.ControlsElementFusion L V) :
    ∃ (E : Additive V ≃ₗ[ZMod 2] core (Fin 8)) (u w : V),
      (∀ l v, E (seedRepresentation L V H.chosen.normalizes l v) =
        alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E v)) ∧
      (∀ v, coreToNatural (Fin 8) (E v) = D.coordinates (Submodule.Quotient.mk v)) ∧
      wordWeight (E (Additive.ofMul u)).val = 2 ∧
      wordWeight (E (Additive.ofMul w)).val = 6 ∧ IsConj (u : G) (w : G) := by
  have hz : ZV L V ≠ ⊥ := fun hz => hf (H.fixed_free_controls_element_fusion D hTV hTI hz)
  obtain ⟨E,hE,hproj⟩ := D.core_marking_of_fixed_ne_bot H.chosen hz
  by_contra! hnone
  apply hf
  intro x hx g hg
  let u : V := ⟨x,hx⟩
  let w : V := ⟨MulAut.conj g x,hg⟩
  have hc : IsConj (u : G) (w : G) := isConj_iff.mpr ⟨g,rfl⟩
  rcases H.fixed_space_fusion_weights D hTV hTI hz E hE hproj u w hc with he | he | he
  · obtain ⟨l,hl⟩ := D.core_orbit_of_same_weight H.chosen E hE u w he
    exact ⟨l,l.property,congrArg Subtype.val hl⟩
  · exact (hnone E u w hE hproj he.1 he.2 hc).elim
  · exact (hnone E w u hE hproj he.2 he.1 hc.symm).elim

/-- Original-source application: choose the seven-dimensional coordinates
and supply every weight-four centralizer transporter simultaneously. -/
theorem SourceHypothesis.exists_core_marking_weight_four_transport
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥) :
    ∃ E : Additive V ≃ₗ[ZMod 2] core (Fin 8),
      (∀ l u, E (seedRepresentation L V H.chosen.normalizes l u) =
        alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E u)) ∧
      (∀ u, coreToNatural (Fin 8) (E u) = D.coordinates (Submodule.Quotient.mk u)) ∧
      ∀ (u : V) (g : G), wordWeight (E (Additive.ofMul u)).val = 4 →
        (u : G) ∈ V.map (MulAut.conj g).toMonoidHom →
        ∃ c : Gv (u : G), V.map (MulAut.conj (c : G)).toMonoidHom =
          V.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨E,hE,hproj⟩ := D.core_marking_of_fixed_ne_bot H.chosen hz
  exact ⟨E,hE,hproj,fun u g hu hg =>
    H.fixed_space_weight_four_centralizer_conjugator D hTV hTI hz E hE hproj u hu g hg⟩

/-- The two complementary nonsingular vectors have exactly the same full
centralizer. Each centralizer normalizes V by TI, so its action fixes the
unique nonzero L-fixed word. -/
theorem SourceHypothesis.nonsingular_complement_centralizer_eq
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hproj : ∀ u, coreToNatural (Fin 8) (E u) = D.coordinates (Submodule.Quotient.mk u))
    (u : V) (hu : wordWeight (E (Additive.ofMul u)).val = 2) :
    let z : V := (E.symm EightCore.oneWord).toMul
    Gv (u : G) = Gv ((u * z : V) : G) := by
  let z : V := (E.symm EightCore.oneWord).toMul
  let w : V := u * z
  have hzE : E (Additive.ofMul z) = EightCore.oneWord := E.apply_symm_apply _
  have hz8 : wordWeight (E (Additive.ofMul z)).val = 8 := by
    rw [hzE]
    exact (EightCore.weight_eight_iff _).mpr rfl
  have hzfix := fixed_of_core_weight_eight H.chosen D E hproj z hz8
  have hwE : E (Additive.ofMul w) = E (Additive.ofMul u) + EightCore.oneWord := by
    change E (Additive.ofMul u + Additive.ofMul z) = _
    rw [map_add,hzE]
  have hw6 : wordWeight (E (Additive.ofMul w)).val = 6 := by
    rw [hwE,EightCore.weight_complement,hu]
  have huN := nonsingular_of_core_weight H.chosen D E hproj u (Or.inl hu)
  have hwN := nonsingular_of_core_weight H.chosen D E hproj w (Or.inr hw6)
  have hfix (a : V) (ha : D.Nonsingular a) : Gv (a : G) ≤ Gv (z : G) := by
    intro c hc
    have hcM := H.nonsingular_centralizer_le_of_fixed D hTV hTI hz a ha hc
    have hcV := Mv_le_module_normalizer_of_TI hTI a (nonsingular_ne_one D ha) ⟨hcM,hc⟩
    obtain ⟨l,hl⟩ := D.normalizer_orbit_control H.chosen c hcM hcV z
    have he : (l : G)*(z : G)*(l : G)⁻¹ = z :=
      mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hzfix.2 l l.property)
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp (hl.trans he))
  apply le_antisymm
  · intro c hc
    have hc1 := mem_centralizer_singleton_iff.mp hc
    have hc2 := mem_centralizer_singleton_iff.mp (hfix u huN hc)
    apply mem_centralizer_singleton_iff.mpr
    change c * ((u : G) * (z : G)) = (u : G) * (z : G) * c
    calc
      _ = ((u : G) * c) * (z : G) := by rw [←mul_assoc,hc1]
      _ = _ := by rw [mul_assoc,hc2,mul_assoc]
  · intro c hc
    have hc1 := mem_centralizer_singleton_iff.mp hc
    have hc2 := mem_centralizer_singleton_iff.mp (hfix w hwN hc)
    apply mem_centralizer_singleton_iff.mpr
    apply mul_right_cancel (b := (z : G))
    calc
      (c * (u : G)) * (z : G) = c * ((u : G) * (z : G)) := mul_assoc _ _ _
      _ = ((u : G) * (z : G)) * c := hc1
      _ = ((u : G) * c) * (z : G) := by rw [mul_assoc,←hc2,←mul_assoc]

/-- Any remaining fusion failure gives a normalizer of a full nonsingular
centralizer outside M, carrying a weight-two point to its product with the
original fixed vector. This is a reduction, not a claim that the normalizer
is controlled by the preceding centralizer-containment theorem. -/
theorem SourceHypothesis.fusion_failure_has_complement_normalizer
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (hf : ¬ CentralLine.ControlsElementFusion L V) :
    ∃ (E : Additive V ≃ₗ[ZMod 2] core (Fin 8)) (u : V) (g : G),
      (∀ l v, E (seedRepresentation L V H.chosen.normalizes l v) =
        alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E v)) ∧
      (∀ v, coreToNatural (Fin 8) (E v) = D.coordinates (Submodule.Quotient.mk v)) ∧
      wordWeight (E (Additive.ofMul u)).val = 2 ∧
      g ∈ normalizer (Gv (u : G) : Set G) ∧ g ∉ M L ∧
      MulAut.conj g (u : G) = (u : G) * ((E.symm EightCore.oneWord).toMul : G) := by
  have hz : ZV L V ≠ ⊥ := fun hz => hf (H.fixed_free_controls_element_fusion D hTV hTI hz)
  obtain ⟨E,u,w,hE,hproj,hu,hw,hc⟩ := H.fusion_failure_has_weight_two_six D hTV hTI hf
  let z : V := (E.symm EightCore.oneWord).toMul
  let v : V := u * z
  have hzE : E (Additive.ofMul z) = EightCore.oneWord := E.apply_symm_apply _
  have hvE : E (Additive.ofMul v) = E (Additive.ofMul u) + EightCore.oneWord := by
    change E (Additive.ofMul u + Additive.ofMul z) = _
    rw [map_add,hzE]
  have hv : wordWeight (E (Additive.ofMul v)).val = 6 := by
    rw [hvE,EightCore.weight_complement,hu]
  obtain ⟨l,hl⟩ := D.core_orbit_of_same_weight H.chosen E hE w v (hw.trans hv.symm)
  obtain ⟨a,ha⟩ := isConj_iff.mp hc
  let g : G := (l : G) * a
  have hg : MulAut.conj g (u : G) = (v : G) := by
    change ((l : G)*a)*(u : G)*((l : G)*a)⁻¹ = (v : G)
    calc
      _ = (l : G) * (a * (u : G) * a⁻¹) * (l : G)⁻¹ := by group
      _ = _ := by rw [ha]; exact congrArg Subtype.val hl
  have hn : g ∈ normalizer (Gv (u : G) : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    change (centralizer ({(u : G)} : Set G)).map (MulAut.conj g).toMonoidHom = _
    rw [map_pointCentralizer,hg]
    exact (H.nonsingular_complement_centralizer_eq D hTV hTI hz E hproj u hu).symm
  have hout : g ∉ M L := by
    intro hgM
    have hgV : g ∈ normalizer (V : Set G) := by
      rcases hTI g hgM with hi | he
      · have hm : (v : G) ∈ V ⊓ V.map (MulAut.conj g).toMonoidHom :=
          ⟨v.property,u,u.property,hg⟩
        have hv1 : v = 1 := Subtype.ext (mem_bot.mp (hi ▸ hm))
        have he : E (Additive.ofMul v) = 0 := by rw [hv1]; exact E.map_zero
        rw [he,(EightCore.weight_zero_iff _).mpr rfl] at hv
        omega
      · exact mem_normalizer_iff_map_conj_eq.mpr he
    obtain ⟨b,hb⟩ := D.normalizer_orbit_control H.chosen g hgM hgV u
    have hbu : conjugation L V H.chosen.normalizes b u = v := Subtype.ext (hb.symm.trans hg)
    have he := congrArg (fun x : core (Fin 8) => wordWeight x.val) (hE b (Additive.ofMul u))
    change wordWeight (E (Additive.ofMul (conjugation L V H.chosen.normalizes b u))).val =
      wordWeight (representation (Fin 8) (D.actorMap b).val (E (Additive.ofMul u)).val) at he
    rw [wordWeight_permute,hbu,hu,hv] at he
    omega
  exact ⟨E,u,g,hE,hproj,hu,hn,hout,hg⟩

end CFSG.Quasithin.Chapter12.Section06
