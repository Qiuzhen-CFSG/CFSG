module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.CanonicalRank
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.FullCoordinates
public import Theory.Representation.BinaryPermutation.EightFormOrbits
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Theory.GroupTheory.DoubleCoverCentralizer.TwoCentralSylow

/-!
# Original nonsingular Sylow exclusion and fixed-free fusion

No original nonsingular vector centralizes an ambient Sylow two-subgroup.
For a centralizer contained in M, the original orbit has length 28, excluding
full Sylow containment. Otherwise the completed nonquasisimple exclusion
produces a preferred escaping quasisimple residual and forces C_V(L)=1.
The actual single nonsingular orbit transports an ambient Sylow to that
point, contradicting even characteristic and its quasisimple component.
This argument does not require the remaining HS/J4 exclusions.

When C_V(L)=1, a nontrivial Sylow-fixed vector exists in the original V.
It is singular by the preceding exclusion. The two actual A8 orbits then
identify nonidentity singular vectors with two-central involutions. This
proves L controls G-fusion in V, and supplies the literal centralizer
conjugator in 12.6.20(2). The intersection consumer also removes its fusion
premise and proves the weight-four/rank-three bound and r(G,V)>=3, retaining
only the still-open nonsingular centralizer containment.

Full 12.6.2 still needs the HS/J4 exclusions. Fusion with nontrivial fixed
space, weak closure and fixed-space elimination remain with this owner;
12.6.23 is not asserted. Earlier invariance/TI retain qt-d-1222-source,
and final source discharge retains qt-d-12634-source.

Source: Aschbacher--Smith, 12.6.1(1), 12.6.12 and 12.6.19--20, combined
manuscript of 1 March 2004, printed pp.823,825--826,828--829.
-/

public section
open Subgroup Theory.GroupTheory BinaryPermutation
open Theory.GroupTheory.DoubleCoverCentralizer
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

omit [Finite G] in
/-- The two nonidentity orbits on the original V when its original fixed space vanishes. -/
theorem OrthogonalMarking.fixed_free_orbit_of_same_form
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) (hz : ZV L V = ⊥)
    (v w : V) (hv : v ≠ 1) (hw : w ≠ 1)
    (hf : D.Nonsingular v ↔ D.Nonsingular w) :
    ∃ l : L, conjugation L V chosen.normalizes l v = w := by
  let E := D.fullCoordinates hz
  have hv0 : (E v).toAdd ≠ 0 := fun h => hv (E.injective (h.trans E.map_one.symm))
  have hw0 : (E w).toAdd ≠ 0 := fun h => hw (E.injective (h.trans E.map_one.symm))
  have heq : BinaryPermutation.TerminalOrthogonal.Eight.form (E v).toAdd =
      BinaryPermutation.TerminalOrthogonal.Eight.form (E w).toAdd := by
    have hh : ∀ a b : ZMod 2, (a ≠ 0 ↔ b ≠ 0) → a = b := by decide
    apply hh
    exact (D.fullCoordinates_nonsingular_iff hz v).trans
      (hf.trans (D.fullCoordinates_nonsingular_iff hz w).symm)
  obtain ⟨g,hg⟩ := EightGeometry.exists_alternating_of_form_eq (E v).toAdd (E w).toAdd hv0 hw0 heq
  obtain ⟨l,rfl⟩ := D.actorMap_surjective g
  refine ⟨l,E.injective ?_⟩
  exact (D.fullCoordinates_equivariant hz l v).trans hg

private theorem no_ambient_sylow_of_control
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (v : V) (hv : D.Nonsingular v) (hc : Gv (v : G) ≤ M L)
    (P : Sylow 2 G) (hP : (P : Subgroup G) ≤ Gv (v : G)) : False := by
  let J := M L ⊓ normalizer (V : Set G)
  have hPJ : (P : Subgroup G) ≤ J := le_inf (hP.trans hc)
    ((le_inf (hP.trans hc) hP).trans
      (Mv_le_module_normalizer_of_TI hTI v (nonsingular_ne_one D hv)))
  let C := (J ⊓ Gv (v : G)).subgroupOf J
  have hi : C.index = 28 := by
    change (J ⊓ Gv (v : G)).relIndex J = 28
    rw [inf_relIndex_left,Gv,point_centralizer_index_of_orbit_control L J
      (le_inf L.le_normalizer H.chosen.normalizes) (v : G)
      (fun n => D.normalizer_orbit_control H.chosen n n.property.1 n.property.2 v)]
    simpa only [CLv,inf_relIndex_left,Gv] using D.nonsingular_centralizer_index H.chosen v hv
  have hPC : ((P.subtype hPJ) : Subgroup J) ≤ C := fun x hx => ⟨x.property,hP hx⟩
  exact (P.subtype hPJ).not_dvd_index ((by rw [hi]; decide : 2 ∣ C.index).trans
    (index_dvd_of_le hPC))

/-- Nonsingular vectors cannot be central in an ambient Sylow, even in
an unresolved HS/J4 centralizer row. -/
theorem SourceHypothesis.nonsingular_no_ambient_sylow
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (v : V) (hv : D.Nonsingular v) (P : Sylow 2 G) :
    ¬ (P : Subgroup G) ≤ Gv (v : G) := by
  intro hP
  by_cases hc : Gv (v : G) ≤ M L
  · exact no_ambient_sylow_of_control H D hTI v hv hc P hP
  obtain ⟨hz,_,w,hw,_,_,_,_,_,_,_,_,hK,_⟩ :=
    H.exists_preferred_nonsingular_quasisimple_escape D hTV hTI v hv hc
  obtain ⟨l,hl⟩ := D.fixed_free_orbit_of_same_form H.chosen hz v w
    (nonsingular_ne_one D hv) (nonsingular_ne_one D hw) (by simp [hv,hw])
  let e := MulAut.conj (l : G)
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  apply H.nonsingular_quasisimple_no_ambient_sylow D w hw hK P'
  rintro _ ⟨x,hx,rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  have hw' : e (v : G) = (w : G) := congrArg Subtype.val hl
  rw [←hw']
  change e x * e (v : G) = e (v : G) * e x
  rw [←map_mul,←map_mul]
  exact congrArg e (mem_centralizer_singleton_iff.mp (hP hx))
end CFSG.Quasithin.Chapter12.Section06

public section
open Subgroup Theory.GroupTheory BinaryPermutation
open Theory.GroupTheory.DoubleCoverCentralizer
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- In the original fixed-free module, the nonidentity singular vectors
are precisely those central in an ambient Sylow two-subgroup. -/
theorem SourceHypothesis.fixed_free_twoCentral_iff_singular
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V = ⊥)
    (v : V) (hv : v ≠ 1) : TwoCentral (v : G) ↔ ¬ D.Nonsingular v := by
  constructor
  · intro hc hn
    obtain ⟨P,hP⟩ := hc.exists_sylow_le_centralizer
    exact H.nonsingular_no_ambient_sylow D hTV hTI v hn P hP
  · intro hs
    let A := V.subgroupOf (T : Subgroup G)
    let : A.Normal := (normal_subgroupOf_iff_le_normalizer H.chosen.le_sylow).mpr hTV
    have hA : A ≠ ⊥ := by
      intro ha
      apply H.chosen.ne_bot
      rw [←map_subgroupOf_eq_of_le H.chosen.le_sylow]
      change A.map (T : Subgroup G).subtype = ⊥
      rw [ha,Subgroup.map_bot]
    have hn := center_inf_ne_bot_of_normal T.isPGroup' A hA
    obtain ⟨x,hx,hxne⟩ := (center (T : Subgroup G) ⊓ A).bot_or_exists_ne_one.resolve_left hn
    let u : V := ⟨(x : G),hx.2⟩
    have hu : u ≠ 1 := by
      intro he
      apply hxne
      apply Subtype.ext
      exact congrArg (fun a : V => (a : G)) he
    have huc : TwoCentral (u : G) := ⟨T,x.property,hx.1⟩
    have hus : ¬ D.Nonsingular u := by
      intro h
      obtain ⟨P,hP⟩ := huc.exists_sylow_le_centralizer
      exact H.nonsingular_no_ambient_sylow D hTV hTI u h P hP
    obtain ⟨l,hl⟩ := D.fixed_free_orbit_of_same_form H.chosen hz u v hu hv (by simp [hus,hs])
    have hh := huc.map (MulAut.conj (l : G))
    have he : MulAut.conj (l : G) (u : G) = (v : G) := congrArg Subtype.val hl
    rwa [he] at hh

/-- Source 12.6.19(1) in the original fixed-free branch, without assuming
12.6.2 or either remaining sporadic exclusion. -/
theorem SourceHypothesis.fixed_free_controls_element_fusion
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V = ⊥) :
    CentralLine.ControlsElementFusion L V := by
  intro x hx g hg
  by_cases h1 : x = 1
  · subst x
    exact ⟨1,L.one_mem,by simp⟩
  let v : V := ⟨x,hx⟩
  let w : V := ⟨MulAut.conj g x,hg⟩
  have hv : v ≠ 1 := fun he => h1 (congrArg Subtype.val he)
  have hw : w ≠ 1 := fun he => h1 ((MulAut.conj g).injective
    ((congrArg Subtype.val he).trans (MulAut.conj g).map_one.symm))
  have hc : TwoCentral (v : G) ↔ TwoCentral (w : G) := by
    constructor
    · intro h
      exact h.map (MulAut.conj g)
    · intro h
      have hh := h.map (MulAut.conj g).symm
      simpa only [w,v,MulEquiv.symm_apply_apply] using hh
  have hf : D.Nonsingular v ↔ D.Nonsingular w := by
    have hh := (H.fixed_free_twoCentral_iff_singular D hTV hTI hz v hv).symm.trans
      (hc.trans (H.fixed_free_twoCentral_iff_singular D hTV hTI hz w hw))
    exact not_iff_not.mp hh
  obtain ⟨l,hl⟩ := D.fixed_free_orbit_of_same_form H.chosen hz v w hv hw hf
  exact ⟨l,l.property,congrArg Subtype.val hl⟩
end CFSG.Quasithin.Chapter12.Section06

public section
open Subgroup Theory.GroupTheory BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open CentralLine
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The actual correcting conjugator of 12.6.20(2) in the fixed-free
branch; the fusion premise is now discharged. -/
theorem SourceHypothesis.fixed_free_centralizer_conjugator
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : HasTIConjugatesIn V (M L)) (hz : ZV L V = ⊥)
    {v g : G} (hv : v ∈ V) (hvg : v ∈ V.map (MulAut.conj g).toMonoidHom) :
    ∃ c : centralizer ({v} : Set G),
      V.map (MulAut.conj (c : G)).toMonoidHom = V.map (MulAut.conj g).toMonoidHom :=
  centralizer_conjugator H.chosen.normalizes
    (H.fixed_free_controls_element_fusion D hTV hTI hz) hv hvg

/-- Source 12.6.20(1,3) on the unchanged six-space. Only the still-open
nonsingular-centralizer theorem is retained; no fusion premise is needed. -/
theorem SourceHypothesis.fixed_free_intersections_of_control
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : HasTIConjugatesIn V (M L)) (hz : ZV L V = ⊥)
    (hcontrol : ∀ v : V, D.Nonsingular v → Gv (v : G) ≤ M L) :
    (∀ g ∉ normalizer (V : Set G),
      (∀ x ∈ V ⊓ V.map (MulAut.conj g).toMonoidHom,
        x ≠ 1 → x ∈ markedVectors (D.fullLinearCoordinates hz) naturalWeightFour) ∧
      Nat.log 2 (Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G)) ≤ 3) ∧
      3 ≤ ChapterE.globalR V := by
  refine natural_intersections_and_globalR (D.fullLinearCoordinates hz) ?_
    H.chosen.normalizes (H.fixed_free_controls_element_fusion D hTV hTI hz) hTI ?_
  · intro X hX
    apply EightGeometry.finrank_nonzero_singular_le X
    intro x hx hn
    obtain ⟨w,hw,hweight⟩ := hX x hx hn
    apply (EightGeometry.singular_iff_weight_four x hn).mpr
    refine ⟨w,hw,?_⟩
    simpa only [coreWeightFour,Fintype.card_subtype,hammingNorm] using hweight
  · intro x hx hn hnot
    apply hcontrol ⟨x,hx⟩
    by_contra hs
    have hn0 : D.fullLinearCoordinates hz (Additive.ofMul (show V from ⟨x,hx⟩)) ≠ 0 := by
      intro he
      have hx1 := (D.fullLinearCoordinates hz).injective
        (he.trans (D.fullLinearCoordinates hz).map_zero.symm)
      exact hn (congrArg (fun a : Additive V => (a.toMul : G)) hx1)
    have hs0 : BinaryPermutation.TerminalOrthogonal.Eight.form
        (D.fullLinearCoordinates hz (Additive.ofMul (show V from ⟨x,hx⟩))) = 0 := by
      rw [D.fullLinearCoordinates_apply]
      exact not_ne_iff.mp hs
    obtain ⟨w,hw,hweight⟩ := (EightGeometry.singular_iff_weight_four _ hn0).mp hs0
    exact hnot ⟨hx,w,hw,by
      simpa only [coreWeightFour,Fintype.card_subtype,hammingNorm] using hweight⟩
end CFSG.Quasithin.Chapter12.Section06
