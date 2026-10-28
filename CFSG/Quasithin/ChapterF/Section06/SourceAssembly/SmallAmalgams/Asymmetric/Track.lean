module
public import Theory.GroupTheory.SylowOmegaSpan
public import Theory.GroupTheory.PGroup.CharacteristicPairReduction
public import CFSG.Quasithin.ChapterF.Section07.Track
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Asymmetric.Centers

/-!
# The original cubic amalgam constructs its omega-center track

Faithfulness forces the actual Ω₁(Z(S)) to be moved by at least one vertex.
Choose such an orientation and form its literal normal closure. The index-three
Sylow calculation supplies reducedness and its exact two-core centralizer.
The original subgroup inclusions and common Sylow images then construct every
field of F.7's source setup. Its existing geometry gives a genuine critical
vertex and minimal radius. No noncentrality witness remains in the orientation
existence theorem, and no reciprocal criticality or numerical radius bound is
assumed or asserted.

Source: Aschbacher–Smith F.6.1 and F.7.1,6–11, pp.305,311–314;
Kurzweil–Stellmacher §10.3.4–6, pp.285–287.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Asymmetric
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}

abbrev pairFamily (A B : Subgroup G) (i : Bool) : Subgroup G := if i then B else A

omit [Finite G] in
/-- The restricted Sylow omega-center is exactly the original ambient subgroup. -/
theorem map_sylow_omega (S : Sylow 2 G) (hSA : (S : Subgroup G)≤A) :
    (SylowOmegaSpan.seed (S.subtype hSA)).map A.subtype=omegaCenterIn (S : Subgroup G) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    have hy' := (mem_omegaCenterIn_iff _ _).mp hy
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨hy'.1,?_,congrArg Subtype.val hy'.2.2⟩
    rw [mem_centralizer_iff]
    intro s hs
    exact congrArg Subtype.val (mem_centralizer_iff.mp hy'.2.1 ⟨s,hSA hs⟩ hs)
  · intro hx
    have hx' := (mem_omegaCenterIn_iff _ _).mp hx
    refine ⟨⟨x,hSA hx'.1⟩,?_,rfl⟩
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨hx'.1,?_,Subtype.ext hx'.2.2⟩
    rw [mem_centralizer_iff]
    intro s hs
    exact Subtype.ext (mem_centralizer_iff.mp hx'.2.1 s hs)

omit [Finite G] in
theorem sylow_omega_noncentral (S : Sylow 2 G) (hSA : (S : Subgroup G)≤A)
    (hn : ¬ omegaCenterIn (S : Subgroup G)≤centralizer (A : Set G)) :
    ¬ SylowOmegaSpan.seed (S.subtype hSA)≤center A := by
  intro hc
  apply hn
  rw [←map_sylow_omega S hSA]
  rintro _ ⟨z,hz,rfl⟩
  rw [mem_centralizer_iff]
  intro a ha
  exact congrArg Subtype.val (mem_center_iff.mp (hc hz) ⟨a,ha⟩)

/-- Faithfulness guarantees an actual noncentral orientation; no movement
assumption is added to the original source pair. -/
theorem noncentral_orientation
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A)
    (S : Sylow 2 G) (hS : A⊓B=(S : Subgroup G)) :
    (¬ omegaCenterIn (S : Subgroup G)≤centralizer (A : Set G)) ∨
      (¬ omegaCenterIn (S : Subgroup G)≤centralizer (B : Set G)) := by
  by_contra! hc
  let Z := omegaCenterIn (S : Subgroup G)
  have hZS : Z≤A⊓B := hS.symm ▸ map_subtype_le _
  have hz := h.common_normal_eq_bot hcore Z hZS
    ((normal_subgroupOf_iff_le_normalizer (hZS.trans inf_le_left)).mpr
      ((le_centralizer_iff.mp hc.1).trans (Subgroup.centralizer_le_normalizer _)))
    ((normal_subgroupOf_iff_le_normalizer (hZS.trans inf_le_right)).mpr
      ((le_centralizer_iff.mp hc.2).trans (Subgroup.centralizer_le_normalizer _)))
  have hs : 1<Nat.card S := by
    have hh := BothAbelian.intersection_card_gt_four h hA
    rw [hS] at hh
    omega
  let : Nontrivial (S : Subgroup G) := (Finite.one_lt_card_iff_nontrivial).mp hs
  have hn := omega_center_ne_bot S.isPGroup'
  exact hn ((map_eq_bot_iff_of_injective _ (S : Subgroup G).subtype_injective).mp hz)

/-- All F.7.1/6 inputs on the original pair and original omega-center span. -/
noncomputable def sourceTrackSetup
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A)
    (S : Sylow 2 G) (hS : A⊓B=(S : Subgroup G))
    (hn : ¬ omegaCenterIn (S : Subgroup G)≤centralizer (A : Set G)) :
    Section07.Track.SourceSetup (pairFamily A B) := by
  let F := pairFamily A B
  have hSF (i : Bool) : (S : Subgroup G)≤F i := by
    cases i
    · exact hS.symm.le.trans inf_le_left
    · exact hS.symm.le.trans inf_le_right
  let P (i : Bool) : Sylow 2 (F i) := S.subtype (hSF i)
  have hi : (P false : Subgroup (F false)).index=3 := SymmetricThreeTwoCore.sylow_index_three
    h.quotient_left.some (P false)
  have hn' := sylow_omega_noncentral S (hSF false) hn
  have hc := h.local_core_selfCentralizing hA
  have hr := SylowOmegaSpan.span_reduced (P false) hi hn' hc
  refine {
    finite := fun _ => inferInstance
    generates := h.generated
    characteristicTwo := hA
    core_free := ?_
    sylow := P
    same_sylow := (map_subgroupOf_eq_of_le (hSF false)).trans
      (map_subgroupOf_eq_of_le (hSF true)).symm
    V := SylowOmegaSpan.span (P false)
    reduced := hr
    centralizer_eq := ?_ }
  · let e : (F false⊔F true : Subgroup G)≃*G :=
      (MulEquiv.subgroupCongr h.generated).trans Subgroup.topEquiv
    apply (map_eq_bot_iff_of_injective _ (f:=e.toMonoidHom) e.injective).mp
    rw [pCore_map_iso]
    exact hcore
  · rw [Theory.GroupTheory.AmalgamLocalCores.reduced_centralizer_core _ hr]
    rw [SylowOmegaSpan.span_centralizer (P false) hi hn']
    exact inf_eq_right.mpr (pCore_isPGroup.le_sylow_of_normal (P false))

/-- The chosen span is nontrivial because the source omega-center is moved. -/
theorem sourceTrackSetup_ne_bot
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A)
    (S : Sylow 2 G) (hS : A⊓B=(S : Subgroup G))
    (hn : ¬ omegaCenterIn (S : Subgroup G)≤centralizer (A : Set G)) :
    (sourceTrackSetup h hcore hA S hS hn).V≠⊥ :=
  SylowOmegaSpan.span_ne_bot _ (sylow_omega_noncentral S (hS.symm.le.trans inf_le_left) hn)

/-- The original source constructs a genuine minimal critical vertex. -/
theorem source_critical_witness
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A)
    (S : Sylow 2 G) (hS : A⊓B=(S : Subgroup G))
    (hn : ¬ omegaCenterIn (S : Subgroup G)≤centralizer (A : Set G)) :
    let D := sourceTrackSetup h hcore hA S hS hn
    let hne := sourceTrackSetup_ne_bot h hcore hA S hS hn
    ∃ v : Subgroup.CosetGeometry.RankTwo.Vertex (pairFamily A B),
      (Subgroup.CosetGeometry.RankTwo.graph (pairFamily A B)).dist
        (Subgroup.CosetGeometry.RankTwo.base (pairFamily A B) false) v=D.track hne ∧
      ¬D.seed≤Subgroup.CosetGeometry.RankTwo.ballKernel (pairFamily A B) v 1 :=
  ((sourceTrackSetup h hcore hA S hS hn).critical_witness
    (sourceTrackSetup_ne_bot h hcore hA S hS hn)).1
/-- The original faithful pair itself chooses a moved orientation and its
literal F.7 setup; no seed or action witness is assumed. -/
theorem exists_oriented_source_track
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B)
    (S : Sylow 2 G) (hS : A⊓B=(S : Subgroup G)) :
    ∃ C D : Subgroup G, ((C=A ∧ D=B) ∨ (C=B ∧ D=A)) ∧
      ∃ (hSC : (S : Subgroup G)≤C) (E : Section07.Track.SourceSetup (pairFamily C D)),
        E.V=SylowOmegaSpan.span (S.subtype hSC) ∧ E.V≠⊥ ∧
        (E.sylow false : Subgroup (pairFamily C D false)).map (pairFamily C D false).subtype=(S : Subgroup G) := by
  rcases noncentral_orientation h hcore hA S hS with hn | hn
  · refine ⟨A,B,Or.inl ⟨rfl,rfl⟩,hS.symm.le.trans inf_le_left,
      sourceTrackSetup h hcore hA S hS hn,rfl,sourceTrackSetup_ne_bot h hcore hA S hS hn,?_⟩
    exact map_subgroupOf_eq_of_le (hS.symm.le.trans inf_le_left)
  · have hs' : B⊓A=(S : Subgroup G) := (inf_comm _ _).trans hS
    refine ⟨B,A,Or.inr ⟨rfl,rfl⟩,hs'.symm.le.trans inf_le_left,
      sourceTrackSetup h.symm hcore hB S hs' hn,rfl,
      sourceTrackSetup_ne_bot h.symm hcore hB S hs' hn,?_⟩
    exact map_subgroupOf_eq_of_le (hs'.symm.le.trans inf_le_left)
end CFSG.Quasithin.ChapterF.SourceAssembly.Asymmetric
