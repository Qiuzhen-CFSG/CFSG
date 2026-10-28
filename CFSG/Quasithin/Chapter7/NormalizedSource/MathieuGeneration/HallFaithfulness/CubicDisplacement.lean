module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.CubicFullResolution
public import Theory.GroupTheory.Commutator.CoprimeCentralRow
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.CubicResidual.TwoCentralizer

/-!
# Commutator displacement on the original Mathieu pushing-up core

A Sylow section centralizer containing the original R = O₂(J) is selected,
with its actual section-centralizer conjugator from O₂(LT). Inside its
relative normalizer of R, take the subgroup centralizing V whose
commutators with the selected involution r lie in V. This is an explicitly
defined subgroup; it has not yet been identified with the whole relative
normalizer used in the source.

Commutation with r gives a homomorphism to V with exactly the relative
centralizer as kernel. The residual covers L modulo O₂(L), so irreducibility
makes its image either trivial or all of V. Coprime fixed-point lifting and
the proved normality of the full cubic residual force its cubic-fixed image
to centralize that residual. The native J₄ centralizer bound, transported
through the same full cover, then bounds C_V(x) by two in the nontrivial
image case. The original fixed-space condition proves injectivity on this
binary subgroup, without deleting the cover's center.

The literal Hall application constructs these data on its existing full
configuration. Nontrivial displacement, exclusion of the small fixed-space
alternative, and the separate M₂₄ and odd-actor comparisons remain open.
Source: Aschbacher--Smith 4.2.13, printed p.612, and 4.4.14, pp.624--625.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
/-- The part of the actual relative core normalizer whose commutators with
r lie in V; centralization of V is retained explicitly in the domain. -/
@[expose] def pushingDisplacementDomain {G : Type*} [Group G]
    (P R V : Subgroup G) (r : G) : Subgroup G :=
  commutatorPreimage (P ⊓ normalizer (R : Set G) ⊓ centralizer (V : Set G))
    (zpowers r) V

private theorem displacement_domain_data {G : Type*} [Group G]
    (P R V F : Subgroup G) (r : G)
    (hrP : r ∈ P) (hrR : r ∈ R) (hrV : r ∈ centralizer (V : Set G))
    (hFP : F ≤ normalizer (P : Set G)) (hFR : F ≤ normalizer (R : Set G))
    (hFV : F ≤ normalizer (V : Set G)) (hFr : F ≤ centralizer ({r} : Set G)) :
    let Q := pushingDisplacementDomain P R V r
    r ∈ Q ∧ Q ≤ P ∧ Q ≤ centralizer (V : Set G) ∧
      F ≤ normalizer (Q : Set G) ∧ ⁅zpowers r,Q⁆ ≤ V ∧
      F ≤ normalizer ((⁅zpowers r,Q⁆ : Subgroup G) : Set G) := by
  let B := P ⊓ normalizer (R : Set G) ⊓ centralizer (V : Set G)
  let Q := pushingDisplacementDomain P R V r
  have hBV : B ≤ normalizer (V : Set G) := inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have hQB : Q ≤ B := commutatorPreimage_le _ _ _
  have hFZ : F ≤ normalizer (zpowers r : Set G) := by
    rw [←centralizer_closure ({r} : Set G),←zpowers_eq_closure r] at hFr
    exact hFr.trans (Subgroup.centralizer_le_normalizer _)
  have hFB : F ≤ normalizer (B : Set G) :=
    (le_inf ((le_inf hFP (hFR.trans ((normalizer (R : Set G)).le_normalizer))).trans
      inf_normalizer_le_normalizer_inf)
      (hFV.trans (normalizer_le_normalizer_centralizer V))).trans
        inf_normalizer_le_normalizer_inf
  have hFQ : F ≤ normalizer (Q : Set G) :=
    commutatorPreimage_normalized B (zpowers r) V F hBV hFB hFZ hFV
  refine ⟨?_,hQB.trans (inf_le_left.trans inf_le_left),hQB.trans inf_le_right,hFQ,?_,?_⟩
  · apply (le_commutatorPreimage (zpowers_le.mpr
      (show r ∈ B from ⟨⟨hrP,R.le_normalizer hrR⟩,hrV⟩))
      ((commutator_self_eq_bot_iff.mpr (inferInstance : IsMulCommutative (zpowers r))).le.trans bot_le))
      (mem_zpowers r)
  · rw [commutator_comm]
    exact commutator_commutatorPreimage_le B (zpowers r) V hBV
  · intro f hf
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (hFZ hf),
      mem_normalizer_iff_map_conj_eq.mp (hFQ hf)]
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
include D

omit [Finite G] in
/-- Irreducibility on the original residual follows from its literal covering
of L and from the two-core's trivial action on the original chosen module. -/
theorem sourceOrbit_residual_invariant_subgroup
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    (F U : Subgroup G) (hcover : (L : Set G) = (F : Set G) * (L.pCoreIn 2 : Set G))
    (hUV : U ≤ V) (hFU : F ≤ normalizer (U : Set G)) : U = ⊥ ∨ U = V := by
  have hcore : L.pCoreIn 2 ≤ centralizer (U : Set G) :=
    ((pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer D.sylow_normalizes_component)).trans D.core_centralizes).trans
        (centralizer_le hUV)
  have hLU : L ≤ normalizer (U : Set G) := by
    intro l hl
    obtain ⟨f,hf,q,hq,rfl⟩ := hcover ▸ (show l ∈ (L : Set G) from hl)
    exact (normalizer (U : Set G)).mul_mem (hFU hf)
      ((Subgroup.centralizer_le_normalizer _) (hcore hq))
  rcases ReducedNormal.subspaceImage_eq_or_le_centralizer
    (L ⊔ (T : Subgroup G)) L le_sup_left D.irrPlus.isIrrPlus U
    (hUV.trans_eq D.image_eq.symm) hLU with he | hc
  · exact .inr (he.trans D.image_eq)
  · exact .inl (bot_unique ((le_inf hUV hc).trans_eq hfix))


/-- On the full original cover, a cubic-fixed subgroup centralizing the
full cubic residual has at most two elements. The marked quotient is
injective on this subgroup because the original module has no fixed layer. -/
theorem sourceOrbit_cubic_fixed_card_le_two
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) [K.Normal]
    (hFK : ((solvableResidual (L ⊓ H : Subgroup G)).map
      (L ⊓ H).subtype).subgroupOf H ≤ K)
    (e : (K ⧸ center K) ≃* Janko4.Model) (x : K) (hx : orderOf x = 3)
    (hc : V ⊓ centralizer ({((x : H) : G)} : Set G) ≤
      centralizer (cubicResidualImage H K x : Set G)) :
    Nat.card (V ⊓ centralizer ({((x : H) : G)} : Set G) : Subgroup G) ≤ 2 := by
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let f : K →* G := H.subtype.comp K.subtype
  have hi : Function.Injective f := H.subtype_injective.comp K.subtype_injective
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFKg : F ≤ K.map H.subtype := by
    have hh := map_mono (f := H.subtype) hFK
    rwa [map_subgroupOf_eq_of_le hFH] at hh
  have hVF : V ≤ F := hw.2.2.2.2.2.2.2.2.2.2.1
  have hcover : (L : Set G) = (F : Set G) * (L.pCoreIn 2 : Set G) :=
    hw.2.2.2.2.2.2.2.1
  let Z := V ⊓ centralizer ({((x : H) : G)} : Set G)
  let P := Z.comap f
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hk : q.ker = center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hcore : L.pCoreIn 2 ≤ centralizer (V : Set G) :=
    (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer D.sylow_normalizes_component)).trans D.core_centralizes
  have hqi : Function.Injective (q.comp P.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply le_bot_iff.mp
    intro p hp
    have hz : (p : K) ∈ center K := hk ▸ hp
    have hpc : f (p : K) ∈ centralizer (F : Set G) := by
      intro y hy
      obtain ⟨k,hk',he⟩ := hFKg hy
      exact he ▸ congrArg f (mem_center_iff.mp hz (⟨k,hk'⟩ : K))
    have hpl : f (p : K) ∈ centralizer (L : Set G) := by
      intro y hy
      obtain ⟨a,ha,b,hb,rfl⟩ := hcover ▸ (show y ∈ (L : Set G) from hy)
      calc
        (a*b) * f (p : K) = a * (b * f (p : K)) := mul_assoc _ _ _
        _ = a * (f (p : K) * b) := congrArg (a * ·) ((hcore hb) _ p.property.1).symm
        _ = f (p : K) * (a*b) := by rw [←mul_assoc,hpc a ha,mul_assoc]
    apply Subtype.ext
    apply hi
    exact (show f (p : K) = 1 from hfix.le ⟨p.property.1,hpl⟩).trans f.map_one.symm
  have hp : IsPGroup 2 P := by
    let := D.elementary
    exact ((IsElementaryAbelian.isPGroup 2 V).to_le (show Z ≤ V from inf_le_left)).comap_of_injective f hi
  have hpc : P ≤ centralizer ((solvableResidual (centralizer ({x} : Set K))).map
      (centralizer ({x} : Set K)).subtype : Set K) := by
    intro p hp y hy
    apply hi
    simpa only [map_mul] using hc hp (f y) (mem_map_of_mem f hy)
  have hb := Janko4.LocalStructure.cover_cubic_residual_two_centralizer_bound
    q (e.surjective.comp (QuotientGroup.mk'_surjective _))
    (hk.symm ▸ pushingUp_component_center_three_coprime hw K) x hx P hp hqi hpc
  let g : P →* Z := f.subgroupComap Z
  have hg : Function.Bijective g := by
    refine ⟨fun a b hh => Subtype.ext (hi (congrArg Z.subtype hh)),?_⟩
    intro z
    obtain ⟨k,hk',he⟩ := hFKg (hVF z.property.1)
    refine ⟨⟨⟨k,hk'⟩,?_⟩,Subtype.ext he⟩
    change f (⟨k,hk'⟩ : K) ∈ Z
    exact he.symm ▸ z.property
  exact (Nat.card_congr (MulEquiv.ofBijective g hg).toEquiv).symm.trans_le hb

/-- The actual displacement domain has either zero image or all of V.
Its cubic-fixed image centralizes the full original cubic residual. -/
theorem sourceOrbit_cubic_displacement
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H)
    (hFK : ((solvableResidual (L ⊓ H : Subgroup G)).map
      (L ⊓ H).subtype).subgroupOf H ≤ K)
    (r : G) (hrR : r ∈ J.pCoreIn 2)
    (hKr : K.map H.subtype ≤ centralizer ({r} : Set G))
    (x : K) (hx : orderOf x = 3)
    (hxF : ((x : H) : G) ∈ (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
    (hfull : CubicPumpupFullResolution H K x r)
    (P : Subgroup G) (hP : IsPGroup 2 P) (hRP : J.pCoreIn 2 ≤ P)
    (hFP : (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype ≤
      normalizer (P : Set G)) :
    let Q := pushingDisplacementDomain P (J.pCoreIn 2) V r
    let U := ⁅zpowers r,Q⁆
    r ∈ Q ∧ U ≤ V ∧
      (U = ⊥ ∨ U = V) ∧
      U ⊓ centralizer ({((x : H) : G)} : Set G) ≤ centralizer (cubicResidualImage H K x : Set G) ∧
      (Q ≤ centralizer ({r} : Set G) ∨
        V ⊓ centralizer ({((x : H) : G)} : Set G) ≤
          centralizer (cubicResidualImage H K x : Set G)) := by
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFL : F ≤ L := (map_subtype_le _).trans inf_le_left
  have hFKg : F ≤ K.map H.subtype := by
    have hh := map_mono (f := H.subtype) hFK
    rwa [map_subgroupOf_eq_of_le hFH] at hh
  obtain ⟨hJ,hpush,hH,hJH,hstrict,hVJ,hc,hcover,hN,hmove,hVF,hrest⟩ := hw
  have hFr : F ≤ centralizer ({r} : Set G) := hFKg.trans hKr
  have hrV : r ∈ centralizer (V : Set G) := by
    intro v hv
    exact mem_centralizer_singleton_iff.mp (hFr (hVF hv))
  have hFR : F ≤ normalizer (J.pCoreIn 2 : Set G) :=
    (le_conjugateSpanBy F (H ⊓ normalizer (L : Set G))).trans hc.span_normalizes_radical
  let Q := pushingDisplacementDomain P (J.pCoreIn 2) V r
  let U := ⁅zpowers r,Q⁆
  obtain ⟨hrQ,hQP,hQV,hFQ,hUV,hFU⟩ := displacement_domain_data P (J.pCoreIn 2) V F r
    (hRP hrR) hrR hrV hFP hFR (hFL.trans D.normalizes) hFr
  have hd := D.sourceOrbit_residual_invariant_subgroup hfix F U hcover hUV hFU
  have hUQ : U ≤ centralizer (Q : Set G) := hUV.trans (le_centralizer_iff.mp hQV)
  let C := zpowers (((x : H) : G))
  have hCQ : C ≤ normalizer (Q : Set G) := zpowers_le.mpr (hFQ hxF)
  have hCr : C ≤ centralizer ({r} : Set G) := zpowers_le.mpr (hFr hxF)
  have hCc : centralizer (C : Set G) = centralizer ({((x : H) : G)} : Set G) := by
    change centralizer (zpowers (((x : H) : G)) : Set G) = _
    rw [zpowers_eq_closure,centralizer_closure]
  have hQp : IsPGroup 2 Q := hP.to_le hQP
  have hsolv : Group.IsSolvable Q := by
    let := hQp.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card C) (Nat.card Q) := by
    have hxG : orderOf (((x : H) : G)) = 3 :=
      (orderOf_coe (x : H)).trans ((orderOf_coe x).trans hx)
    obtain ⟨n,hn⟩ := hQp.exists_card_eq
    rw [Nat.card_zpowers,hxG,hn]
    exact Nat.Coprime.pow_right n (by decide : Nat.Coprime 3 2)
  have hfixed := CentralRow.fixed_commutator_le_centralizer Q C (cubicResidualImage H K x)
    ⟨r,hrQ⟩ hUQ hCQ hCr hsolv hcop (by rw [hCc]; exact hfull.2.2.2)
  rw [hCc] at hfixed
  refine ⟨hrQ,hUV,hd,hfixed,?_⟩
  rcases hd with hz | he
  · left
    have hh := commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm Q (zpowers r)).trans hz)
    rwa [zpowers_eq_closure,centralizer_closure] at hh
  · exact .inr (he ▸ hfixed)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4
/-- The exact Sylow section centralizer, conjugator, displacement domain and
fixed-image conclusion. No claim of whole-module movement is built into it. -/
@[expose] def CubicDisplacementConclusion {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (L V J H : Subgroup G) (K : Subgroup H) (x : K) (r : G) : Prop :=
  ∃ P : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L),
    let Pg := (P : Subgroup _).map (sectionCentralizerIn (normalizer (L : Set G)) L).subtype
    J.pCoreIn 2 ≤ Pg ∧
    ∃ c : sectionCentralizerIn (normalizer (L : Set G)) L,
      ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom = Pg ∧
      let Q := pushingDisplacementDomain Pg (J.pCoreIn 2) V r
      let U := ⁅zpowers r,Q⁆
      r ∈ Q ∧ U ≤ V ∧ (U = ⊥ ∨ U = V) ∧
        U ⊓ centralizer ({((x : H) : G)} : Set G) ≤ centralizer (cubicResidualImage H K x : Set G) ∧
        (Q ≤ centralizer ({r} : Set G) ∨
          Nat.card (V ⊓ centralizer ({((x : H) : G)} : Set G) : Subgroup G) ≤ 2) ∧
        ∃ χ : Q →* V, (∀ s : Q, (χ s : G) = ⁅r,(s : G)⁆) ∧
          χ.ker = (centralizer ({r} : Set G)).subgroupOf Q ∧
          χ.range.map V.subtype = U
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- Construct the source Sylow section centralizer and displacement control
from the original witness, keeping its actual core and quotient maps. -/
theorem sourceOrbit_cubic_displacement_selection
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) [K.Normal]
    (hFK : ((solvableResidual (L ⊓ H : Subgroup G)).map
      (L ⊓ H).subtype).subgroupOf H ≤ K)
    (e : (K ⧸ center K) ≃* Janko4.Model)
    (r : G) (hrR : r ∈ J.pCoreIn 2)
    (hKr : K.map H.subtype ≤ centralizer ({r} : Set G))
    (x : K) (hx : orderOf x = 3)
    (hxF : ((x : H) : G) ∈ (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
    (hfull : CubicPumpupFullResolution H K x r) :
    CubicDisplacementConclusion T L V J H K x r := by
  have hM := h.sylow_normalized_maximal_unique D.sylow_normalizes_component
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hjoin : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer D.sylow_normalizes_component,hM.2⟩
  have hyp := source_hypothesis411 h hjoin
  let M := normalizer (L : Set G)
  let C := sectionCentralizerIn M L
  let Mminus := coveringOvergroup M L (oddActorResidual L A)
  have hs : Mminus ∈ sigma M L := by
    refine ⟨sup_le (((oddActorResidual_le L A).trans inf_le_left).trans L.le_normalizer)
      inf_le_left,sup_le ?_ le_sup_right⟩
    intro l hl
    obtain ⟨j,hj,q,hq,rfl⟩ := hw.1.1.1.2.2.1 hl
    exact Mminus.mul_mem (hw.1.1.1.1 hj)
      ((show C ≤ Mminus from le_sup_right) (componentCore_le_sectionCentralizer L.le_normalizer hq))
  have hRC : J.pCoreIn 2 ≤ C := core_le_sectionCentralizer_of_eta
    hyp.plus_le hyp.plus_normal hyp.plus_perfect hs.1 hw.1.1.1
  obtain ⟨P,hRP⟩ := ((isPGroup_pCoreIn 2 J).comap_subtype :
    IsPGroup 2 ((J.pCoreIn 2).subgroupOf C)).exists_le_sylow
  let Pg := (P : Subgroup C).map C.subtype
  have hRPg : J.pCoreIn 2 ≤ Pg := fun j hj => ⟨⟨j,hRC hj⟩,hRP hj,rfl⟩
  obtain ⟨c,hmark,_⟩ := Chapter4.Section02.Unitary.exists_fullModule_comparison h D hjoin P
  refine ⟨P,hRPg,c,hmark,?_⟩
  have hd := D.sourceOrbit_cubic_displacement hfix hw K hFK r hrR hKr x hx hxF hfull Pg
    (P.isPGroup'.map C.subtype) hRPg
    (((map_subtype_le _).trans inf_le_left).trans
      (Chapter4.Section02.Unitary.sectionSylow_normalized
        hyp.plus_le hyp.plus_normal hyp.plus_perfect P))
  obtain ⟨hrQ,hUV,halt,hfixed,hcases⟩ := hd
  let Q := pushingDisplacementDomain Pg (J.pCoreIn 2) V r
  have hQV : Q ≤ centralizer (V : Set G) :=
    (commutatorPreimage_le _ _ _).trans inf_le_right
  exact ⟨hrQ,hUV,halt,hfixed,hcases.imp id
    (D.sourceOrbit_cubic_fixed_card_le_two hfix hw K hFK e x hx),
    CentralRow.subgroupHom Q V ⟨r,hrQ⟩ hUV hQV,fun _ => rfl,
    CentralRow.subgroupHom_ker Q V ⟨r,hrQ⟩ hUV hQV,
    CentralRow.subgroupHom_range_map Q V ⟨r,hrQ⟩ hUV hQV⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Sporadic.Mathieu Janko4.InvolutionCentralizers
/-- The original full source configuration with the commutator map, exact
kernel, and cubic-fixed image bound added to its resolved cubic residual. -/
@[expose] def MathieuPushingUpDisplacementCase {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (L V A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H ∧
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
      F.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K ∧
      H = K.map H.subtype ⊔ (H ⊓ centralizer (K.map H.subtype : Set G)) ∧
      ∃ (r : H.pCoreIn 2) (H₁ : Subgroup G), orderOf r = 2 ∧
        centralizer ({(r : G)} : Set G) ≤ H₁ ∧
        IsComponentIn (K.map H.subtype) H₁ ∧
        ((K.map H.subtype).subgroupOf H₁).Normal ∧
        IsComponentIn (K.map H.subtype) (centralizer ({(r : G)} : Set G)) ∧
      ∃ e : (K ⧸ center K) ≃* Janko4.Model,
        let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
        let R := First.centralizer.comap q
        ∃ x : R, orderOf x = 3 ∧ orderOf (q (x : K)) = 3 ∧
          (⟨x,mem_centralizer_singleton_iff.mpr rfl⟩ : Subgroup.centralizer ({x} : Set R)) ∈
            solvableResidual (Subgroup.centralizer ({x} : Set R)) ∧
          solvableResidual (Subgroup.centralizer ({(x : K)} : Set K)) =
            (solvableResidual (Subgroup.centralizer ({x} : Set R))).map
              (R.subtype.elementCentralizerMap x) ∧
          IsQuasisimple (solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))) ∧
          Nonempty (((solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))) ⧸
            center (solvableResidual (Subgroup.centralizer ({(x : K)} : Set K)))) ≃* M22) ∧
          (∃ g : K, ((g * (x : K) * g⁻¹ : K) : H) ∈ F.subgroupOf H ∧
            let y := g * (x : K) * g⁻¹
            IsQuasisimple (solvableResidual (centralizer ({y} : Set K))) ∧
              Nonempty ((solvableResidual (centralizer ({y} : Set K)) ⧸
                center (solvableResidual (centralizer ({y} : Set K)))) ≃* M22) ∧
              CubicAmbientData H K y ∧
              (let C := centralizer ({((y : H) : G)} : Set G) ⊓ centralizer ({(r : G)} : Set G)
               IsComponentIn (cubicResidualImage H K y) C ∧
                 ((cubicResidualImage H K y).subgroupOf C).Normal) ∧
              CubicPumpupData H K y (r : G) ∧
              CubicPumpupQuotientAction H K y (r : G) ∧
              CubicPumpupFullResolution H K y (r : G) ∧
              CubicDisplacementConclusion T L V J H K y (r : G) ∧
              ∀ Q : Subgroup (centralizer ({y} : Set K)), Q.IsCComponent →
                Q = solvableResidual (centralizer ({y} : Set K))) ∧
          ∀ Q : Subgroup (Subgroup.centralizer ({(x : K)} : Set K)), Q.IsCComponent →
            Q = solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))


end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The same full residual now has its actual displacement domain and fixed-image control. -/
theorem pushingUp_cubic_displacement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {A : Subgroup G} (hc : MathieuPushingUpNormalCubicCase L V A) :
    MathieuPushingUpDisplacementCase T L V A := by
  obtain ⟨J,H,W,hw,hesc,K,hK,hn,hout,hFK,hWK,hprod,r,H₁,hr,hCH,hrel,hn₁,hKr,
    e,x,hx,hqx,hmem,he,hquasi,heq,⟨g,hg,hqy,hey,hdata,hs,hp,hact,hfull,huy⟩,hux⟩ := hc
  have hy : orderOf (g * (x : K) * g⁻¹) = 3 :=
    ((MulAut.conj g).orderOf_eq (x : K)).trans ((orderOf_coe x).trans hx)
  let := hn
  have hdisp := D.sourceOrbit_cubic_displacement_selection h.toHypothesis1221
    (D.sourceOrbit_fixed_and_thompson_of_many h hmany hnon).1 hw K hFK e (r : G)
    (hw.2.2.2.2.2.2.1.ambient_core_le_radical r.property) hKr.1
    (g * (x : K) * g⁻¹) hy hg hfull
  exact ⟨J,H,W,hw,hesc,K,hK,hn,hout,hFK,hWK,hprod,r,H₁,hr,hCH,hrel,hn₁,hKr,
    e,x,hx,hqx,hmem,he,hquasi,heq,⟨g,hg,hqy,hey,hdata,hs,hp,hact,hfull,hdisp,huy⟩,hux⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal Hall obstruction controls cubic-fixed commutator displacements.
The full cover, original quotient maps and all Hall hypotheses are retained. -/
theorem sourceOrbit_mathieu_hall_displacement_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < ChapterE.generationParameter H)
    (B : Subgroup H) (hBN : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H)))
    (hker : B.map H.subtype ⊓ sectionCentralizer L ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ sectionCentralizer L ∧
      A ≤ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ normalizer (L : Set G)) ∧
      (∀ Q : Subgroup G, (T : Subgroup G) ≤ normalizer (Q : Set G) →
        A ≤ sectionCentralizer Q → Q ≤ normalizer (L : Set G)) ∧
      (MathieuPushingUpDisplacementCase T L V A ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoSeedResidualCase (T : Subgroup G) L V A
            (D.orbitComponent ⧸ center D.orbitComponent))) := by
  have hsource :=
    @sourceOrbit_mathieu_hall_normal_cubic_obstruction G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  refine hsource.imp fun p hp => hp.imp fun A => ?_
  iterate 11 apply And.imp_right
  exact Or.imp (D.pushingUp_cubic_displacement h hmany hnon) id

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
