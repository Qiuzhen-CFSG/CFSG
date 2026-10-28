module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient
public import Theory.Representation.PSL3Two.NaturalOrbits
public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual
public import Theory.GroupTheory.CentralCommutatorQuotient
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Large Frattini commutators in the fourth MS alternative

Write Q = msQ K R, Z = Z(Q), Φ = Φ(Q), and D = C_Q(Φ). The genuine
MS-pair puts Q inside O₂(K). Its action on Φ/Z is trivial, so [Φ,Q] ≤ Z
and commutator evaluation on Q is a homomorphism.

The dual natural action is transitive on nonzero vectors. Thus three actual
K-conjugates of any x ∈ Φ ∖ Z represent a basis of Φ/Z. If [⟨x⟩,Q] had
order at most two, the three corresponding centralizers would each have index
at most two. Their intersection is D, giving |Q/D| ≤ 8, whereas the supplied
two-natural-copy model gives |Q/D| = 64.

All quotient maps and conjugates below use the same supplied actor e. No
assertion about the image being C_Q(K) is needed. The consumer applications
discharge FrattiniCommutatorLarge and leave only the independent structural
hypothesis FrattiniCentralizerControl explicit for the assembly owner.

Sources: Aschbacher–Smith, combined manuscript of 1 March 2004, C.1.34(4),
printed pp.136–137 (PDF147–148), and 13.6.22, printed pp.932–933
(PDF949–950); Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of
rank two*, Lemma 4.5, printed pp.895–900 (PDF72–77).
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters
open BinaryLinearThree.AutomorphismAction
local notation "sCenter" => CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient

private abbrev Dual := Module.Dual (ZMod 2) BinaryLinearThree.Vector

private lemma dual_transitive (u v : Dual) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ g : BinaryLinearThree.Group, BinaryLinearThree.W.dual g u = v := by
  let E := graphDualNatural.toLinearEquiv
  obtain ⟨g, hg⟩ := BinaryLinearThree.natural_transitive_nonzero (E u) (E v)
    (by simpa using hu) (by simpa using hv)
  refine ⟨graph g, E.injective ?_⟩
  have hh := LinearMap.congr_fun (graphDualNatural.isIntertwining' g) u
  exact hh.trans hg

private noncomputable def dualBasis : Module.Basis (Fin 3) (ZMod 2) Dual :=
  (Pi.basisFun (ZMod 2) (Fin 3)).map graphNaturalDual.toLinearEquiv

private lemma dualBasis_generates :
    Subgroup.closure (Set.range fun i => Multiplicative.ofAdd (dualBasis i)) = ⊤ := by
  have hadd : AddSubgroup.closure (Set.range fun i => dualBasis i) = ⊤ := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.toAddSubgroup_eq_top]
    have hsurj : Function.Surjective (algebraMap ℤ (ZMod 2)) := by
      simpa using (ZMod.intCast_surjective (n := 2))
    calc
      Submodule.span ℤ (Set.range fun i => dualBasis i) =
          (Submodule.span (ZMod 2) (Set.range fun i => dualBasis i)).restrictScalars ℤ := by
        symm
        exact Submodule.restrictScalars_span ℤ (ZMod 2) hsurj _
      _ = ⊤ := by simp [dualBasis.span_eq]
  have hr : Multiplicative.toAdd ⁻¹' Set.range (fun i => dualBasis i) =
      Set.range (fun i => Multiplicative.ofAdd (dualBasis i)) := by
    ext v
    simp only [Set.mem_preimage, Set.mem_range]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, congrArg Multiplicative.ofAdd hi⟩,
      fun ⟨i, hi⟩ => ⟨i, congrArg Multiplicative.toAdd hi⟩⟩
  rw [← hr, ← AddSubgroup.toSubgroup_closure, hadd]
  rfl

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private lemma core_commutator_section {K P Z : Subgroup G}
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (h : HasSectionModel K P Z (linearThreeActor e) BinaryLinearThree.W.dual) :
    ⁅K.pCoreIn 2,P⁆ ≤ Z := by
  obtain ⟨_, hKP, _, hn, f, he⟩ := h
  let := hn
  apply commutator_le.mpr
  intro x hx y hy
  obtain ⟨k,hk,rfl⟩ := hx
  let y' := P.normalizerMonoidHom ⟨k,hKP k.property⟩ ⟨y,hy⟩
  have ha : linearThreeActor e k = 1 := by
    change k ∈ (linearThreeActor e).ker
    rwa [linearThreeActor_kernel]
  have hh : f (QuotientGroup.mk' _ y') = f (QuotientGroup.mk' _ ⟨y,hy⟩) := by
    apply Multiplicative.toAdd.injective
    simpa only [ha, map_one, Module.End.one_apply] using he k ⟨y,hy⟩ y' rfl
  have hd := QuotientGroup.eq_iff_div_mem.mp (f.injective hh)
  change (k : G) * y * (k : G)⁻¹ / y ∈ Z at hd
  simpa only [div_eq_mul_inv, commutatorElement_def, Subgroup.coe_subtype] using hd

omit [Finite G] in
private lemma centralizer_index_bound (P Q Z : Subgroup G)
    (hZ : Z ≤ centralizer (Q : Set G)) [(Z.subgroupOf P).Normal]
    (e : (P ⧸ Z.subgroupOf P) ≃* Multiplicative Dual)
    (y : Fin 3 → P)
    (hy : ∀ i, e (QuotientGroup.mk' _ (y i)) = Multiplicative.ofAdd (dualBasis i))
    (hb : ∀ i, ((centralizer ({(y i : G)} : Set G)).subgroupOf Q).index ≤ 2) :
    ((Q ⊓ centralizer (P : Set G)).subgroupOf Q).index ≤ 8 := by
  let A (i : Fin 3) := (centralizer ({(y i : G)} : Set G)).subgroupOf Q
  have hi : (Q ⊓ centralizer (P : Set G)).subgroupOf Q = ⨅ i, A i := by
    ext q
    constructor
    · intro hq
      apply mem_iInf.mpr
      intro i
      exact mem_centralizer_singleton_iff.mpr ((hq.2 (y i) (y i).property).symm)
    · intro hq
      let C := centralizer ({(q : G)} : Set G)
      let f := e.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf P))
      have hfker : f.ker = Z.subgroupOf P := by
        ext a
        change e (QuotientGroup.mk' _ a) = 1 ↔ _
        rw [← map_one e, e.injective.eq_iff]
        exact QuotientGroup.eq_one_iff a
      have hZC : Z ≤ C := by
        intro z hz
        exact mem_centralizer_singleton_iff.mpr (hZ hz q q.property).symm
      have hyC (i : Fin 3) : (y i : G) ∈ C := by
        exact mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp (mem_iInf.mp hq i)).symm
      have htop : (C.subgroupOf P).map f = ⊤ := by
        apply top_unique
        rw [← dualBasis_generates]
        apply (closure_le _).mpr
        rintro _ ⟨i,rfl⟩
        exact ⟨y i, hyC i, hy i⟩
      have hCtop : C.subgroupOf P = ⊤ := by
        have hh := congrArg (Subgroup.comap f) htop
        rw [comap_map_eq, hfker, sup_of_le_left (show Z.subgroupOf P ≤ C.subgroupOf P from fun _ hz => hZC hz), comap_top] at hh
        exact hh
      refine ⟨q.property, ?_⟩
      intro p hp
      have hh : (⟨p,hp⟩ : P) ∈ C.subgroupOf P := by rw [hCtop]; trivial
      simpa only [Subgroup.coe_subtype] using (mem_centralizer_singleton_iff.mp hh)
  rw [hi]
  calc
    (⨅ i, A i).index ≤ ∏ i, (A i).index := index_iInf_le A
    _ ≤ ∏ _i : Fin 3, 2 := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => hb i)
    _ = 8 := by decide

open CFSG.Quasithin.ChapterC

/-- The fourth MS sections force every noncentral Frattini element to have
more than two commutators. Subnormality and two-perfection put Q in O₂(K),
so the same actor makes its commutators with Φ(Q) central. -/
theorem caseFour_frattiniCommutatorLarge_of_core_hypotheses {K R S : Subgroup G}
    (hs : (K.subgroupOf (K ⊔ R)).IsSubnormal) (hp : IsPPerfect 2 K)
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e) :
    FrattiniCommutatorLarge (msQ K R) := by
  classical
  let Q := msQ K R
  let P := frattiniIn Q
  let Z := sCenter Q
  have hQcore : Q ≤ K.pCoreIn 2 := by
    dsimp [Q]
    rw [msQ_eq_ambient_blockU K R hs hp]
    exact map_mono blockU_le_core
  obtain ⟨_, _, _, _, _, _, hP, _, hQ, _⟩ := h
  -- O₂(K) acts trivially on the literal Frattini quotient.
  have hc : ⁅P,Q⁆ ≤ Z := by
    rw [commutator_comm]
    exact (commutator_mono hQcore le_rfl).trans (core_commutator_section e hP)
  obtain ⟨_, hKP, _, hnP, f, he⟩ := hP
  let := hnP
  obtain ⟨_, hKQ, _, hnQ, fQ, _⟩ := hQ
  let := hnQ
  have hidx : ((Q ⊓ centralizer (P : Set G)).subgroupOf Q).index = 64 := by
    change Nat.card (Q ⧸ (Q ⊓ centralizer (P : Set G)).subgroupOf Q) = 64
    rw [Nat.card_congr fQ.toEquiv]
    rw [Nat.card_congr Multiplicative.toAdd]
    simp [BinaryLinearThree.Vector]
  have hZ : Z ≤ centralizer (Q : Set G) := by
    change sCenter Q ≤ _
    rw [centerIn_eq]
    exact inf_le_right
  intro x hx hxn
  by_contra! hsmall
  let u : Dual := (f (QuotientGroup.mk' _ ⟨x,hx⟩)).toAdd
  have hu : u ≠ 0 := by
    intro hu0
    have hh : f (QuotientGroup.mk' _ ⟨x,hx⟩) = 1 :=
      Multiplicative.toAdd.injective hu0
    have hz := (QuotientGroup.eq_one_iff (⟨x,hx⟩ : P)).mp
      (f.injective (hh.trans (map_one f).symm))
    exact hxn hz
  -- Lift a dual basis to three actual K-conjugates of x.
  have horbit (i : Fin 3) : ∃ k : K,
      BinaryLinearThree.W.dual (linearThreeActor e k) u = dualBasis i := by
    obtain ⟨g,hg⟩ := dual_transitive u (dualBasis i) hu (dualBasis.ne_zero i)
    obtain ⟨k,rfl⟩ := linearThreeActor_surjective e g
    exact ⟨k,hg⟩
  choose k hk using horbit
  let y (i : Fin 3) : P :=
    P.normalizerMonoidHom ⟨k i, hKP (k i).property⟩ ⟨x,hx⟩
  have hy (i : Fin 3) : f (QuotientGroup.mk' _ (y i)) =
      Multiplicative.ofAdd (dualBasis i) := by
    apply Multiplicative.toAdd.injective
    exact (he (k i) ⟨x,hx⟩ (y i) rfl).trans (hk i)
  have hcard (i : Fin 3) : Nat.card (⁅zpowers (y i : G),Q⁆ : Subgroup G) ≤ 2 := by
    have hmap : (⁅zpowers x,Q⁆ : Subgroup G).map (MulAut.conj (k i : G)).toMonoidHom =
        ⁅zpowers (y i : G),Q⁆ := by
      have hQmap : Q.map (MulAut.conj (k i : G)).toMonoidHom = Q :=
        mem_normalizer_iff_map_conj_eq.mp (hKQ (k i).property)
      rw [map_commutator, MonoidHom.map_zpowers, hQmap]
      rfl
    rw [← hmap, card_map_of_injective (MulAut.conj (k i : G)).injective]
    exact hsmall
  -- Each centralizer has index at most the common commutator order.
  have hb (i : Fin 3) : ((centralizer ({(y i : G)} : Set G)).subgroupOf Q).index ≤ 2 := by
    let V := ⁅zpowers (y i : G),Q⁆
    have hV : V ≤ centralizer (Q : Set G) :=
      ((commutator_mono (zpowers_le.mpr (y i).property) le_rfl).trans hc).trans hZ
    have hr : ∀ q ∈ Q, ⁅(y i : G),q⁆ ∈ V := fun q hq =>
      commutator_mem_commutator (mem_zpowers _) hq
    rw [← centralCommutatorHom_ker Q V hV (y i) hr, index_ker]
    exact (centralCommutatorHom Q V hV (y i) hr).range.card_le_card_group.trans (hcard i)
  -- Their intersection is C_Q(Φ(Q)), so its index is at most 2³.
  have hbound := centralizer_index_bound P Q Z hZ f y hy hb
  omega


/-- The requested large-commutator bound for a genuine fourth-case MS-pair. -/
theorem caseFour_frattiniCommutatorLarge {κ : CFSG.Quasithin.GroupClass}
    {K R S : Subgroup G} (hMS : LinearThreeMSPair κ K R 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e) :
    FrattiniCommutatorLarge (msQ K R) :=
  caseFour_frattiniCommutatorLarge_of_core_hypotheses
    (msPair_core_hypotheses hMS).1 (msPair_core_hypotheses hMS).2 e h

/-- Application to the published central-quotient reduction: the Frattini
commutator premise is discharged from CaseFour. The independent D-control
premise remains with the source-theorem assembly owner. -/
theorem caseFour_quotient_control_of_frattiniCentralizerControl
    {κ : CFSG.Quasithin.GroupClass} {K R S : Subgroup G}
    (hMS : LinearThreeMSPair κ K R 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e)
    {H : Type*} [Group H] (f : K →* H) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (hcard : Nat.card f.ker ∣ 2)
    (hN : f.ker.map K.subtype ≤ sCenter (K ⊔ R))
    (hD : FrattiniCentralizerControl (msQ K R) (msQ K R ⊓ centralizer (K : Set G))) :
    ⁅(sCenter (pCore 2 H)).comap f, (⊤ : Subgroup K)⁆ ≤ sCenter (pCore 2 K) ∧
    ⁅(sCenter (pCore 2 H)).comap f, (⊤ : Subgroup K)⁆ =
      ⁅sCenter (pCore 2 K), (⊤ : Subgroup K)⁆ :=
  caseFour_quotient_control_of_structure
    (msPair_core_hypotheses hMS).1 (msPair_core_hypotheses hMS).2 e h
    f hf hk hcard hN hD (caseFour_frattiniCommutatorLarge hMS e h)

open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels

/-- The literal R = Tv T v application in 13.6.22, with only the independent
Frattini-centralizer control still explicit. -/
theorem caseFour_checked_commutator_of_frattiniCentralizerControl
    {κ : CFSG.Quasithin.GroupClass} {K S : Subgroup G}
    (T : Subgroup G) (v : G) (hK : K ≤ Gv v) (hv : v ^ 2 = 1)
    (hMS : LinearThreeMSPair κ K (Tv T v) 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K (Tv T v) S e)
    (hD : FrattiniCentralizerControl (msQ K (Tv T v))
      (msQ K (Tv T v) ⊓ centralizer (K : Set G))) :
    ⁅sourceZ0 K v hK,K⁆ = sourceU K :=
  caseFour_checked_commutator_of_structure T v hK hv hMS e h hD
    (caseFour_frattiniCommutatorLarge hMS e h)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient
