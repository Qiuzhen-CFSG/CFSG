module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenSetup
public import CFSG.Quasithin.Chapter15.Section01.CentralizingControl
public import Theory.GroupTheory.PResidual.PrimeTo
public import Theory.GroupTheory.SylowIndexTwoExtension
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Stellmacher.BaumannTwoOvergroupNormalizer
public import Stellmacher.OmegaOneCenterMap

/-!
# The common reduction for the distinguished-plane uniqueness theorem

Let ZS be the actual Section 15.2 plane and S = C_T(ZS). Its full centralizer
lies in Mc = C_G(Z). An escaping overgroup therefore forces |Z| = 2 and
|T:S| = 2. The residual K = O²(H) lies in that centralizer and cannot lie in M,
so no escaping H-overgroup contains T.

To prove S is Sylow in such an I, extend S to a Sylow subgroup R of I.
Baumann control puts R in M. If R is larger than S, the ambient order bound
makes |R:S| = 2. Thus R normalizes Ω₁Z(S) = ZS and lies in Mc. The literal
intersection formula M ∩ Mc = C_M(V)T, with C_M(V) already in I, would force
T into I. This proves 15.2.18(1) without a new action-model assumption.
Index-two inheritance also gives F*(Mc ∩ I) = O₂(Mc ∩ I).

The explicit preceding inputs are ChosenSmallSource, ChosenPlaneGeometry,
15.2.5, 15.2.11(2), the literal residual identity in 15.2.12(4), and
15.2.14(1), the numerical alternatives of (2), (4), and (5).
The Kc structural alternatives, the action restrictions of 15.2.13, and the
subsequent classification arguments are not encoded by this common packet.
The prime-to-three residual is O^{3′}, not O³ or O₃.

The equal-plane case proves the requested singleton statement. In the other
case, failure of uniqueness yields a minimal genuine H-overgroup, whose
intersection with Mc is maximal inside I. The characteristic-two exclusion
15.2.23 and ordinary-component exclusion 15.2.24 and the following argument
remain required; this module does not assert the full 15.2.15 theorem.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.2.15--20 and the minimal selection preceding 15.2.23,
printed pp.1112--1115, refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The literal two-centralizer S of the distinguished plane. -/
abbrev planeSylow (T : Sylow 2 G) (ZS : Subgroup G) : Subgroup G :=
  (T : Subgroup G) ⊓ centralizer (ZS : Set G)

/-- Earlier source clauses used in the common uniqueness reduction. The action
and Kc structural alternatives are additional inputs to the later classification
branches; they are not encoded by this record. -/
structure PlaneUniquenessPreceding {T : Sylow 2 G} {M Mc V : Subgroup G}
    (hsource : ChosenSmallSource T M Mc V) (H ZS : Subgroup G) : Prop where
  geometry : ChosenPlaneGeometry hsource H ZS
  two_maximals : maximalTwoLocalOvergroups (T : Subgroup G) = {M, Mc}
  partner_eq : Mc = centralizer (centralInvolutions T : Set G)
  seed_le : centralInvolutions T ≤ ZS
  center_cases : centralInvolutions T = ZS ∨
    Nat.card (centralInvolutions T) = 2 ∧ (planeSylow T ZS).relIndex (T : Subgroup G) = 2
  omega_center : ZS = omegaOneCenterAmbient (planeSylow T ZS)
  residual_centralizes : (pResidual 2 H).map H.subtype ≤ centralizer (ZS : Set G)
  orbit_residual : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc =
    (primeToResidual 3 Mc).map Mc.subtype
  intersection : M ⊓ Mc = (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G)

/-- The source family before imposing minimality: I has nontrivial two-core,
contains the actual plane centralizer, and escapes Mc. -/
@[expose] def PlaneEscapes (Mc ZS I : Subgroup G) : Prop :=
  I ∈ Chapter1.H G ∧ Mc ⊓ centralizer (ZS : Set G) ≤ I ∧ ¬ I ≤ Mc

/-- Minimality is in the source H-family, not in all subgroups of G. -/
@[expose] def MinimalPlaneEscape (Mc ZS I : Subgroup G) : Prop :=
  Minimal (PlaneEscapes Mc ZS) I

namespace PlaneUniquenessPreceding
variable {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- Original 15.2.16: the full centralizer already lies in Mc. -/
theorem centralizer_eq : centralizer (ZS : Set G) = Mc ⊓ centralizer (ZS : Set G) := by
  symm
  apply inf_eq_right.mpr
  rw [d.partner_eq]
  exact centralizer_le d.seed_le

/-- The original residual K together with T generates H. -/
theorem residual_sup_sylow : (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H := by
  have hTH : (T : Subgroup G) ≤ H := d.geometry.outside.1.1.2
  have he := congrArg (Subgroup.map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTH))
  rw [Subgroup.map_sup, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH,
    ← MonoidHom.range_eq_map, range_subtype] at he
  exact he

/-- K cannot lie in M, since H = KT is the original H-star member outside M. -/
theorem residual_not_le : ¬ (pResidual 2 H).map H.subtype ≤ M := by
  intro hKM
  have hHM : H ≤ M := by
    rw [← d.residual_sup_sylow]
    exact sup_le hKM hsource.maximal.1.2
  exact d.geometry.outside.1.2 hHM

/-- Original 15.2.12(3)'s uniqueness for H follows from 15.2.5. -/
theorem local_unique : maximalTwoLocalOvergroups H = {Mc} := by
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hsource.partner ▸ Set.mem_singleton Mc
  ext N
  constructor
  · intro hN
    have hNT : N ∈ maximalTwoLocalOvergroups (T : Subgroup G) :=
      ⟨hN.1,d.geometry.outside.1.1.2.trans hN.2⟩
    rw [d.two_maximals,Set.mem_insert_iff,Set.mem_singleton_iff] at hNT
    rcases hNT with rfl | rfl
    · exact (d.geometry.outside.1.2 hN.2).elim
    · exact Set.mem_singleton _
  · rintro rfl
    exact ⟨hMc.1,d.geometry.in_partner⟩

/-- The equal-plane alternative of 15.2.14(2a) proves 15.2.15 immediately. -/
theorem unique_of_seed_eq (he : centralInvolutions T = ZS) :
    maximalTwoLocalOvergroups (Mc ⊓ centralizer (ZS : Set G)) = {Mc} := by
  rw [← d.centralizer_eq, ← he]
  exact hsource.partner

/-- The plane itself, not only its centralizer in T, lies in C_G(ZS). -/
theorem plane_le_centralizer : ZS ≤ centralizer (ZS : Set G) := by
  let := hsource.prepared.elementary
  have hVV : V ≤ centralizer (V : Set G) := le_centralizer_iff_isMulCommutative.mpr inferInstance
  exact d.geometry.plane_le.trans (hVV.trans (centralizer_le d.geometry.plane_le))

/-- Source 15.2.16 with the literal intersection MI. -/
theorem centralizer_le_intersection {I : Subgroup G} (hI : PlaneEscapes Mc ZS I) :
    centralizer (ZS : Set G) ≤ Mc ⊓ I := by
  rw [d.centralizer_eq]
  exact le_inf inf_le_left hI.2.1

/-- Both source generators K and S lie in MI. -/
theorem residual_sup_planeSylow_le {I : Subgroup G} (hI : PlaneEscapes Mc ZS I) :
    (pResidual 2 H).map H.subtype ⊔ planeSylow T ZS ≤ Mc ⊓ I :=
  (sup_le d.residual_centralizes inf_le_right).trans (d.centralizer_le_intersection hI)

/-- Original 15.2.17(2--3), derived by excluding the equal-plane case. -/
theorem escape_index {I : Subgroup G} (hI : PlaneEscapes Mc ZS I) :
    Nat.card (centralInvolutions T) = 2 ∧ (planeSylow T ZS).relIndex (T : Subgroup G) = 2 := by
  rcases d.center_cases with he | hi
  · have hMcI : Mc ≤ I := by
      have hle := hI.2.1
      rw [← he,← d.partner_eq,inf_idem] at hle
      exact hle
    have hcore : pCore 2 I ≠ ⊥ := by
      intro he
      apply hI.1
      change (pCore 2 I).map I.subtype = ⊥
      rw [he,Subgroup.map_bot]
    obtain ⟨N,hN,hIN⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot I hcore
    have hNM : N = Mc := by
      apply Set.mem_singleton_iff.mp
      rw [← hsource.partner]
      exact ⟨hN,d.partner_eq ▸ hMcI.trans hIN⟩
    exact (hI.2.2 (hNM ▸ hIN)).elim
  · exact hi

/-- An escaping H-member cannot contain the original ambient Sylow T. -/
theorem sylow_not_le_escape {I : Subgroup G} (hI : PlaneEscapes Mc ZS I) :
    ¬ (T : Subgroup G) ≤ I := by
  intro hTI
  have hcore : pCore 2 I ≠ ⊥ := by
    intro he
    apply hI.1
    change (pCore 2 I).map I.subtype = ⊥
    rw [he,Subgroup.map_bot]
  obtain ⟨N,hN,hIN⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot I hcore
  have hNT : N ∈ maximalTwoLocalOvergroups (T : Subgroup G) := ⟨hN,hTI.trans hIN⟩
  rw [d.two_maximals,Set.mem_insert_iff,Set.mem_singleton_iff] at hNT
  rcases hNT with rfl | rfl
  · exact d.residual_not_le ((le_sup_left.trans (d.residual_sup_planeSylow_le hI)).trans
      (inf_le_right.trans hIN))
  · exact hI.2.2 hIN

/-- The chosen module centralizer is already contained in every escaping I. -/
theorem module_centralizer_le {I : Subgroup G} (hI : PlaneEscapes Mc ZS I) :
    centralizer (V : Set G) ≤ I :=
  (centralizer_le d.geometry.plane_le).trans
    ((d.centralizer_le_intersection hI).trans inf_le_right)

/-- Original 15.2.18(1): the literal S is a Sylow subgroup of every escaping I.
Baumann control first puts a Sylow extension in M. If it grew, its index over
S would be two, so it would normalize Ω₁Z(S) = ZS and lie in Mc as well.
The preceding intersection formula would then force T into I. -/
theorem sylow_in_escape {I : Subgroup G} (hI : PlaneEscapes Mc ZS I) :
    ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = planeSylow T ZS := by
  let S := planeSylow T ZS
  have hSI : S ≤ I := (le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
  obtain ⟨P,hSP⟩ := ((T.isPGroup'.to_le (show S ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
    (K := I)).exists_le_sylow
  let R : Subgroup G := (P : Subgroup I).map I.subtype
  have hSR : S ≤ R := by
    rw [← map_subgroupOf_eq_of_le hSI]
    exact map_mono hSP
  refine ⟨P,?_⟩
  change R = S
  by_contra hne
  have hp : IsPGroup 2 R := P.isPGroup'.map I.subtype
  have hRI : R ≤ I := map_subtype_le _
  have hB : ChapterB.baumann (T : Subgroup G) ≤ R := d.geometry.baumann_le.trans hSR
  have hRM : R ≤ M :=
    (twoSubgroup_le_normalizer_baumann T R hp hB).trans
      (source_centralizing_baumann_control hsource.ambient T hsource.maximal hsource.centralizing).2.2.2.2.1
  have hmul : Nat.card S * S.relIndex R = Nat.card R := by
    simpa only [relIndex_bot_left] using relIndex_mul_relIndex ⊥ S R bot_le hSR
  have hmulT : Nat.card S * 2 = Nat.card T := by
    have he := relIndex_mul_relIndex ⊥ S (T : Subgroup G) bot_le inf_le_left
    have hhalf : S.relIndex (T : Subgroup G) = 2 := (d.escape_index hI).2
    simpa only [relIndex_bot_left,hhalf] using he
  have hbound : Nat.card R ≤ Nat.card T := card_le_sylow_two hp T
  have hpos : 0 < Nat.card S := Nat.card_pos
  have hiPos : 0 < S.relIndex R := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hiNe : S.relIndex R ≠ 1 := by
    intro he
    exact hne (le_antisymm (relIndex_eq_one.mp he) hSR)
  have hiLower : 2 ≤ S.relIndex R := by omega
  have hi : S.relIndex R = 2 := by nlinarith only [hmul,hmulT,hbound,hpos,hiLower]
  have hcard : Nat.card R = Nat.card T := by rw [← hmul,hi,hmulT]
  have hnS : (S.subgroupOf R).Normal := normal_of_index_eq_two hi
  have hRS : R ≤ normalizer (S : Set G) := (normal_subgroupOf_iff_le_normalizer hSR).mp hnS
  have hRZ : R ≤ normalizer (ZS : Set G) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq,d.omega_center,
      ← omegaOneCenterAmbient_map_injective _ (MulAut.conj x).injective,
      (mem_normalizer_iff_map_conj_eq.mp (hRS hx))]
  have hRA : R ≤ M ⊓ Mc := le_inf hRM (hRZ.trans d.geometry.plane_normalizer)
  obtain ⟨Q,hRQ⟩ := hp.exists_le_sylow
  have hRcardQ : Nat.card Q ≤ Nat.card R := by
    rw [hcard]
    exact (Nat.card_congr (Q.equiv T).toEquiv).le
  have hRQeq : R = (Q : Subgroup G) := eq_of_le_of_card_ge hRQ hRcardQ
  let A := M ⊓ Mc
  let C := M ⊓ centralizer (V : Set G)
  have hCA : C ≤ A := by
    change C ≤ M ⊓ Mc
    rw [d.intersection]
    exact le_sup_left
  have hTA : (T : Subgroup G) ≤ A := by
    change (T : Subgroup G) ≤ M ⊓ Mc
    rw [d.intersection]
    exact le_sup_right
  have hAC : A ≤ normalizer (C : Set G) :=
    inf_le_left.trans ((le_inf M.le_normalizer
      (hsource.prepared.normalized.trans (normalizer_le_normalizer_centralizer V))).trans
        inf_normalizer_le_normalizer_inf)
  let : (C.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer hAC
  have hgen : C.subgroupOf A ⊔ (T : Subgroup G).subgroupOf A = ⊤ := by
    apply map_injective A.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hCA,map_subgroupOf_eq_of_le hTA,
      ← MonoidHom.range_eq_map,range_subtype]
    exact d.intersection.symm
  have hquot : IsPGroup 2 (A ⧸ C.subgroupOf A) :=
    isPGroup_quotient_of_sup_eq_top _ _ T.isPGroup'.comap_subtype hgen
  have hQA : (Q : Subgroup G) ≤ A := hRQeq ▸ hRA
  have hcover := congrArg (Subgroup.map A.subtype)
    ((Q.subtype hQA).sup_eq_top_of_quotient_isPGroup (C.subgroupOf A) hquot)
  have hcover' : R ⊔ C = A := by
    rw [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hQA,
      map_subgroupOf_eq_of_le hCA,← MonoidHom.range_eq_map,range_subtype,← hRQeq] at hcover
    exact hcover
  apply d.sylow_not_le_escape hI
  exact hTA.trans (hcover' ▸ sup_le hRI (inf_le_right.trans (d.module_centralizer_le hI)))

/-- Original 15.2.20(2) follows directly from the index-two inheritance theorem,
with normality and Sylow restriction taken inside Mc. -/
theorem intersection_characteristicTwo {I : Subgroup G} (hI : PlaneEscapes Mc ZS I) :
    generalizedFitting (Mc ⊓ I : Subgroup G) = pCore 2 (Mc ⊓ I : Subgroup G) := by
  have hMc : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hsource.partner ▸ Set.mem_singleton Mc).1
  have hTMc : (T : Subgroup G) ≤ Mc := by
    have he := d.intersection
    exact (show (T : Subgroup G) ≤ M ⊓ Mc by rw [he]; exact le_sup_right).trans inf_le_right
  have hSMI : planeSylow T ZS ≤ Mc ⊓ I :=
    le_sup_right.trans (d.residual_sup_planeSylow_le hI)
  have hne : Mc ⊓ I ≠ ⊥ := by
    intro he
    have hb : ZS = ⊥ := bot_unique ((d.plane_le_centralizer.trans
      (d.centralizer_le_intersection hI)).trans_eq he)
    have hc := d.geometry.plane_card
    rw [hb,Subgroup.card_bot] at hc
    omega
  have hi : ((Mc ⊓ I).subgroupOf Mc).relIndex ((T.subtype hTMc : Sylow 2 Mc) : Subgroup Mc) ≤ 2 := by
    change ((Mc ⊓ I).subgroupOf Mc).relIndex ((T : Subgroup G).subgroupOf Mc) ≤ 2
    rw [relIndex_subgroupOf hTMc]
    exact (relIndex_le_of_le_left hSMI index_ne_zero_of_finite).trans_eq (d.escape_index hI).2
  exact generalizedFitting_eq_pCore_of_selfCentralizing 2 (Chapter1.mem_He_iff.mp
    (Chapter1.lemma_1_1_4_7
      (Chapter1.mem_He_iff.mpr (hsource.ambient.evenCharacteristic T Mc hMc hTMc))
      (T.subtype hTMc) hne inf_le_left hi))

/-- Minimality applies to all intermediate subgroups containing MI: the actual
normal two-core of I is carried by S and survives in each such subgroup. -/
theorem minimal_intermediate {I J : Subgroup G} (hI : MinimalPlaneEscape Mc ZS I)
    (hMIJ : Mc ⊓ I ≤ J) (hJI : J ≤ I) : J = Mc ⊓ I ∨ J = I := by
  by_cases hJMc : J ≤ Mc
  · exact Or.inl (le_antisymm (le_inf hJMc hJI) hMIJ)
  · right
    apply le_antisymm hJI
    apply hI.2
    · have hcore : I.pCoreIn 2 ≤ planeSylow T ZS := by
        obtain ⟨P,hP⟩ := d.sylow_in_escape hI.1
        exact (pCoreIn_le_sylow I P).trans_eq hP
      have hQJ : I.pCoreIn 2 ≤ J := hcore.trans
        ((le_sup_right.trans (d.residual_sup_planeSylow_le hI.1)).trans hMIJ)
      have hQQ : I.pCoreIn 2 ≤ J.pCoreIn 2 := by
        simpa only [inf_eq_right.mpr hQJ] using inf_pCoreIn_le_of_le 2 hJI
      refine ⟨?_,?_,hJMc⟩
      · intro hbot
        exact hI.1.1 (bot_unique (hQQ.trans_eq hbot))
      · exact (le_inf inf_le_left hI.1.2.1).trans hMIJ
    · exact hJI

omit [Finite G] d in
/-- The strict intersection is the source maximal subgroup MI of the minimal I. -/
theorem minimal_intersection_lt {I : Subgroup G} (hI : MinimalPlaneEscape Mc ZS I) :
    Mc ⊓ I < I :=
  lt_of_le_of_ne inf_le_right (fun he => hI.1.2.2 (he ▸ inf_le_left))

/-- Failure of the requested singleton theorem produces a minimal genuine
H-overgroup. This is the selection made on printed p.1115. -/
theorem exists_minimal_escape
    (hne : maximalTwoLocalOvergroups (Mc ⊓ centralizer (ZS : Set G)) ≠ {Mc}) :
    ∃ I : Subgroup G, MinimalPlaneEscape Mc ZS I := by
  classical
  have hMc : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hsource.partner ▸ Set.mem_singleton Mc).1
  have hex : ∃ N ∈ maximalTwoLocalOvergroups (Mc ⊓ centralizer (ZS : Set G)), N ≠ Mc := by
    by_contra! hn
    apply hne
    ext N
    constructor
    · exact fun hN => Set.mem_singleton_iff.mpr (hn N hN)
    · rintro rfl
      exact ⟨hMc,inf_le_left⟩
  obtain ⟨N,hN,hNM⟩ := hex
  have hescape : PlaneEscapes Mc ZS N := by
    refine ⟨Chapter1.mem_H_of_isTwoLocal hN.1.1,hN.2,?_⟩
    intro hle
    exact hNM (le_antisymm hle (hN.1.2 hMc.1 hle))
  exact (Set.toFinite {I | PlaneEscapes Mc ZS I}).exists_minimal ⟨N,hescape⟩

end PlaneUniquenessPreceding
end CFSG.Quasithin.Chapter15.Section02
