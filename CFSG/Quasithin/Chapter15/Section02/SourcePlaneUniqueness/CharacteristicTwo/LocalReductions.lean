module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo
public import Theory.GroupTheory.UniqueLocalResidualKernel
public import Theory.GroupTheory.PResidual.PrimeToMonotone
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Families
public import CFSG.Quasithin.Chapter1.Section03.Terminal.Modules
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.WreathOuter

/-!
# Local reductions for the characteristic-two plane escape

Write K = O²(H), Kc = ⟨K^Mc⟩ = O^{3′}(Mc), and S = C_T(ZS).
The literal residual images are used throughout. Normality of an auxiliary
X is always relative to I, expressed by X ≤ I and I ≤ N_G(X).

First, a T-invariant subgroup of I containing S and K lies in Mc: its
nontrivial two-core survives after adjoining T, and 15.2.12(3) controls the
resulting two-local overgroup. This rules out T-invariance of
O²(M ∩ I) C_M(V) when that residual does not centralize V, the group-theoretic
reduction in 15.2.18(3).

Next, |T:S| = 2 controls the intersection of I with every two-subgroup of T.
Applied to O₂(Kc), it shows that this two-core normalizes any relatively
normal, two-perfect X ≤ I which lies in Kc. The Thompson A × B argument
then transfers nontrivial action on Ω₁Z(O₂(X)) to that of Kc on Ω₁Z(O₂(Kc)).
Even characteristic supplies the self-centralizing core of Kc. If Kc = K,
its wreath quotient makes H solvable. In the other case the earlier orbit
alternative gives a forbidden faithful local component.

Thus `no_normal_perfect_threeResidual` proves the first preliminary
exclusion in 15.2.23. Its only additional source premise is the stated
weakening of 15.2.12(2): Kc is K or a T-orbit of a member of L(G,T).
The producers are the earlier small-parabolic/plane-geometry branches;
the outer chosen-action assembly must discharge this earlier premise.
The remaining block and terminal component exclusions are not asserted here.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.2.18(3), printed p.1113, and the first paragraph of the proof of
15.2.23, printed p.1115; refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d
namespace PlaneUniquenessPreceding

/-- The actual core of I lies in its proved Sylow subgroup S. -/
theorem core_le_plane (hI : PlaneEscapes Mc ZS I) :
    I.pCoreIn 2 ≤ planeSylow T ZS := by
  obtain ⟨P,hP⟩ := d.sylow_in_escape hI
  exact (pCoreIn_le_sylow I P).trans_eq hP

/-- The overgroup-uniqueness argument used in 15.2.18 and 15.2.22. -/
theorem normalized_intermediate_le_partner (hI : PlaneEscapes Mc ZS I)
    {J : Subgroup G} (hJI : J ≤ I) (hSJ : planeSylow T ZS ≤ J)
    (hKJ : (pResidual 2 H).map H.subtype ≤ J)
    (hTJ : (T : Subgroup G) ≤ normalizer (J : Set G)) : J ≤ Mc := by
  have hQJ : I.pCoreIn 2 ≤ J := (d.core_le_plane hI).trans hSJ
  have hQQ : I.pCoreIn 2 ≤ J.pCoreIn 2 := by
    simpa only [inf_eq_right.mpr hQJ] using inf_pCoreIn_le_of_le 2 hJI
  have hQne : J.pCoreIn 2 ≠ ⊥ := by
    intro he
    exact hI.1 (bot_unique (hQQ.trans_eq he))
  let D := J ⊔ (T : Subgroup G)
  have hQD : J.pCoreIn 2 ≤ D.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left (sup_le J.le_normalizer hTJ)
  have hDne : pCore 2 D ≠ ⊥ := by
    intro he
    apply hQne
    apply bot_unique
    simpa only [pCoreIn, he, Subgroup.map_bot] using hQD
  obtain ⟨N,hN,hDN⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot D hDne
  have hHN : H ≤ N := by
    rw [← d.residual_sup_sylow]
    exact (sup_le_sup_right hKJ _).trans hDN
  have hNM : N = Mc := by
    apply Set.mem_singleton_iff.mp
    rw [← d.local_unique]
    exact ⟨hN,hHN⟩
  exact (le_sup_left.trans hDN).trans_eq hNM

/-- The two-residual of the literal M ∩ Mc lies in C_M(V), by 15.2.14(5). -/
theorem partner_intersection_residual_le_module_centralizer :
    (pResidual 2 (M ⊓ Mc : Subgroup G)).map (M ⊓ Mc).subtype ≤
      M ⊓ centralizer (V : Set G) := by
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
  have hres := map_mono ((pResidual_le_iff_isPGroup_quotient 2 (C.subgroupOf A)).mpr hquot)
    (f := A.subtype)
  rwa [map_subgroupOf_eq_of_le hCA] at hres

/-- The noncentral residual image in 15.2.18 cannot have T-invariant full preimage. -/
theorem residual_join_centralizer_not_normalized
    (hI : PlaneEscapes Mc ZS I)
    (hout : ¬ (pResidual 2 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype ≤
      centralizer (V : Set G)) :
    ¬ (T : Subgroup G) ≤ normalizer
      (((pResidual 2 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype ⊔
        (M ⊓ centralizer (V : Set G)) : Subgroup G) : Set G) := by
  let X := (pResidual 2 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype
  let C := M ⊓ centralizer (V : Set G)
  let K := (pResidual 2 H).map H.subtype
  let S := planeSylow T ZS
  intro hT
  have hSI : S ≤ I :=
    (le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
  have hKI : K ≤ I :=
    (le_sup_left.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
  have hCI : C ≤ I := inf_le_right.trans (d.module_centralizer_le hI)
  have hXI : X ≤ I := (map_subtype_le _).trans inf_le_right
  have hTS : (T : Subgroup G) ≤ normalizer (S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).mp
      (normal_of_index_eq_two (d.escape_index hI).2)
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    d.geometry.outside.1.1.2.trans
      (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pResidual 2 H)))
  have hTJ : (T : Subgroup G) ≤ normalizer ((X ⊔ C ⊔ S ⊔ K : Subgroup G) : Set G) :=
    (le_inf ((le_inf hT hTS).trans (normalizer_inf_normalizer_le_normalizer_sup _ _))
      hTK).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hJMc := d.normalized_intermediate_le_partner hI
    (sup_le (sup_le (sup_le hXI hCI) hSI) hKI)
    (le_sup_right.trans le_sup_left) le_sup_right hTJ
  have hXA : X ≤ M ⊓ Mc := le_inf ((map_subtype_le _).trans inf_le_left)
    ((le_sup_left.trans (le_sup_left.trans le_sup_left)).trans hJMc)
  have hpX : IsPPerfect 2 X := isPPerfect_embedded_pResidual 2 (M ⊓ I)
  have hres := embedded_pResidual_mono 2 hXA
  rw [(pResidual_eq_top_iff 2 X).mpr hpX, ← MonoidHom.range_eq_map, range_subtype] at hres
  exact hout ((hres.trans d.partner_intersection_residual_le_module_centralizer).trans inf_le_right)

/-- Intersecting I with a two-subgroup of T is the same as intersecting S. -/
theorem twoGroup_intersection (hI : PlaneEscapes Mc ZS I)
    {Q : Subgroup G} (hQT : Q ≤ (T : Subgroup G)) :
    I ⊓ Q = planeSylow T ZS ⊓ Q := by
  obtain ⟨P,hP⟩ := d.sylow_in_escape hI
  have hTI : (T : Subgroup G) ⊓ I = planeSylow T ZS := by
    rw [← hP]
    exact inf_eq_sylow_map P T.isPGroup' (hP ▸ inf_le_left)
  apply le_antisymm
  · exact le_inf (fun x hx => hTI ▸ (show x ∈ (T : Subgroup G) ⊓ I from ⟨hQT hx.2,hx.1⟩)) inf_le_right
  · exact inf_le_inf_right Q ((le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right)

/-- Every such intersection has index at most two in the given two-subgroup. -/
theorem twoGroup_intersection_index (hI : PlaneEscapes Mc ZS I)
    {Q : Subgroup G} (hQT : Q ≤ (T : Subgroup G)) :
    (I ⊓ Q).relIndex Q ≤ 2 := by
  let S := planeSylow T ZS
  let Sn := S.subgroupOf (T : Subgroup G)
  let : Sn.Normal := normal_of_index_eq_two (d.escape_index hI).2
  have hd := Sn.relIndex_dvd_index_of_normal (Q.subgroupOf (T : Subgroup G))
  have he : Sn.index = 2 := (d.escape_index hI).2
  rw [he] at hd
  rw [d.twoGroup_intersection hI hQT, inf_relIndex_right]
  rw [relIndex_subgroupOf hQT] at hd
  exact Nat.le_of_dvd (by decide) hd

/-- Relative normality and two-perfectness upgrade mutual normalization. -/
theorem normal_twoPerfect_normalized_by_twoGroup (hI : PlaneEscapes Mc ZS I)
    {X Q : Subgroup G} (hXI : X ≤ I) (hIX : I ≤ normalizer (X : Set G))
    (hpX : IsPPerfect 2 X) (hQT : Q ≤ (T : Subgroup G))
    (hXQ : X ≤ normalizer (Q : Set G)) : Q ≤ normalizer (X : Set G) := by
  let W := I ⊓ Q
  have hXW : X ≤ normalizer (W : Set G) :=
    (le_inf (hXI.trans I.le_normalizer) hXQ).trans inf_normalizer_le_normalizer_inf
  have hi : W.relIndex Q ≤ 2 := d.twoGroup_intersection_index hI hQT
  have hpos : 0 < W.relIndex Q := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hc : ⁅Q,X⁆ ≤ W := by
    have hcases : W.relIndex Q = 1 ∨ W.relIndex Q = 2 := by omega
    rcases hcases with hi | hi
    · exact (le_normalizer_iff_commutator_le_left.mp hXQ).trans (relIndex_eq_one.mp hi)
    · exact commutator_le_of_normalized_index_two Q W X inf_le_right hi hXQ hXW
  have hQW : Q ≤ normalizer (W : Set G) := by
    change Q ≤ normalizer ((I ⊓ Q : Subgroup G) : Set G)
    rw [d.twoGroup_intersection hI hQT]
    have hTS : (T : Subgroup G) ≤ normalizer (planeSylow T ZS : Set G) :=
      (normal_subgroupOf_iff_le_normalizer inf_le_left).mp
        (normal_of_index_eq_two (d.escape_index hI).2)
    exact (le_inf (hQT.trans hTS) Q.le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hx : (pResidual 2 X).map X.subtype = X := by
    rw [(pResidual_eq_top_iff 2 X).mpr hpX, ← MonoidHom.range_eq_map, range_subtype]
  have hn := normalizes_residual_of_commutator_le_two Q I X W hIX inf_le_left
    ((T.isPGroup'.to_le hQT).to_le inf_le_right) hQW (by simpa only [hx] using hc)
  simpa only [hx] using hn

/-- The core of the actual normal closure Kc lies in the original T. -/
theorem partner_residual_core_le_sylow :
    (conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc).pCoreIn 2 ≤
      (T : Subgroup G) := by
  have hTMc : (T : Subgroup G) ≤ Mc := by
    have h := d.intersection
    exact (show (T : Subgroup G) ≤ M ⊓ Mc by rw [h]; exact le_sup_right).trans inf_le_right
  have hKcMc : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc ≤ Mc :=
    conjugateSpanBy_le_self ((map_subtype_le _).trans d.geometry.in_partner)
  have hcore := pCoreIn_mono_of_normalizes (p := 2) hKcMc
    (le_normalizer_conjugateSpanBy _ _)
  have hSylow := pCoreIn_le_sylow Mc (T.subtype hTMc)
  rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc] at hSylow
  exact hcore.trans hSylow

/-- O₂(Kc) normalizes the source X, with O^{3′}(X) = X retained literally. -/
theorem normal_threeResidual_core_normalizes (hI : PlaneEscapes Mc ZS I)
    {X : Subgroup G} (hXI : X ≤ I) (hIX : I ≤ normalizer (X : Set G))
    (hpX : IsPPerfect 2 X) (hXMc : X ≤ Mc) (hXres : primeToResidual 3 X = ⊤) :
    (conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc).pCoreIn 2 ≤
      normalizer (X : Set G) := by
  have hXKc : X ≤ conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc := by
    rw [d.orbit_residual]
    have hm := embedded_primeToResidual_mono 3 hXMc
    rwa [hXres,←MonoidHom.range_eq_map,range_subtype] at hm
  exact d.normal_twoPerfect_normalized_by_twoGroup hI hXI hIX hpX
    d.partner_residual_core_le_sylow
    (hXKc.trans ((conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))))

/-- Even characteristic descends from Mc to its actual normal closure Kc. -/
theorem partner_residual_core_selfCentralizing :
    let Kc := conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc
    Kc ⊓ centralizer (Kc.pCoreIn 2 : Set G) ≤ Kc.pCoreIn 2 := by
  let Kc := conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    have h := d.intersection
    exact (show (T : Subgroup G) ≤ M ⊓ Mc by rw [h]; exact le_sup_right).trans inf_le_right
  have hMc : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hsource.partner ▸ Set.mem_singleton Mc).1
  have hc := hsource.ambient.evenCharacteristic T Mc hMc hTMc
  have hc' : Mc ⊓ centralizer (Mc.pCoreIn 2 : Set G) ≤ Mc.pCoreIn 2 := by
    intro x hx
    have hi : (⟨x,hx.1⟩ : Mc) ∈ centralizer (pCore 2 Mc : Set Mc) := by
      intro q hq
      apply Subtype.ext
      exact hx.2 q (mem_map_of_mem Mc.subtype hq)
    exact mem_map_of_mem Mc.subtype (hc hi)
  have hKcMc : Kc ≤ Mc :=
    conjugateSpanBy_le_self ((map_subtype_le _).trans d.geometry.in_partner)
  have hn : (Kc.subgroupOf Mc).Normal :=
    normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  exact pCoreIn_selfCentralizing_of_subnormal hc' hKcMc hn.isSubnormal

open ChapterA.Section04 in
/-- The Thompson A × B argument transfers the nontrivial omega-center action. -/
theorem normal_threeResidual_moves_partner_core (hI : PlaneEscapes Mc ZS I)
    {X : Subgroup G} (hXI : X ≤ I) (hIX : I ≤ normalizer (X : Set G))
    (hpX : IsPPerfect 2 X) (hXMc : X ≤ Mc) (hXres : primeToResidual 3 X = ⊤)
    (hmove : intrinsicSignalizerModule X ≠ ⊥) :
    intrinsicSignalizerModule (conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc) ≠ ⊥ := by
  let Kc := conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc
  let Q := Kc.pCoreIn 2
  let Z0 := omegaOneCenterAmbient (X.pCoreIn 2)
  have hXKc : X ≤ Kc := by
    change X ≤ conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc
    rw [d.orbit_residual]
    have hm := embedded_primeToResidual_mono 3 hXMc
    rwa [hXres,←MonoidHom.range_eq_map,range_subtype] at hm
  have hKcQ : Kc ≤ normalizer (Q : Set G) :=
    Kc.le_normalizer.trans (normalizer_le_normalizer_intrinsicCore Kc)
  have hXQ : X ≤ normalizer (Q : Set G) := hXKc.trans hKcQ
  have hQX : Q ≤ normalizer (X : Set G) :=
    d.normal_threeResidual_core_normalizes hI hXI hIX hpX hXMc hXres
  have hcomm : ⁅Q,X⁆ ≤ X.pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes
      ((isPGroup_pCoreIn 2 Kc).to_le (le_normalizer_iff_commutator_le_left.mp hXQ))
      (le_normalizer_iff_commutator_le_right.mp hQX)
      (normalizer_commutator_ge_right Q X)
  have hXZ : X ≤ normalizer (Z0 : Set G) :=
    X.le_normalizer.trans ((normalizer_le_normalizer_intrinsicCore X).trans
      (normalizer_le_normalizer_omegaCenter _))
  have hQZ : Q ≤ normalizer (Z0 : Set G) :=
    hQX.trans ((normalizer_le_normalizer_intrinsicCore X).trans
      (normalizer_le_normalizer_omegaCenter _))
  have hkill : X.pCoreIn 2 ≤ centralizer (Z0 : Set G) := by
    intro q hq z hz
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 q hq |>.symm
  have hfixed : Z0 ⊓ centralizer (Q : Set G) ≤ omegaOneCenterAmbient Q := by
    intro z hz
    have hzm := (mem_omegaOneCenterAmbient_iff _ _).mp hz.1
    refine (mem_omegaOneCenterAmbient_iff Q z).mpr ⟨?_,hzm.2.1,hz.2⟩
    exact d.partner_residual_core_selfCentralizing
      ⟨hXKc (pCoreIn_le 2 X hzm.1),hz.2⟩
  intro hz
  change signalizerModule Kc Q = ⊥ at hz
  rw [signalizerModule_eq_commutator_omegaCenter] at hz
  have hcent : Kc ≤ centralizer (omegaOneCenterAmbient Q : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp hz
  have hfix : ⁅Z0 ⊓ centralizer (Q : Set G),X⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (hfixed.trans (le_centralizer_iff.mp (hXKc.trans hcent)))
  let : IsElementaryAbelian 2 Z0 := omegaOneCenterAmbient_elementaryAbelian _
  have htriv := hpX.centralizes_of_commuting_fixed X Q Z0 (isPGroup_pCoreIn 2 Kc)
    hXZ hQZ (hcomm.trans hkill) hfix
  apply hmove
  change signalizerModule X (X.pCoreIn 2) = ⊥
  rw [signalizerModule_eq_commutator_omegaCenter,commutator_comm]
  exact htriv

open ChapterA.Section04 Chapter1.Section02.Adequate in
/-- The first exclusion in 15.2.23, retaining only the earlier orbit alternative. -/
theorem no_normal_perfect_threeResidual
    (horbit : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = (pResidual 2 H).map H.subtype ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) {X : Subgroup G}
    (hXI : X ≤ I) (hIX : I ≤ normalizer (X : Set G))
    [Group.IsPerfect X] (hXMc : X ≤ Mc) (hXres : primeToResidual 3 X = ⊤)
    (hmove : intrinsicSignalizerModule X ≠ ⊥) : False := by
  have hpX : IsPPerfect 2 X := by
    intro N hn hp
    let := hn
    let := hp.isNilpotent
    exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ N)
  have hm := d.normal_threeResidual_moves_partner_core hI hXI hIX hpX hXMc hXres hmove
  rcases horbit with he | ⟨L,hL,he⟩
  · have hXK : X ≤ (pResidual 2 H).map H.subtype := by
      rw [← he,d.orbit_residual]
      have hh := embedded_primeToResidual_mono 3 hXMc
      rwa [hXres,←MonoidHom.range_eq_map,range_subtype] at hh
    obtain ⟨e⟩ := d.geometry.quotient
    let : Group.IsSolvable BinaryFourPlus.Wreath := BinaryFourPlus.wreath_isSolvable
    let : Group.IsSolvable (H ⧸ pCore 2 H) :=
      Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    let : Group.IsNilpotent (pCore 2 H) := (pCore_isPGroup (p := 2) (G := H)).isNilpotent
    let : Group.IsSolvable H := Group.isSolvable_of_ker_le_range
      (pCore 2 H).subtype (QuotientGroup.mk' (pCore 2 H))
      (by rw [QuotientGroup.ker_mk',range_subtype])
    let : Group.IsSolvable X := Group.isSolvable_of_isSolvable_injective
      (inclusion_injective (hXK.trans (map_subtype_le _)))
    have hXne : X ≠ ⊥ := by
      intro he
      apply hmove
      change signalizerModule X (X.pCoreIn 2) = ⊥
      rw [signalizerModule_eq_commutator_omegaCenter,he,commutator_bot_left]
    let : Nontrivial X := (nontrivial_iff_ne_bot X).mpr hXne
    exact Group.IsPerfect.not_isSolvable X inferInstance
  · rw [he] at hm
    have hf : L ∈ MainForward.faithfulLocalComponents T :=
      (mem_faithfulLocalComponents_iff_module T (hsource.ambient.evenCharacteristic T)).mpr
        ⟨hL,Chapter1.Terminal.intrinsicModule_ne_bot_of_orbit hL hm⟩
    rw [hsource.empty] at hf
    exact hf

end PlaneUniquenessPreceding
end CFSG.Quasithin.Chapter15.Section02
