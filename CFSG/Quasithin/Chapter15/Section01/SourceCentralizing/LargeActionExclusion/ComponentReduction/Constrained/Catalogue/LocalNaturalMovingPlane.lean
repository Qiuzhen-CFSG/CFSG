module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalNaturalSylow
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2SylowFixed
public import Theory.GroupTheory.Commutator.CentralizingComplement

/-!
# The original moving and fixed planes in an escaping natural local block

The full natural Borel acts nontrivially on the original V. Its image
therefore equals the original prime-order residual. The Sylow subgroup
acts trivially on V. Every nontrivial odd subgroup of the Borel also has
nontrivial image, by the full-cover Sylow/odd-subgroup fixer theorem, and
hence gives exactly the same displacement as the original residual on
every subgroup of V.

A Sylow-fixing automorphism has displacement in the full U-layer of K.
Coprime fixed/moved disjointness makes the original moving plane disjoint
from the center of K. Its image thus embeds in the natural Sylow fixed
line, giving order at most 2^n. Its order is at least four: order one
contradicts the original movement, and a normalized group of order two
would be fixed by the odd actor. The existing field restriction now gives
p=3, n=2 and order exactly four.

This excludes every escaping natural local block on an original marker
with moving plane of order sixteen, and completes the local-family group
and intersection rows in that branch. The same original maps and full
central covers are retained. The actual-marker and separate exchanged
applications use this bound without a new component selection.

The same odd actor identifies the original fixed plane with C_V(K),
and coprime splitting gives V as the direct product of its moving and
fixed planes. The commutator [V,K] is normal in K and lies in U(K).
Irreducibility on U(K) modulo its central attachment makes this commutator
either central or full modulo the center. Perfectness and the three
subgroup lemma exclude the central case; [U(K),K]=U(K) then removes the
central supplement. Thus [V,K] is the full U(K), including its central
attachment. Both original-marker and exchanged consumers retain the same
fixed and moving planes.

The original moving plane and V now have the same centralizer in K,
namely S intersect K, and the same normalizer, namely the full natural
Borel. The centralizer follows from the fixed-plane splitting and the
original M_Z intersection; normalizers preserve that centralizer. The
normal closure of V in K S is exactly V joined with U(K). It is elementary
abelian and lies in O₂(K S), with the central attachment retained. Both
source applications use these literal stabilizers and the same local group.

The cubic order-four moving-plane exclusion and the full source assembly
remain open. Original 15.1.14 and whole-core A6 reconstruction retain their
existing producers. No ambient C-component condition is imposed on K.

Source: Aschbacher--Smith 15.1.16(c)--20 and 15.1.21(i), printed
pp.1092--1095,1097--1098; C.1.12 for the natural block module.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem prime_displacement
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hVC : V ≤ M ⊓ d.G1) {B : Subgroup G} (hBC : B ≤ M ⊓ d.G1)
    (hpB : IsPPerfect 2 B) (hne : ¬ B ≤ centralizer (V : Set G)) (hp2 : p ≠ 2) :
    (∀ A : Subgroup G, A ≤ V →
      ⁅A,B⁆ = ⁅A,(pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆) ∧
      ∀ P : Subgroup G, P ≤ B → IsPGroup 2 P → P ≤ centralizer (V : Set G) := by
  let C := M ⊓ d.G1
  let V0 := V.subgroupOf C
  let B0 := B.subgroupOf C
  let N := (M ⊓ centralizer (V : Set G)).subgroupOf C
  let : N.Normal := caseI_module_centralizer_normal (Z1 := d.Z1) h.normalized
  let q := QuotientGroup.mk' N
  let R := pResidual 2 (C ⧸ N)
  have hker : q.ker ≤ centralizer (V0 : Set C) := by
    intro x hx v hv
    exact Subtype.ext (((QuotientGroup.eq_one_iff x).mp hx).2 v hv)
  have hB0 : IsPPerfect 2 B0 := hpB.of_surjective
    (subgroupOfEquivOfLe hBC).symm.toMonoidHom (subgroupOfEquivOfLe hBC).symm.surjective
  have hBR : B0.map q ≤ R :=
    (map_mono (le_pResidual_of_isPPerfect B0 hB0)).trans
      (map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective N)).le
  have hcard : Nat.card R = p := s.residual_card
  have hnon : B0.map q ≠ ⊥ := by
    intro hz
    apply hne
    intro b hb
    have hk := (map_eq_bot_iff B0).mp hz (show (⟨b,hBC hb⟩ : C) ∈ B0 from hb)
    exact ((QuotientGroup.eq_one_iff _).mp hk).2
  have himage : B0.map q = R := by
    apply eq_of_le_of_card_ge hBR
    have hd : Nat.card (B0.map q) ∣ p := hcard ▸ card_dvd_of_le hBR
    have he : Nat.card (B0.map q) = p :=
      (Nat.dvd_prime s.prime_prime).mp hd |>.resolve_left (fun he => hnon (card_eq_one.mp he))
    exact le_of_eq (hcard.trans he.symm)
  refine ⟨?_,?_⟩
  · intro A hAV
    have he := commutator_eq_of_centralizing_kernel V0 (A.subgroupOf C) B0 (pResidual 2 C)
      q hker (fun _ hx => hAV hx) (himage.trans (map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective N)).symm)
    have hm := congrArg (map C.subtype) he
    have hAmap : (A.subgroupOf C).map C.subtype = A :=
      map_subgroupOf_eq_of_le (hAV.trans hVC)
    have hBmap : B0.map C.subtype = B := map_subgroupOf_eq_of_le hBC
    simp only [map_commutator,hAmap,hBmap] at hm
    exact hm
  · intro P hPB hP
    let P0 := P.subgroupOf C
    have hPR : P0.map q ≤ R := (map_mono (show P0 ≤ B0 from fun _ hx => hPB hx)).trans hBR
    have hpR : IsPGroup p R := IsPGroup.of_card_dvd_pow (n := 1) (by rw [hcard,pow_one])
    have hz : P0.map q = ⊥ := by
      apply bot_unique
      have hd := IsPGroup.disjoint_of_coprime (hP.comap_subtype.map q) hpR
        (Nat.coprime_primes Nat.prime_two s.prime_prime |>.mpr hp2.symm)
      exact fun x hx => disjoint_def.mp hd hx (hPR hx)
    intro x hx
    have hk := (map_eq_bot_iff P0).mp hz
      (show (⟨x,hBC (hPB hx)⟩ : C) ∈ P0 from hx)
    exact ((QuotientGroup.eq_one_iff _).mp hk).2

private theorem sylow_fixer_displacement {L : Type*} [Group L] [Finite L]
    {n : ℕ} (hb : IsL2EvenBlock L n) (P : Sylow 2 L) (a : MulAut L)
    (hP : ∀ x ∈ P, a x = x) (x : L) : a x * x⁻¹ ∈ blockU L := by
  let U := blockU L
  have hU (u : L) (hu : u ∈ U) : a u = u :=
    hP u (pCore_isPGroup.le_sylow_of_normal P (blockU_le_core hu))
  have hdcore (x : L) : a x * x⁻¹ ∈ pCore 2 L := by
    have hh := hb.2.1.centralizer_blockU.le
      (Theory.GroupAction.NormalizerGeneratingFixer.displacement_mem_centralizer U a
        hU x⁻¹ (by rw [normalizer_eq_top]; trivial))
    simpa only [inv_inv,map_inv,mul_inv_rev] using (pCore 2 L).inv_mem hh
  have he := DFunLike.congr_fun (hb.2.1.quotient_blockU_aut_eq_one a hdcore)
    (QuotientGroup.mk' U x)
  rw [quotientAut_apply_mk] at he
  simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp he

private theorem odd_twoPerfect {A : Type*} [Group A] [Finite A]
    (ho : Odd (Nat.card A)) : IsPPerfect 2 A := by
  intro N hn htwo
  let := hn
  apply index_eq_one.mp
  change Nat.card (A ⧸ N) = 1
  apply htwo.card_eq_or_dvd.resolve_right
  intro hd
  exact (Nat.not_even_iff_odd.mpr ho)
    (even_iff_two_dvd.mpr (hd.trans N.card_quotient_dvd_card))

private theorem natural_moving_actor
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    {n : ℕ} (hb : IsL2EvenBlock K n) (hp2 : p ≠ 2) :
    ∃ P : Sylow 2 K, ∃ D : Subgroup G,
      V ≤ normalizer (K : Set G) ∧
      (P : Subgroup K).map K.subtype ≤ centralizer (V : Set G) ∧
      D ≤ K ∧ Odd (Nat.card D) ∧ D ≠ ⊥ ∧ D ≤ normalizer (V : Set G) ∧
      ∀ A : Subgroup G, A ≤ V →
        ⁅A,D⁆ = ⁅A,(pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆ := by
  let := h.elementary
  let B := d.localSylowBorel K
  have hBC : B ≤ M ⊓ d.G1 := le_inf
    (d.localFamily_linearTwo_borel_le_selected hG hM hJ hu h hK hq hout hb)
    (inf_le_left.trans hK.1)
  have hVG : V ≤ d.G1 := V.le_centralizer.trans
    (centralizer_le (d.Z1_le_fixed.trans inf_le_left))
  have hVC := le_inf h.le_selected hVG
  have hBne : ¬ B ≤ centralizer (V : Set G) := by
    intro hc
    apply s.localFamily_linearTwo_borel_not_le_MZ (h := h) hG hM hJ hu hfull hK hq hout hb
    rw [hfull] at hc
    exact le_inf (inf_le_left.trans hK.1) (hc.trans (localModule_centralizer_le_partner T M hu))
  obtain ⟨hBW,hpfix⟩ := prime_displacement (h := h) s hVC hBC
    (d.localFamily_linearTwo_borel_twoPerfect hK hb) hBne hp2
  obtain ⟨P,hP⟩ := ComponentModels.source20_sylow_intersection hK.2
  have hPB : (P : Subgroup K).map K.subtype ≤ B := by
    rw [hP]
    exact le_inf inf_le_right (d.S ⊓ K).le_normalizer
  have hPV := hpfix _ hPB (P.isPGroup'.map K.subtype)
  have hVS : V ≤ d.S := by
    have hVJ : V ≤ elementaryAbelianMaxJ d.S := by
      have he := (h.caseI_marked_thompson_control hG T hM hJ d.Z1_le_fixed).1
      change elementaryAbelianMaxJ d.S = elementaryAbelianMaxJ (T : Subgroup G) at he
      rw [he,hfull]
      intro v hv
      exact ((mem_omegaOneCenterAmbient_iff _ _).mp
        ((source_centralizing_baumann_control hG T hM hJ).1 hv)).1
    exact hVJ.trans (sSup_le fun _ hA => hA.1)
  have hVN := hVS.trans (s.localFamily_linearTwo_sylow_normalizes (h := h)
    hG hM hJ hu hfull hK hq hout hb hp2)
  obtain ⟨D0,hDB,hDo,hDne⟩ := hb.exists_odd_borel_subgroup P
  let D := D0.map K.subtype
  have heP : (P : Subgroup K) = (d.S ⊓ K).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le inf_le_right]
  have hDB' : D ≤ B := by
    rw [show B = d.localSylowBorel K from rfl,d.localSylowBorel_eq,←heP]
    exact map_mono hDB
  have ho : Odd (Nat.card D) := by rwa [card_map_of_injective K.subtype_injective]
  have hne : D ≠ ⊥ := fun he => hDne ((map_eq_bot_iff_of_injective _ K.subtype_injective).mp he)
  have hDK : D ≤ K := map_subtype_le _
  have hDnon : ¬ D ≤ centralizer (V : Set G) := by
    intro hc
    have hKV := hb.centralizes_of_sylow_odd_fixed K V D P hVN hPV hDK ho hne hc
    rw [hfull] at hKV
    exact hout (le_inf hK.1 (hKV.trans (localModule_centralizer_le_partner T M hu)))
  exact ⟨P,D,hVN,hPV,hDK,ho,hne,
    hDB'.trans (hBC.trans inf_le_left) |>.trans h.normalized,
    (prime_displacement (h := h) s hVC (hDB'.trans hBC)
      (odd_twoPerfect ho) hDnon hp2).1⟩

/-- The original residual displacement in an escaping natural local member
lies in the Sylow-fixed U-layer and has order at most the field order. -/
theorem PreExclusionSource.localFamily_linearTwo_moving_plane_bound
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    {n : ℕ} (hb : IsL2EvenBlock K n) (hp2 : p ≠ 2) :
    let W := ⁅V,(pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆
    W ≤ (blockU K).map K.subtype ∧ 4 ≤ Nat.card W ∧ Nat.card W ≤ 2 ^ n := by
  let := h.elementary
  let W := ⁅V,(pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆
  obtain ⟨P,D,hVN,hPV,hDK,ho,hne,hDV,hDX⟩ := natural_moving_actor (h := h)
    s hG hM hJ hu hfull hK hq hout hb hp2
  have hDW : ⁅V,D⁆ = W := hDX V le_rfl
  have hWV : W ≤ V := hDW ▸ le_normalizer_iff_commutator_le_left.mp hDV
  have hWU : W ≤ (blockU K).map K.subtype := by
    rw [←hDW]
    apply commutator_le.mpr
    intro v hv k hk
    let a := K.normalizerMonoidHom ⟨v,hVN hv⟩
    have hfix : ∀ x ∈ P, a x = x := by
      intro x hx
      apply Subtype.ext
      change v*(x : G)*v⁻¹=(x : G)
      exact mul_inv_eq_iff_eq_mul.mpr (hPV (mem_map_of_mem K.subtype hx) v hv)
    have hm := sylow_fixer_displacement hb P a hfix (⟨k,hDK hk⟩ : K)
    exact ⟨_,hm,rfl⟩
  have hWK : W ≤ K := hWU.trans (map_subtype_le _)
  let E := W.subgroupOf K
  have hEU : E ≤ blockU K := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hWU hx
    exact (Subtype.ext he : y = x) ▸ hy
  have hEP : E ≤ centralizer (P : Set K) := by
    intro x hx y hy
    exact Subtype.ext ((hPV (mem_map_of_mem K.subtype hy) x (hWV hx)).symm)
  have hcop : Nat.Coprime (Nat.card D) (Nat.card V) := by
    obtain ⟨a,ha⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [ha]
    exact ho.coprime_two_right.pow_right a
  have hdis : Disjoint W (V ⊓ centralizer (D : Set G)) :=
    hDW ▸ commutator_disjoint_centralizer_of_coprime V D hDV hcop
  have hEZ : Disjoint E (center K) := by
    apply disjoint_def.mpr
    intro x hx hz
    apply Subtype.ext
    exact disjoint_def.mp hdis hx ⟨hWV hx,fun y hy =>
      congrArg Subtype.val (mem_center_iff.mp hz ⟨y,hDK hy⟩)⟩
  have hWne : W ≠ ⊥ := by
    intro hz
    exact s.moving_noncentral (by change ⁅d.L,W⁆ = ⊥; rw [hz,commutator_bot_right])
  have hWnotTwo : Nat.card W ≠ 2 := by
    intro hc
    have hnW : D ≤ normalizer (W : Set G) := hDW ▸ normalizer_commutator_ge_right V D
    have hWC : W ≤ centralizer (D : Set G) := le_centralizer_iff.mp
      (hnW.trans (normalizer_le_centralizer_of_card_two W hc))
    exact hWne (bot_unique (fun x hx => hdis.le_bot ⟨hx,hWV hx,hWC hx⟩))
  have hWcard : 4 ≤ Nat.card W := by
    obtain ⟨a,ha⟩ := ((IsElementaryAbelian.isPGroup 2 V).to_le hWV).exists_card_eq
    have h0 : a ≠ 0 := by
      intro hz
      exact hWne (card_eq_one.mp (by simpa [hz] using ha))
    have h1 : a ≠ 1 := by
      intro hz
      exact hWnotTwo (by simpa [hz] using ha)
    rw [ha]
    exact (by norm_num : 4 = 2 ^ 2).le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  refine ⟨hWU,hWcard,?_⟩
  rw [←Nat.card_congr (subgroupOfEquivOfLe hWK).toEquiv]
  exact hb.card_le_of_sylow_fixed_disjoint_center P E hEU hEP hEZ

/-- The fixed space of the original residual is exactly the fixed space of
an escaping natural local block. The whole original V splits over its
moving plane, so its action on K is induced inside the full U-layer. -/
theorem PreExclusionSource.localFamily_linearTwo_fixed_plane
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    {n : ℕ} (hb : IsL2EvenBlock K n) (hp2 : p ≠ 2) :
    let R := (pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype
    let W := ⁅V,R⁆
    let F := V ⊓ centralizer (R : Set G)
    V = W ⊔ F ∧ Disjoint W F ∧ F = V ⊓ centralizer (K : Set G) ∧
      V ≤ (blockU K).map K.subtype ⊔ centralizer (K : Set G) := by
  let := h.elementary
  let W := ⁅V,(pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆
  obtain ⟨P,D,hVN,hPV,hDK,ho,hne,hDV,hDX⟩ := natural_moving_actor (h := h)
    s hG hM hJ hu hfull hK hq hout hb hp2
  have hDW : ⁅V,D⁆ = W := hDX V le_rfl
  let R := (pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype
  let F := V ⊓ centralizer (R : Set G)
  have hfixed : V ⊓ centralizer (D : Set G) = F := by
    apply le_antisymm
    · refine le_inf inf_le_left ?_
      apply commutator_eq_bot_iff_le_centralizer.mp
      rw [←hDX _ inf_le_left]
      exact commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
    · refine le_inf inf_le_left ?_
      apply commutator_eq_bot_iff_le_centralizer.mp
      rw [hDX _ inf_le_left]
      exact commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
  have hFK : F ≤ centralizer (K : Set G) :=
    le_centralizer_iff.mp (hb.centralizes_of_sylow_odd_fixed K F D P
      (inf_le_left.trans hVN) (hPV.trans (centralizer_le inf_le_left)) hDK ho hne
      (le_centralizer_iff.mpr (hfixed ▸ inf_le_right)))
  have hFKexact : F = V ⊓ centralizer (K : Set G) := by
    apply le_antisymm (le_inf inf_le_left hFK)
    exact (inf_le_inf_left _ (centralizer_le hDK)).trans hfixed.le
  have hcop : Nat.Coprime (Nat.card D) (Nat.card V) := by
    obtain ⟨a,ha⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [ha]
    exact ho.coprime_two_right.pow_right a
  have hsplit : V = W ⊔ F := by
    rw [←hDW,←hfixed]
    exact eq_commutator_sup_centralizer_of_solvable_coprime V D hDV
      (Group.isSolvable_of_comm fun a b : V => mul_comm a b) hcop
  have hdis : Disjoint W F := by
    rw [←hDW,←hfixed]
    exact commutator_disjoint_centralizer_of_coprime V D hDV hcop
  have hWU := (s.localFamily_linearTwo_moving_plane_bound (h := h)
    hG hM hJ hu hfull hK hq hout hb hp2).1
  exact ⟨hsplit,hdis,hFKexact,hsplit.le.trans (sup_le_sup hWU hFK)⟩

/-- The original V produces the whole natural U-layer, including its
central attachment, and has precisely the original fixed plane as kernel. -/
theorem PreExclusionSource.localFamily_linearTwo_full_action
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    {n : ℕ} (hb : IsL2EvenBlock K n) (hp2 : p ≠ 2) :
    let R := (pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype
    let W := ⁅V,R⁆
    let F := V ⊓ centralizer (R : Set G)
    V = W ⊔ F ∧ Disjoint W F ∧ F = V ⊓ centralizer (K : Set G) ∧
      ⁅V,K⁆ = (blockU K).map K.subtype := by
  let R := (pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype
  let W := ⁅V,R⁆
  let F := V ⊓ centralizer (R : Set G)
  let U := (blockU K).map K.subtype
  let X := ⁅V,K⁆
  obtain ⟨hsplit,hdis,hfixed,_⟩ := s.localFamily_linearTwo_fixed_plane (h := h)
    hG hM hJ hu hfull hK hq hout hb hp2
  obtain ⟨hWU,hfour,_⟩ := s.localFamily_linearTwo_moving_plane_bound (h := h)
    hG hM hJ hu hfull hK hq hout hb hp2
  have hUK : ⁅U,K⁆ = U := by
    have hh := congrArg (map K.subtype) (ExceptionalRestrictions.short_commutator hb.2.1)
    simpa only [map_commutator,←MonoidHom.range_eq_map,range_subtype] using hh
  have hXeq : X = ⁅W,K⁆ := by
    have he := commutator_eq_of_centralizing_sup
      ((sup_comm F W).trans hsplit.symm) (hfixed.le.trans inf_le_right)
      (hWU.trans (map_subtype_le _) |>.trans K.le_normalizer)
    exact (commutator_comm V K).trans (he.symm.trans (commutator_comm K W))
  have hXU : X ≤ U := hXeq.le.trans ((commutator_mono hWU le_rfl).trans hUK.le)
  have hXK : X ≤ K := hXU.trans (map_subtype_le _)
  let X0 := X.subgroupOf K
  let Z := blockU K ⊓ center K
  have hX0U : X0 ≤ blockU K := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hXU hx
    exact (Subtype.ext he : y = x) ▸ hy
  let : X0.Normal := normal_subgroupOf_of_le_normalizer
    (normalizer_commutator_ge_right V K)
  have hUZ : X0 ⊔ Z = blockU K := by
    rcases hb.2.1.irreducible.2 (X0 ⊔ Z) inferInstance le_sup_right
      (sup_le hX0U inf_le_left) with he | he
    · have hXZ : X0 ≤ center K := le_sup_left.trans (he.le.trans inf_le_right)
      have hXC : X ≤ centralizer (K : Set G) := by
        intro x hx k hk
        exact congrArg Subtype.val (mem_center_iff.mp
          (hXZ (show (⟨x,hXK hx⟩ : K) ∈ X0 from hx)) ⟨k,hk⟩)
      let : Group.IsPerfect (K.subgroupOf (K ⊔ d.S)) := hK.2.1.perfect
      let e : K.subgroupOf (K ⊔ d.S) ≃* K := subgroupOfEquivOfLe le_sup_left
      let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
        (f := e.toMonoidHom) e.surjective
      have hquad : ⁅⁅V,K⁆,K⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hXC
      have hrot := commutator_commutator_eq_bot_of_rotate
        (show ⁅⁅K,V⁆,K⁆ = ⊥ by rw [commutator_comm K V]; exact hquad) hquad
      have hzX : X = ⊥ := by
        simpa only [K.commutator_eq_self,commutator_comm K V] using hrot
      have hVC : V ≤ centralizer (K : Set G) :=
        commutator_eq_bot_iff_le_centralizer.mp hzX
      have hz : W = ⊥ := bot_unique (fun x hx => disjoint_def.mp hdis hx
        (hfixed.symm ▸ ⟨(le_sup_left.trans hsplit.symm.le) hx,
          hVC ((le_sup_left.trans hsplit.symm.le) hx)⟩))
      have hc := hfour
      change Nat.card W ≥ 4 at hc
      rw [hz,card_bot] at hc
      omega
    · exact he
  have hUX : blockU K ≤ X0 := by
    have he := commutator_eq_of_centralizing_sup (V := (⊤ : Subgroup K))
      ((sup_comm Z X0).trans hUZ)
      ((show Z ≤ center K from inf_le_right).trans (center_le_centralizer _))
      ((show X0 ≤ (⊤ : Subgroup K) from le_top).trans (⊤ : Subgroup K).le_normalizer)
    calc
      blockU K = ⁅blockU K,(⊤ : Subgroup K)⁆ :=
        (ExceptionalRestrictions.short_commutator hb.2.1).symm
      _ = ⁅(⊤ : Subgroup K),blockU K⁆ := commutator_comm _ _
      _ = ⁅(⊤ : Subgroup K),X0⁆ := he.symm
      _ ≤ X0 := commutator_le_right _ _
  refine ⟨hsplit,hdis,hfixed,le_antisymm hXU ?_⟩
  have hh := map_mono (f := K.subtype) hUX
  rwa [map_subgroupOf_eq_of_le hXK] at hh

/-- The original moving plane and the full local module have the same
centralizer and normalizer inside an escaping natural local member.
These are the actual Sylow subgroup and Borel, with no ambient
C-component hypothesis. -/
theorem PreExclusionSource.localFamily_linearTwo_plane_stabilizers
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    {n : ℕ} (hb : IsL2EvenBlock K n) (hp2 : p ≠ 2) :
    let W := ⁅V,(pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆
    K ⊓ centralizer (V : Set G) = d.S ⊓ K ∧
      K ⊓ centralizer (W : Set G) = d.S ⊓ K ∧
      K ⊓ normalizer (V : Set G) = d.localSylowBorel K ∧
      K ⊓ normalizer (W : Set G) = d.localSylowBorel K := by
  let C := M ⊓ d.G1
  let R := (pResidual 2 C).map C.subtype
  let W := ⁅V,R⁆
  let F := V ⊓ centralizer (R : Set G)
  obtain ⟨P,D,_,hPV,_,_,_,_,_⟩ := natural_moving_actor (h := h)
    s hG hM hJ hu hfull hK hq hout hb hp2
  obtain ⟨P',hP'⟩ := ComponentModels.source20_sylow_intersection hK.2
  have hP : (P : Subgroup K).map K.subtype = d.S ⊓ K := by
    have hPC : (P : Subgroup K).map K.subtype ≤ d.MZ ⊓ K := by
      refine le_inf (le_inf (map_subtype_le _ |>.trans hK.1) ?_) (map_subtype_le _)
      rw [hfull] at hPV
      exact hPV.trans (localModule_centralizer_le_partner T M hu)
    rw [s.localFamily_linearTwo_marked_eq_sylow (h := h)
      hG hM hJ hu hfull hK hq hout hb hp2,←hP'] at hPC
    exact congrArg (map K.subtype)
      (P.is_maximal' P'.isPGroup' ((map_le_map_iff_of_injective K.subtype_injective).mp hPC))
      |>.symm.trans hP'
  have hcentV : K ⊓ centralizer (V : Set G) = d.S ⊓ K := by
    apply le_antisymm ?_ (le_inf inf_le_right (hP ▸ hPV))
    rw [←s.localFamily_linearTwo_marked_eq_sylow (h := h)
      hG hM hJ hu hfull hK hq hout hb hp2]
    exact le_inf (le_inf (inf_le_left.trans hK.1)
      (inf_le_right.trans (hfull.symm ▸ localModule_centralizer_le_partner T M hu))) inf_le_left
  obtain ⟨hsplit,_,hfixed,_⟩ := s.localFamily_linearTwo_fixed_plane (h := h)
    hG hM hJ hu hfull hK hq hout hb hp2
  have hWV : W ≤ V := le_sup_left.trans hsplit.symm.le
  have hcentW : K ⊓ centralizer (W : Set G) = d.S ⊓ K := by
    rw [←hcentV]
    apply le_antisymm ?_ (inf_le_inf_left _ (centralizer_le hWV))
    have hKF : K ≤ centralizer (F : Set G) :=
      le_centralizer_iff.mp (hfixed.le.trans inf_le_right)
    refine le_inf inf_le_left (le_centralizer_iff.mpr ?_)
    calc
      V = W ⊔ F := hsplit
      _ ≤ centralizer (K ⊓ centralizer (W : Set G) : Set G) := sup_le
        (le_centralizer_iff.mp inf_le_right)
        (le_centralizer_iff.mp (inf_le_left.trans hKF))
  have hCR : C ≤ normalizer (R : Set G) := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pResidual 2 C))
  have hCW : C ≤ normalizer (W : Set G) := by
    intro c hc
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (h.normalized hc.1),
      mem_normalizer_iff_map_conj_eq.mp (hCR hc)]
  have hBC : d.localSylowBorel K ≤ C := le_inf
    (d.localFamily_linearTwo_borel_le_selected hG hM hJ hu h hK hq hout hb)
    (inf_le_left.trans hK.1)
  have upper (A : Subgroup G) (he : K ⊓ centralizer (A : Set G) = d.S ⊓ K) :
      K ⊓ normalizer (A : Set G) ≤ d.localSylowBorel K := by
    have hn : K ⊓ normalizer (A : Set G) ≤ normalizer (d.S ⊓ K : Set G) := by
      change K ⊓ normalizer (A : Set G) ≤ normalizer ((d.S ⊓ K : Subgroup G) : Set G)
      rw [←he]
      exact (le_inf (inf_le_left.trans K.le_normalizer)
        (inf_le_right.trans (normalizer_le_normalizer_centralizer A))).trans
          inf_normalizer_le_normalizer_inf
    exact le_inf inf_le_left hn
  exact ⟨hcentV,hcentW,
    le_antisymm (upper V hcentV) (le_inf inf_le_left (hBC.trans inf_le_left |>.trans h.normalized)),
    le_antisymm (upper W hcentW) (le_inf inf_le_left (hBC.trans hCW))⟩

/-- The normal closure of the original module in the actual local group
is elementary abelian and is obtained by adjoining the full U-layer.
In particular it lies in the local two-core, including any central
attachment of the natural block. -/
theorem PreExclusionSource.localFamily_linearTwo_module_closure
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    {n : ℕ} (hb : IsL2EvenBlock K n) (hp2 : p ≠ 2) :
    conjugateSpanBy V (K ⊔ d.S) = V ⊔ (blockU K).map K.subtype ∧
      IsElementaryAbelian 2 (conjugateSpanBy V (K ⊔ d.S)) ∧
      conjugateSpanBy V (K ⊔ d.S) ≤ (K ⊔ d.S).pCoreIn 2 := by
  let := h.elementary
  let := hb.2.1.elementary
  let U := (blockU K).map K.subtype
  let R := (pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype
  let W := ⁅V,R⁆
  let F := V ⊓ centralizer (R : Set G)
  let E := V ⊔ U
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map K.subtype
  obtain ⟨hsplit,_,hfixed,hcomm⟩ := s.localFamily_linearTwo_full_action (h := h)
    hG hM hJ hu hfull hK hq hout hb hp2
  change ⁅V,K⁆ = U at hcomm
  have hWU : W ≤ U := (s.localFamily_linearTwo_moving_plane_bound (h := h)
    hG hM hJ hu hfull hK hq hout hb hp2).1
  have hFK : F ≤ centralizer (K : Set G) := hfixed.le.trans inf_le_right
  have hVU : V ≤ centralizer (U : Set G) := by
    calc
      V = W ⊔ F := hsplit
      _ ≤ centralizer (U : Set G) := sup_le (hWU.trans U.le_centralizer)
        (hFK.trans (centralizer_le (map_subtype_le _)))
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.sup_of_le_centralizer
    (le_centralizer_iff.mp hVU)
  have hE : E = U ⊔ F := by
    apply le_antisymm
    · exact sup_le (hsplit.le.trans (sup_le (hWU.trans le_sup_left) le_sup_right)) le_sup_left
    · exact sup_le le_sup_right ((le_sup_right.trans hsplit.symm.le).trans le_sup_left)
  have hKU : K ≤ normalizer (U : Set G) := K.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image K (blockU K))
  have hKN : K ≤ normalizer (E : Set G) := by
    rw [hE]
    exact (le_inf hKU ((le_centralizer_iff.mp hFK).trans
      (Subgroup.centralizer_le_normalizer (F : Set G)))).trans
      (normalizer_inf_normalizer_le_normalizer_sup U F)
  have hSK := s.localFamily_linearTwo_sylow_normalizes (h := h)
    hG hM hJ hu hfull hK hq hout hb hp2
  have hSN : d.S ≤ normalizer (E : Set G) :=
    (le_inf (d.S_le_T.trans hM.1.2 |>.trans h.normalized)
      (hSK.trans (normalizer_le_normalizer_characteristic_image K (blockU K)))).trans
        (normalizer_inf_normalizer_le_normalizer_sup V U)
  have hspan : conjugateSpanBy V (K ⊔ d.S) = E := by
    apply le_antisymm (conjugateSpanBy_le le_sup_left (sup_le hKN hSN))
    apply sup_le (le_conjugateSpanBy _ _)
    rw [←hcomm]
    exact (commutator_mono (le_conjugateSpanBy V (K ⊔ d.S)) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp
        (le_sup_left.trans (le_normalizer_conjugateSpanBy V (K ⊔ d.S))))
  have hVS : V ≤ d.S := by
    have hVJ : V ≤ elementaryAbelianMaxJ d.S := by
      have he := (h.caseI_marked_thompson_control hG T hM hJ d.Z1_le_fixed).1
      change elementaryAbelianMaxJ d.S = elementaryAbelianMaxJ (T : Subgroup G) at he
      rw [he,hfull]
      intro v hv
      exact ((mem_omegaOneCenterAmbient_iff _ _).mp
        ((source_centralizing_baumann_control hG T hM hJ).1 hv)).1
    exact hVJ.trans (sSup_le fun _ hA => hA.1)
  refine ⟨hspan,hspan.symm ▸ inferInstance,?_⟩
  rw [hspan]
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 E)
    (sup_le (hVS.trans le_sup_right) ((map_subtype_le _).trans le_sup_left))
    (sup_le hKN hSN)

/-- At either original source prime the entire original moving plane of
an escaping natural local member has order four. -/
theorem PreExclusionSource.localFamily_linearTwo_moving_plane_four
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    {n : ℕ} (hb : IsL2EvenBlock K n) :
    let W := ⁅V,(pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆
    p = 3 ∧ n = 2 ∧ W ≤ (blockU K).map K.subtype ∧ Nat.card W = 4 := by
  obtain ⟨hp3,hn⟩ := s.localFamily_linearTwo_small_field (h := h) hp hG hM hJ hu hfull hK hq hout hb
  obtain ⟨hWU,hlo,hhi⟩ := s.localFamily_linearTwo_moving_plane_bound (h := h)
    hG hM hJ hu hfull hK hq hout hb (by omega)
  refine ⟨hp3,hn,hWU,?_⟩
  norm_num [hn] at hhi
  omega

/-- For an original moving plane larger than four, every natural local
block lies in M_Z. This uses its literal residual, before exchanged selection. -/
theorem PreExclusionSource.localFamily_linearTwo_le_MZ_of_large_plane
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    (hlarge : 4 < Nat.card (⁅V,(pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆ : Subgroup G))
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {n : ℕ} (hb : IsL2EvenBlock K n) : K ≤ d.MZ := by
  by_contra hout
  have he := (s.localFamily_linearTwo_moving_plane_four (h := h)
    hp hG hM hJ hu hfull hK hq hout hb).2.2.2
  omega

/-- The later exchanged application keeps the same cubic marker and
component. Its natural row forces the order-four moving plane. -/
theorem ExchangedSource.constrained_natural_moving_plane_four
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.ExchangedSource) (sp : d.PreExclusionSource h.normalized 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    {n : ℕ} (hb : IsL2EvenBlock d.L n) :
    n = 2 ∧ d.nineMovingPlane ≤ (blockU d.L).map d.L.subtype ∧
      Nat.card d.nineMovingPlane = 4 :=
  (sp.localFamily_linearTwo_moving_plane_four (h := h) (Or.inl rfl)
    hG hM hJ hu hfull ⟨d.L_component.1,s.local_component⟩
    s.quasisimple d.L_not_le_MZ hb).2

/-- The later exchanged source retains its same component and both planes;
the full U-layer is reconstructed from the original V-action. -/
theorem ExchangedSource.constrained_natural_full_action
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.ExchangedSource) (sp : d.PreExclusionSource h.normalized 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    {n : ℕ} (hb : IsL2EvenBlock d.L n) :
    V = d.nineMovingPlane ⊔ d.nineFixedPlane ∧
      Disjoint d.nineMovingPlane d.nineFixedPlane ∧
      d.nineFixedPlane = V ⊓ centralizer (d.L : Set G) ∧
      ⁅V,d.L⁆ = (blockU d.L).map d.L.subtype :=
  sp.localFamily_linearTwo_full_action (h := h) hG hM hJ hu hfull
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hb (by decide)

/-- The exchanged application retains its original component, moving plane
and full U-layer in the literal stabilizers and module closure. -/
theorem ExchangedSource.constrained_natural_plane_stabilizers
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.ExchangedSource) (sp : d.PreExclusionSource h.normalized 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    {n : ℕ} (hb : IsL2EvenBlock d.L n) :
    (d.L ⊓ centralizer (V : Set G) = d.SL ∧
      d.L ⊓ centralizer (d.nineMovingPlane : Set G) = d.SL ∧
      d.L ⊓ normalizer (V : Set G) = d.localSylowBorel d.L ∧
      d.L ⊓ normalizer (d.nineMovingPlane : Set G) = d.localSylowBorel d.L) ∧
    (conjugateSpanBy V (d.L ⊔ d.S) = V ⊔ (blockU d.L).map d.L.subtype ∧
      IsElementaryAbelian 2 (conjugateSpanBy V (d.L ⊔ d.S)) ∧
      conjugateSpanBy V (d.L ⊔ d.S) ≤ (d.L ⊔ d.S).pCoreIn 2) :=
  ⟨sp.localFamily_linearTwo_plane_stabilizers (h := h) hG hM hJ hu hfull
      ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hb (by decide),
    sp.localFamily_linearTwo_module_closure (h := h) hG hM hJ hu hfull
      ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hb (by decide)⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The actual original marker, with the same prime, row, fixed centralizer
and moving plane. A natural escape forces that plane to be a four-group.
Original 15.1.14 remains with its existing producer and assembly owner. -/
theorem PreparedChosenModule.source_preExclusion_local_natural_moving_plane
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hp : m.prime = 3 ∨ m.prime = 5)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → ∀ n : ℕ, IsL2EvenBlock K n →
          m.prime = 3 ∧ n = 2 ∧ m.movingPlane ≤ (blockU K).map K.subtype ∧
            Nat.card m.movingPlane = 4 := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hout n hb
  have he := s.localFamily_linearTwo_moving_plane_four (h := h)
    hp hG hM hJ hu hfull hK hq hout hb
  have hG1 : d.G1 = centralizer (m.Z1 : Set G) := by change centralizer (d.Z1 : Set G) = _; rw [hZ]
  dsimp only at he
  rw [hG1] at he
  exact he

/-- In particular the actual original order-sixteen moving plane excludes
all natural escapes. The full local-family group and intersection rows then
hold at either source prime, including both marked binary parabolics. -/
theorem PreparedChosenModule.source_preExclusion_sixteen_plane_local_rows
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hp : m.prime = 3 ∨ m.prime = 5) (hplane : Nat.card m.movingPlane = 16)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → generalizedFitting K = pCore 2 K →
          ⁅K,elementaryAbelianMaxJ d.S⁆ = K ∧ CaseIComponentData.LocalConstrainedSourceRows d K := by
  obtain ⟨d,hZ,hr,s,hnatural⟩ := h.source_preExclusion_local_natural_moving_plane
    hG T hempty hM hmany hJ hu hne hfull m hp hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hout hf
  obtain ⟨hm,hr⟩ := d.localFamily_constrained_rows hG hempty hM hJ hu h hK hq hout hf
  refine ⟨hm,?_⟩
  cases hr with
  | naturalTwo n hb _ _ =>
    have hc := (hnatural K hK hq hout n hb).2.2.2
    omega
  | alternatingFive hb he hc => exact .alternatingFive hb he hc
  | small model equiv marking => exact .small model equiv marking
  | linear n hn e t ht hz hm => exact .linear n hn e t ht hz hm

/-- Every original natural escape has the original fixed plane as its
kernel on K and generates the full U-layer, retaining either source prime. -/
theorem PreparedChosenModule.source_preExclusion_local_natural_full_action
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hp : m.prime = 3 ∨ m.prime = 5)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → ∀ n : ℕ, IsL2EvenBlock K n →
          m.prime = 3 ∧ n = 2 ∧ m.movingPlane ≤ (blockU K).map K.subtype ∧
            Nat.card m.movingPlane = 4 ∧ V = m.movingPlane ⊔ m.fixedPlane ∧
            Disjoint m.movingPlane m.fixedPlane ∧
            m.fixedPlane = V ⊓ centralizer (K : Set G) ∧
            ⁅V,K⁆ = (blockU K).map K.subtype := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hout n hb
  have hp2 : m.prime ≠ 2 := by omega
  have hsize := s.localFamily_linearTwo_moving_plane_four (h := h)
    hp hG hM hJ hu hfull hK hq hout hb
  have ha := s.localFamily_linearTwo_full_action (h := h)
    hG hM hJ hu hfull hK hq hout hb hp2
  have hG1 : d.G1 = centralizer (m.Z1 : Set G) := by
    change centralizer (d.Z1 : Set G) = _
    rw [hZ]
  dsimp only at hsize ha
  rw [hG1] at hsize ha
  exact ⟨hsize.1,hsize.2.1,hsize.2.2.1,hsize.2.2.2,ha⟩

/-- On the unchanged original marker, the natural local row identifies both
stabilizers of the original moving plane and constructs the entire elementary
normal closure of V in KS. Earlier 15.1.14 remains explicit. -/
theorem PreparedChosenModule.source_preExclusion_local_natural_plane_stabilizers
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hp : m.prime = 3 ∨ m.prime = 5)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → ∀ n : ℕ, IsL2EvenBlock K n →
          (K ⊓ centralizer (V : Set G) = d.S ⊓ K ∧
            K ⊓ centralizer (m.movingPlane : Set G) = d.S ⊓ K ∧
            K ⊓ normalizer (V : Set G) = d.localSylowBorel K ∧
            K ⊓ normalizer (m.movingPlane : Set G) = d.localSylowBorel K) ∧
          (conjugateSpanBy V (K ⊔ d.S) = V ⊔ (blockU K).map K.subtype ∧
            IsElementaryAbelian 2 (conjugateSpanBy V (K ⊔ d.S)) ∧
            conjugateSpanBy V (K ⊔ d.S) ≤ (K ⊔ d.S).pCoreIn 2) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hout n hb
  have hs := s.localFamily_linearTwo_plane_stabilizers (h := h)
    hG hM hJ hu hfull hK hq hout hb (by omega)
  have hG1 : d.G1 = centralizer (m.Z1 : Set G) := by
    change centralizer (d.Z1 : Set G) = _
    rw [hZ]
  dsimp only at hs
  rw [hG1] at hs
  exact ⟨hs,s.localFamily_linearTwo_module_closure (h := h)
    hG hM hJ hu hfull hK hq hout hb (by omega)⟩

end CFSG.Quasithin.Chapter15.Section01
