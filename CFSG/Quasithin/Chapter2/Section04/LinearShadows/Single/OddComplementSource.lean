module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.InvolutionSource
public import Theory.SpecificGroups.PSL2.FieldDegreeOuterOrder
/-!
# The outside involution when the half-degree is odd

The literal action embeds H/L in the outer group of L/O₂(L), of order n.
The chosen field complement therefore has order dividing n. Its marked
involution and odd n/2 force its two-power order to equal two. The original
index-two row makes the ambient torus complement have order four, and
transfer makes it noncyclic. Every nonidentity element is consequently an
involution, including the chosen outside representative.

Source: Aschbacher–Smith, Lemma 2.4.24(2), first paragraph of the noncentral
odd half-degree branch, printed p.540.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
include hG hST hsingle hL hM hTM hunique

theorem source_single_quotient_card_dvd_field_degree :
    let : d.block.Normal := hsingle ▸ d.L0_normal
    Nat.card (d.H ⧸ d.block) ∣ n := by
  let : d.block.Normal := hsingle ▸ d.L0_normal
  have hQL : pCore 2 d.H ≤ d.block := by
    intro a ha
    have hcore := (source_core_absorption d hG T hST hsingle hL hM hTM hunique).2
    have ha' : (a:G) ∈ (d.block.map d.H.subtype).pCoreIn 2 := by
      change (a:G) ∈ twoCore (d.block.map d.H.subtype)
      rw [hcore]
      exact mem_map_of_mem d.H.subtype ha
    exact (mem_map_iff_mem d.H.subtype_injective).mp (pCoreIn_le 2 _ ha')
  let K := d.block ⧸ pCore 2 d.block
  obtain ⟨F, _, _, hF, _, _, ⟨m⟩, _⟩ := hL.2.2
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let e : K ≃* Theory.PSL2.Group F := m.quotientIso.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL
  have hi := normalQuotientOuterAction_injective d.block (pCore 2 d.block)
    ((source_block_quotient_action_kernel d hsingle hL).trans hQL)
  have hc := card_dvd_of_injective (normalQuotientOuterAction d.block (pCore 2 d.block)) hi
  have he := Nat.card_congr (MulAut.outerCongr e).toEquiv
  rw [he,Theory.PSL2.outer_card_eq_field_degree F hF] at hc
  exact hc

theorem source_field_complement_card_dvd_degree (c : CyclicTorusSetup d T n) :
    Nat.card (((d.S:Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall:Set G)):Subgroup G) ∣ n := by
  let : d.block.Normal := hsingle ▸ d.L0_normal
  let A := ((d.S:Subgroup d.H).map d.H.subtype) ⊓ normalizer (c.hall:Set G)
  let f : A →* d.H ⧸ d.block := (QuotientGroup.mk' d.block).comp
    (inclusion (show A≤d.H from inf_le_left.trans (map_subtype_le _)))
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro a ha
    have haL : (a:G)∈d.block.map d.H.subtype := mem_map_of_mem d.H.subtype
      ((QuotientGroup.eq_one_iff _).mp ha)
    have hd := (source_torus_normalizer_complements_of_choice d hG T hST hsingle hL hM hTM hunique c.hall c.split_ambient).2.2.2.1
    exact Subtype.ext (disjoint_def.mp hd haL a.property)
  exact (card_dvd_of_injective f hf).trans
    (source_single_quotient_card_dvd_field_degree d hG T hST hsingle hL hM hTM hunique)

theorem source_odd_half_degree_outside_involution (c : CyclicTorusSetup d T n)
    (s : T) (hs : (s:G)∈(d.S:Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall:Set G))
    (hs2 : orderOf s=2)
    (hclosed : ∀ r t:T, orderOf r=2 →
      (r:G)∈Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype) →
      IsConj (r:G) (t:G) → (t:G)∈Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype))
    (hn : Odd (n/2)) :
    ∃ x∈T, x∉(d.S:Subgroup d.H).map d.H.subtype ∧
      x∈normalizer (c.hall:Set G) ∧ orderOf x=2 := by
  let S := (d.S:Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let F := S⊓normalizer (c.hall:Set G)
  let C := (normalizer (c.hall:Set G)).subgroupOf (T:Subgroup G)
  have hFp : IsPGroup 2 F := T.isPGroup'.to_le (inf_le_left.trans hST.le)
  have hFd : Nat.card F∣n := source_field_complement_card_dvd_degree d hG T hST hsingle hL hM hTM hunique c
  have hsF : orderOf (⟨(s:G),hs⟩:F)=2 := by
    exact (orderOf_coe (⟨(s:G),hs⟩:F)).symm.trans ((orderOf_coe s).trans hs2)
  have h2F : 2∣Nat.card F := hsF ▸ orderOf_dvd_natCard (x:=(⟨(s:G),hs⟩:F))
  obtain ⟨k,hk⟩ := hFp.exists_card_eq
  have hk0 : k≠0 := by intro he; rw [he,pow_zero] at hk; rw [hk] at h2F; norm_num at h2F
  have hk2 : ¬2≤k := by
    intro hh
    have h4 : 4∣n := (show 4∣2^k from pow_dvd_pow 2 hh).trans (hk ▸ hFd)
    obtain ⟨a,ha⟩ := h4
    apply hn.not_two_dvd_nat
    exact ⟨a,by omega⟩
  have hFcard : Nat.card F=2 := by
    have he : k=1 := by omega
    simpa only [he,pow_one] using hk
  have hRS : R≤S := sSup_le fun _ h=>h.1
  have hindex := (d.lemma_2_4_8_1 hG T hST hsingle
    (hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective))).1
  have hRF : R.relIndex S=2 := by
    change (R.subgroupOf S).index=2
    rw [c.split_sylow.symm.index_eq_card,
      Nat.card_congr (subgroupOfEquivOfLe (show F≤S from inf_le_left)).toEquiv,hFcard]
  have hRC : R.relIndex (T:Subgroup G)=4 := by
    rw [←relIndex_mul_relIndex R S (T:Subgroup G) hRS hST.le,hRF,hindex]
  have hCcard : Nat.card C=4 := by
    rw [←c.split_ambient.symm.index_eq_card]
    exact hRC
  let := c.normal_in_sylow
  have hCcyc : ¬IsCyclic C := by
    intro hc
    have hcyc := c.split_ambient.symm.QuotientMulEquiv.isCyclic.mpr hc
    exact c.quotient_not_cyclic_of_fusion hG hclosed hcyc
  have hCexp : Monoid.exponent C=2 :=
    (not_isCyclic_iff_exponent_eq_prime Nat.prime_two hCcard).mp hCcyc
  obtain ⟨x,hxT,hxS,hxB⟩ := c.outside
  let xC : C := ⟨⟨x,hxT⟩,hxB⟩
  have hx2 : x^2=1 := by
    have hh := Monoid.pow_exponent_eq_one xC
    rw [hCexp] at hh
    exact congrArg (fun a:C=>((a:T):G)) hh
  exact ⟨x,hxT,hxS,hxB,orderOf_eq_prime hx2 (fun he=>hxS (he ▸ S.one_mem))⟩
end CFSG.Quasithin.Chapter2.LinearShadows.Single
