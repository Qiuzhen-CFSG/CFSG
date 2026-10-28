module
public import Stellmacher.SectionOne.LemmaOneFiveRelativeM
public import Stellmacher.SectionOne.InvolutionPGroupSmallIndexClassification
public import Stellmacher.SectionOne.OneARelativeM

/-!
# Relative actions for elementary two-subgroups

For any nontrivial elementary two-subgroup A of the given Sylow subgroup,
E=[O₂′(G),A]A acts faithfully on the original elementary abelian module,
with trivial two-core. Its Sylow two-subgroup is exactly A restricted to E,
and its odd core is the A-commutator, both internally and after mapping
back to G. This public structural setup requires no bound on the action ratio.

Coprime decomposition writes the odd core as its A-fixed subgroup times
its A-commutator. Consequently an element of A centralizing the latter
centralizes the whole odd core; the Fitting-centralizer theorem excludes
such a nonidentity element. The odd normal complement in E then gives the
Sylow and core assertions, while faithfulness restricts directly.

The existing oneA wrappers reuse this shared construction. For a member of
that offender family, the relative form of (1.5)(e) additionally supplies
ratio one and minimality on nontrivial subgroups. Their statements and exact
inherited actions remain unchanged.

Source: the first reduction of Stellmacher (1.7), journal p.19,
`refs/latex/stellmacher-n-group.tex`, and the relative group used for the
bounded (1.6) application in (9.1)(7), journal p.47. The structural setup
also applies when the elementary actor has ratio two.
-/

open scoped IsMulCommutative
namespace Stellmacher.SectionOne
universe u

private theorem oneA_commutator_centralizer_bot
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) (A : Subgroup G)
    (hAS : A ≤ (S : Subgroup G)) (hAp : IsPGroup 2 A) :
    A ⊓ Subgroup.centralizer ((⁅oddCore G, A⁆ : Subgroup G) : Set G) = ⊥ := by
  let W : Subgroup G := oddCore G
  let _ : W.Normal := pPrimeCore_normal
  let _ : Group.IsSolvable G := h.G_solvable
  have hAnorm : A ≤ Subgroup.normalizer (W : Set G) :=
    Subgroup.le_normalizer_of_normal
  let _ : MulDistribMulAction A W :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer A W hAnorm
  have hcop : Nat.Coprime (Nat.card A) (Nat.card W) := by
    obtain ⟨n, hn⟩ := hAp.exists_card_eq
    rw [hn]
    exact (pPrimeCore_coprime_card (p := 2) (G := G)).pow_left n
  have hsup := fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (G := W) (A := A) (inferInstance : Group.IsSolvable W) hcop
  apply le_bot_iff.mp
  intro a ha
  have haWcent : a ∈ Subgroup.centralizer (W : Set G) := by
    have hWle : W ≤ Subgroup.centralizer ({a} : Set G) := by
      have htop : (⊤ : Subgroup W).map W.subtype = W := by ext w; simp
      rw [← htop, ← hsup, Subgroup.map_sup]
      apply sup_le
      · rintro w ⟨w', hw', rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        have hza : z = a := Set.mem_singleton_iff.mp hz
        subst z
        have he := (FixedPoints.mem_subgroup (M := A) (a := w')).mp hw' (⟨a, ha.1⟩ : A)
        have he' : a * (w' : G) * a⁻¹ = (w' : G) := congrArg Subtype.val he
        exact (mul_inv_eq_iff_eq_mul.mp he')
      · rw [commutatorAction_subgroup_conj_map_eq_commutator W A hAnorm]
        intro w hw
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        have hza : z = a := Set.mem_singleton_iff.mp hz
        subst z
        exact (Subgroup.mem_centralizer_iff.mp ha.2 w hw).symm
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (hWle hw) a (Set.mem_singleton a)).symm
  have haS : a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (oddCore G : Set G) :=
    ⟨hAS ha.1, haWcent⟩
  rw [lemma_one_five_sylow_oddCore_centralizer_bot h S] at haS
  exact haS

private theorem oddCore_eq_normal_complement
    {H : Type u} [Group H] [Finite H] (N B : Subgroup H) [N.Normal]
    (hcomp : N.IsComplement' B) (hBp : IsPGroup 2 B)
    (hNodd : Nat.Coprime 2 (Nat.card N)) : oddCore H = N := by
  let q : H →* H ⧸ N := QuotientGroup.mk' N
  have hQp : IsPGroup 2 (H ⧸ N) :=
    hBp.of_equiv hcomp.symm.QuotientMulEquiv.symm
  have hmapP : IsPGroup 2 ((oddCore H).map q) := hQp.to_subgroup _
  have hmapOdd : Nat.Coprime 2 (Nat.card ((oddCore H).map q)) :=
    (pPrimeCore_coprime_card (p := 2) (G := H)).of_dvd_right
      (Subgroup.card_map_dvd (H := oddCore H) q)
  have hmapBot : (oddCore H).map q = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rcases hmapP.card_eq_or_dvd with hc | hd
    · exact hc
    · exact False.elim ((Nat.prime_two.coprime_iff_not_dvd.mp hmapOdd) hd)
  apply le_antisymm
  · have hle := (Subgroup.map_eq_bot_iff (f := q) (H := oddCore H)).mp hmapBot
    simpa [q, QuotientGroup.ker_mk'] using hle
  · exact le_sSup ⟨inferInstance, hNodd⟩

/-- Any nontrivial elementary two-subgroup of the given Sylow supplies the
relative faithful action, its exact Sylow, and its odd-core commutator map. -/
public theorem elementary_relative_group_setup
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) (A : Subgroup G)
    (hAS : A ≤ (S : Subgroup G)) (hElem : IsElementaryAbelian 2 A) (hAne : A ≠ ⊥) :
    let E : Subgroup G := ⁅oddCore G, A⁆ ⊔ A
    ∃ T : Sylow 2 E, (T : Subgroup E) = A.subgroupOf E ∧
      Hypotheses E V ∧ IsElementaryAbelian 2 (T : Subgroup E) ∧
      oddCore E = ⁅oddCore E, (T : Subgroup E)⁆ ∧
      (oddCore E).map E.subtype = ⁅oddCore G, A⁆ := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let W : Subgroup G := oddCore G
  let F : Subgroup G := ⁅W, A⁆
  let E : Subgroup G := F ⊔ A
  let N : Subgroup E := F.subgroupOf E
  let B : Subgroup E := A.subgroupOf E
  let _ : W.Normal := pPrimeCore_normal
  let _ : Group.IsSolvable G := h.G_solvable
  let _ : IsElementaryAbelian 2 A := hElem
  have hAp : IsPGroup 2 A := IsElementaryAbelian.isPGroup 2 A
  have hFA : F ≤ E := le_sup_left
  have hAE : A ≤ E := le_sup_right
  have hFW : F ≤ W := Subgroup.commutator_le_left W A
  have hFodd : Nat.Coprime 2 (Nat.card F) :=
    (pPrimeCore_coprime_card (p := 2) (G := G)).of_dvd_right
      (Subgroup.card_dvd_of_le hFW)
  have hNcard : Nat.card N = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFA).toEquiv
  have hBcard : Nat.card B = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAE).toEquiv
  have hNodd : Nat.Coprime 2 (Nat.card N) := by rwa [hNcard]
  have hAnormW : A ≤ Subgroup.normalizer (W : Set G) :=
    Subgroup.le_normalizer_of_normal
  have hcopAW : Nat.Coprime (Nat.card A) (Nat.card W) := by
    obtain ⟨n, hn⟩ := hAp.exists_card_eq
    rw [hn]
    exact (pPrimeCore_coprime_card (p := 2) (G := G)).pow_left n
  have hcommFA : ⁅F, A⁆ = F :=
    commutator_double_eq_self_of_coprime A W hAnormW hcopAW
  have hEnormF : E ≤ Subgroup.normalizer (F : Set G) :=
    sup_le Subgroup.le_normalizer
      (Subgroup.le_normalizer_iff_commutator_le_left.mpr (by rw [hcommFA]))
  let _ : N.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFA).mpr hEnormF
  let _ : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hAE
  have hBp : IsPGroup 2 B := IsElementaryAbelian.isPGroup 2 B
  have hcopNB : Nat.Coprime (Nat.card N) (Nat.card B) := by
    obtain ⟨n, hn⟩ := hBp.exists_card_eq
    rw [hn]
    exact hNodd.symm.pow_right n
  have hdisj : Disjoint N B := Subgroup.disjoint_of_coprime_natCard hcopNB
  have hsup : N ⊔ B = ⊤ := (Subgroup.codisjoint_subgroupOf_sup F A).eq_top
  have hcomp : N.IsComplement' B := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
    rw [Set.eq_univ_iff_forall]
    intro e
    have he : e ∈ N ⊔ B := by rw [hsup]; trivial
    exact Subgroup.mem_sup_of_normal_left.mp he
  let T : Sylow 2 E := hBp.toSylow (by
    rw [hcomp.index_eq_card]
    exact Nat.prime_two.coprime_iff_not_dvd.mp hNodd)
  have hTN : (T : Subgroup E) = B := rfl
  have hoddCore : oddCore E = N := oddCore_eq_normal_complement N B hcomp hBp hNodd
  have hcentB : B ⊓ Subgroup.centralizer (N : Set E) = ⊥ := by
    apply le_bot_iff.mp
    intro b hb
    have hbG : (b : G) ∈ A ⊓ Subgroup.centralizer (F : Set G) := by
      refine ⟨hb.1, ?_⟩
      change (b : G) ∈ Subgroup.centralizer (F : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      exact congrArg Subtype.val
        (Subgroup.mem_centralizer_iff.mp hb.2 (⟨f, hFA hf⟩ : E) hf)
    rw [oneA_commutator_centralizer_bot h S A hAS hAp] at hbG
    exact Subtype.ext hbG
  have hcoreB : pCore 2 E ≤ B :=
    (pCore_isPGroup (p := 2) (G := E)).le_sylow_of_normal T
  have hcoreCentN : pCore 2 E ≤ Subgroup.centralizer (N : Set E) := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    have hc : Nat.Coprime (Nat.card (pCore 2 E)) (Nat.card N) := by
      obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := E)).exists_card_eq
      rw [hn]
      exact hNodd.pow_left n
    exact le_bot_iff.mp ((Subgroup.commutator_le_inf
      (H₁ := pCore 2 E) (H₂ := N)).trans
        (Subgroup.disjoint_of_coprime_natCard hc).le_bot)
  have hcoreBot : pCore 2 E = ⊥ := by
    apply le_bot_iff.mp
    exact (le_inf hcoreB hcoreCentN).trans (le_of_eq hcentB)
  have hEeven : Even (Nat.card E) := by
    have hAeven : 2 ∣ Nat.card A := by
      rcases hAp.card_eq_or_dvd with hcard | hdvd
      · exact False.elim (hAne (Subgroup.card_eq_one.mp hcard))
      · exact hdvd
    exact even_iff_two_dvd.mpr
      (hAeven.trans (by rw [← hBcard]; exact Subgroup.card_subgroup_dvd_card B))
  have hfaithE : fixingSubgroup E (Set.univ : Set V) = ⊥ := by
    apply le_bot_iff.mp
    intro e he
    have heG : (e : G) ∈ fixingSubgroup G (Set.univ : Set V) := by
      rw [mem_fixingSubgroup_iff] at he ⊢
      intro v hv
      exact he v hv
    rw [h.action_faithful] at heG
    exact Subtype.ext heG
  have hcommNB : ⁅N, B⁆ = N := by
    apply Subgroup.map_injective E.subtype_injective
    rw [Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le hFA,
      Subgroup.map_subgroupOf_eq_of_le hAE, hcommFA]
  refine ⟨T, hTN, ⟨inferInstance, hEeven, hfaithE, hcoreBot⟩,
    (by rw [hTN]; infer_instance), ?_, ?_⟩
  · rw [hoddCore, hTN, hcommNB]
  · rw [hoddCore, Subgroup.map_subgroupOf_eq_of_le hFA]

/-- The action needed to apply the valid small-m form of (1.6) to a
nontrivial member of the source's family `𝒜(V,S)`. -/
public theorem oneA_relative_rank_one_setup
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) (A : Subgroup G)
    (hA : oneA (G := G) (V := V) (S : Subgroup G) A) (hAne : A ≠ ⊥) :
    let E : Subgroup G := ⁅oddCore G, A⁆ ⊔ A
    ∃ T : Sylow 2 E, (T : Subgroup E) = A.subgroupOf E ∧
      Hypotheses E V ∧ IsElementaryAbelian 2 (T : Subgroup E) ∧
      oddCore E = ⁅oddCore E, (T : Subgroup E)⁆ ∧
      m (G := E) (V := V) (T : Subgroup E) = 1 ∧
      ∀ Y : Subgroup E, Y ≤ (T : Subgroup E) → Y ≠ ⊥ →
        m (G := E) (V := V) (T : Subgroup E) ≤ m (G := E) (V := V) Y := by
  let E : Subgroup G := ⁅oddCore G, A⁆ ⊔ A
  obtain ⟨T, hTA, hE, hT, hcomm, _hmap⟩ := elementary_relative_group_setup h S A hA.1 hA.2.1 hAne
  obtain ⟨hm, hmin⟩ := oneA_relative_m_eq_one_and_min h S A E hA le_sup_right
  refine ⟨T, hTA, hE, hT, hcomm, ?_, ?_⟩
  · simpa only [hTA] using hm
  · simpa only [hTA] using hmin

/-- The odd core in the relative action maps back to the original commutator. -/
public theorem oneA_relative_oddCore_map
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) (A : Subgroup G)
    (hA : oneA (G := G) (V := V) (S : Subgroup G) A) (hAne : A ≠ ⊥) :
    let E : Subgroup G := ⁅oddCore G, A⁆ ⊔ A
    (oddCore E).map E.subtype = ⁅oddCore G, A⁆ := by
  obtain ⟨T, _hTA, _hE, _hT, _hcomm, hmap⟩ := elementary_relative_group_setup h S A hA.1 hA.2.1 hAne
  exact hmap

end Stellmacher.SectionOne
