module

public import Glauberman.Signalizer.InvariantAbelianSupplement
public import Glauberman.Signalizer.RelativeCoreFactorization
public import Theory.GroupTheory.NormalPSubgroupCoprimeSupplement
public import Theory.GroupTheory.Signalizer.LocalCompleteness
public import Glauberman.Signalizer.ValueFactorCompletion
public import Theory.GroupTheory.Signalizer.ValueCoreTransfer

/-!
# A normalizer factorization criterion for binary signalizer completeness

Let an elementary binary group of order at least eight act on a finite
ambient group, and let θ be a locally complete odd solvable signalizer
family. Suppose a prime q at least five occurs in some family value and
M is a signalizer subgroup. If every nontrivial q-signalizer W has its
normalizer closure supplemented by its q′-core and a common-subgroup
conjugate of M, then θ is complete. Every core and normalizer closure in
the hypothesis is the actual subgroup in the original ambient group.

Invariant full-Sylow ZJ supplements first produce a nontrivial W in a
family value. Since W is normal in its normalizer closure, the normal
q-subgroup containment theorem puts W in a conjugate of M; hence q divides
|M|. The same ZJ construction in M gives a nontrivial invariant Q and a
core supplement using L = θ(N(Q)). For each family value containing q,
repeat the construction and apply the relative factorization theorem to
L^c, M^c, and θ(N(W)). The fixed-factor transfer theorem absorbs the local
core into the value's own core. The resulting conjugator lies in every
family value and normalizes its core, so conjugating back removes it.
Values of order prime to q are already their own q′-cores. Thus all values
have the factorizations required by the proved value-completion theorem.

This is the q≥5 case of Kurzweil–Stellmacher, *The Theory of Finite Groups*,
11.2.7, printed pp. 321–323, using the proved full-Sylow ZJ form of 9.4.6
and the relative factorization 11.2.6. The original supplied action is
retained through all subgroup restrictions. Left conjugation composes as
c₁*c, as used explicitly in the proof.
-/

open Theory.GroupTheory

namespace Glauberman

private theorem ambient_core_map_conj
    {G : Type*} [Group G] (q : ℕ) (H : Subgroup G) (c : G) :
    ((pPrimeCore q H).map H.subtype).map (MulAut.conj c : G →* G) =
      (pPrimeCore q (H.map (MulAut.conj c : G →* G))).map
        (H.map (MulAut.conj c : G →* G)).subtype := by
  let e := H.equivMapOfInjective (MulAut.conj c : G →* G) (MulAut.conj c).injective
  rw [← pPrimeCore_map_iso q e, Subgroup.map_map, Subgroup.map_map]
  rfl

private theorem factor_map_conj
    {G : Type*} [Group G] (q : ℕ) (H L : Subgroup G) (c : G)
    (h : H = (pPrimeCore q H).map H.subtype ⊔ (H ⊓ L)) :
    H.map (MulAut.conj c : G →* G) =
      (pPrimeCore q (H.map (MulAut.conj c : G →* G))).map
        (H.map (MulAut.conj c : G →* G)).subtype ⊔
      (H.map (MulAut.conj c : G →* G) ⊓ L.map (MulAut.conj c : G →* G)) := by
  have hh := congrArg (fun D : Subgroup G => D.map (MulAut.conj c : G →* G)) h
  rw [Subgroup.map_sup, Subgroup.map_inf H L (MulAut.conj c : G →* G) (MulAut.conj c).injective,
    ambient_core_map_conj] at hh
  exact hh

private theorem normal_p_le_ambient_supplement
    {G : Type*} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]
    (U M W : Subgroup G) (hWU : W ≤ U)
    (hUN : U ≤ Subgroup.normalizer (W : Set G)) (hW : IsPGroup q W)
    (hU : U = (pPrimeCore q U).map U.subtype ⊔ (U ⊓ M)) : W ≤ M := by
  have hsup : pPrimeCore q U ⊔ M.subgroupOf U = ⊤ := by
    apply Subgroup.map_injective (f := U.subtype) U.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    simpa only [inf_comm] using hU.symm
  let _ : (W.subgroupOf U).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUN
  have hw := normal_pSubgroup_le_of_coprime_normal_supplement
    (pPrimeCore q U) (M.subgroupOf U) (W.subgroupOf U) pPrimeCore_coprime_card hsup
    (hW.of_equiv (Subgroup.subgroupOfEquivOfLe hWU).symm)
  intro w hwW
  exact hw (show (⟨w,hWU hwW⟩ : U) ∈ W.subgroupOf U from hwW)

variable {A G : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
  [Group G] [Finite G] [MulDistribMulAction A G]

private theorem exists_signalizer_normalizer_supplement
    (θ : TwoSignalizerFamily A G) (hA : 4 ≤ Nat.card A)
    {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q)
    (H : Subgroup G) (hH : θ.IsSignalizerSubgroup H) (hdiv : q ∣ Nat.card H) :
    ∃ W : Subgroup G, θ.IsSignalizerSubgroup W ∧ IsPGroup q W ∧ W ≠ ⊥ ∧
      H = (pPrimeCore q H).map H.subtype ⊔
        (H ⊓ θ.closureWithin (Subgroup.normalizer (W : Set G))) := by
  let _ : IsInvariant A G H := hH.2.2.1
  obtain ⟨R, hRn, hRq, _, hRI, hsup⟩ :=
    exists_invariant_abelian_prime_normalizer_supplement
      (IsElementaryAbelian.isPGroup 2 A) hH.1 hH.2.1 hq hdiv
  let _ : IsInvariant A H R := hRI
  let W := R.map H.subtype
  have hW : θ.IsSignalizerSubgroup W :=
    hH.mono (Subgroup.map_subtype_le R) (isInvariant_map_subtype H R)
  have hWq : IsPGroup q W := hRq.map H.subtype
  have hWn : W ≠ ⊥ := by
    intro heq
    apply hRn
    exact (Subgroup.map_injective H.subtype_injective) (by simpa only [Subgroup.map_bot] using heq)
  refine ⟨W, hW, hWq, hWn, ?_⟩
  let _ : IsInvariant A G W := hW.2.2.1
  let N := Subgroup.normalizer (W : Set G)
  let _ : IsInvariant A G N := isInvariant_normalizer W
  have hHN := (hH.mono (inf_le_left : H ⊓ N ≤ H) (isInvariant_inf H N)).le_closureWithin
    hA (inf_le_right : H ⊓ N ≤ N)
  have hmap : (pPrimeCore q H).map H.subtype ⊔
      (Subgroup.normalizer (R : Set H)).map H.subtype = H := by
    have hh := congrArg (fun D : Subgroup H => D.map H.subtype) hsup
    simpa only [Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype] using hh
  apply le_antisymm
  · calc
      H = _ := hmap.symm
      _ ≤ _ := sup_le le_sup_left (by
        intro x hx
        exact Subgroup.mem_sup_right ⟨Subgroup.map_subtype_le _ hx,
          hHN ⟨Subgroup.map_subtype_le _ hx, R.le_normalizer_map H.subtype hx⟩⟩)
  · exact sup_le (Subgroup.map_subtype_le _) inf_le_left

private theorem signalizer_le_normalizer_closure
    (θ : TwoSignalizerFamily A G) (hA : 4 ≤ Nat.card A)
    (W : Subgroup G) (hW : θ.IsSignalizerSubgroup W) :
    W ≤ θ.closureWithin (Subgroup.normalizer (W : Set G)) := by
  let _ : IsInvariant A G W := hW.2.2.1
  let _ := isInvariant_normalizer (A := A) W
  exact hW.le_closureWithin hA W.le_normalizer

private theorem map_conj_comp {K : Type*} [Group K]
    (H : Subgroup K) (c d : K) :
    (H.map (MulAut.conj c : K →* K)).map (MulAut.conj d : K →* K) =
      H.map (MulAut.conj (d * c) : K →* K) := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  change d * (c * x * c⁻¹) * d⁻¹ = (d * c) * x * (d * c)⁻¹
  group

omit [Finite A] [IsElementaryAbelian 2 A] [Finite G] in
private theorem remove_common_conjugate
    (θ : TwoSignalizerFamily A G) (q : ℕ) (a : {a : A // a ≠ 1})
    (L : Subgroup G) (d : G) (hd : d ∈ θ.common)
    (h : θ.subgroup a = (pPrimeCore q (θ.subgroup a)).map (θ.subgroup a).subtype ⊔
      (θ.subgroup a ⊓ L.map (MulAut.conj d : G →* G))) :
    θ.subgroup a = (pPrimeCore q (θ.subgroup a)).map (θ.subgroup a).subtype ⊔
      (θ.subgroup a ⊓ L) := by
  have hC : (θ.subgroup a).map (MulAut.conj d⁻¹ : G →* G) = θ.subgroup a :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((θ.subgroup a).le_normalizer ((θ.subgroup a).inv_mem (θ.common_le a hd)))
  have hcore : ((pPrimeCore q (θ.subgroup a)).map (θ.subgroup a).subtype).map
      (MulAut.conj d⁻¹ : G →* G) =
      (pPrimeCore q (θ.subgroup a)).map (θ.subgroup a).subtype :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (θ.value_le_normalizer_core q a ((θ.subgroup a).inv_mem (θ.common_le a hd)))
  have hL : (L.map (MulAut.conj d : G →* G)).map (MulAut.conj d⁻¹ : G →* G) = L := by
    rw [map_conj_comp, inv_mul_cancel]
    have hi : (MulAut.conj (1 : G) : G →* G) = MonoidHom.id G := by
      ext x
      simp
    rw [hi, Subgroup.map_id]
  have hh := congrArg (fun D : Subgroup G => D.map (MulAut.conj d⁻¹ : G →* G)) h
  rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ (MulAut.conj d⁻¹).injective,
    hC, hcore, hL] at hh
  exact hh

/-- The q≥5 normalizer core-factorization criterion for a locally complete family. -/
public theorem complete_of_normalizer_core_factorizations
    (θ : TwoSignalizerFamily A G) (hA : 8 ≤ Nat.card A) (hl : θ.IsLocallyComplete)
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (hdiv : ∃ a, q ∣ Nat.card (θ.subgroup a))
    (M : Subgroup G) (hM : θ.IsSignalizerSubgroup M)
    (hfactor : ∀ W : Subgroup G, θ.IsSignalizerSubgroup W → IsPGroup q W → W ≠ ⊥ →
      let U := θ.closureWithin (Subgroup.normalizer (W : Set G))
      ∃ c : G, c ∈ θ.common ∧
        U = (pPrimeCore q U).map U.subtype ⊔
          (U ⊓ M.map (MulAut.conj c : G →* G))) : θ.IsComplete := by
  have hA4 : 4 ≤ Nat.card A := by omega
  have hMdiv : q ∣ Nat.card M := by
    obtain ⟨a, ha⟩ := hdiv
    obtain ⟨W, hW, hWq, hWn, _⟩ := exists_signalizer_normalizer_supplement θ hA4 hq
      (θ.subgroup a) (θ.value_isSignalizerSubgroup a) ha
    obtain ⟨c, _, hU⟩ := hfactor W hW hWq hWn
    have hWM := normal_p_le_ambient_supplement
      (θ.closureWithin (Subgroup.normalizer (W : Set G)))
      (M.map (MulAut.conj c : G →* G)) W
      (signalizer_le_normalizer_closure θ hA4 W hW) (θ.closureWithin_le _) hWq hU
    have hdvd := (hWq.card_eq_or_dvd.resolve_left (fun h => hWn (Subgroup.card_eq_one.mp h))).trans
      (Subgroup.card_dvd_of_le hWM)
    rwa [Subgroup.card_map_of_injective (MulAut.conj c).injective] at hdvd
  obtain ⟨Q, hQ, hQq, hQn, hMfactor⟩ :=
    exists_signalizer_normalizer_supplement θ hA4 hq M hM hMdiv
  let L := θ.closureWithin (Subgroup.normalizer (Q : Set G))
  have hL : θ.IsSignalizerSubgroup L := hl.normalizer Q hQ hQn
  apply complete_of_value_core_factorizations θ hA hl q Q hQ hQq hQn
  intro a
  by_cases hadiv : q ∣ Nat.card (θ.subgroup a)
  · obtain ⟨W, hW, hWq, hWn, hCfactor⟩ := exists_signalizer_normalizer_supplement θ hA4 hq
      (θ.subgroup a) (θ.value_isSignalizerSubgroup a) hadiv
    let U := θ.closureWithin (Subgroup.normalizer (W : Set G))
    have hU : θ.IsSignalizerSubgroup U := hl.normalizer W hW hWn
    obtain ⟨c, hc, hUfactor⟩ := hfactor W hW hWq hWn
    let Mc := M.map (MulAut.conj c : G →* G)
    let Lc := L.map (MulAut.conj c : G →* G)
    have hMc : θ.IsSignalizerSubgroup Mc := hM.map_conj_of_mem_common hc
    have hLc : θ.IsSignalizerSubgroup Lc := hL.map_conj_of_mem_common hc
    have hWM : W ≤ Mc := normal_p_le_ambient_supplement U Mc W
      (signalizer_le_normalizer_closure θ hA4 W hW) (θ.closureWithin_le _) hWq hUfactor
    have hMN : Mc ⊓ Subgroup.normalizer (W : Set G) ≤ U := by
      let _ : IsInvariant A G W := hW.2.2.1
      let _ : IsInvariant A G Mc := hMc.2.2.1
      let _ := isInvariant_normalizer (A := A) W
      exact (hMc.mono inf_le_left (isInvariant_inf Mc _)).le_closureWithin hA4 inf_le_right
    have hMcfactor : Mc = (pPrimeCore q Mc).map Mc.subtype ⊔ (Lc ⊓ Mc) := by
      simpa only [inf_comm] using factor_map_conj q M L c hMfactor
    obtain ⟨c₁, hc₁, hUfinal⟩ := relative_signalizer_core_factorization θ Lc Mc U W
      hLc hMc hU hW hWq hWM (θ.closureWithin_le _) hMN hMcfactor hUfactor
    have hcommon : c₁ * c ∈ θ.common := θ.common.mul_mem hc₁.1 hc
    have hUfinal' : U = (pPrimeCore q U).map U.subtype ⊔
        (U ⊓ L.map (MulAut.conj (c₁ * c) : G →* G)) := by
      simpa only [Lc, map_conj_comp] using hUfinal
    have hCfinal := θ.value_core_factorization_of_local_factorization q a U (L.map (MulAut.conj (c₁ * c) : G →* G))
      hU (hL.map_conj_of_mem_common hcommon) hCfactor hUfinal'
    exact remove_common_conjugate θ q a L (c₁ * c) hcommon hCfinal
  · have htop : pPrimeCore q (θ.subgroup a) = ⊤ := by
      apply top_unique
      apply le_sSup
      refine ⟨inferInstance, ?_⟩
      simpa only [Subgroup.card_top] using (Fact.out : q.Prime).coprime_iff_not_dvd.mpr hadiv
    rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact (sup_eq_left.mpr inf_le_left).symm

end Glauberman

