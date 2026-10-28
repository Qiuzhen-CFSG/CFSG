module

public import Theory.GroupTheory.Signalizer.LocalCompleteness
public import Theory.GroupTheory.Signalizer.PrimeCompletion
public import Theory.GroupAction.OddInvariantSylow
public import Glauberman.Signalizer.SolvableZJNormalizer
public import Glauberman.CharacteristicFunctor.Invariant
public import Glauberman.Signalizer.RelativeCoreFactorization
public import Glauberman.Signalizer.FactorizationCriterion

/-!
# Local completeness implies binary signalizer completeness

Let a finite elementary abelian two-group of order at least eight act on a
finite group, with an odd solvable signalizer family for that exact action.
If the family is locally complete, then its actual generated closure is a
signalizer subgroup: it has odd order, is solvable and invariant, and its
fixed subgroups satisfy the family bounds.

If every value is a three-group, prime-valued completeness applies. Otherwise
oddness supplies a prime `q ≥ 5` dividing a value. Choose a nontrivial maximal
q-signalizer subgroup `S` and let `M` be the signalizer closure inside the
normalizer of `ZJ(S)`. The proved normalizer-factorization criterion reduces
completeness to showing that each nontrivial q-signalizer subgroup `W` has
normalizer closure `U` equal to its q-prime core times its intersection with
a common-subgroup conjugate of `M`.

Assume a counterexample and maximize the order of an invariant Sylow q-subgroup
`T` of `U`. The solvable ZJ normalizer theorem factors `U` over the closure
`L` inside the normalizer of `ZJ(T)`. Extend `T` to a maximal q-signalizer
subgroup. If it is already maximal, transitivity and functor naturality
identify `L` with a common-subgroup conjugate of `M`. Otherwise the normalizer
condition in the larger q-group gives a strictly larger q-subgroup inside
`L`. Maximality supplies the required factorization for `L`; the proved
relative core-factorization theorem, with the original subgroup `W`, then
supplies it for `U`, a contradiction.

This is Kurzweil--Stellmacher, *The Theory of Finite Groups*, 11.2.8,
printed pp. 324--325 (`refs/Qwen/kurzweil/Chapter12.tex`). The canonical ZJ
functor replaces the book's characteristic functor W using its proved
nontriviality, naturality, and solvable normalizer supplement. Two verified
source slips are read as `N_{S*}(ZJ(T)) ≤ L` and a final intersection with
`U`, respectively; the displayed factorization interfaces retain these
correct ambient groups. The proof uses the actual previously proved
normalizer criterion and relative factorization, with no auxiliary
completion assumption in its public statement.
-/

open scoped Pointwise
open Theory.GroupTheory

namespace Glauberman

variable {A G : Type*} [Group A] [Finite A] [Group G] [Finite G]
  [IsElementaryAbelian 2 A] [MulDistribMulAction A G]

omit [Finite A] [IsElementaryAbelian 2 A] in
private theorem exists_large_prime (θ : TwoSignalizerFamily A G)
    (hnot : ¬ ∀ a, IsPGroup 3 (θ.subgroup a)) :
    ∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ ∃ a, q ∣ Nat.card (θ.subgroup a) := by
  classical
  by_contra hn
  apply hnot
  intro a
  apply IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_)
  intro d hd hdiv
  have hne2 : d ≠ 2 := fun he => (θ.odd a).not_two_dvd_nat (he ▸ hdiv)
  have hsmall : ¬ 5 ≤ d := fun h5 => hn ⟨d, hd, h5, a, hdiv⟩
  have hne4 : d ≠ 4 := by
    intro h
    subst d
    norm_num at hd
  have := hd.two_le
  omega

private def HasSylowImage (q : ℕ) (T U : Subgroup G) : Prop :=
  ∃ P : Sylow q U, (P : Subgroup U).map U.subtype = T

omit [Finite A] in
private theorem signalizer_sylow_extension (θ : TwoSignalizerFamily A G)
    {q : ℕ} [Fact q.Prime] (U W : Subgroup G)
    (hU : θ.IsSignalizerSubgroup U) (hW : θ.IsSignalizerSubgroup W)
    (hWq : IsPGroup q W) (hWU : W ≤ U) :
    ∃ T : Subgroup G, θ.IsSignalizerSubgroup T ∧ IsPGroup q T ∧
      W ≤ T ∧ HasSylowImage q T U := by
  let _ : IsInvariant A G U := hU.2.2.1
  let _ : IsInvariant A G W := hW.2.2.1
  have hWI : IsInvariant A U (W.subgroupOf U) := isInvariant_subgroupOf W U
  obtain ⟨P, hWP, hPI⟩ := exists_invariant_sylow_le_of_isPGroup
    (G := U) (A := A) (IsElementaryAbelian.isPGroup 2 A) hU.1
    (W.subgroupOf U) hWq.comap_subtype hWI
  let _ : IsInvariant A U (P : Subgroup U) := hPI
  refine ⟨(P : Subgroup U).map U.subtype,
    hU.mono (Subgroup.map_subtype_le _) (isInvariant_map_subtype U _),
    P.isPGroup'.map U.subtype, ?_, P, rfl⟩
  intro w hw
  exact ⟨⟨w, hWU hw⟩, hWP hw, rfl⟩

omit [Finite A] [IsElementaryAbelian 2 A] in
private theorem zero_signalizer (θ : TwoSignalizerFamily A G) :
    θ.IsSignalizerSubgroup (⊥ : Subgroup G) := by
  refine ⟨by simp, inferInstance, isInvariant_of_characteristic (A := A) ⊥, ?_⟩
  intro a
  simp

omit [Finite A] in
private theorem exists_nontrivial_prime_signalizer (θ : TwoSignalizerFamily A G)
    {q : ℕ} [Fact q.Prime] (hdiv : ∃ a, q ∣ Nat.card (θ.subgroup a)) :
    ∃ S : Subgroup G, θ.IsSignalizerSubgroup S ∧ IsPGroup q S ∧ S ≠ ⊥ := by
  obtain ⟨a, ha⟩ := hdiv
  obtain ⟨S, hS, hSq, _, P, hP⟩ := signalizer_sylow_extension θ (q := q)
    (θ.subgroup a) ⊥ (θ.value_isSignalizerSubgroup a) (zero_signalizer θ)
    IsPGroup.of_bot bot_le
  refine ⟨S, hS, hSq, ?_⟩
  intro hbot
  have hPbot : (P : Subgroup (θ.subgroup a)) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (θ.subgroup a).subtype_injective).mp
      (hP.trans hbot)
  exact P.ne_bot_of_dvd_card ha hPbot

private abbrev localZJ (q : ℕ) [Fact q.Prime] (T : Subgroup G) :=
  (zjCharacteristicFunctor q).K T

private theorem local_sylow_zj_factorization (θ : TwoSignalizerFamily A G)
    (hA : 4 ≤ Nat.card A) {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q)
    (U T : Subgroup G) (hU : θ.IsSignalizerSubgroup U)
    (hT : HasSylowImage q T U) (hZ : IsInvariant A G (localZJ q T)) :
    U = (pPrimeCore q U).map U.subtype ⊔
      (U ⊓ θ.closureWithin (Subgroup.normalizer (localZJ q T : Set G))) := by
  obtain ⟨P, hP⟩ := hT
  let _ : IsInvariant A G U := hU.2.2.1
  let _ : IsInvariant A G (localZJ q T) := hZ
  let N := Subgroup.normalizer (localZJ q T : Set G)
  let _ : IsInvariant A G N := isInvariant_normalizer (localZJ q T)
  have hUN : θ.IsSignalizerSubgroup (U ⊓ N) :=
    hU.mono inf_le_left (isInvariant_inf U N)
  have hUNL : U ⊓ N ≤ θ.closureWithin N :=
    hUN.le_closureWithin hA inf_le_right
  have hZmap : ((zjCharacteristicFunctor q).K (P : Subgroup U)).map U.subtype =
      localZJ q T := by
    rw [← (zjCharacteristicFunctor q).K_map U.subtype (P : Subgroup U)
      (U.subtype_injective.comp (P : Subgroup U).subtype_injective), hP]
  have hnormalizer : (Subgroup.normalizer
      ((zjCharacteristicFunctor q).K (P : Subgroup U) : Set U)).map U.subtype ≤ N := by
    have h := ((zjCharacteristicFunctor q).K (P : Subgroup U)).le_normalizer_map U.subtype
    rwa [hZmap] at h
  have hfactor : (pPrimeCore q U).map U.subtype ⊔
      (Subgroup.normalizer
        ((zjCharacteristicFunctor q).K (P : Subgroup U) : Set U)).map U.subtype = U := by
    have h := congrArg (fun V : Subgroup U => V.map U.subtype)
      (solvable_oddPrime_normalizer_zj_supplement hq hU.2.1 P)
    simpa only [Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype] using h
  apply le_antisymm
  · calc
      U = _ := hfactor.symm
      _ ≤ _ := ?_
    refine sup_le le_sup_left ?_
    intro x hx
    exact Subgroup.mem_sup_right ⟨Subgroup.map_subtype_le _ hx,
      hUNL ⟨Subgroup.map_subtype_le _ hx, hnormalizer hx⟩⟩
  · exact sup_le (Subgroup.map_subtype_le _) inf_le_left

omit [Finite A] [Finite G] [IsElementaryAbelian 2 A] in
private theorem zj_signalizer (θ : TwoSignalizerFamily A G)
    {q : ℕ} [Fact q.Prime] (T : Subgroup G) (hT : θ.IsSignalizerSubgroup T) :
    θ.IsSignalizerSubgroup (localZJ q T) := by
  let _ : IsInvariant A G T := hT.2.2.1
  exact hT.mono ((zjCharacteristicFunctor q).K_le T)
    ((zjCharacteristicFunctor q).isInvariant T)

omit [Finite A] [Finite G] [IsElementaryAbelian 2 A] in
private theorem localZJClosure_conj (θ : TwoSignalizerFamily A G)
    {q : ℕ} [Fact q.Prime] (S : Subgroup G) {c : G} (hc : c ∈ θ.common) :
    (θ.closureWithin (Subgroup.normalizer (localZJ q S : Set G))).map
        (MulAut.conj c : G →* G) =
      θ.closureWithin (Subgroup.normalizer
        (localZJ q (S.map (MulAut.conj c : G →* G)) : Set G)) := by
  rw [θ.closureWithin_map_conj _ hc]
  congr 1
  have hK := (zjCharacteristicFunctor q).K_conj S c
  simp only [MulEquiv.toMonoidHom_eq_coe] at hK
  dsimp only [localZJ]
  rw [hK]
  exact Subgroup.map_equiv_normalizer_eq _ _

private theorem signalizer_zj_growth (θ : TwoSignalizerFamily A G)
    (hA : 4 ≤ Nat.card A) {q : ℕ} [Fact q.Prime]
    (T S : Subgroup G) (hT : θ.IsSignalizerSubgroup T)
    (hS : θ.IsSignalizerSubgroup S) (hSq : IsPGroup q S) (hTS : T < S) :
    ∃ R : Subgroup G, θ.IsSignalizerSubgroup R ∧ IsPGroup q R ∧ T < R ∧
      R ≤ θ.closureWithin (Subgroup.normalizer (localZJ q T : Set G)) := by
  let _ : IsInvariant A G T := hT.2.2.1
  let _ : IsInvariant A G S := hS.2.2.1
  let _ : IsInvariant A G (localZJ q T) := (zjCharacteristicFunctor q).isInvariant T
  let N := Subgroup.normalizer (localZJ q T : Set G)
  let _ : IsInvariant A G N := isInvariant_normalizer (localZJ q T)
  let R := S ⊓ N
  have hR : θ.IsSignalizerSubgroup R := hS.mono inf_le_left (isInvariant_inf S N)
  have hTN : T ≤ N := T.le_normalizer.trans
    ((zjCharacteristicFunctor q).normalizer_le_normalizer_K T)
  refine ⟨R, hR, hSq.to_le inf_le_left, ?_, hR.le_closureWithin hA inf_le_right⟩
  apply lt_of_le_of_ne (le_inf hTS.le hTN)
  intro heq
  let _ := hSq.isNilpotent
  have hproper : T.subgroupOf S < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro htop
    exact hTS.not_ge (Subgroup.subgroupOf_eq_top.mp htop)
  have hgrowth := Group.normalizerCondition_of_isNilpotent (G := S) (T.subgroupOf S) hproper
  obtain ⟨x, hx, hxnot⟩ := SetLike.exists_of_lt hgrowth
  have hxN : (x : G) ∈ Subgroup.normalizer (T : Set G) := by
    change x ∈ (Subgroup.normalizer (T : Set G)).subgroupOf S
    rw [Subgroup.subgroupOf_normalizer_eq hTS.le]
    exact hx
  have hxR : (x : G) ∈ R :=
    ⟨x.property, (zjCharacteristicFunctor q).normalizer_le_normalizer_K T hxN⟩
  exact hxnot (heq.symm ▸ hxR)

private theorem signalizer_le_normalizer_closure (θ : TwoSignalizerFamily A G)
    (hA : 4 ≤ Nat.card A) (W : Subgroup G) (hW : θ.IsSignalizerSubgroup W) :
    W ≤ θ.closureWithin (Subgroup.normalizer (W : Set G)) := by
  let _ : IsInvariant A G W := hW.2.2.1
  let _ := isInvariant_normalizer (A := A) W
  exact hW.le_closureWithin hA W.le_normalizer

private def CoreFactor (θ : TwoSignalizerFamily A G) (q : ℕ) (M W : Subgroup G) : Prop :=
  let U := θ.closureWithin (Subgroup.normalizer (W : Set G))
  ∃ c : G, c ∈ θ.common ∧
    U = (pPrimeCore q U).map U.subtype ⊔ (U ⊓ M.map (MulAut.conj c : G →* G))

private theorem normalizer_core_factorizations (θ : TwoSignalizerFamily A G)
    (hA : 8 ≤ Nat.card A) (hl : θ.IsLocallyComplete)
    {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q) (S : Subgroup G)
    (hS : Maximal (fun V : Subgroup G => θ.IsSignalizerSubgroup V ∧ IsPGroup q V) S)
    (hSne : S ≠ ⊥) :
    ∀ W : Subgroup G, θ.IsSignalizerSubgroup W → IsPGroup q W → W ≠ ⊥ →
      CoreFactor θ q (θ.closureWithin (Subgroup.normalizer (localZJ q S : Set G))) W := by
  classical
  have hA4 : 4 ≤ Nat.card A := by omega
  let M := θ.closureWithin (Subgroup.normalizer (localZJ q S : Set G))
  have hM : θ.IsSignalizerSubgroup M := hl.normalizer _ (zj_signalizer θ S hS.1.1)
    ((zjCharacteristicFunctor q).K_nontrivial S hS.1.2 hSne)
  intro W₀ hW₀ hW₀q hW₀ne
  by_contra hbad₀
  let U₀ := θ.closureWithin (Subgroup.normalizer (W₀ : Set G))
  have hU₀ : θ.IsSignalizerSubgroup U₀ := hl.normalizer W₀ hW₀ hW₀ne
  obtain ⟨T₀, hT₀, hT₀q, hW₀T₀, hT₀syl⟩ := signalizer_sylow_extension θ U₀ W₀ hU₀ hW₀ hW₀q
    (signalizer_le_normalizer_closure θ hA4 W₀ hW₀)
  let bad : Set (Subgroup G × Subgroup G) := {p |
    θ.IsSignalizerSubgroup p.1 ∧ IsPGroup q p.1 ∧ p.1 ≠ ⊥ ∧
    θ.IsSignalizerSubgroup p.2 ∧ IsPGroup q p.2 ∧ p.1 ≤ p.2 ∧
    HasSylowImage q p.2 (θ.closureWithin (Subgroup.normalizer (p.1 : Set G))) ∧
    ¬ CoreFactor θ q M p.1}
  obtain ⟨⟨W, T⟩, ⟨hW, hWq, hWne, hT, hTq, hWT, hTsyl, hbad⟩, hmax⟩ :=
    bad.exists_max_image (fun p => Nat.card p.2) bad.toFinite
      ⟨(W₀,T₀), hW₀, hW₀q, hW₀ne, hT₀, hT₀q, hW₀T₀, hT₀syl, hbad₀⟩
  let U := θ.closureWithin (Subgroup.normalizer (W : Set G))
  have hU : θ.IsSignalizerSubgroup U := hl.normalizer W hW hWne
  have hTne : T ≠ ⊥ := fun heq => hWne (bot_unique (heq ▸ hWT))
  have hZT : θ.IsSignalizerSubgroup (localZJ q T) := zj_signalizer θ T hT
  have hZne : localZJ q T ≠ ⊥ := (zjCharacteristicFunctor q).K_nontrivial T hTq hTne
  let L := θ.closureWithin (Subgroup.normalizer (localZJ q T : Set G))
  have hL : θ.IsSignalizerSubgroup L := hl.normalizer _ hZT hZne
  have hUfactor : U = (pPrimeCore q U).map U.subtype ⊔ (U ⊓ L) :=
    local_sylow_zj_factorization θ hA4 hq U T hU hTsyl hZT.2.2.1
  obtain ⟨Sstar, hTSstar, hSstar⟩ := Finite.exists_le_maximal
    (p := fun V : Subgroup G => θ.IsSignalizerSubgroup V ∧ IsPGroup q V) ⟨hT, hTq⟩
  by_cases heq : T = Sstar
  · have hTmax : Maximal (fun V : Subgroup G => θ.IsSignalizerSubgroup V ∧ IsPGroup q V) T :=
      heq.symm ▸ hSstar
    obtain ⟨c, hc, hconj⟩ := θ.maximal_pSubgroups_conjugate hA (by omega) S T hS hTmax
    have hML : M.map (MulAut.conj c : G →* G) = L := by
      dsimp only [M, L]
      rw [localZJClosure_conj θ S hc, ← hconj]
    apply hbad
    exact ⟨c, hc, by simpa only [hML] using hUfactor⟩
  · have hproper : T < Sstar := lt_of_le_of_ne hTSstar heq
    obtain ⟨R, hR, hRq, hTR, hRL⟩ :=
      signalizer_zj_growth θ hA4 T Sstar hT hSstar.1.1 hSstar.1.2 hproper
    obtain ⟨T₁, hT₁, hT₁q, hRT₁, hT₁syl⟩ := signalizer_sylow_extension θ L R hL hR hRq hRL
    have hTT₁ : T < T₁ := lt_of_lt_of_le hTR hRT₁
    have hZfactor : CoreFactor θ q M (localZJ q T) := by
      by_contra hbadZ
      have hbound := hmax (localZJ q T, T₁)
        ⟨hZT, hTq.to_le ((zjCharacteristicFunctor q).K_le T), hZne,
          hT₁, hT₁q, ((zjCharacteristicFunctor q).K_le T).trans hTT₁.le, hT₁syl, hbadZ⟩
      exact hTT₁.ne (Subgroup.eq_of_le_of_card_ge hTT₁.le hbound)
    obtain ⟨c, hc, hLfactor⟩ := hZfactor
    have hWL : W ≤ L := hWT.trans (hTR.le.trans hRL)
    have hLN : L ⊓ Subgroup.normalizer (W : Set G) ≤ U := by
      let _ : IsInvariant A G W := hW.2.2.1
      let _ : IsInvariant A G L := hL.2.2.1
      let _ := isInvariant_normalizer (A := A) W
      exact (hL.mono inf_le_left (isInvariant_inf L _)).le_closureWithin hA4 inf_le_right
    obtain ⟨c₁, hc₁, hfinal⟩ := relative_signalizer_core_factorization θ
      (M.map (MulAut.conj c : G →* G)) L U W
      (hM.map_conj_of_mem_common hc) hL hU hW hWq hWL
      (θ.closureWithin_le _) hLN (by simpa only [inf_comm] using hLfactor) hUfactor
    have hmap : (M.map (MulAut.conj c : G →* G)).map (MulAut.conj c₁ : G →* G) =
        M.map (MulAut.conj (c₁ * c) : G →* G) := by
      rw [Subgroup.map_map]
      congr 1
      ext x
      change c₁ * (c * x * c⁻¹) * c₁⁻¹ = (c₁ * c) * x * (c₁ * c)⁻¹
      group
    apply hbad
    exact ⟨c₁ * c, θ.common.mul_mem hc₁.1 hc, by simpa only [hmap] using hfinal⟩

/-- Local completeness suffices for a rank-three binary signalizer family. -/
public theorem complete_of_locally_complete (θ : TwoSignalizerFamily A G)
    (hA : 8 ≤ Nat.card A) (hl : θ.IsLocallyComplete) : θ.IsComplete := by
  classical
  by_cases hthree : ∀ a, IsPGroup 3 (θ.subgroup a)
  · exact θ.complete_of_values_pGroup hA (by decide : (3 : ℕ) ≠ 2) hthree
  obtain ⟨q, hqprime, hq, hdiv⟩ := exists_large_prime θ hthree
  let _ : Fact q.Prime := ⟨hqprime⟩
  obtain ⟨S₀, hS₀, hS₀q, hS₀ne⟩ := exists_nontrivial_prime_signalizer θ hdiv
  obtain ⟨S, hS₀S, hS⟩ := Finite.exists_le_maximal
    (p := fun V : Subgroup G => θ.IsSignalizerSubgroup V ∧ IsPGroup q V) ⟨hS₀, hS₀q⟩
  have hSne : S ≠ ⊥ := fun heq => hS₀ne (bot_unique (heq ▸ hS₀S))
  let M := θ.closureWithin (Subgroup.normalizer (localZJ q S : Set G))
  have hM : θ.IsSignalizerSubgroup M := hl.normalizer _ (zj_signalizer θ S hS.1.1)
    ((zjCharacteristicFunctor q).K_nontrivial S hS.1.2 hSne)
  exact complete_of_normalizer_core_factorizations θ hA hl q hq hdiv M hM
    (normalizer_core_factorizations θ hA hl hq S hS hSne)

end Glauberman
