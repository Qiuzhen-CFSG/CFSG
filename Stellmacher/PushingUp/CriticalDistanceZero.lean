module

public import Stellmacher.PushingUp.CriticalDistanceBasic
public import Stellmacher.PushingUp.NestedSL2ResidualCentralizer

/-!
# The distance-zero branch of pushing up

This module proves Stellmacher, *Pushing up*, Arch. Math. 46 (1986), (3.1),
journal p. 14, specialized to `p = 2` and `n = 1`: if the critical distance
of the free-amalgam graph is zero, then the original Sylow 2-subgroup is
elementary abelian.

The proof first realizes the attained critical distance at the base vertex.
The escaping subgroup `Z_a` supplies an involution outside the local 2-core
which centralizes that core; the canonical equivalence from the original
group to the base stabilizer transports this involution back to `M`.  The
graph-free residual-centralization theorem then gives
`[O₂(M),O²(M)] = 1`.  Finally, the nested `SL₂(2)` quotient makes the Sylow
image modulo `O₂(M)` have order two, so `Φ(S) ≤ O₂(M)`.  It is normalized by
both `S` and `O²(M)`; these generate `M`, and condition (P) forces
`Φ(S)=1`.

No finiteness assumption is made on the vertex set or free amalgam.
-/

namespace Stellmacher.PushingUp

open AmalgamGraph
open scoped Pointwise

universe u

variable {M : Type u} [Group M]

private def zeroBaseMHom (S : Subgroup M) :
    M →* stabilizer S (mVertex S 1) :=
  (embedM S).codRestrict _ (fun m ↦ by
    rw [stabilizer_m_base]
    exact ⟨m, rfl⟩)

private theorem zeroBaseMHom_injective (S : Subgroup M) :
    Function.Injective (zeroBaseMHom S) := by
  intro x y hxy
  apply embedM_injective S
  exact congrArg Subtype.val hxy

private theorem zeroBaseMHom_surjective (S : Subgroup M) :
    Function.Surjective (zeroBaseMHom S) := by
  intro y
  have hy : (y : FreeAmalgam S) ∈ Mbar S := by
    rw [← stabilizer_m_base]
    exact y.property
  obtain ⟨m, hm⟩ := hy
  exact ⟨m, Subtype.ext hm⟩

private noncomputable def zeroBaseMEquiv (S : Subgroup M) :
    M ≃* stabilizer S (mVertex S 1) :=
  MulEquiv.ofBijective (zeroBaseMHom S)
    ⟨zeroBaseMHom_injective S, zeroBaseMHom_surjective S⟩

private theorem zero_vertexZ_base_ne_bot [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) : vertexZ S (mVertex S 1) ≠ ⊥ := by
  classical
  let Ta : Sylow 2 (stabilizer S (mVertex S 1)) := default
  have hbasic := criticalDistance_basic S T hTS hP hSne
    (mVertex S 1) (hVertex S 1) ⟨1, by simp⟩ (base_adjacent S)
  intro hZbot
  have hOmegaLe : sylowOmegaAt S (mVertex S 1) Ta ≤
      vertexZ S (mVertex S 1) := le_sSup ⟨Ta, rfl⟩
  have hOmegaBot : sylowOmegaAt S (mVertex S 1) Ta = ⊥ := by
    apply le_bot_iff.mp
    rw [← hZbot]
    exact hOmegaLe
  exact hbasic.vertexZ_ne_sylowOmega Ta (hZbot.trans hOmegaBot.symm)

private theorem zero_criticalDistanceSet_nonempty [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) : (criticalDistanceSet S).Nonempty := by
  classical
  have hZne := zero_vertexZ_base_ne_bot S T hTS hP hSne
  have hfaith := actionKernel_eq_bot S T hTS hP
  obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  have hmoved : ∃ d : Vertex S, act S (z : FreeAmalgam S) d ≠ d := by
    by_contra hfix
    push Not at hfix
    have hzker : (z : FreeAmalgam S) ∈ actionKernel S := hfix
    have hzone : (z : FreeAmalgam S) = 1 := by
      rw [hfaith] at hzker
      simpa using hzker
    exact hz (Subtype.ext hzone)
  obtain ⟨d, hzd⟩ := hmoved
  exact ⟨(cosetGraph S).dist (mVertex S 1) d, d, rfl, fun hZkernel ↦
    hzd (hZkernel z.property).1⟩

private theorem zero_vertexZ_not_le_twoCore [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) (hb : criticalDistance S = 0) :
    ¬ vertexZ S (mVertex S 1) ≤ vertexTwoCore S (mVertex S 1) := by
  have hmem : criticalDistance S ∈ criticalDistanceSet S :=
    Nat.sInf_mem (zero_criticalDistanceSet_nonempty S T hTS hP hSne)
  rw [hb] at hmem
  obtain ⟨d, hdist, hnot⟩ := hmem
  have hd : d = mVertex S 1 :=
    ((cosetGraph_connected S).dist_eq_zero_iff).mp hdist |>.symm
  subst d
  have hbasic := criticalDistance_basic S T hTS hP hSne
    (mVertex S 1) (hVertex S 1) ⟨1, by simp⟩ (base_adjacent S)
  obtain ⟨P, hP⟩ := hbasic.twoCore_sylow_kernel
  have hQkernel : vertexTwoCore S (mVertex S 1) ≤
      neighborhoodKernel S (mVertex S 1) := by
    rw [← hP]
    exact Subgroup.map_subtype_le
      ((P : Sylow 2 (neighborhoodKernel S (mVertex S 1))) :
        Subgroup (neighborhoodKernel S (mVertex S 1)))
  exact fun hZQ ↦ hnot (hZQ.trans hQkernel)

private theorem zero_exists_local_central_involution [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) (hb : criticalDistance S = 0) :
    ∃ z : stabilizer S (mVertex S 1),
      z ∉ pCore 2 (stabilizer S (mVertex S 1)) ∧
        z ∈ Subgroup.centralizer
          (pCore 2 (stabilizer S (mVertex S 1)) : Set _) ∧ z ^ 2 = 1 := by
  classical
  have hnot := zero_vertexZ_not_le_twoCore S T hTS hP hSne hb
  have hsome : ∃ Ta : Sylow 2 (stabilizer S (mVertex S 1)),
      ¬ sylowOmegaAt S (mVertex S 1) Ta ≤
        vertexTwoCore S (mVertex S 1) := by
    by_contra hall
    push Not at hall
    apply hnot
    apply sSup_le
    rintro A ⟨Ta, rfl⟩
    exact hall Ta
  obtain ⟨Ta, hTa⟩ := hsome
  obtain ⟨x, hxOmega, hxQ⟩ := Set.not_subset.mp hTa
  have hxSylow : x ∈ sylowAt S (mVertex S 1) Ta :=
    (mem_omegaOneCenterAmbient_iff _ _).mp hxOmega |>.1
  obtain ⟨z, hzTa, hzx⟩ := hxSylow
  have hzQ : z ∉ pCore 2 (stabilizer S (mVertex S 1)) := by
    intro hz
    apply hxQ
    unfold vertexTwoCore twoCoreAmbient
    exact ⟨z, hz, hzx⟩
  have hzsq : z ^ 2 = 1 := by
    apply (stabilizer S (mVertex S 1)).subtype_injective
    simpa [← hzx] using
      (mem_omegaOneCenterAmbient_iff _ _).mp hxOmega |>.2.1
  have hzC : z ∈ Subgroup.centralizer
      (pCore 2 (stabilizer S (mVertex S 1)) : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hqTa : q ∈ Ta :=
      (pCore_isPGroup (p := 2) (G := stabilizer S (mVertex S 1))).le_sylow_of_normal Ta hq
    have hqMap : (q : FreeAmalgam S) ∈ sylowAt S (mVertex S 1) Ta :=
      Subgroup.mem_map_of_mem (stabilizer S (mVertex S 1)).subtype hqTa
    have hcomm := (mem_omegaOneCenterAmbient_iff _ _).mp hxOmega |>.2.2
      (q : FreeAmalgam S) hqMap
    apply (stabilizer S (mVertex S 1)).subtype_injective
    simpa [← hzx] using hcomm
  exact ⟨z, hzQ, hzC, hzsq⟩

private theorem zero_exists_original_central_involution [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) (hb : criticalDistance S = 0) :
    ∃ z : M, z ∉ pCore 2 M ∧
      z ∈ Subgroup.centralizer (pCore 2 M : Set M) ∧ z ^ 2 = 1 := by
  obtain ⟨y, hyQ, hyC, hysq⟩ :=
    zero_exists_local_central_involution S T hTS hP hSne hb
  let e := zeroBaseMEquiv S
  let z : M := e.symm y
  have hcore : (pCore 2 M).map e.toMonoidHom =
      pCore 2 (stabilizer S (mVertex S 1)) := pCore_map_iso 2 e
  have hzQ : z ∉ pCore 2 M := by
    intro hz
    apply hyQ
    rw [← hcore]
    simpa [z] using Subgroup.mem_map_of_mem e.toMonoidHom hz
  have hzC : z ∈ Subgroup.centralizer (pCore 2 M : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have heqQ : e q ∈ pCore 2 (stabilizer S (mVertex S 1)) := by
      rw [← hcore]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hq
    have hcomm := (Subgroup.mem_centralizer_iff.mp hyC) (e q) heqQ
    exact e.injective (by simpa [z] using hcomm)
  have hzsq : z ^ 2 = 1 := e.injective (by simpa [z] using hysq)
  exact ⟨z, hzQ, hzC, hzsq⟩

private theorem zero_pCore_quotient_pCore_eq_bot
    {G : Type u} [Group G] :
    pCore 2 (G ⧸ pCore 2 G) = ⊥ := by
  have hmap := pCore_map_mk'_eq_of_normal_isPGroup
    (G := G) (p := 2) (pCore 2 G)
      (pCore_isPGroup (p := 2) (G := G))
  rw [← hmap]
  exact QuotientGroup.map_mk'_self (N := pCore 2 G)

private theorem zero_frattini_odd_of_core_eq_bot
    {G : Type u} [Group G] [Finite G] (hcore : pCore 2 G = ⊥) :
    ¬ 2 ∣ Nat.card (frattini G) := by
  let Φ : Subgroup G := frattini G
  let P : Sylow 2 Φ := default
  have hΦnil : Group.IsNilpotent Φ := by
    simpa [Φ] using (frattini_nilpotent (G := G))
  have hPnormal : (P : Subgroup Φ).Normal :=
    Group.IsNilpotent.sylow_normal hΦnil 2 P
  let _ : (P : Subgroup Φ).Characteristic :=
    Sylow.characteristic_of_normal P hPnormal
  have hPmapNormal : ((P : Subgroup Φ).map Φ.subtype).Normal := by
    infer_instance
  have hPmapCore : (P : Subgroup Φ).map Φ.subtype ≤ pCore 2 G :=
    le_sSup ⟨hPmapNormal, P.isPGroup'.map Φ.subtype⟩
  intro hdvd
  have hPne : (P : Subgroup Φ) ≠ ⊥ := P.ne_bot_of_dvd_card hdvd
  have hPmapBot : (P : Subgroup Φ).map Φ.subtype = ⊥ :=
    le_bot_iff.mp (hPmapCore.trans (le_of_eq hcore))
  exact hPne <|
    (Subgroup.map_eq_bot_iff_of_injective
      (H := (P : Subgroup Φ)) (f := Φ.subtype) Φ.subtype_injective).mp hPmapBot

private theorem zero_inf_eq_bot_of_two_group_odd_card
    {G : Type u} [Group G] [Finite G]
    (P K : Subgroup G) (hP : IsPGroup 2 P)
    (hKodd : ¬ 2 ∣ Nat.card K) : P ⊓ K = ⊥ := by
  have hI : IsPGroup 2 ↥(P ⊓ K) := hP.to_le inf_le_left
  rcases hI.card_eq_or_dvd with hcard | hdvd
  · exact Subgroup.card_eq_one.mp hcard
  · exact False.elim (hKodd (hdvd.trans (Subgroup.card_dvd_of_le inf_le_right)))

private theorem zero_sylow_quotient_pCore_card_two
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hA : IsSL2Two
      ((G ⧸ pCore 2 G) ⧸ frattini (G ⧸ pCore 2 G))) :
    Nat.card (S.mapSurjective
      (QuotientGroup.mk'_surjective (pCore 2 G))) = 2 := by
  let H := G ⧸ pCore 2 G
  let Φ : Subgroup H := frattini H
  let q : G →* H := QuotientGroup.mk' (pCore 2 G)
  let T : Sylow 2 H := S.mapSurjective
    (QuotientGroup.mk'_surjective (pCore 2 G))
  let r : H →* H ⧸ Φ := QuotientGroup.mk' Φ
  let Tbar : Sylow 2 (H ⧸ Φ) :=
    T.mapSurjective (QuotientGroup.mk'_surjective Φ)
  have hquotcard : Nat.card (H ⧸ Φ) = 6 := by
    simpa [H, Φ] using
      SectionOne.RankOneThreeGroupAssembly.isSL2Two_card hA
  have hTbarcard : Nat.card Tbar = 2 := by
    rw [Tbar.card_eq_multiplicity, hquotcard]
    have hf6 : Nat.factorization 6 2 = 1 := by
      change Nat.factorization (3 * 2) 2 = 1
      rw [Nat.factorization_mul (by decide) (by decide)]
      norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
    simp [hf6]
  have hcore : pCore 2 H = ⊥ := by
    simpa [H] using zero_pCore_quotient_pCore_eq_bot (G := G)
  have hodd : ¬ 2 ∣ Nat.card Φ := by
    simpa [H, Φ] using zero_frattini_odd_of_core_eq_bot hcore
  have hinter : (T : Subgroup H) ⊓ Φ = ⊥ :=
    zero_inf_eq_bot_of_two_group_odd_card (T : Subgroup H) Φ T.isPGroup' hodd
  have hrinj : Function.Injective (r.comp (T : Subgroup H).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm
    · intro t ht
      have htΦ : (t : H) ∈ Φ :=
        (QuotientGroup.eq_one_iff (N := Φ) (x := (t : H))).mp ht
      have htI : (t : H) ∈ (T : Subgroup H) ⊓ Φ := ⟨t.property, htΦ⟩
      rw [hinter] at htI
      simpa using htI
    · exact bot_le
  let fT : T →* H ⧸ Φ := r.comp (T : Subgroup H).subtype
  have hfrange : fT.range = (T : Subgroup H).map r := by
    ext x
    simp [fT]
  have hcardmap : Nat.card ((T : Subgroup H).map r) = Nat.card T := by
    rw [← hfrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hrinj).toEquiv).symm
  have hcoe : (Tbar : Subgroup (H ⧸ Φ)) = (T : Subgroup H).map r := rfl
  change Nat.card T = 2
  rw [← hcardmap, ← hcoe, hTbarcard]

private theorem zero_isCoatom_of_index_eq_prime
    {G : Type u} [Group G] {p : ℕ} [Fact p.Prime]
    (H : Subgroup G) (hidx : H.index = p) : IsCoatom H := by
  have hp : p.Prime := Fact.out
  rw [← covBy_top_iff]
  refine ⟨Ne.lt_top (fun htop ↦ ?_), fun K hHK hKtop ↦ ?_⟩
  · have hp_one : p = 1 := by simpa [htop] using hidx.symm
    exact hp.ne_one hp_one
  · have hrel := Subgroup.relIndex_mul_index hHK.le
    have hprime : (H.relIndex K * K.index).Prime := by
      rw [hrel, hidx]
      exact hp
    rcases Nat.prime_mul_iff.mp hprime with ⟨_, hindex_one⟩ | ⟨_, hrel_one⟩
    · rw [Subgroup.index_eq_one] at hindex_one
      simp [hindex_one] at hKtop
    · rw [Subgroup.relIndex_eq_one] at hrel_one
      exact hHK.not_ge hrel_one

private theorem zero_frattini_map_le_pCore
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hA : IsSL2Two
      ((G ⧸ pCore 2 G) ⧸ frattini (G ⧸ pCore 2 G))) :
    (frattini S).map (S : Subgroup G).subtype ≤ pCore 2 G := by
  let Q : Subgroup G := pCore 2 G
  let X := G ⧸ Q
  let q : G →* X := QuotientGroup.mk' Q
  let f : S →* X := q.comp (S : Subgroup G).subtype
  let SX : Sylow 2 X :=
    S.mapSurjective (f := q) (QuotientGroup.mk'_surjective Q)
  have hSXcard : Nat.card SX = 2 := by
    change Nat.card (S.mapSurjective
      (f := QuotientGroup.mk' (pCore 2 G))
      (QuotientGroup.mk'_surjective (pCore 2 G))) = 2
    exact zero_sylow_quotient_pCore_card_two (G := G) S hA
  have hfrange : f.range = (SX : Subgroup X) := by
    ext x
    simp [f, SX, q]
  have hindex : f.ker.index = 2 := by
    rw [Subgroup.index_ker, hfrange]
    exact hSXcard
  have hPhiKer : frattini S ≤ f.ker :=
    frattini_le_coatom (zero_isCoatom_of_index_eq_prime f.ker hindex)
  intro x hx
  obtain ⟨s, hs, rfl⟩ := hx
  have hsKer : s ∈ f.ker := hPhiKer hs
  exact (QuotientGroup.eq_one_iff (N := Q) (x := (s : G))).mp hsKer

private theorem zero_elementary_of_core_residual_commute
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hP : ∀ K : Subgroup S, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (S : Subgroup G).subtype).Normal)
    (hA : IsSL2Two
      ((G ⧸ pCore 2 G) ⧸ frattini (G ⧸ pCore 2 G)))
    (hcomm : ⁅pCore 2 G,
      twoResidualAmbient (⊤ : Subgroup G)⁆ = ⊥) :
    IsElementaryAbelian 2 (S : Subgroup G) := by
  classical
  let Q : Subgroup G := pCore 2 G
  let R : Subgroup G := twoResidualAmbient (⊤ : Subgroup G)
  let K0 : Subgroup S := frattini S
  let K : Subgroup G := K0.map (S : Subgroup G).subtype
  have hKQ : K ≤ Q := by
    simpa [K, K0, Q] using zero_frattini_map_le_pCore S hA
  have hKS : K ≤ (S : Subgroup G) := Subgroup.map_subtype_le K0
  have hKsub : K.subgroupOf (S : Subgroup G) = K0 := by
    simpa [K] using Subgroup.comap_map_eq_self_of_injective
      (S : Subgroup G).subtype_injective K0
  have hSnormK : (S : Subgroup G) ≤ Subgroup.normalizer (K : Set G) := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hKS).mp
    rw [hKsub]
    infer_instance
  have hRQ : R ≤ Subgroup.centralizer (Q : Set G) := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    rw [Subgroup.commutator_comm]
    simpa [Q, R] using hcomm
  have hRnormK : R ≤ Subgroup.normalizer (K : Set G) :=
    hRQ.trans (Subgroup.centralizer_le hKQ) |>.trans
      (Subgroup.centralizer_le_normalizer (K : Set G))
  have hRS : R ⊔ (S : Subgroup G) = ⊤ :=
    twoResidualAmbient_top_sup_sylow S
  have hnormalizer : Subgroup.normalizer (K : Set G) = ⊤ := by
    apply top_unique
    rw [← hRS]
    exact sup_le hRnormK hSnormK
  have hKnormal : K.Normal := Subgroup.normalizer_eq_top_iff.mp hnormalizer
  have hK0bot : K0 = ⊥ := by
    by_contra hK0ne
    exact hP K0 (by infer_instance) hK0ne hKnormal
  let _ : Fact (IsPGroup 2 S) := ⟨S.isPGroup'⟩
  exact (frattini_eq_bot_iff_isElementaryAbelian (R := S) (p := 2)).mp
    (by simpa [K0] using hK0bot)

/-- Stellmacher, *Pushing up* (1986), (3.1), specialized to `p=2,n=1`. -/
public theorem criticalDistance_zero_isElementaryAbelian [Finite M]
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (hb : criticalDistance S = 0) :
    IsElementaryAbelian 2 S := by
  subst S
  obtain ⟨z, hzQ, hzC, hzsq⟩ :=
    zero_exists_original_central_involution (T : Subgroup M) T rfl hP hSne hb
  have hcomm := residual_centralizes_twoCore_of_nestedSL2Two
    z hzQ hzC hzsq hA
  exact zero_elementary_of_core_residual_commute T hP hA hcomm

end Stellmacher.PushingUp
