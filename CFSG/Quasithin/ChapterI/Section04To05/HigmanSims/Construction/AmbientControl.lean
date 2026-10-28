module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SeedGeometry
public import Theory.GroupTheory.CentralProductCenter
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Theory.GroupTheory.RelativeSylowNormalizer
public import Theory.GroupTheory.PGroup.OmegaAmbient
public import Theory.GroupTheory.SelfCentralizingCore
public import Theory.GroupTheory.OddThreeCentralizerContainment
public import Theory.GroupTheory.PPrimeCoreReduction
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# Ambient Sylow control and trivial normal cores for type HS

The center of the quaternion--cyclic core in HS1 is C₄. Self-centralization
places every central involution of a local Sylow subgroup in that center,
so the marked z is its unique central involution. The full ambient
normalizer of the local Sylow therefore centralizes z. The relative Sylow
criterion promotes the previously constructed common local Sylow to an
ambient Sylow of order 512.

A normal subgroup contained in V is trivial: full seed fusion makes any
nontrivial one equal V, contradicting the properness of its normalizer.
The first omega subgroup of the ambient two-core lies in V, which kills
that core. Finally all seven seed-involution centralizers have trivial odd
core. Their fixed subgroups in the ambient odd core are trivial, and the
three-centralizer theorem kills the ambient odd core as well.

These are consequences of the exact HS1--HS2 hypotheses preceding I.4.8,
Aschbacher--Smith, printed p.418. They provide ambient local control for the
L₃(4) and M₂₂ construction without assuming simplicity, group order, or the
rank-three action. The subgroup construction itself is not asserted here.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims

/-- The central-product presentation forces the intrinsic center to be cyclic of order four. -/
theorem CoreShape.center_model {Q : Type*} [Group Q] [Finite Q] (h : CoreShape Q) :
    Nonempty (center Q ≃* Multiplicative (ZMod 4)) := by
  obtain ⟨B, D, ⟨hB⟩, ⟨eD⟩, hi, hc, hs⟩ := h
  have hDc : D ≤ center Q := by
    intro d hd
    have hfix : B ⊔ D ≤ centralizer ({d} : Set Q) := by
      apply sup_le
      · intro b hb
        exact mem_centralizer_singleton_iff.mpr (hc b hb d hd)
      · intro a ha
        apply mem_centralizer_singleton_iff.mpr
        have he : (⟨a, ha⟩ : D) * ⟨d, hd⟩ = ⟨d, hd⟩ * ⟨a, ha⟩ :=
          eD.injective (by simp only [map_mul, mul_comm])
        exact congrArg Subtype.val he
    exact mem_center_iff.mpr fun q =>
      mem_centralizer_singleton_iff.mp (hfix (hs ▸ mem_top q))
  have hBZ : (B ⊓ D : Subgroup Q) = (center B).map B.subtype := by
    apply eq_of_le_of_card_ge
    · intro b hb
      refine ⟨⟨b, hb.1⟩, mem_center_iff.mpr ?_, rfl⟩
      intro a
      exact Subtype.ext (hc a a.property b hb.2)
    · rw [card_map_of_injective B.subtype_injective, hB.center_card, hi]
  have he : center Q = D := center_eq_of_central_product D B hDc
    (by simpa only [sup_comm] using hs) (by rw [← hBZ]; exact inf_le_right)
  exact ⟨(MulEquiv.subgroupCongr he).trans eD⟩

variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- The marked involution is the unique involution in the center of every Sylow two-subgroup of its centralizer. -/
theorem TypeAt.local_center_involution_unique (h : TypeAt z V)
    (S : Sylow 2 (involutionCentralizer z))
    (x : center (S : Subgroup (involutionCentralizer z))) (hx : orderOf x = 2) :
    ((x.val.val : involutionCentralizer z) : G) = z := by
  let H := involutionCentralizer z
  let Q := pCore 2 H
  have hQS : Q ≤ S := pCore_isPGroup.le_sylow_of_normal S
  have hxQ : x.val.val ∈ Q := h.centralizer_twoCore_selfCentralizing <| by
    intro q hq
    exact congrArg (fun s : (S : Subgroup H) => (s : H))
      (mem_center_iff.mp x.property ⟨q, hQS hq⟩)
  have hxZ : (⟨x.val.val, hxQ⟩ : Q) ∈ center Q := by
    apply mem_center_iff.mpr
    intro q
    apply Subtype.ext
    exact congrArg (fun s : (S : Subgroup H) => (s : H))
      (mem_center_iff.mp x.property ⟨q, hQS q.property⟩)
  let zH : H := ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩
  have hzQ : zH ∈ Q := h.centralizer_twoCore_selfCentralizing <| by
    intro q _
    exact Subtype.ext (mem_centralizer_singleton_iff.mp q.property)
  have hzZ : (⟨zH, hzQ⟩ : Q) ∈ center Q := by
    apply mem_center_iff.mpr
    intro q
    exact Subtype.ext (Subtype.ext (mem_centralizer_singleton_iff.mp q.val.property))
  obtain ⟨e⟩ := (h.centralizer_core.of_equiv
    (MulEquiv.subgroupCongr h.centralizer_fitting)).center_model
  let : IsCyclic (center Q) := e.isCyclic.mpr inferInstance
  have he := IsCyclic.eq_of_orderOf_eq_two
    (x := (⟨⟨x.val.val, hxQ⟩, hxZ⟩ : center Q))
    (y := (⟨⟨zH, hzQ⟩, hzZ⟩ : center Q))
    (by simpa only [← orderOf_coe] using hx)
    (by simpa only [← orderOf_coe] using h.involution)
  exact congrArg (fun a : center Q => ((a.val.val : H) : G)) he

/-- The full ambient normalizer of a local Sylow subgroup centralizes the marked involution. -/
theorem TypeAt.local_sylow_normalizer_le (h : TypeAt z V)
    (S : Sylow 2 (involutionCentralizer z)) :
    normalizer (((S : Subgroup (involutionCentralizer z)).map
      (involutionCentralizer z).subtype : Subgroup G) : Set G) ≤ involutionCentralizer z := by
  let H := involutionCentralizer z
  let R := (S : Subgroup H).map H.subtype
  let e : (S : Subgroup H) ≃* R :=
    (S : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective
  let zH : H := ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩
  have hzQ : zH ∈ pCore 2 H := h.centralizer_twoCore_selfCentralizing <| by
    intro q _
    exact Subtype.ext (mem_centralizer_singleton_iff.mp q.property)
  have hzS : zH ∈ S := pCore_isPGroup.le_sylow_of_normal S hzQ
  let zS : (S : Subgroup H) := ⟨zH, hzS⟩
  have hzZ : zS ∈ center (S : Subgroup H) := by
    apply mem_center_iff.mpr
    intro s
    exact Subtype.ext (Subtype.ext (mem_centralizer_singleton_iff.mp s.val.property))
  intro g hg
  let a := R.normalizerMonoidHom ⟨g, hg⟩
  let b := e.trans (a.trans e.symm)
  have hbZ : b zS ∈ center (S : Subgroup H) := (centerCongr b ⟨zS, hzZ⟩).property
  have hb2 : orderOf (⟨b zS, hbZ⟩ : center (S : Subgroup H)) = 2 := by
    rw [← orderOf_coe (a := (⟨b zS, hbZ⟩ : center (S : Subgroup H))), b.orderOf_eq]
    simpa only [← orderOf_coe] using h.involution
  have hh := TypeAt.local_center_involution_unique h S ⟨b zS, hbZ⟩ hb2
  have heS : b zS = zS := Subtype.ext (Subtype.ext hh)
  have heR := congrArg (fun s : (S : Subgroup H) => (e s : G)) heS
  simp only [b, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at heR
  change g * z * g⁻¹ = z at heR
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp heR)

/-- Every Sylow two-subgroup of the involution centralizer is Sylow in the ambient group. -/
theorem TypeAt.local_sylow_is_ambient (h : TypeAt z V)
    (S : Sylow 2 (involutionCentralizer z)) :
    ∃ P : Sylow 2 G, (P : Subgroup G) =
      (S : Subgroup (involutionCentralizer z)).map (involutionCentralizer z).subtype := by
  obtain ⟨P, hP⟩ := exists_sylow_eq_of_relative_normalizer_le
    (R := (S : Subgroup (involutionCentralizer z)).map (involutionCentralizer z).subtype)
    (H := ⊤) ⟨S, rfl⟩ le_top (by simpa only [top_inf_eq] using TypeAt.local_sylow_normalizer_le h S)
  refine ⟨P.mapSurjective (f := (⊤ : Subgroup G).subtype)
    (fun g => ⟨⟨g, mem_top g⟩, rfl⟩), ?_⟩
  exact hP

/-- The two local subgroups contain the same ambient Sylow two-subgroup of order 512. -/
theorem TypeAt.exists_common_ambient_sylow (h : TypeAt z V) :
    ∃ S : Sylow 2 G, (S : Subgroup G) ≤
      involutionCentralizer z ⊓ normalizer (V : Set G) ∧ Nat.card S = 512 := by
  obtain ⟨S, T, he, hc⟩ := h.exists_common_local_sylow
  obtain ⟨P, hP⟩ := TypeAt.local_sylow_is_ambient h S
  refine ⟨P, ?_, ?_⟩
  · rw [hP]
    exact le_inf (map_subtype_le _) (he ▸ map_subtype_le _)
  · rw [hP, card_map_of_injective (involutionCentralizer z).subtype_injective]
    exact hc

/-- The original elementary seed contains no nontrivial ambient normal subgroup. -/
theorem TypeAt.normal_subgroup_le_seed_eq_bot (h : TypeAt z V)
    (N : Subgroup G) [N.Normal] (hNV : N ≤ V) : N = ⊥ := by
  by_contra hN
  obtain ⟨x, hx, hx1⟩ := N.bot_or_exists_ne_one.resolve_left hN
  have hVN : V ≤ N := by
    intro y hy
    by_cases hy1 : y = 1
    · exact hy1 ▸ N.one_mem
    obtain ⟨g, hg⟩ := h.seed_transitive (⟨x, hNV hx⟩ : V) ⟨y, hy⟩
      (fun he => hx1 (congrArg Subtype.val he))
      (fun he => hy1 (congrArg Subtype.val he))
    have hxy := congrArg Subtype.val hg
    change (g : G) * x * (g : G)⁻¹ = y at hxy
    exact hxy ▸ (inferInstance : N.Normal).conj_mem x hx g
  have he : N = V := le_antisymm hNV hVN
  let : V.Normal := he ▸ inferInstance
  exact h.centralizer_not_le_normalizer le_normalizer_of_normal

/-- The exact local hypotheses force the ambient two-core to be trivial. -/
theorem TypeAt.ambient_twoCore_eq_bot (h : TypeAt z V) : pCore 2 G = ⊥ := by
  obtain ⟨S, hS, _⟩ := TypeAt.exists_common_ambient_sylow h
  let M := normalizer (V : Set G)
  let N := pCore 2 G
  have hNM : N ≤ M := (pCore_isPGroup.le_sylow_of_normal S).trans (hS.trans inf_le_right)
  have hNQ : N.subgroupOf M ≤ pCore 2 M :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
  have hOV : omegaOneAmbient N ≤ V := by
    apply (omegaOneAmbient_le_iff N V).mpr
    intro x hx hx2
    let xM : M := ⟨x, hNM hx⟩
    have hxQ : xM ∈ pCore 2 M := hNQ hx
    have hxO : xM ∈ (omega (pCore 2 M) (p := 2) 1).map (pCore 2 M).subtype := by
      refine ⟨⟨xM, hxQ⟩, subset_closure ?_, rfl⟩
      exact Subtype.ext (Subtype.ext hx2)
    rw [← h.seed_eq_omega_normalizer_core] at hxO
    exact hxO
  let : (omega₁ N (p := 2)).Characteristic := omega₁_characteristic _
  let : (omegaOneAmbient N).Normal := ConjAct.normal_of_characteristic_of_normal
  have hObot := TypeAt.normal_subgroup_le_seed_eq_bot h (omegaOneAmbient N) hOV
  by_contra hN
  have hNt : Nontrivial N := (nontrivial_iff_ne_bot N).mpr hN
  obtain ⟨n, hn, hc⟩ := (pCore_isPGroup (p := 2) (G := G)).nontrivial_iff_card.mp hNt
  exact omega₁_map_subtype_ne_bot N 2 (hc ▸ dvd_pow_self 2 (by omega)) hObot

/-- Each of the seven seed-involution centralizers has trivial odd core. -/
theorem TypeAt.seed_centralizer_oddCore_eq_bot (h : TypeAt z V) (x : V) (hx : x ≠ 1) :
    pPrimeCore 2 (involutionCentralizer (x : G)) = ⊥ := by
  have hz : (⟨z, h.involution_mem_seed⟩ : V) ≠ 1 := by
    intro he
    have hz1 : z = 1 := congrArg Subtype.val he
    have hh := h.involution
    rw [hz1, orderOf_one] at hh
    contradiction
  obtain ⟨g, hg⟩ := h.seed_transitive ⟨z, h.involution_mem_seed⟩ x hz hx
  have hconj : MulAut.conj (g : G) z = (x : G) := congrArg Subtype.val hg
  have hzcore := pPrimeCore_eq_bot_of_centralizer_pCore_le 2
    h.centralizer_twoCore_selfCentralizing
  have hc := pPrimeCore_eq_bot_of_equiv
    (CentralizerSmallKernelTransport.centralizerEquiv (MulAut.conj (g : G)) z).symm hzcore
  rwa [hconj] at hc

/-- The exact local hypotheses force the ambient odd core to be trivial. -/
theorem TypeAt.ambient_oddCore_eq_bot (h : TypeAt z V) : pPrimeCore 2 G = ⊥ := by
  let := h.elementary
  let N := pPrimeCore 2 G
  have hfixed (v : V) (hv : v ≠ 1) :
      N ⊓ involutionCentralizer (v : G) = ⊥ :=
    normal_coprime_inf_eq_bot N _ pPrimeCore_coprime_card
      (TypeAt.seed_centralizer_oddCore_eq_bot h v hv)
  have square (v : V) : v ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) v
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by rw [h.seed_card]; decide)
  obtain ⟨a, ha⟩ := exists_ne (1 : V)
  obtain ⟨b, hb, hba⟩ := ENat.exists_ne_ne_of_three_le (α := V)
    (by rw [ENat.card_eq_coe_natCard, h.seed_card]; norm_num) 1 a
  have hab : a * b ≠ 1 := by
    intro he
    exact hba ((eq_inv_of_mul_eq_one_right he).trans
      (inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using square a)))
  let f : V →* normalizer (N : Set G) := inclusion le_normalizer_of_normal
  apply bot_unique
  apply le_of_three_odd_centralizers N ⊥
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card) (f a) (f b)
    (by rw [← map_pow, square, map_one]) (by rw [← map_pow, square, map_one])
    ((show Commute a b from h.elementary.toIsMulCommutative.is_comm.comm a b).map f)
  intro t ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl | rfl
  · exact (hfixed a ha).le
  · exact (hfixed b hb).le
  · exact (hfixed (a * b) hab).le

end CFSG.Quasithin.HigmanSims
