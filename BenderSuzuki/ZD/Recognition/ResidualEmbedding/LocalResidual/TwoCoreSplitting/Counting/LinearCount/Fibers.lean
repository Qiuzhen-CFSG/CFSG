module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.Counting.LinearCount.FixedPoints
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.CoprimeGeneration
public import Theory.GroupTheory.OddKernelInvolutionFibers
public import Theory.GroupTheory.PPrimeCoreNormalComplement
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.Counting.LinearCount.Incidence
public import Theory.GroupTheory.SubgroupProductCard

/-!
# Section 17 swapping fibers and centralizer factorizations

For the original pair of cosets, a swapping involution v in the class of u
has displacement vt in D. Source 3.5 puts its square in the actual odd core
of D. The normal odd complement and cyclic Sylow two-subgroups make the
quotient cyclic, so the image of vt is either 1 or the image of u. Odd-kernel
fusion excludes the first possibility because D contains no distinguished
involution. It identifies the swapping fiber with the D-conjugates of tu,
and orbit–stabilizer gives the index used in the actual moved-pair count.

For the two centralizer factorizations, the intersections with their circles
have odd order. In the group obtained by adjoining t, the conjugates of t
have the same image modulo the odd intersection. Kernel fusion supplies a
conjugator in that intersection; the remaining factor centralizes t. All
normality is relative to these local subgroups. The finite set-product
formula then gives both common-centralizer indices and the rational ratio
identity for the same explicit `TwoCoreLocalData`.

The fusion u ~ tu and the earlier local normal-complement/cyclic-Sylow
hypothesis remain explicit. No model or counting value is assumed here.
Existence of the local data and final Section 17 assembly remain upstream.

Source: GLS4, Chapter 2, proof of Lemma 17.1 and the opening Frattini
argument in Lemma 17.2 (`refs/KGroup/GLS4/Chapter2.tex`).
-/

noncomputable section
namespace BenderSuzuki.ZD.Section17
open Subgroup PFAppendixIII Theory.GroupTheory PFchapter1section1
open scoped Pointwise commutatorElement
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

private theorem cyclic_oddCore_quotient {D : Type*} [Group D] [Finite D]
    (hcomp : HasNormalPComplement 2 D) (hcyc : ∀ S : Sylow 2 D, IsCyclic S) :
    IsCyclic (D ⧸ pPrimeCore 2 D) := by
  let q := QuotientGroup.mk' (pPrimeCore 2 D)
  let S : Sylow 2 D := Classical.choice inferInstance
  let : IsCyclic S := hcyc S
  let T := S.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 2 D))
  have hQ := isPGroup_quotient_pPrimeCore_of_hasNormalPComplement 2 D hcomp
  have hT : (T : Subgroup (D ⧸ pPrimeCore 2 D)) = ⊤ :=
    (T.is_maximal' (hQ.to_subgroup ⊤) le_top).symm
  apply isCyclic_of_surjective (q.comp (S : Subgroup D).subtype)
  intro y
  have hy : y ∈ (S : Subgroup D).map q := hT.ge (mem_top y)
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨⟨x, hx⟩, rfl⟩

private theorem odd_coset_fusion (N : Subgroup G) (hodd : Odd (Nat.card N))
    {a b : G} (ha : PFAppendixIII.IsInvolution a) (hb : PFAppendixIII.IsInvolution b)
    (haN : a ∈ normalizer (N : Set G)) (hab : a * b⁻¹ ∈ N) :
    ∃ c : N, (c : G) * a * (c : G)⁻¹ = b := by
  let H := N ⊔ zpowers a
  have hNH : N ≤ H := le_sup_left
  have hHnorm : H ≤ normalizer (N : Set G) :=
    sup_le N.le_normalizer (zpowers_le.mpr haN)
  let O := N.subgroupOf H
  let : O.Normal := normal_subgroupOf_of_le_normalizer hHnorm
  let f := QuotientGroup.mk' O
  have hkernel : Nat.Coprime 2 (Nat.card f.ker) := by
    rw [QuotientGroup.ker_mk', Nat.card_congr (subgroupOfEquivOfLe hNH).toEquiv]
    exact hodd.coprime_two_left
  have haH : a ∈ H := (show zpowers a ≤ H from le_sup_right) (mem_zpowers a)
  have hbH : b ∈ H := by
    have hh := H.mul_mem (H.inv_mem (hNH hab)) haH
    simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using hh
  obtain ⟨c, hc⟩ := involutions_same_image_conj_ker f hkernel
    (a := ⟨a, haH⟩) (b := ⟨b, hbH⟩)
    (by rw [Subgroup.orderOf_mk]; exact orderOf_eq_prime ha.sq_eq_one ha.ne_one)
    (by rw [Subgroup.orderOf_mk]; exact orderOf_eq_prime hb.sq_eq_one hb.ne_one)
    (QuotientGroup.eq_iff_div_mem.mpr (by change a / b ∈ N; simpa only [div_eq_mul_inv] using hab))
  have hcN : ((c : H) : G) ∈ N := by
    exact (QuotientGroup.eq_one_iff (c : H)).mp c.property
  exact ⟨⟨c, hcN⟩, congrArg Subtype.val hc⟩

omit [Finite G] in
private theorem pair_eq_stabilizers (h : IsProductDisconnected Z M)
    (d : TwoCoreLocalData Z M) :
    residualPairStabilizer M d.t =
      MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M) ⊓
        MulAction.stabilizer G (d.t • (QuotientGroup.mk 1 : G ⧸ M)) := by
  have he := rightConjugate_stabilizer (QuotientGroup.mk 1 : G ⧸ M) d.t
  rw [(h.involutions d.t d.t_mem).inv_eq_self, MulAction.stabilizer_quotient] at he
  rw [residualPairStabilizer, he, MulAction.stabilizer_quotient]

private theorem swapping_odd_coset (h : IsProductDisconnected Z M)
    (d : TwoCoreLocalData Z M)
    (hcomp : HasNormalPComplement 2 (residualPairStabilizer M d.t))
    (hcyc : ∀ S : Sylow 2 (residualPairStabilizer M d.t), IsCyclic S)
    {v : G} (hv : IsConj ((d.u : M) : G) v)
    (hswap : v • (QuotientGroup.mk 1 : G ⧸ M) =
      d.t • (QuotientGroup.mk 1 : G ⧸ M)) :
    (d.t * ((d.u : M) : G)) * v⁻¹ ∈ residualOddCore M d.t := by
  let D := residualPairStabilizer M d.t
  let O := pPrimeCore 2 D
  let q := QuotientGroup.mk' O
  let u : D := ⟨((d.u : M) : G), d.u.property⟩
  have hu : orderOf u = 2 := by
    rw [← Subgroup.orderOf_coe u]
    change orderOf ((d.u : M) : G) = 2
    simpa only [Subgroup.orderOf_coe] using d.u_order
  have huG : orderOf ((d.u : M) : G) = 2 := by simpa only [Subgroup.orderOf_coe] using d.u_order
  have hvG : orderOf v = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hv
    change MulAut.conj g ((d.u : M) : G) = v at hg
    rw [← hg, MulEquiv.orderOf_eq, huG]
  have ht := h.involutions d.t d.t_mem
  have hvI : PFAppendixIII.IsInvolution v := ⟨(orderOf_eq_prime_iff.mp hvG).2, (orderOf_eq_prime_iff.mp hvG).1⟩
  have tt : d.t * d.t = 1 := by simpa only [pow_two] using ht.sq_eq_one
  have vv : v * v = 1 := by simpa only [pow_two] using hvI.sq_eq_one
  let a : G ⧸ M := QuotientGroup.mk 1
  let b := d.t • a
  have hvb : v • b = a := by
    change v • (d.t • a) = a
    rw [← hswap, ← mul_smul, vv, one_smul]
  have htb : d.t • b = a := by rw [← mul_smul, tt, one_smul]
  have hxD : v * d.t ∈ D := by
    rw [show D = _ from pair_eq_stabilizers h d]
    exact ⟨by change (v * d.t) • a = a; rw [mul_smul]; exact hvb,
      by change (v * d.t) • b = b; rw [mul_smul, htb]; exact hswap⟩
  let x : D := ⟨v * d.t, hxD⟩
  have hxx : (v * d.t) ^ 2 ∈ residualOddCore M d.t := by
    have hh := residualPair_commutator_le_oddCore h d.t_mem d.t_not_mem
      (commutator_mem_commutator hxD (mem_zpowers d.t))
    have he : ⁅v * d.t, d.t⁆ = (v * d.t) ^ 2 := by
      calc
        ⁅v * d.t, d.t⁆ = v * d.t * v⁻¹ * d.t⁻¹ := by
          simp only [commutatorElement_def]
          group
        _ = (v * d.t) ^ 2 := by rw [ht.inv_eq_self, hvI.inv_eq_self, pow_two]; group
    rwa [he] at hh
  have hxO : x ^ 2 ∈ O := by
    obtain ⟨y, hy, he⟩ := hxx
    exact (Subtype.ext he : y = x ^ 2) ▸ hy
  have hqx : q x ^ 2 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hxO
  let : IsCyclic (D ⧸ O) := cyclic_oddCore_quotient hcomp hcyc
  have hqune : q u ≠ 1 := by
    intro he
    have huO := (QuotientGroup.eq_one_iff u).mp he
    have hd := O.orderOf_dvd_natCard huO
    rw [hu] at hd
    exact (Nat.prime_two.coprime_iff_not_dvd.mp (pPrimeCore_coprime_card (p := 2) (G := D))) hd
  have hqu : orderOf (q u) = 2 := orderOf_eq_prime
    (by rw [← map_pow, show u ^ 2 = 1 by rw [← hu]; exact pow_orderOf_eq_one u, map_one]) hqune
  have hcases : q x = 1 ∨ q x = q u := by
    by_cases he : q x = 1
    · exact Or.inl he
    · exact Or.inr (IsCyclic.eq_of_orderOf_eq_two (orderOf_eq_prime hqx he) hqu)
  rcases hcases with hxone | hxu
  · have hxN : v * d.t ∈ residualOddCore M d.t :=
      mem_map_of_mem D.subtype ((QuotientGroup.eq_one_iff x).mp hxone)
    have htv : d.t * v⁻¹ ∈ residualOddCore M d.t := by
      simpa only [mul_inv_rev, ht.inv_eq_self] using (residualOddCore M d.t).inv_mem hxN
    obtain ⟨c, hc⟩ := odd_coset_fusion (residualOddCore M d.t) residualOddCore_odd ht hvI
      (pair_sup_zpowers_le_normalizer_residualOddCore ht ((show zpowers d.t ≤ residualPairStabilizer M d.t ⊔ zpowers d.t from le_sup_right) (mem_zpowers d.t))) htv
    have hvZ : v ∈ Z := hc ▸ h.invariant (c : G) d.t d.t_mem
    obtain ⟨g, hg⟩ := isConj_iff.mp hv.symm
    exact (not_mem_Z_of_mem_residualPairStabilizer h d.t_not_mem d.u.property
      (by
        have hh := h.invariant g v hvZ
        change g * v * g⁻¹ ∈ Z at hh
        rw [hg] at hh
        exact hh)).elim
  · have hxuO : x * u⁻¹ ∈ O := by
      simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp hxu
    have hxN : (v * d.t) * ((d.u : M) : G)⁻¹ ∈ residualOddCore M d.t :=
      mem_map_of_mem D.subtype hxuO
    have hh := (residualOddCore M d.t).inv_mem hxN
    simpa only [mul_inv_rev, inv_inv, ht.inv_eq_self, mul_assoc,
      d.commutes_t.eq] using hh

/-- The literal swapping fiber Π is the conjugacy orbit of tu under the
actual two-point stabilizer D. Its forward inclusion is proved by fusion
through the odd core, retaining a conjugator in that core. -/
public theorem swapping_fiber_eq_conjugates (h : IsProductDisconnected Z M)
    (d : TwoCoreLocalData Z M)
    (hlocal : ∀ Y : Subgroup G, closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S)
    (hfusion : IsConj ((d.u : M) : G) (d.t * ((d.u : M) : G))) :
    {v : G | IsConj ((d.u : M) : G) v ∧
      v • (QuotientGroup.mk 1 : G ⧸ M) = d.t • (QuotientGroup.mk 1 : G ⧸ M)} =
    {v : G | ∃ g : residualPairStabilizer M d.t,
      (g : G) * (d.t * ((d.u : M) : G)) * (g : G)⁻¹ = v} := by
  let D := residualPairStabilizer M d.t
  let O := residualOddCore M d.t
  let w := d.t * ((d.u : M) : G)
  have ht := h.involutions d.t d.t_mem
  have hw : PFAppendixIII.IsInvolution w := by
    have ho : orderOf w = 2 := by
      obtain ⟨g, hg⟩ := isConj_iff.mp hfusion
      change MulAut.conj g ((d.u : M) : G) = w at hg
      rw [← hg, MulEquiv.orderOf_eq]
      simpa only [Subgroup.orderOf_coe] using d.u_order
    exact ⟨(orderOf_eq_prime_iff.mp ho).2, (orderOf_eq_prime_iff.mp ho).1⟩
  ext v
  constructor
  · rintro ⟨hv, hswap⟩
    have ho : orderOf v = 2 := by
      obtain ⟨g, hg⟩ := isConj_iff.mp hv
      change MulAut.conj g ((d.u : M) : G) = v at hg
      rw [← hg, MulEquiv.orderOf_eq]
      simpa only [Subgroup.orderOf_coe] using d.u_order
    have hvI : PFAppendixIII.IsInvolution v :=
      ⟨(orderOf_eq_prime_iff.mp ho).2, (orderOf_eq_prime_iff.mp ho).1⟩
    obtain ⟨hcomp, hcyc⟩ := hlocal D (residualPairStabilizer_localClosure_eq_bot h d.t_not_mem)
    have hwO : w ∈ normalizer (O : Set G) :=
      pair_sup_zpowers_le_normalizer_residualOddCore ht
        ((D ⊔ zpowers d.t).mul_mem
          ((show zpowers d.t ≤ D ⊔ zpowers d.t from le_sup_right) (mem_zpowers d.t))
          ((show D ≤ D ⊔ zpowers d.t from le_sup_left) d.u.property))
    obtain ⟨c, hc⟩ := odd_coset_fusion O residualOddCore_odd hw hvI hwO
      (swapping_odd_coset h d hcomp hcyc hv hswap)
    exact ⟨⟨c, residualOddCore_le_pair c.property⟩, hc⟩
  · rintro ⟨g, rfl⟩
    refine ⟨hfusion.trans (isConj_iff.mpr ⟨g, rfl⟩), ?_⟩
    have hg : (g : G) ∈ D := g.property
    have hgi := D.inv_mem g.property
    rw [show D = _ from pair_eq_stabilizers h d] at hg hgi
    have hga : (g : G)⁻¹ • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk 1 := hgi.1
    have hgb : (g : G) • (d.t • (QuotientGroup.mk 1 : G ⧸ M)) =
      d.t • (QuotientGroup.mk 1 : G ⧸ M) := hg.2
    rw [mul_smul, mul_smul, hga, (twisted_involution_swaps h d).1, hgb]

/-- Orbit–stabilizer for Π, with centralizer index taken inside D. -/
public theorem swapping_fiber_card (h : IsProductDisconnected Z M)
    (d : TwoCoreLocalData Z M)
    (hlocal : ∀ Y : Subgroup G, closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S)
    (hfusion : IsConj ((d.u : M) : G) (d.t * ((d.u : M) : G))) :
    Nat.card {v : G // IsConj ((d.u : M) : G) v ∧
      v • (QuotientGroup.mk 1 : G ⧸ M) = d.t • (QuotientGroup.mk 1 : G ⧸ M)} =
    (centralizer ({d.t * ((d.u : M) : G)} : Set G)).relIndex
      (residualPairStabilizer M d.t) := by
  let D := residualPairStabilizer M d.t
  let w := d.t * ((d.u : M) : G)
  let : MulAction D G := MulAction.compHom G
    (ConjAct.toConjAct.toMonoidHom.comp D.subtype)
  have hstab : MulAction.stabilizer D w = (centralizer ({w} : Set G)).subgroupOf D := by
    ext g
    change (g : G) * w * (g : G)⁻¹ = w ↔ _
    rw [mul_inv_eq_iff_eq_mul]
    exact mem_centralizer_singleton_iff.symm
  have he := swapping_fiber_eq_conjugates h d hlocal hfusion
  change {v : G | IsConj ((d.u : M) : G) v ∧
    v • (QuotientGroup.mk 1 : G ⧸ M) = d.t • (QuotientGroup.mk 1 : G ⧸ M)} =
    MulAction.orbit D w at he
  calc
    _ = Nat.card (MulAction.orbit D w) := Nat.card_congr (Equiv.setCongr he)
    _ = (MulAction.stabilizer D w).index :=
      Nat.card_congr (MulAction.orbitEquivQuotientStabilizer D w)
    _ = _ := congrArg Subgroup.index hstab

/-- The same cardinality for the nested subtype appearing in the Δ count. -/
public theorem swapping_nested_fiber_card (h : IsProductDisconnected Z M)
    (d : TwoCoreLocalData Z M)
    (hlocal : ∀ Y : Subgroup G, closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S)
    (hfusion : IsConj ((d.u : M) : G) (d.t * ((d.u : M) : G))) :
    Nat.card {v : {v : G // IsConj ((d.u : M) : G) v} //
      v.val • (QuotientGroup.mk 1 : G ⧸ M) = d.t • (QuotientGroup.mk 1 : G ⧸ M)} =
    (centralizer ({d.t * ((d.u : M) : G)} : Set G)).relIndex
      (residualPairStabilizer M d.t) := by
  calc
    _ = Nat.card {v : G // IsConj ((d.u : M) : G) v ∧
        v • (QuotientGroup.mk 1 : G ⧸ M) = d.t • (QuotientGroup.mk 1 : G ⧸ M)} :=
      Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter _ _)
    _ = _ := swapping_fiber_card h d hlocal hfusion

/-- Source (17E): apply the swapping-fiber calculation to the actual
incidence identity of Lemma 17.1. -/
public theorem moved_pair_count_at_centralizer_index (h : IsProductDisconnected Z M)
    (ha : ResidualAction Z M) (d : TwoCoreLocalData Z M)
    (hlocal : ∀ Y : Subgroup G, closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S)
    (hfusion : IsConj ((d.u : M) : G) (d.t * ((d.u : M) : G))) :
    Nat.card {v : G // IsConj ((d.u : M) : G) v} *
      (Nat.card (G ⧸ M) - Nat.card {beta : G ⧸ M // ((d.u : M) : G) • beta = beta}) =
    (Nat.card (G ⧸ M) * (Nat.card (G ⧸ M) - 1)) *
      (centralizer ({d.t * ((d.u : M) : G)} : Set G)).relIndex
        (residualPairStabilizer M d.t) := by
  have hh := moved_pair_count h ha d
  rwa [swapping_nested_fiber_card h d hlocal hfusion] at hh

omit [Finite G] in
private theorem circle_normalized (h : IsProductDisconnected Z M) (v : G) :
    centralizer ({v} : Set G) ≤ normalizer (centralizerClosure Z v : Set G) := by
  apply le_normalizer_closure_iff.mpr
  intro g hg x hx
  exact subset_closure ⟨h.invariant g x hx.1,
    (centralizer ({v} : Set G)).mul_mem
      ((centralizer ({v} : Set G)).mul_mem hg hx.2)
      ((centralizer ({v} : Set G)).inv_mem hg)⟩

private theorem circle_involution_distinguished (h : IsProductDisconnected Z M)
    (r : SimpleReduction Z M) (d : TwoCoreLocalData Z M)
    {x : G} (hx : x ∈ centralizerClosure Z ((d.u : M) : G))
    (hxi : PFAppendixIII.IsInvolution x) : x ∈ Z := by
  let u : G := ((d.u : M) : G)
  have hu : PFAppendixIII.IsInvolution u := by
    have ho : orderOf u = 2 := by simpa only [u, Subgroup.orderOf_coe] using d.u_order
    exact ⟨(orderOf_eq_prime_iff.mp ho).2, (orderOf_eq_prime_iff.mp ho).1⟩
  rw [centralizerClosure_eq_map] at hx
  obtain ⟨y0, hy0, hyx⟩ := hx
  let y : localCircle Z (centralizer ({u} : Set G)) := ⟨y0, hy0⟩
  have he : localCircleHom Z (centralizer ({u} : Set G)) y = x := hyx
  rw [← he]
  apply localCircle_involution_mem h r _ (r.involution_centralizer_ne_top h hu)
    (fun hle => d.t_not_mem (hle (mem_centralizer_singleton_iff.mpr d.commutes_t.symm.eq)))
    ⟨d.z, d.z_mem, mem_centralizer_singleton_iff.mpr d.commutes_z.symm.eq, d.z.property⟩
  refine ⟨?_, ?_⟩
  · intro hy
    apply hxi.ne_one
    have h := he
    rw [hy, map_one] at h
    exact h.symm
  · apply localCircleHom_injective Z (centralizer ({u} : Set G))
    rw [map_pow, he, hxi.sq_eq_one, map_one]

private theorem pair_circle_odd (h : IsProductDisconnected Z M)
    (r : SimpleReduction Z M) (d : TwoCoreLocalData Z M) :
    Odd (Nat.card (residualPairStabilizer M d.t ⊓
      centralizerClosure Z ((d.u : M) : G) : Subgroup G)) := by
  apply Nat.not_even_iff_odd.mp
  intro he
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 he.two_dvd
  have hxi : PFAppendixIII.IsInvolution (x : G) := by
    have ho : orderOf (x : G) = 2 := by simpa only [Subgroup.orderOf_coe] using hx
    exact ⟨(orderOf_eq_prime_iff.mp ho).2, (orderOf_eq_prime_iff.mp ho).1⟩
  exact not_mem_Z_of_mem_residualPairStabilizer h d.t_not_mem x.property.1
    (circle_involution_distinguished h r d x.property.2 hxi)

-- In the subgroup generated by E and t, the intersection with B has odd
-- kernel E ∩ B and quotient of order at most two. Kernel fusion is the
-- order-two Frattini argument, with its conjugator retained in E ∩ B.
private theorem odd_intersection_factorization
    (E B : Subgroup G) (t : G) (ht : PFAppendixIII.IsInvolution t)
    (htE : t ∈ normalizer (E : Set G)) (htB : t ∈ B)
    (hEB : E ≤ normalizer (B : Set G))
    (hodd : Odd (Nat.card (E ⊓ B : Subgroup G))) :
    (E : Set G) = (E ⊓ B : Subgroup G) * (E ⊓ centralizer ({t} : Set G) : Subgroup G) := by
  let H := E ⊔ zpowers t
  let N := H ⊓ B
  let O := (E ⊓ B).subgroupOf N
  have hHN : H ≤ normalizer (E : Set G) := sup_le E.le_normalizer (zpowers_le.mpr htE)
  have hNO : N ≤ normalizer ((E ⊓ B : Subgroup G) : Set G) :=
    (le_inf (inf_le_left.trans hHN) (inf_le_right.trans B.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  let : O.Normal := normal_subgroupOf_of_le_normalizer hNO
  have hON : E ⊓ B ≤ N := inf_le_inf le_sup_left le_rfl
  have hOodd : Odd (Nat.card O) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hON).toEquiv]
    exact hodd
  let f := QuotientGroup.mk' O
  have hker : Nat.Coprime 2 (Nat.card f.ker) := by
    rw [QuotientGroup.ker_mk']
    exact hOodd.coprime_two_left
  have htN : t ∈ N := ⟨(show zpowers t ≤ H from le_sup_right) (mem_zpowers t), htB⟩
  apply Set.Subset.antisymm
  · intro x hx
    have hsN : x * t * x⁻¹ ∈ N :=
      ⟨H.mul_mem (H.mul_mem ((show E ≤ H from le_sup_left) hx) htN.1) (H.inv_mem ((show E ≤ H from le_sup_left) hx)),
        (mem_normalizer_iff.mp (hEB hx) t).mp htB⟩
    let a : N := ⟨t, htN⟩
    let b : N := ⟨x * t * x⁻¹, hsN⟩
    have ha : orderOf a = 2 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime ht.sq_eq_one ht.ne_one
    have hb : orderOf b = 2 := by
      rw [Subgroup.orderOf_mk]
      exact ((MulAut.conj x).orderOf_eq t).trans (orderOf_eq_prime ht.sq_eq_one ht.ne_one)
    have hab : f a = f b := by
      apply (QuotientGroup.eq_iff_div_mem).mpr
      simp only [div_eq_mul_inv]
      change t * (x * t * x⁻¹)⁻¹ ∈ E ⊓ B
      constructor
      · have hconj := (mem_normalizer_iff.mp htE x).mp hx
        have he : t * (x * t * x⁻¹)⁻¹ = (t * x * t⁻¹) * x⁻¹ := by group
        rw [he]
        exact E.mul_mem hconj (E.inv_mem hx)
      · exact B.mul_mem htB (B.inv_mem hsN.2)
    obtain ⟨c, hc⟩ := involutions_same_image_conj_ker f hker ha hb hab
    have hcO : ((c : N) : G) ∈ E ⊓ B := by
      exact (QuotientGroup.eq_one_iff (c : N)).mp c.property
    have hcG : ((c : N) : G) * t * ((c : N) : G)⁻¹ = x * t * x⁻¹ :=
      congrArg Subtype.val hc
    refine ⟨c, hcO, ((c : N) : G)⁻¹ * x, ⟨E.mul_mem (E.inv_mem hcO.1) hx, ?_⟩, ?_⟩
    · apply mem_centralizer_singleton_iff.mpr
      calc
        _ = ((c : N) : G)⁻¹ * (x * t * x⁻¹) * x := by group
        _ = t * (((c : N) : G)⁻¹ * x) := by rw [← hcG]; group
    · exact mul_inv_cancel_left _ _
  · rintro x ⟨a, ha, b, hb, rfl⟩
    exact E.mul_mem ha.1 hb.1

private theorem pair_circle_factorization (h : IsProductDisconnected Z M)
    (d : TwoCoreLocalData Z M) (w : G) (htw : Commute d.t w)
    (hodd : Odd (Nat.card (residualPairStabilizer M d.t ⊓
      centralizerClosure Z w : Subgroup G))) :
    ((residualPairStabilizer M d.t ⊓ centralizer ({w} : Set G) : Subgroup G) : Set G) =
      (residualPairStabilizer M d.t ⊓ centralizerClosure Z w : Subgroup G) *
        (residualPairStabilizer M d.t ⊓ centralizer ({w} : Set G) ⊓
          centralizer ({d.t} : Set G) : Subgroup G) := by
  let D := residualPairStabilizer M d.t
  let B := centralizerClosure Z w
  let E := D ⊓ centralizer ({w} : Set G)
  have he : E ⊓ B = D ⊓ B := by
    rw [inf_assoc, inf_of_le_right (centralizerClosure_le Z w)]
  have htE : d.t ∈ normalizer (E : Set G) :=
    inf_normalizer_le_normalizer_inf
      ⟨involution_mem_normalizer_residualPairStabilizer (h.involutions d.t d.t_mem),
        (centralizer ({w} : Set G)).le_normalizer (mem_centralizer_singleton_iff.mpr htw.eq)⟩
  have hh := odd_intersection_factorization E B d.t (h.involutions d.t d.t_mem)
    htE (mem_centralizerClosure d.t_mem htw)
    (inf_le_right.trans (circle_normalized h w)) (he.symm ▸ hodd)
  simpa only [he] using hh

/-- The first Frattini set-product identity in Lemma 17.2, inside C_D(u).
The odd circle intersection is proved from local strong embedding. -/
public theorem centralizer_u_factorization (h : IsProductDisconnected Z M)
    (r : SimpleReduction Z M) (d : TwoCoreLocalData Z M) :
    ((residualPairStabilizer M d.t ⊓ centralizer ({((d.u : M) : G)} : Set G) : Subgroup G) : Set G) =
      (residualPairStabilizer M d.t ⊓ centralizerClosure Z ((d.u : M) : G) : Subgroup G) *
        (residualPairStabilizer M d.t ⊓ centralizer ({((d.u : M) : G)} : Set G) ⊓
          centralizer ({d.t} : Set G) : Subgroup G) :=
  pair_circle_factorization h d _ d.commutes_t.symm (pair_circle_odd h r d)

omit [Finite G] in
/-- Centralizing t and tu is equivalent to centralizing t and u.
Both centralizer factorizations therefore use exactly the same subgroup. -/
public theorem common_centralizer_eq (d : TwoCoreLocalData Z M) :
    residualPairStabilizer M d.t ⊓ centralizer ({d.t * ((d.u : M) : G)} : Set G) ⊓
      centralizer ({d.t} : Set G) =
    residualPairStabilizer M d.t ⊓ centralizer ({((d.u : M) : G)} : Set G) ⊓
      centralizer ({d.t} : Set G) := by
  ext x
  simp only [mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨⟨hxD, hxw⟩, hxt⟩
    refine ⟨⟨hxD, ?_⟩, hxt⟩
    apply mul_left_cancel (a := d.t)
    calc
      d.t * (x * ((d.u : M) : G)) = x * (d.t * ((d.u : M) : G)) := by rw [← mul_assoc, ← hxt, mul_assoc]
      _ = d.t * (((d.u : M) : G) * x) := by rw [hxw, mul_assoc]
  · rintro ⟨⟨hxD, hxu⟩, hxt⟩
    exact ⟨⟨hxD, (show Commute x d.t from hxt).mul_right (show Commute x ((d.u : M) : G) from hxu)⟩, hxt⟩

/-- The second Frattini set-product identity in Lemma 17.2, inside C_D(tu),
using the actual D₀ = D ∩ C_G(tu)° of the supplied local data. -/
public theorem centralizer_twisted_factorization (h : IsProductDisconnected Z M)
    (d : TwoCoreLocalData Z M) :
    ((residualPairStabilizer M d.t ⊓ centralizer ({d.t * ((d.u : M) : G)} : Set G) : Subgroup G) : Set G) =
      (residualPairStabilizer M d.t ⊓ centralizerClosure Z (d.t * ((d.u : M) : G)) : Subgroup G) *
        (residualPairStabilizer M d.t ⊓ centralizer ({((d.u : M) : G)} : Set G) ⊓
          centralizer ({d.t} : Set G) : Subgroup G) := by
  have hh := pair_circle_factorization h d _
    ((Commute.refl d.t).mul_right d.commutes_t.symm) d.odd_twisted_pair
  rwa [common_centralizer_eq d] at hh

omit [Finite G] in
private theorem card_inf_mul_relIndex (A C : Subgroup G) :
    Nat.card (A ⊓ C : Subgroup G) * C.relIndex A = Nat.card A := by
  have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (A ⊓ C) A bot_le inf_le_left
  simpa only [relIndex_bot_left, inf_relIndex_left] using hh

private theorem factor_card_index (E A C : Subgroup G)
    (hf : (E : Set G) = (A : Set G) * (C : Set G)) :
    Nat.card C * C.relIndex A = Nat.card E := by
  have hp := card_set_mul_mul_card_inf A C
  rw [← hf] at hp
  have ha := card_inf_mul_relIndex A C
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := (A ⊓ C : Subgroup G)))
  calc
    Nat.card (A ⊓ C : Subgroup G) * (Nat.card C * C.relIndex A) =
      (Nat.card (A ⊓ C : Subgroup G) * C.relIndex A) * Nat.card C := by ac_rfl
    _ = Nat.card A * Nat.card C := by rw [ha]
    _ = Nat.card E * Nat.card (A ⊓ C : Subgroup G) := hp.symm
    _ = Nat.card (A ⊓ C : Subgroup G) * Nat.card E := Nat.mul_comm _ _

private theorem factor_relIndex (E A C : Subgroup G) (hCE : C ≤ E)
    (hf : (E : Set G) = (A : Set G) * (C : Set G)) :
    C.relIndex E = C.relIndex A := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := C))
  have hh := card_inf_mul_relIndex E C
  rw [inf_of_le_right hCE] at hh
  exact hh.trans (factor_card_index E A C hf).symm

private theorem factor_centralizer_index (D A : Subgroup G) (w t : G)
    (hA : A ≤ D ⊓ centralizer ({w} : Set G))
    (hf : ((D ⊓ centralizer ({w} : Set G) : Subgroup G) : Set G) =
      (A : Set G) * (D ⊓ centralizer ({w} : Set G) ⊓
        centralizer ({t} : Set G) : Subgroup G)) :
    (D ⊓ centralizer ({w} : Set G) ⊓ centralizer ({t} : Set G)).relIndex
        (D ⊓ centralizer ({w} : Set G)) =
      (centralizer ({t} : Set G)).relIndex A := by
  rw [factor_relIndex _ _ _ inf_le_left hf]
  rw [← inf_relIndex_left A, ← inf_assoc, inf_of_le_left hA, inf_relIndex_left]

/-- The first set-product identity identifies the common-centralizer
index with the index of C_(D ∩ B°)(t) in D ∩ B°. -/
public theorem centralizer_u_common_index (h : IsProductDisconnected Z M)
    (r : SimpleReduction Z M) (d : TwoCoreLocalData Z M) :
    (residualPairStabilizer M d.t ⊓ centralizer ({((d.u : M) : G)} : Set G) ⊓
      centralizer ({d.t} : Set G)).relIndex
      (residualPairStabilizer M d.t ⊓ centralizer ({((d.u : M) : G)} : Set G)) =
    (centralizer ({d.t} : Set G)).relIndex
      (residualPairStabilizer M d.t ⊓ centralizerClosure Z ((d.u : M) : G)) := by
  exact factor_centralizer_index _ _ _ _ (inf_le_inf le_rfl (centralizerClosure_le Z _))
    (centralizer_u_factorization h r d)

/-- Source 17.2(c)'s index equality: c is the index of C_D₀(t) in D₀. -/
public theorem centralizer_twisted_common_index (h : IsProductDisconnected Z M)
    (d : TwoCoreLocalData Z M) :
    (residualPairStabilizer M d.t ⊓ centralizer ({((d.u : M) : G)} : Set G) ⊓
      centralizer ({d.t} : Set G)).relIndex
      (residualPairStabilizer M d.t ⊓ centralizer ({d.t * ((d.u : M) : G)} : Set G)) =
    (centralizer ({d.t} : Set G)).relIndex
      (residualPairStabilizer M d.t ⊓ centralizerClosure Z (d.t * ((d.u : M) : G))) := by
  have hf := centralizer_twisted_factorization h d
  rw [← common_centralizer_eq d] at hf ⊢
  exact factor_centralizer_index _ _ _ _ (inf_le_inf le_rfl (centralizerClosure_le Z _)) hf

/-- The source rational identity a c = |D ∩ B° : C_(D ∩ B°)(t)|,
with both factors evaluated on the original local data. This precedes the
model-specific evaluation of the right side as q − 1. -/
public theorem centralizerRatio_mul_twisted_index (h : IsProductDisconnected Z M)
    (r : SimpleReduction Z M) (d : TwoCoreLocalData Z M) :
    centralizerRatio d *
        ((centralizer ({d.t} : Set G)).relIndex
          (residualPairStabilizer M d.t ⊓
            centralizerClosure Z (d.t * ((d.u : M) : G))) : ℚ) =
      ((centralizer ({d.t} : Set G)).relIndex
        (residualPairStabilizer M d.t ⊓ centralizerClosure Z ((d.u : M) : G)) : ℚ) := by
  let D := residualPairStabilizer M d.t
  let E := D ⊓ centralizer ({((d.u : M) : G)} : Set G)
  let F := D ⊓ centralizer ({d.t * ((d.u : M) : G)} : Set G)
  let C := E ⊓ centralizer ({d.t} : Set G)
  have hCE : E ⊓ C = C := inf_of_le_right inf_le_left
  have hCF : F ⊓ C = C := inf_of_le_right (by
    rw [show C = _ from (common_centralizer_eq d).symm]
    exact inf_le_left)
  have he := card_inf_mul_relIndex E C
  have hf := card_inf_mul_relIndex F C
  rw [hCE, centralizer_u_common_index h r d] at he
  rw [hCF, centralizer_twisted_common_index h d] at hf
  unfold centralizerRatio
  rw [div_mul_eq_mul_div]
  apply (div_eq_iff (show (Nat.card F : ℚ) ≠ 0 from
    Nat.cast_ne_zero.mpr Nat.card_pos.ne')).mpr
  exact_mod_cast (show Nat.card E *
      (centralizer ({d.t} : Set G)).relIndex
        (D ⊓ centralizerClosure Z (d.t * ((d.u : M) : G))) =
      (centralizer ({d.t} : Set G)).relIndex
        (D ⊓ centralizerClosure Z ((d.u : M) : G)) * Nat.card F from by
    rw [← he, ← hf]
    dsimp only [D]
    ac_rfl)

end BenderSuzuki.ZD.Section17
