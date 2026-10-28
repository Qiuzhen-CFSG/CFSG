module


public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.Freeness.TorusFixedPoints.Contracts
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.Freeness.TorusFixedPoints.Reduction
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.EmbeddingNormalizers.OddNormalizer
public import Theory.GroupTheory.CyclicSubgroupNormalizer
public import Theory.GroupTheory.PGroup.NormalPrimeImage
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupAction.AbelianCoprimeFullFixedGeneration

/-!
# The two branches of prime torus weak closure

The cyclic normal torus makes its prime-order subgroup central in P.
For y = g⁻¹*x*g, conjugate C_P(y) into P inside C_G(x). When K ∩ P
centralizes y, (12G) makes the adjusted conjugator preserve the two
marked cosets, hence the torus and its prime line.

In the other branch, x and y generate an elementary plane of order p².
A plane whose nonidentity elements fuse into K
acts on the actual normal distinguished closure A = ⟨Z ∩ M⟩. Equation
(12F) makes every nonidentity actor fixed-point-free on A. Coprime
fixed-point generation forces A = 1, contradicting the chosen z.

The conditional assembly retains exactly the cyclic-extension
line-orbit statement. Its independent producer must discharge that
premise before claiming (12H). The last theorem applies the assembly
to the literal fixed-coset consumer in TorusFixedPoints.Reduction.

Source: GLS4, Chapter 2, Proposition 12.13, equations (12F)--(12H),
`refs/KGroup/GLS4/Chapter2.tex`, lines 2290--2320.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d

/-- Every subgroup of the torus is preserved by its ambient normalizer. -/
public theorem Context.torus_line_normalizer
    {x : G} (hx : x ∈ residualCommutator M t) :
    normalizer (residualCommutator M t : Set G) ≤ normalizer (zpowers x : Set G) := by
  let : IsCyclic (residualCommutator M t) := d.torus_structure.2.1
  exact normalizer_le_normalizer_of_le_cyclic _ _ (zpowers_le.mpr hx)

/-- A prime torus element is central in the supplied ambient Sylow subgroup. -/
public theorem Context.torus_prime_centralizes_sylow
    {x : G} (hx : x ∈ residualCommutator M t) {p : ℕ} (hp : p.Prime)
    (hxorder : orderOf x = p) (S : TorusSylowData M t x p) :
    (S.P : Subgroup G) ≤ centralizer ({x} : Set G) := by
  let : Fact p.Prime := ⟨hp⟩
  have hPQ : (S.P : Subgroup G) ≤ normalizer (zpowers x : Set G) :=
    S.le_pair.trans ((d.pair_normalizes_torus).trans (d.torus_line_normalizer hx))
  let Q := (zpowers x).subgroupOf (S.P : Subgroup G)
  let : Q.Normal := normal_subgroupOf_of_le_normalizer hPQ
  have hQP : zpowers x ≤ (S.P : Subgroup G) := zpowers_le.mpr S.mem
  have hQcard : Nat.card Q = p := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hQP).toEquiv, Nat.card_zpowers, hxorder]
  have hQZ := S.P.isPGroup'.normal_le_center_of_card_dvd_prime Q (by rw [hQcard])
  have hxZ := hQZ (show (⟨x, S.mem⟩ : S.P) ∈ Q from mem_zpowers x)
  intro a ha
  exact mem_centralizer_singleton_iff.mpr
    (show Commute a x from congrArg Subtype.val ((mem_center_iff.mp hxZ) ⟨a, ha⟩))

private theorem pair_eq_stabilizers :
    residualPairStabilizer M t =
      MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M) ⊓
        MulAction.stabilizer G (QuotientGroup.mk t : G ⧸ M) := by
  rw [baseCoset_stabilizer, conjugateCoset_stabilizer,
    (d.minimal.disconnected.involutions t d.t_mem).inv_eq_self]
  rfl

private theorem pair_preserver_normalizes_torus (a : G)
    (ha : ∀ beta : G ⧸ M,
      beta = QuotientGroup.mk 1 ∨ beta = QuotientGroup.mk t →
      a • beta = QuotientGroup.mk 1 ∨ a • beta = QuotientGroup.mk t) :
    a ∈ normalizer (residualCommutator M t : Set G) := by
  have hab : (QuotientGroup.mk 1 : G ⧸ M) ≠ QuotientGroup.mk t := by
    intro he
    exact d.t_not_mem_M (by simpa using QuotientGroup.eq.mp he)
  have hinj : Function.Injective (fun b : G ⧸ M => a • b) := MulAction.injective a
  have hDN := d.pair_normalizes_torus
  have htN : t ∈ normalizer (residualCommutator M t : Set G) :=
    normalizer_commutator_ge_right _ _ (mem_zpowers t)
  have ht := d.minimal.disconnected.involutions t d.t_mem
  have htab : t • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk t := by
    simp only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  have htba : t • (QuotientGroup.mk t : G ⧸ M) = QuotientGroup.mk 1 := by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, ← pow_two, ht.sq_eq_one]
  rcases ha (QuotientGroup.mk 1) (Or.inl rfl) with hα | hα
  · have hβ : a • (QuotientGroup.mk t : G ⧸ M) = QuotientGroup.mk t := by
      rcases ha (QuotientGroup.mk t) (Or.inr rfl) with hh | hh
      · exact (hab (hinj (hα.trans hh.symm))).elim
      · exact hh
    apply hDN
    rw [pair_eq_stabilizers d]
    exact ⟨hα, hβ⟩
  · have hβ : a • (QuotientGroup.mk t : G ⧸ M) = QuotientGroup.mk 1 := by
      rcases ha (QuotientGroup.mk t) (Or.inr rfl) with hh | hh
      · exact hh
      · exact (hab (hinj (hα.trans hh.symm))).elim
    have hta : t * a ∈ residualPairStabilizer M t := by
      rw [pair_eq_stabilizers d]
      exact ⟨by change (t * a) • _ = _; rw [mul_smul, hα, htba],
        by change (t * a) • _ = _; rw [mul_smul, hβ, htab]⟩
    have hn := (normalizer (residualCommutator M t : Set G)).mul_mem
      ((normalizer (residualCommutator M t : Set G)).inv_mem htN) (hDN hta)
    simpa only [inv_mul_cancel_left] using hn

/-- The centralizing branch of (12H), including the adjustment in the full centralizer. -/
public theorem Context.torus_prime_weakClosure_of_centralizes
    {x : G} (hx : x ∈ residualCommutator M t) {p : ℕ} (hp : p.Prime)
    (hxorder : orderOf x = p) (S : TorusSylowData M t x p)
    (g : G)
    (hcentral : residualCommutator M t ⊓ (S.P : Subgroup G) ≤
      centralizer ({rightConjugateElem x g} : Set G)) :
    g ∈ normalizer (zpowers x : Set G) := by
  let : Fact p.Prime := ⟨hp⟩
  let y := rightConjugateElem x g
  let R := (S.P : Subgroup G) ⊓ centralizer ({y} : Set G)
  let C := centralizer ({x} : Set G)
  have hPC : (S.P : Subgroup G) ≤ C := d.torus_prime_centralizes_sylow hx hp hxorder S
  have hyx : MulAut.conj g y = x := by
    simp only [y, rightConjugateElem, MulAut.conj_apply, mul_assoc,
      mul_inv_cancel_left, mul_inv_cancel, mul_one]
  have hRC : R.map (MulAut.conj g).toMonoidHom ≤ C := by
    rintro _ ⟨r, hr, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have hh := (show Commute r y from mem_centralizer_singleton_iff.mp hr.2).map
      (MulAut.conj g).toMonoidHom
    simpa only [MulEquiv.coe_toMonoidHom, hyx] using hh.eq
  let Q := (R.map (MulAut.conj g).toMonoidHom).subgroupOf C
  have hQp : IsPGroup p Q :=
    ((S.P.isPGroup'.to_le inf_le_left).map (MulAut.conj g).toMonoidHom).comap_subtype
  obtain ⟨T, hQT⟩ := hQp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C T (S.P.subtype hPC)
  let a : G := (c : G) * g
  have hRP : ∀ r ∈ R, MulAut.conj a r ∈ (S.P : Subgroup G) := by
    intro r hr
    let rC : C := ⟨MulAut.conj g r, hRC (mem_map_of_mem _ hr)⟩
    have hh : MulAut.conj c rC ∈ (S.P.subtype hPC : Subgroup C) := by
      rw [← hc]
      exact mem_map_of_mem (MulAut.conj c).toMonoidHom (hQT (mem_map_of_mem _ hr))
    change (c : G) * (g * r * g⁻¹) * (c : G)⁻¹ ∈ (S.P : Subgroup G) at hh
    simpa only [a, MulAut.conj_apply, mul_inv_rev, mul_assoc] using hh
  have hfix : ∀ beta : G ⧸ M,
      beta = QuotientGroup.mk 1 ∨ beta = QuotientGroup.mk t →
      ∀ v ∈ (S.P : Subgroup G), v • beta = beta := by
    intro beta hb v hv
    have hD := S.le_pair hv
    rw [pair_eq_stabilizers d] at hD
    rcases hb with rfl | rfl
    · exact hD.1
    · exact hD.2
  have ha : a⁻¹ ∈ normalizer (residualCommutator M t : Set G) := by
    apply pair_preserver_normalizes_torus d
    intro beta hb
    apply (S.fixed_torus (a⁻¹ • beta)).mp
    intro r hr
    have hrR : r ∈ R := ⟨hr.2, hcentral hr⟩
    have hh := hfix beta hb _ (hRP r hrR)
    apply MulAction.injective a
    simpa only [MulAut.conj_apply, mul_smul, smul_inv_smul] using hh
  have haN : a ∈ normalizer (zpowers x : Set G) :=
    d.torus_line_normalizer hx (inv_mem_iff.mp ha)
  have hcN : (c : G) ∈ normalizer (zpowers x : Set G) := by
    apply centralizer_le_normalizer (zpowers x : Set G)
    rw [zpowers_eq_closure, Subgroup.centralizer_closure]
    exact c.property
  have hgN := (normalizer (zpowers x : Set G)).mul_mem
    ((normalizer (zpowers x : Set G)).inv_mem hcN) haN
  simpa only [a, inv_mul_cancel_left] using hgN

/-- A plane all of whose nonidentity elements fuse into the torus contradicts coprime generation. -/
public theorem Context.no_elementary_torus_plane
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (U : Subgroup G)
    (helem : IsElementaryAbelian p U) (hcard : Nat.card U = p ^ 2)
    (hUM : U ≤ M)
    (hfusion : ∀ u ∈ U, u ≠ 1 → ∃ g : G, MulAut.conj g u ∈ residualCommutator M t) :
    False := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsElementaryAbelian p U := helem
  let : CommGroup U := IsMulCommutative.instCommGroup
  let : Fact (IsPGroup p U) := ⟨IsElementaryAbelian.isPGroup p U⟩
  let A := closure (Z ∩ (M : Set G))
  have hUN : U ≤ normalizer (A : Set G) := by
    rw [distinguishedClosure_normalizer d.minimal.disconnected]
    exact hUM
  let rho : U →* MulAut A := A.normalizerMonoidHom.comp (inclusion hUN)
  let : MulDistribMulAction U A := MulDistribMulAction.compHom A rho
  have hcop : Nat.Coprime p (Nat.card A) := by
    rw [d.distinguished_elementary_card.2]
    exact hpodd.coprime_two_right.pow_right _
  have hgen := iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup_action
    (G := A) (A := U) p hcop
  have hnoncyc : ¬ IsCyclic U := IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hcard
  have hfix : ∀ Y : Subgroup U, IsCyclic (U ⧸ Y) → fixedPointSubgroup Y A = ⊥ := by
    intro Y hY
    have hYne : Y ≠ ⊥ := by
      intro he
      subst Y
      let : IsCyclic (U ⧸ (⊥ : Subgroup U)) := hY
      exact hnoncyc (isCyclic_of_surjective (QuotientGroup.quotientBot (G := U))
        (QuotientGroup.quotientBot (G := U)).surjective)
    obtain ⟨v, hvne⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hYne
    have hune : ((v : U) : G) ≠ 1 := fun he => hvne (Subtype.ext (Subtype.ext he))
    obtain ⟨g, hgK⟩ := hfusion v.val v.val.property hune
    have hgne : MulAut.conj g ((v : U) : G) ≠ 1 := by
      intro he
      exact hune ((MulAut.conj g).injective (he.trans (map_one _).symm))
    apply eq_bot_iff.mpr
    intro a ha
    by_contra hane
    have haG : (a : G) ≠ 1 := fun he => hane (Subtype.ext he)
    have hAL := proper_residualGenerated_contains_distinguishedClosure d.minimal d.reduction
      d.action d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.even_pair
    let : IsElementaryAbelian 2 A := d.distinguished_elementary_card.1
    have haZ : (a : G) ∈ Z :=
      (isInvolution_iff_mem_Z_in_proper_residualGenerated d.minimal.disconnected d.reduction
        d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper (hAL a.property)).mp
        ⟨haG, elemPow_eq_one_of_isElementaryAbelian (a : G) a.property⟩
    rw [FixedPoints.mem_subgroup] at ha
    have hh := congrArg Subtype.val (ha v)
    change ((v : U) : G) * (a : G) * ((v : U) : G)⁻¹ = (a : G) at hh
    have hcomm : Commute ((v : U) : G) (a : G) := mul_inv_eq_iff_eq_mul.mp hh
    have hga : MulAut.conj g (a : G) ∈ centralizerClosure Z (MulAut.conj g ((v : U) : G)) :=
      subset_closure ⟨d.minimal.disconnected.invariant g a haZ,
        mem_centralizer_singleton_iff.mpr (hcomm.symm.map (MulAut.conj g).toMonoidHom)⟩
    rw [d.torus_centralizerClosure_eq_bot hgK hgne] at hga
    exact haG ((MulAut.conj g).injective (hga.trans (map_one _).symm))
  have hbot : (⊤ : Subgroup A) ≤ ⊥ := by
    rw [← hgen]
    exact iSup₂_le fun Y hY => (hfix Y hY).le
  have hzA : z ∈ A := subset_closure ⟨d.z_mem, d.z_mem_M⟩
  have hz := hbot (show (⟨z, hzA⟩ : A) ∈ (⊤ : Subgroup A) from mem_top _)
  exact (d.minimal.disconnected.involutions z d.z_mem).ne_one (congrArg Subtype.val hz)

/-- A noncentralizing prime element and the central torus line generate an elementary plane. -/
public theorem Context.torus_noncentralizing_plane
    {x : G} (hx : x ∈ residualCommutator M t) {p : ℕ} (hp : p.Prime)
    (hxorder : orderOf x = p) (S : TorusSylowData M t x p)
    {y : G} (hy : y ∈ (S.P : Subgroup G)) (hyorder : orderOf y = p)
    (hnon : ¬ residualCommutator M t ⊓ (S.P : Subgroup G) ≤ centralizer ({y} : Set G)) :
    IsElementaryAbelian p (zpowers x ⊔ zpowers y : Subgroup G) ∧
      Nat.card (zpowers x ⊔ zpowers y : Subgroup G) = p ^ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  let K := residualCommutator M t
  let : IsCyclic K := d.torus_structure.2.1
  have hyK : y ∉ K := by
    intro hyK
    apply hnon
    intro k hk
    exact mem_centralizer_singleton_iff.mpr ((K.le_centralizer hyK) k hk.1)
  have hyline : y ∉ zpowers x := fun hh => hyK ((zpowers_le.mpr hx) hh)
  have hxc : x ∈ centralizer ({y} : Set G) := by
    have hc := d.torus_prime_centralizes_sylow hx hp hxorder S hy
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hc).symm
  let : IsElementaryAbelian p (zpowers x) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (hxorder ▸ pow_orderOf_eq_one x)
  exact IsElementaryAbelian.fixed_join_card (n := 1) (zpowers x) y hyorder
    ((zpowers x).disjoint_zpowers_of_prime_order_not_mem y hyorder hyline)
    (zpowers_le.mpr hxc) (by rw [Nat.card_zpowers, hxorder, pow_one])

/-- Assemble (12H), with only the cyclic-extension line orbits explicit. -/
public theorem Context.torus_prime_weakClosure_of_plane_orbits
    {x : G} (hx : x ∈ residualCommutator M t) {p : ℕ} (hp : p.Prime)
    (hxorder : orderOf x = p) (S : TorusSylowData M t x p)
    (horbits : ∀ y ∈ (S.P : Subgroup G), orderOf y = p →
      ¬ residualCommutator M t ⊓ (S.P : Subgroup G) ≤ centralizer ({y} : Set G) →
      ∀ u ∈ (zpowers x ⊔ zpowers y : Subgroup G), u ≠ 1 →
        u ∈ zpowers x ∨ ∃ k ∈ residualCommutator M t ⊓ (S.P : Subgroup G),
          MulAut.conj k u ∈ zpowers y) :
    ∀ g : G, rightConjugateElem x g ∈ (S.P : Subgroup G) →
      g ∈ normalizer (zpowers x : Set G) := by
  intro g hy
  by_cases hc : residualCommutator M t ⊓ (S.P : Subgroup G) ≤
      centralizer ({rightConjugateElem x g} : Set G)
  · exact d.torus_prime_weakClosure_of_centralizes hx hp hxorder S g hc
  let y := rightConjugateElem x g
  have hgy : MulAut.conj g y = x := by
    simp only [y, rightConjugateElem, MulAut.conj_apply, mul_assoc,
      mul_inv_cancel_left, mul_inv_cancel, mul_one]
  have hyorder : orderOf y = p := by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, y, rightConjugateElem] using
      (orderOf_injective (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective x).trans hxorder
  obtain ⟨helem, hcard⟩ := d.torus_noncentralizing_plane hx hp hxorder S hy hyorder hc
  have hfusion := horbits y hy hyorder hc
  have hpodd : Odd p := hxorder ▸
    d.torus_odd.of_dvd_nat ((residualCommutator M t).orderOf_dvd_natCard hx)
  apply (d.no_elementary_torus_plane hp hpodd (zpowers x ⊔ zpowers y)
    helem hcard ?_ ?_).elim
  · exact sup_le (zpowers_le.mpr ((d.torus_structure.1 ▸ hx).1.1))
      (zpowers_le.mpr (S.le_pair hy).1)
  · intro u hu hune
    rcases hfusion u hu hune with hux | ⟨k, _, hky⟩
    · refine ⟨1, ?_⟩
      simpa only [MulAut.conj_apply, one_mul, inv_one, mul_one] using
        (zpowers_le.mpr hx) hux
    · refine ⟨g * k, ?_⟩
      have hh := mem_map_of_mem (MulAut.conj g).toMonoidHom hky
      rw [MonoidHom.map_zpowers] at hh
      have hxpow : MulAut.conj g (MulAut.conj k u) ∈ zpowers x := by
        simpa only [MulEquiv.coe_toMonoidHom, hgy] using hh
      simpa only [MulAut.conj_apply, mul_inv_rev, mul_assoc] using
        (zpowers_le.mpr hx) hxpow

/-- The plane-orbit prerequisite feeds the literal torus fixed-coset consumer. -/
public theorem Context.torus_fixedPoints_of_plane_orbits
    {x : G} (hx : x ∈ residualCommutator M t) {p : ℕ} (hp : p.Prime)
    (hxorder : orderOf x = p) (S : TorusSylowData M t x p)
    (horbits : ∀ y ∈ (S.P : Subgroup G), orderOf y = p →
      ¬ residualCommutator M t ⊓ (S.P : Subgroup G) ≤ centralizer ({y} : Set G) →
      ∀ u ∈ (zpowers x ⊔ zpowers y : Subgroup G), u ≠ 1 →
        u ∈ zpowers x ∨ ∃ k ∈ residualCommutator M t ⊓ (S.P : Subgroup G),
          MulAut.conj k u ∈ zpowers y) :
    ∀ beta : G ⧸ M, x • beta = beta ↔
      beta = QuotientGroup.mk 1 ∨ beta = QuotientGroup.mk t :=
  d.torus_fixedPoints_of_weakClosure hx hp hxorder S.P S.le_pair
    (d.torus_prime_weakClosure_of_plane_orbits hx hp hxorder S horbits)

end BenderSuzuki.ZD.LinearExclusion
