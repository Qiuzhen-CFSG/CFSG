module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Contracts
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.FixedPoints
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Reduction
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki
public import Theory.GroupAction.NormalizerFixedCentralizer

/-!
# Fusion of nondistinguished involutions into the pair stabilizer

Every ambient involution fixes a coset, since `M` contains an ambient Sylow
2-subgroup. Two fixed cosets give conjugacy into `D` by double transitivity.
For a unique fixed coset, conjugate a swapped pair to the marked pair; the
involution then belongs to `Dt` and normalizes the literal residual group `L`.

Any two distinguished involutions commuting with this involution fix its
unique coset. After transporting that coset to the base point they lie in
the elementary abelian subgroup `A`, so commute. An outer involution of the
actual PSL₂ model fixes a smaller PSL₂, whose upper unipotent and Weyl
involutions do not commute; the actual Suzuki model has no outer involutions.
Thus the normalizer action is inner. The models are centerless, so the actor
is a product of commuting square-one elements in `L` and `C_G(L)`. Unless
it lies in `L`, shearing conjugates it to an involution of `C_G(L) ≤ D`.
Every involution of `L` is distinguished, completing the argument.

The proof uses only shearing from the earlier centralizer premises. The
`of_local_cases` wrapper retains the complete interface of the counting
assembly; neither counting data nor its desired fusion field is assumed.

Source: `refs/KGroup/GLS4/Chapter2.tex`, Lemma 12.11, using Lemmas 12.2
and 12.7; `refs/KGroup/GLS4/Chapter4.tex`, Lemma 3.4(c).
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

private theorem fusion_fixed_exists (r : SimpleReduction Z M) {s : G}
    (hs : PFAppendixIII.IsInvolution s) : ∃ a : G ⧸ M, s • a = a := by
  obtain ⟨S, hSM, _⟩ := r.fusion
  have ho : orderOf s = 2 ^ 1 := by
    simpa using orderOf_eq_prime hs.sq_eq_one hs.ne_one
  obtain ⟨a, ha⟩ := S.exists_isConj_of_orderOf_eq_prime_pow ho
  obtain ⟨g, hg⟩ := isConj_iff.mp ha
  have haf : (a : G) • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk 1 := by
    change (a : G) ∈ MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M)
    rw [baseCoset_stabilizer]
    exact hSM a.property
  refine ⟨g⁻¹ • (QuotientGroup.mk 1 : G ⧸ M), ?_⟩
  apply MulAction.injective g
  simpa only [smul_smul, ← mul_assoc, hg, smul_smul, smul_inv_smul, mul_inv_cancel, one_smul] using haf

private theorem fusion_distinguished_unique (h : IsProductDisconnected Z M)
    (r : SimpleReduction Z M) {x : G} (hx : x ∈ Z) {a b : G ⧸ M}
    (ha : x • a = a) (hb : x • b = b) : a = b := by
  obtain ⟨z, hz, hzM⟩ := h.nonempty
  obtain ⟨g, hg⟩ := isConj_iff.mp (r.one_class z hz x hx)
  have hf (c : G ⧸ M) (hc : x • c = c) : z • (g⁻¹ • c) = g⁻¹ • c := by
    calc
      _ = g⁻¹ • ((g * z * g⁻¹) • c) := by simp only [mul_smul, inv_smul_smul]
      _ = g⁻¹ • c := by rw [hg, hc]
  apply MulAction.injective g⁻¹
  exact (action_fixedPoint_eq_base h hz hzM (hf a ha)).trans
    (action_fixedPoint_eq_base h hz hzM (hf b hb)).symm

omit [Finite G] in
private theorem fusion_two_fixed (ha : ResidualAction Z M) {t s : G} (htM : t ∉ M)
    {a b : G ⧸ M} (hab : a ≠ b) (hsa : s • a = a) (hsb : s • b = b) :
    ∃ d ∈ residualPairStabilizer M t, IsConj s d := by
  let alpha : G ⧸ M := QuotientGroup.mk 1
  have htalpha : alpha ≠ t⁻¹ • alpha := by
    intro he
    apply htM
    rw [← baseCoset_stabilizer M]
    exact (inv_smul_eq_iff.mp he.symm).symm
  obtain ⟨g, hga, hgb⟩ := MulAction.is_two_pretransitive_iff.mp ha.two_transitive hab htalpha
  have hf (c : G ⧸ M) (hc : s • c = c) :
      MulAut.conj g s • (g • c) = g • c := by
    simp only [MulAut.conj_apply, mul_smul, inv_smul_smul, hc]
  refine ⟨MulAut.conj g s, ⟨?_, ?_⟩, isConj_iff.mpr ⟨g, rfl⟩⟩
  · rw [← baseCoset_stabilizer M]
    exact MulAction.mem_stabilizer_iff.mpr (by simpa only [hga] using hf a hsa)
  · rw [← baseCoset_stabilizer M, rightConjugate_stabilizer]
    exact MulAction.mem_stabilizer_iff.mpr (by simpa only [hgb] using hf b hsb)

private theorem fusion_commute_of_unique
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (hA : IsElementaryAbelian 2 (closure (Z ∩ (M : Set G))))
    {s : G} (hu : ∃! a : G ⧸ M, s • a = a)
    {x y : G} (hx : x ∈ Z) (hy : y ∈ Z) (hxs : Commute x s) (hys : Commute y s) :
    Commute x y := by
  obtain ⟨a, ha, hau⟩ := hu
  have hf (v : G) (hv : v ∈ Z) (hvs : Commute v s) : v • a = a := by
    obtain ⟨b, hb⟩ := fusion_fixed_exists r (h.involutions v hv)
    have hsb : v • (s • b) = s • b := by
      rw [← mul_smul, hvs.eq, mul_smul, hb]
    have hsb' : s • b = b := fusion_distinguished_unique h r hv hsb hb
    exact (hau b hsb') ▸ hb
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
  have hm (v : G) (hv : v ∈ Z) (hvs : Commute v s) : MulAut.conj g⁻¹ v ∈ M := by
    rw [← baseCoset_stabilizer M]
    apply MulAction.mem_stabilizer_iff.mpr
    have hg : g • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk g := by
      change QuotientGroup.mk (g * 1) = QuotientGroup.mk g
      rw [mul_one]
    rw [MulAut.conj_apply, inv_inv]
    rw [mul_smul, mul_smul, hg, hf v hv hvs, ← hg, inv_smul_smul]
  let A := closure (Z ∩ (M : Set G))
  let : IsElementaryAbelian 2 A := hA
  have hxA : MulAut.conj g⁻¹ x ∈ A := subset_closure ⟨h.invariant _ _ hx, hm x hx hxs⟩
  have hyA : MulAut.conj g⁻¹ y ∈ A := subset_closure ⟨h.invariant _ _ hy, hm y hy hys⟩
  have hc := congrArg A.subtype (mul_comm' (⟨_, hxA⟩ : A) ⟨_, hyA⟩)
  apply (MulAut.conj g⁻¹).injective
  change MulAut.conj g⁻¹ x * MulAut.conj g⁻¹ y =
    MulAut.conj g⁻¹ y * MulAut.conj g⁻¹ x at hc
  simpa only [map_mul] using hc

open _root_.BenderSuzuki.MatrixGroups

private theorem fusion_psl2_noncommuting (K : Type*) [Field K] [CharP K 2] :
    ∃ x y : PSL2MatrixGroup K, PFAppendixIII.IsInvolution x ∧
      PFAppendixIII.IsInvolution y ∧ ¬ Commute x y := by
  have hu : PFAppendixIII.IsInvolution (Converse.uni (1 : K)) := by
    refine ⟨?_, ?_⟩
    · intro he
      have hh := congrArg (fun a : Converse.SL2 K => a.val 0 1) he
      simp [Converse.uni, Matrix.SpecialLinearGroup.coe_one] at hh
    · rw [pow_two, Converse.uni_mul_uni, CharTwo.add_self_eq_zero, Converse.uni_zero]
  refine ⟨Converse.pi K (Converse.uni 1), Converse.PWeyl K,
    IsInvolution.map_of_injective hu (Converse.pi K) Converse.pi_injective,
    Converse.PWeyl_isInvolution, ?_⟩
  intro hc
  have he : Converse.uni (1 : K) * Converse.weyl K =
      Converse.weyl K * Converse.uni 1 := Converse.pi_injective (by
        simpa only [map_mul, Converse.PWeyl] using hc.eq)
  have hh := congrArg (fun a : Converse.SL2 K => a.val 0 0) he
  change ( (Converse.uni (1 : K) : Matrix (Fin 2) (Fin 2) K) *
    (Converse.weyl K : Matrix (Fin 2) (Fin 2) K)) 0 0 =
    ((Converse.weyl K : Matrix (Fin 2) (Fin 2) K) *
    (Converse.uni (1 : K) : Matrix (Fin 2) (Fin 2) K)) 0 0 at hh
  simp [Converse.uni, Converse.weyl, Matrix.mul_apply, Fin.sum_univ_two] at hh

omit [Finite G] in
private theorem fusion_inner_of_fixed_involutions_commute {n : ℕ} (hn : 2 ≤ n)
    (hm : Nonempty (G ≃* PSL2BinaryMatrixGroup n) ∨
      ∃ m : ℕ, 1 ≤ m ∧ n = 2 * m + 1 ∧ Nonempty (G ≃* SuzukiMatrixGroup m))
    (a : MulAut G) (ha : a ^ 2 = 1)
    (hc : ∀ x y : a.fixedSubgroup, PFAppendixIII.IsInvolution x →
      PFAppendixIII.IsInvolution y → Commute x y) : ∃ b : G, a = MulAut.conj b := by
  rcases hm with he | he
  · obtain ⟨e⟩ := he
    by_contra ho
    have hsq : (MulAut.congr e a) ^ 2 = 1 := by rw [← map_pow, ha, map_one]
    obtain ⟨k, _, _, ⟨f⟩⟩ := Linear.outer_fixed_model hn (MulAut.congr e a) hsq
      (fun hi => ho ((MulAut.congr_inner_iff e a).mp hi))
    let j := (MulAut.fixedSubgroupCongr e a).trans f
    obtain ⟨x, y, hx, hy, hxy⟩ := fusion_psl2_noncommuting (BinaryGaloisField k)
    have hc' := (hc (j.symm x) (j.symm y)
      (IsInvolution.map_of_injective hx j.symm.toMonoidHom j.symm.injective)
      (IsInvolution.map_of_injective hy j.symm.toMonoidHom j.symm.injective)).map j.toMonoidHom
    change Commute (j (j.symm x)) (j (j.symm y)) at hc'
    exact hxy (by simpa only [MulEquiv.apply_symm_apply] using hc')
  · obtain ⟨m, hm, _, ⟨e⟩⟩ := he
    have hsq : (MulAut.congr e a) ^ 2 = 1 := by rw [← map_pow, ha, map_one]
    obtain ⟨b, hb, _⟩ := suzuki_involutoryAut_inner_and_twoRank m hm (MulAut.congr e a) hsq
    exact (MulAut.congr_inner_iff e a).mp ⟨b, hb⟩



omit [Finite G] in
private theorem fusion_unique_conj {s : G} (g : G)
    (hu : ∃! a : G ⧸ M, s • a = a) :
    ∃! a : G ⧸ M, MulAut.conj g s • a = a := by
  obtain ⟨a, ha, hau⟩ := hu
  refine ⟨g • a, ?_, ?_⟩
  · simp only [MulAut.conj_apply, mul_smul, inv_smul_smul, ha]
  · intro b hb
    have hb' : s • (g⁻¹ • b) = g⁻¹ • b := by
      have hh := congrArg (fun c : G ⧸ M => g⁻¹ • c) hb
      simpa only [MulAut.conj_apply, mul_smul, inv_smul_smul] using hh
    have he := congrArg (fun c : G ⧸ M => g • c) (hau _ hb')
    simpa only [smul_inv_smul] using he

omit [Finite G] in
private theorem fusion_conjugate_mem_normalizer
    (ha : ResidualAction Z M) {z t s : G}
    (ht : PFAppendixIII.IsInvolution t) (htM : t ∉ M)
    (hDN : residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G))
    (hs : PFAppendixIII.IsInvolution s) (hu : ∃! a : G ⧸ M, s • a = a) :
    ∃ g : G, MulAut.conj g s ∈ normalizer (residualGenerated M z t : Set G) := by
  let alpha : G ⧸ M := QuotientGroup.mk 1
  have htalpha : alpha ≠ t⁻¹ • alpha := by
    intro he
    apply htM
    rw [← baseCoset_stabilizer M]
    exact (inv_smul_eq_iff.mp he.symm).symm
  have hmoves : ∃ b : G ⧸ M, s • b ≠ b := by
    by_contra! hh
    obtain ⟨a, _, hau⟩ := hu
    exact htalpha ((hau alpha (hh alpha)).trans (hau _ (hh _)).symm)
  obtain ⟨b, hb⟩ := hmoves
  obtain ⟨g, hgb, hgsb⟩ :=
    MulAction.is_two_pretransitive_iff.mp ha.two_transitive hb.symm htalpha
  let v := MulAut.conj g s
  have hswap1 : v • alpha = t⁻¹ • alpha := by
    conv_lhs => rw [← hgb]
    change (g * s * g⁻¹) • (g • b) = t⁻¹ • alpha
    simpa only [mul_smul, inv_smul_smul] using hgsb
  have hswap2 : v • (t⁻¹ • alpha) = alpha := by
    rw [← hswap1, ← mul_smul]
    have hv : v * v = 1 := by
      change MulAut.conj g s * MulAut.conj g s = 1
      rw [← map_mul, show s * s = 1 by simpa only [pow_two] using hs.sq_eq_one, map_one]
    rw [hv, one_smul]
  have htinv : t⁻¹ = t := ht.inv_eq_self
  have hd : v * t ∈ residualPairStabilizer M t := by
    constructor
    · rw [← baseCoset_stabilizer M]
      apply MulAction.mem_stabilizer_iff.mpr
      simpa only [mul_smul, htinv] using hswap2
    · rw [← baseCoset_stabilizer M, rightConjugate_stabilizer]
      apply MulAction.mem_stabilizer_iff.mpr
      rw [mul_smul, smul_inv_smul, hswap1]
  have htL : t ∈ residualGenerated M z t :=
    (show zpowers t ≤ residualGenerated M z t from le_sup_right.trans le_sup_left) (mem_zpowers t)
  refine ⟨g, ?_⟩
  have hh := (normalizer (residualGenerated M z t : Set G)).mul_mem
    (hDN hd) (le_normalizer htL)
  simpa only [mul_assoc, (show t * t = 1 by simpa only [pow_two] using ht.sq_eq_one), mul_one] using hh



private theorem fusion_of_inner_action
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M) {z t s : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (hmodel : IsSimpleBenderGroup (residualGenerated M z t))
    (hCD : centralizer (residualGenerated M z t : Set G) ≤ residualPairStabilizer M t)
    (hshear : ResidualCentralizerShearing Z M t)
    (hs : PFAppendixIII.IsInvolution s) (hsZ : s ∉ Z)
    (hsN : s ∈ normalizer (residualGenerated M z t : Set G))
    (hinner : ∃ l : residualGenerated M z t,
      (residualGenerated M z t).normalizerMonoidHom ⟨s, hsN⟩ = MulAut.conj l) :
    ∃ d ∈ residualPairStabilizer M t, IsConj s d := by
  let L := residualGenerated M z t
  obtain ⟨l, hl⟩ := hinner
  have hcenter : center L = ⊥ := by
    rcases hmodel.isSimple.eq_bot_or_eq_top_of_normal (center L) inferInstance with hb | ht
    · exact hb
    · exact False.elim (hmodel.not_commutative (fun x y =>
        (mem_center_iff.mp (ht ▸ mem_top x) y).symm))
  have hlsq : l ^ 2 = 1 := by
    have hsquare : (L.normalizerMonoidHom ⟨s, hsN⟩) ^ 2 = 1 := by
      rw [← map_pow, show (⟨s, hsN⟩ : normalizer (L : Set G)) ^ 2 = 1 from
        Subtype.ext hs.sq_eq_one, map_one]
    rw [hl, ← map_pow] at hsquare
    have hc : l ^ 2 ∈ center L := by
      rw [mem_center_iff]
      intro x
      have he := congrArg (fun f : MulAut L => f x) hsquare
      change l ^ 2 * x * (l ^ 2)⁻¹ = x at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    simpa only [hcenter, mem_bot] using hc
  let c : G := (l : G)⁻¹ * s
  have hc : c ∈ centralizer (L : Set G) := by
    intro x hx
    have he := congrArg (fun f : MulAut L => (f ⟨x, hx⟩ : G)) hl
    change s * x * s⁻¹ = (l : G) * x * (l : G)⁻¹ at he
    change x * c = c * x
    dsimp only [c]
    calc
      x * ((l : G)⁻¹ * s) = (l : G)⁻¹ * ((l : G) * x * (l : G)⁻¹) * s := by group
      _ = (l : G)⁻¹ * (s * x * s⁻¹) * s := by rw [← he]
      _ = ((l : G)⁻¹ * s) * x := by group
  have hsc : s = (l : G) * c := by dsimp only [c]; group
  have hcl : Commute (l : G) c := mem_centralizer_iff.mp hc l l.property
  have hcsq : c ^ 2 = 1 := by
    have he := hs.sq_eq_one
    rw [hsc, hcl.mul_pow] at he
    have hlG : (l : G) ^ 2 = 1 := congrArg L.subtype hlsq
    simpa only [hlG, one_mul] using he
  have hcne : c ≠ 1 := by
    intro he
    have hsL : s ∈ L := by simpa only [hsc, he, mul_one] using l.property
    exact hsZ ((isInvolution_iff_mem_Z_in_proper_residualGenerated h r hz hzM ht htM hL hsL).mp hs)
  have hci : PFAppendixIII.IsInvolution c := ⟨hcne, hcsq⟩
  have hcD := hCD hc
  refine ⟨c, hcD, ?_⟩
  by_cases hlone : l = 1
  · have hse : s = c := by simpa only [hlone, coe_one, one_mul] using hsc
    rw [hse]
  · have hli : PFAppendixIII.IsInvolution l := ⟨hlone, hlsq⟩
    have hzL : z ∈ L := (show zpowers z ≤ L from le_sup_left.trans le_sup_left) (mem_zpowers z)
    obtain ⟨g, hg⟩ := (stronglyEmbedded_in_proper_residualGenerated h r hz hzM ht htM hL).involutions_conjugate
      hli (IsInvolution.subtype (h.involutions z hz) hzL)
    have hgz : MulAut.conj (g : G)⁻¹ (l : G) = z := by
      simpa only [rightConjugateElem, MulAut.conj_apply, inv_inv, coe_mul, coe_inv] using
        congrArg Subtype.val hg
    have hgc : MulAut.conj (g : G)⁻¹ c = c := by
      rw [MulAut.conj_apply, inv_inv]
      have hcg := mem_centralizer_iff.mp hc g g.property
      calc
        (g : G)⁻¹ * c * (g : G) = (g : G)⁻¹ * ((g : G) * c) := by rw [hcg]; group
        _ = c := inv_mul_cancel_left _ _
    have hconj : IsConj s (z * c) := isConj_iff.mpr ⟨(g : G)⁻¹, by
      change MulAut.conj (g : G)⁻¹ s = z * c
      rw [hsc, map_mul, hgz, hgc]⟩
    exact hconj.trans (hshear c hcD hci z (subset_closure ⟨hz, hzM⟩)
      (mem_centralizer_iff.mp hc z hzL)).symm

/-- The fusion assertion of Lemma 12.11 from the original proper-residual
hypotheses and shearing. The other local counting premises are unnecessary. -/
public theorem proper_residualGenerated_nondistinguished_fusion_of_shearing
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hshear : ResidualCentralizerShearing Z M t) :
    ∀ v : G, PFAppendixIII.IsInvolution v → v ∉ Z →
      ∃ d ∈ residualPairStabilizer M t, IsConj v d := by
  intro v hv hvZ
  obtain ⟨alpha, halpha⟩ := fusion_fixed_exists r hv
  by_cases hu : ∀ beta : G ⧸ M, v • beta = beta → beta = alpha
  · have hunique : ∃! a : G ⧸ M, v • a = a := ⟨alpha, halpha, hu⟩
    obtain ⟨n, hn, hmodels, hAL, hDN, _, _, _, hA, _, _, _, _, hCD, _⟩ :=
      proper_residualGenerated_structure h r ha hz hzM ht htM hL heven
    obtain ⟨g, hgN⟩ := fusion_conjugate_mem_normalizer ha (h.disconnected.involutions t ht)
      htM hDN hv hunique
    let s := MulAut.conj g v
    have hs : PFAppendixIII.IsInvolution s :=
      IsInvolution.map_of_injective hv (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    have hsZ : s ∉ Z := by
      intro hsZ
      have hh := h.disconnected.invariant g⁻¹ s hsZ
      exact hvZ (by simpa [s, MulAut.conj_apply, mul_assoc] using hh)
    have hsunique := fusion_unique_conj g hunique
    let L := residualGenerated M z t
    let a := L.normalizerMonoidHom ⟨s, hgN⟩
    have hasq : a ^ 2 = 1 := by
      change (L.normalizerMonoidHom ⟨s, hgN⟩) ^ 2 = 1
      rw [← map_pow, show (⟨s, hgN⟩ : normalizer (L : Set G)) ^ 2 = 1 from
        Subtype.ext hs.sq_eq_one, map_one]
    have hcomm (x y : a.fixedSubgroup) (hx : PFAppendixIII.IsInvolution x)
        (hy : PFAppendixIII.IsInvolution y) : Commute x y := by
      let f := L.normalizerFixedEquivCentralizer ⟨s, hgN⟩
      have hxi := IsInvolution.map_of_injective hx
        ((L ⊓ centralizer ({s} : Set G) : Subgroup G).subtype.comp f.toMonoidHom)
        (Subtype.val_injective.comp f.injective)
      have hyi := IsInvolution.map_of_injective hy
        ((L ⊓ centralizer ({s} : Set G) : Subgroup G).subtype.comp f.toMonoidHom)
        (Subtype.val_injective.comp f.injective)
      have hxZ := (isInvolution_iff_mem_Z_in_proper_residualGenerated h.disconnected r
        hz hzM ht htM hL (f x).property.1).mp hxi
      have hyZ := (isInvolution_iff_mem_Z_in_proper_residualGenerated h.disconnected r
        hz hzM ht htM hL (f y).property.1).mp hyi
      have hc := fusion_commute_of_unique h.disconnected r hA hsunique hxZ hyZ
        (mem_centralizer_singleton_iff.mp (f x).property.2)
        (mem_centralizer_singleton_iff.mp (f y).property.2)
      apply Subtype.ext
      apply Subtype.ext
      exact hc.eq
    obtain ⟨l, hl⟩ := fusion_inner_of_fixed_involutions_commute hn hmodels a hasq hcomm
    have hmodel : IsSimpleBenderGroup L := by
      rcases hmodels with he | ⟨m, hm, _, he⟩
      · exact IsSimpleBenderGroup.isPSL2 ⟨n, hn, he⟩
      · exact IsSimpleBenderGroup.isSuzuki ⟨m, hm, he⟩
    obtain ⟨d, hd, hsd⟩ := fusion_of_inner_action h.disconnected r hz hzM ht htM hL
      hmodel hCD hshear hs hsZ hgN ⟨l, hl⟩
    exact ⟨d, hd, (isConj_iff.mpr ⟨g, rfl⟩ : IsConj v s).trans hsd⟩
  · push Not at hu
    obtain ⟨beta, hbeta, hne⟩ := hu
    exact fusion_two_fixed ha htM hne hbeta halpha

/-- The nondistinguished-involution clause of GLS4, Chapter 2, Lemma 12.11,
under the earlier-source premises supplied to the counting assembly. -/
public theorem proper_residualGenerated_nondistinguished_fusion_of_local_cases
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (_hlocal : ResidualCentralizerLocalData Z M z t)
    (hshear : ResidualCentralizerShearing Z M t)
    (_hcentralizes : ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
      v ∈ centralizer (residualGenerated M z t : Set G))
    (_hcases : ∃ n : ℕ, 2 ≤ n ∧ Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n ∧
      ResidualCentralizerCases Z M z t n) :
    ∀ v : G, PFAppendixIII.IsInvolution v → v ∉ Z →
      ∃ d ∈ residualPairStabilizer M t, IsConj v d :=
  proper_residualGenerated_nondistinguished_fusion_of_shearing
    h r ha hz hzM ht htM hL heven hshear

end BenderSuzuki.ZD
