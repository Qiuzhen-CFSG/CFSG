module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.LocalStructure.LinearBorel
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.FourObstruction
public import Theory.SpecificGroups.PSL2.SylowPointwiseInner
public import BenderSuzuki.Converse.Lift

/-!
# Localization of the involution centralizer in the linear branch

Let `A = ⟨Z ∩ M⟩`, `L = residualGenerated M z t`, `J = C_G(L)` and
`V = O₂(M)`. Two-centrality of the distinguished involutions implies that
`V` centralizes `A`. The actual PSL₂ Borel calculation gives `|A| = 2^n`;
comparison with the matrix Sylow subgroup shows that `A` is Sylow in `L`.
The pointwise Sylow automorphism theorem then gives `C_{N_G(L)}(A) ≤ AJ`.

If `|J| = 2` and every pair-stabilizer involution has distinguished
centralizer closure `L`, the unique nonidentity element of `J` forces
`N_G(J) ≤ N_G(L)`. Combining these results proves the precise relative
containment `C_V(J_M) ≤ A_M ∨ J_M` used by the local-control consumer.
The final counting lemma converts the actual coset degree `q³+1` into
`|M| = q³|D|` by double transitivity; it does not assert that degree.

The closure-collapse premise is the earlier Proposition 13.1 obligation,
owned by `qt-i68-zd-proper-l-centralizers`. This module proves its conditional
application and does not claim to establish the preceding counting argument.
Source: GLS, Volume 4, Chapter 2, Lemma 15.2(c,d,f,h), using Chapter 4,
Lemma 3.6(a), in `refs/KGroup/GLS4/Chapter2.tex` and `Chapter4.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory PFAppendixIII
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The two-core centralizes the actual distinguished closure in M. -/
public theorem linear_twoCore_le_distinguished_centralizer
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M) :
    pCore 2 M ≤ centralizer ((closure (Z ∩ (M : Set G))).subgroupOf M : Set M) := by
  intro v hv a ha
  apply Subtype.ext
  have hAC : closure (Z ∩ (M : Set G)) ≤ centralizer ({(v : G)} : Set G) := by
    rw [closure_le]
    intro z hz
    obtain ⟨S, _, hS⟩ := r.two_central z hz.1
    have hSM : (S : Subgroup G) ≤ M := by
      intro s hs
      exact mem_of_commute h hz.1 hz.2 (hS ⟨s, hs⟩)
    have hcore : pCore 2 M ≤ (S.subtype hSM : Subgroup M) :=
      IsPGroup.le_sylow_of_normal pCore_isPGroup (S.subtype hSM)
    exact mem_centralizer_singleton_iff.mpr (hS ⟨v, hcore hv⟩).eq
  exact mem_centralizer_singleton_iff.mp (hAC ha)

omit [Finite G] in
/-- Collapse of the distinguished centralizer closure controls the whole
normalizer of the order-two ambient centralizer. -/
public theorem linear_centralizer_normalizer_le_of_centralizerClosure
    (h : IsProductDisconnected Z M) {z t : G} (hz : z ∈ Z) (hzM : z ∈ M)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hcollapse : ∀ u : G, u ∈ residualPairStabilizer M t → PFAppendixIII.IsInvolution u →
      centralizerClosure Z u = residualGenerated M z t) :
    normalizer (centralizer (residualGenerated M z t : Set G) : Set G) ≤
      normalizer (residualGenerated M z t : Set G) := by
  let J := centralizer (residualGenerated M z t : Set G)
  obtain ⟨u, hu, huniq⟩ := (Nat.card_eq_two_iff' (1 : J)).mp hJ
  have huG : (u : G) ≠ 1 := fun he => hu (Subtype.ext he)
  have hu2 : (u : G) ^ 2 = 1 := by
    have he := pow_card_eq_one' (x := u)
    rw [hJ] at he
    exact congrArg Subtype.val he
  have hcl := hcollapse u
    (centralizer_residualGenerated_le_pairStabilizer h hz hzM u.property) ⟨huG, hu2⟩
  have hCN : centralizer ({(u : G)} : Set G) ≤
      normalizer (centralizerClosure Z u : Set G) := by
    apply le_normalizer_closure_iff.mpr
    intro x hx a ha
    exact subset_closure ⟨h.invariant x a ha.1,
      (centralizer ({(u : G)} : Set G)).mul_mem
        ((centralizer ({(u : G)} : Set G)).mul_mem hx ha.2)
        ((centralizer ({(u : G)} : Set G)).inv_mem hx)⟩
  rw [hcl] at hCN
  intro x hx
  apply hCN
  apply mem_centralizer_singleton_iff.mpr
  have hxJ : x * (u : G) * x⁻¹ ∈ J := (mem_normalizer_iff.mp hx u).mp u.property
  have hxne : (⟨x * (u : G) * x⁻¹, hxJ⟩ : J) ≠ 1 := by
    intro he
    apply huG
    have heG := congrArg Subtype.val he
    have heG' := congrArg (fun v : G => x⁻¹ * v * x) heG
    simpa [mul_assoc] using heG'
  have he := congrArg Subtype.val (huniq _ hxne)
  exact mul_inv_eq_iff_eq_mul.mp he

/-- The distinguished closure is the Sylow root subgroup in the actual local PSL₂. -/
public theorem linear_distinguishedClosure_sylow
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t) :
    ∃ S : Sylow 2 (residualGenerated M z t),
      (S : Subgroup (residualGenerated M z t)) =
        (closure (Z ∩ (M : Set G))).subgroupOf (residualGenerated M z t) := by
  let A := (closure (Z ∩ (M : Set G))).subgroupOf (residualGenerated M z t)
  have hcA : Nat.card A = 2 ^ n := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAL).toEquiv]
    exact (psl2_distinguishedClosure_elementary_card h r hz hzM ht htM hL ⟨e⟩ hn hAL).2
  obtain ⟨S, hAS⟩ := (IsPGroup.of_card hcA).exists_le_sylow
  refine ⟨S, (eq_of_le_of_card_ge hAS ?_).symm⟩
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let U := Matrix.SpecialLinearGroup.upperUnipotentSylow (BinaryGaloisField n) 2
  let P := U.mapSurjective (f := Converse.pi (BinaryGaloisField n)) Converse.pi_surjective
  have hcS : Nat.card S = Nat.card Q :=
    (card_map_of_injective e.injective).symm
  have hcP : Nat.card P = Nat.card U := card_map_of_injective Converse.pi_injective
  calc
    Nat.card S = Nat.card Q := hcS
    _ = Nat.card P := Nat.card_congr (Q.equiv P).toEquiv
    _ = Nat.card U := hcP
    _ = 2 ^ n := by
      change Nat.card (Matrix.SpecialLinearGroup.upperUnipotent (BinaryGaloisField n)) = _
      rw [Matrix.SpecialLinearGroup.card_upperUnipotent,
        Converse.card_binaryGaloisField n (by omega)]
    _ ≤ Nat.card A := hcA.symm.le

/-- Centralizing the distinguished root inside its local normalizer leaves
only the root and the ambient centralizer of L. -/
public theorem linear_normalizer_inf_centralizer_le
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t) :
    normalizer (residualGenerated M z t : Set G) ⊓
      centralizer (closure (Z ∩ (M : Set G)) : Set G) ≤
      closure (Z ∩ (M : Set G)) ⊔ centralizer (residualGenerated M z t : Set G) := by
  let L := residualGenerated M z t
  obtain ⟨S, hS⟩ := linear_distinguishedClosure_sylow h r hz hzM ht htM hL hn e hAL
  intro x hx
  let a := L.normalizerMonoidHom ⟨x, hx.1⟩
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hf : ∀ y ∈ Q, (MulAut.congr e a) y = y := by
    rintro y ⟨v, hv, rfl⟩
    change e (a (e.symm (e v))) = e v
    rw [e.symm_apply_apply]
    congr 1
    apply Subtype.ext
    change x * (v : G) * x⁻¹ = v
    have hvA : (v : G) ∈ closure (Z ∩ (M : Set G)) := by
      have hv' : v ∈ (S : Subgroup L) := hv
      rw [hS] at hv'
      exact hv'
    rw [← (mem_centralizer_iff.mp hx.2 v hvA), mul_inv_cancel_right]
  obtain ⟨y, hy, he⟩ := Theory.PSL2.aut_fixing_sylow_inner Q (MulAut.congr e a) hf
  obtain ⟨v, hv, rfl⟩ := hy
  have hav : a = MulAut.conj v := by
    apply (MulAut.congr e).injective
    rw [he]
    ext w
    simp [MulAut.congr, MulAut.conj_apply]
  have hvA : (v : G) ∈ closure (Z ∩ (M : Set G)) := by
    have hv' : v ∈ (S : Subgroup L) := hv
    rw [hS] at hv'
    exact hv'
  have hj : (v : G)⁻¹ * x ∈ centralizer (L : Set G) := by
    intro w hw
    have hh := congrArg Subtype.val (DFunLike.congr_fun hav ⟨w, hw⟩)
    change x * w * x⁻¹ = (v : G) * w * (v : G)⁻¹ at hh
    have hh' := congrArg (fun y : G => (v : G)⁻¹ * y * x) hh
    have hc : (v : G)⁻¹ * x * w = w * ((v : G)⁻¹ * x) := by
      simpa [mul_assoc] using hh'
    exact hc.symm
  have hm := (closure (Z ∩ (M : Set G)) ⊔ centralizer (L : Set G)).mul_mem
    ((show closure (Z ∩ (M : Set G)) ≤ closure (Z ∩ (M : Set G)) ⊔
      centralizer (L : Set G) from le_sup_left) hvA)
    ((show centralizer (L : Set G) ≤ closure (Z ∩ (M : Set G)) ⊔
      centralizer (L : Set G) from le_sup_right) hj)
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hm

/-- The exact involution-centralizer localization needed by local control.
The only extra earlier-source premise is the explicitly permitted collapse. -/
public theorem linear_involution_localization_of_centralizerClosure
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hcollapse : ∀ u : G, u ∈ residualPairStabilizer M t → PFAppendixIII.IsInvolution u →
      centralizerClosure Z u = residualGenerated M z t) :
    pCore 2 M ⊓
      centralizer ((centralizer (residualGenerated M z t : Set G)).subgroupOf M : Set M) ≤
      (closure (Z ∩ (M : Set G))).subgroupOf M ⊔
        (centralizer (residualGenerated M z t : Set G)).subgroupOf M := by
  let A := closure (Z ∩ (M : Set G))
  let J := centralizer (residualGenerated M z t : Set G)
  have hAM : A ≤ M := distinguishedClosure_le
  have hJM : J ≤ M := (centralizer_residualGenerated_le_pairStabilizer h hz hzM).trans inf_le_left
  intro v hv
  have hvJ : (v : G) ∈ centralizer (J : Set G) := by
    intro j hj
    exact congrArg Subtype.val (mem_centralizer_iff.mp hv.2 ⟨j, hJM hj⟩ hj)
  have hvN := linear_centralizer_normalizer_le_of_centralizerClosure h hz hzM hJ hcollapse
    (centralizer_le_normalizer J hvJ)
  have hvA : (v : G) ∈ centralizer (A : Set G) := by
    intro a ha
    exact congrArg Subtype.val (mem_centralizer_iff.mp
      (linear_twoCore_le_distinguished_centralizer h r hv.1) ⟨a, hAM ha⟩ ha)
  have hvSup := linear_normalizer_inf_centralizer_le h r hz hzM ht htM hL hn e hAL ⟨hvN, hvA⟩
  have he : (A.subgroupOf M ⊔ J.subgroupOf M).map M.subtype = A ⊔ J := by
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hAM, map_subgroupOf_eq_of_le hJM]
  obtain ⟨w, hw, hew⟩ := (he.symm ▸ hvSup)
  exact (Subtype.ext hew : w = v) ▸ hw

/-- Double transitivity turns the linear degree into the exact order premise. -/
public theorem linear_stabilizer_card_of_degree (ha : ResidualAction Z M)
    {t : G} (htM : t ∉ M) {q : ℕ} (hdegree : Nat.card (G ⧸ M) = q ^ 3 + 1) :
    Nat.card M = q ^ 3 * Nat.card (residualPairStabilizer M t) := by
  let a : G ⧸ M := QuotientGroup.mk 1
  have hM : MulAction.stabilizer G a = M := MulAction.stabilizer_quotient M
  have hne : t⁻¹ • a ≠ a := by
    intro he
    apply htM
    rw [← hM]
    exact (inv_smul_eq_iff.mp he).symm
  have hc := Converse.card_stabilizer_eq_twoPoint_mul ha.two_transitive hne
  rw [← PFchapter1section1.rightConjugate_stabilizer, hM, hdegree] at hc
  simpa only [Nat.add_sub_cancel, mul_comm, residualPairStabilizer] using hc
end BenderSuzuki.ZD
