module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section213Alpha.Geometry
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section213Alpha.XiFusion.InvolutionReduction
public import Theory.GroupTheory.WeakClosureOvergroups

/-!
# Held's separation of the two xi choices

If both xi and pi*xi were conjugate to pi, the elements of M conjugate to
mu would be precisely its six local mu-conjugates. Their product is pi.
The four-elementary-subgroup catalogue gives a useful invariant: whenever
an elementary sixteen in the displayed Sylow has six mu-conjugates, their
product is either 1 or pi. The calculation allows arbitrary fusion of the
other four local classes, so it assumes no lambda normalization or fusion.

Conjugating M into the Sylow preserves this product and cannot send pi to 1.
It therefore fixes pi, and the conjugator belongs to H = C_G(pi). Since H
normalizes M, this proves weak closure of M, and the same product argument
gives N_G(M) = H. Fusion pi ~ xi supplies an order-64 subgroup of C_G(xi)
containing M. Weak closure makes this two-group normalize M; it would then
lie in H intersect C_G(xi), whose order is 96, a contradiction.

This class-product argument replaces the source's A8 orbit bound and
order-five action, while retaining the order-64 centralizer overgroup and
proving its required normalization. All local computations use the actual
permutation coordinates and kernel reduction. No later recognition theorem
or S-fusion result is used.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 2.7, printed p.229.
The conjugation convention below is g*x*g^-1.
-/

open Subgroup Equiv
open scoped BigOperators IsMulCommutative
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion
open Coordinates Fusion

private def selectedClass (b : Fin 4 → Bool) : Fin 9 → Bool :=
  ![false, false, true, b 0, b 1, b 2, false, false, b 3]

private def selectedCodes (k : Fin 4) (b : Fin 4 → Bool) : Finset BaseCode :=
  Finset.univ.filter fun a => selectedClass b (elementaryClass k a)

private theorem selected_six_sum : ∀ (k : Fin 4) (b : Fin 4 → Bool),
    (selectedCodes k b).card = 6 →
      (∑ a ∈ selectedCodes k b, a) = 0 ∨
        (∑ a ∈ selectedCodes k b, a) = (1, 0, 0, 0) := by
  decide +kernel

private theorem selected_M : ∀ b : Fin 4 → Bool,
    (selectedCodes 0 b).card = 6 ∧
      (∑ a ∈ selectedCodes 0 b, a) = (1, 0, 0, 0) := by
  decide +kernel

private noncomputable def wordIso (k : Fin 4) : Multiplicative BaseCode ≃* elementary k :=
  MulEquiv.ofBijective
    ({
      toFun := fun a => ⟨elementaryWord k a.toAdd, (mem_elementary k _).mpr ⟨a.toAdd, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        have h : ∀ k, elementaryWord k 0 = 1 := by decide +kernel
        exact h k
      map_mul' := by
        intro a b
        apply Subtype.ext
        have h : ∀ k a b, elementaryWord k (a + b) = elementaryWord k a * elementaryWord k b := by
          decide +kernel
        exact h k a.toAdd b.toAdd } : Multiplicative BaseCode →* elementary k)
    (elementaryWord_bijective k)

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

private noncomputable def ambientWordIso (k : Fin 4) :
    Multiplicative BaseCode ≃* ambientElementary D e k :=
  (wordIso k).trans ((elementary k).equivMapOfInjective (D.a10ModelEmbedding e)
    (D.a10ModelEmbedding_injective e))

private noncomputable def fusionProduct (A : Subgroup G) [IsMulCommutative A] (x : G) : A := by
  classical
  let := Fintype.ofFinite A
  exact ∏ a : A, if IsConj x (a : G) then a else 1

private theorem fusionProduct_transport (A B : Subgroup G)
    [IsMulCommutative A] [IsMulCommutative B] (v : A ≃* B) (x : G)
    (hv : ∀ a : A, IsConj x (v a : G) ↔ IsConj x (a : G)) :
    v (fusionProduct A x) = fusionProduct B x := by
  classical
  let := Fintype.ofFinite A
  let := Fintype.ofFinite B
  unfold fusionProduct
  rw [map_prod]
  apply Fintype.prod_equiv v.toEquiv
  intro a
  change v (if IsConj x (a : G) then a else 1) =
    if IsConj x (v a : G) then v a else 1
  rw [hv]
  split_ifs <;> simp only [map_one]

private theorem mu_selection
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hxi : IsConj D.z (D.a10ModelEmbedding e xi))
    (hpiXi : IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * xi))) :
    ∃ b : Fin 4 → Bool, ∀ (k : Fin 4) (a : BaseCode),
      IsConj (D.a10NoncentralInvolution e) (D.a10ModelEmbedding e (elementaryWord k a)) ↔
        a ∈ selectedCodes k b := by
  classical
  let f := D.a10ModelEmbedding e
  let p : H → Prop := fun y => IsConj (f Coordinates.mu) (f y)
  let b : Fin 4 → Bool := fun i => decide (p ((![tau, lam, Coordinates.pi * lam, tau * lam * xi] : Fin 4 → H) i))
  have h1 : ¬ p 1 := by
    intro h
    have hm : f Coordinates.mu ≠ 1 := by
      rw [← map_one f, (D.a10ModelEmbedding_injective e).ne_iff]
      decide +kernel
    exact hm (isConj_one_right.mp (by simpa [p] using h.symm))
  have hp : ¬ p Coordinates.pi := by
    intro h
    have hpz : f Coordinates.pi = D.z := D.a10ModelEmbedding_central e
    change IsConj (D.a10NoncentralInvolution e) (f Coordinates.pi) at h
    rw [hpz] at h
    exact hfusion h.symm
  have hx : ¬ p xi := fun h => hfusion (hxi.trans h.symm)
  have hpx : ¬ p (Coordinates.pi * xi) := fun h => hfusion (hpiXi.trans h.symm)
  have hc (j : Fin 9) : p (localRepresentative j) ↔ selectedClass b j = true := by
    fin_cases j
    · change p 1 ↔ false = true
      simp only [h1, Bool.false_eq_true]
    · change p Coordinates.pi ↔ false = true
      simp only [hp, Bool.false_eq_true]
    · change p Coordinates.mu ↔ true = true
      exact ⟨fun _ => rfl, fun _ => IsConj.refl (f Coordinates.mu)⟩
    · change p tau ↔ decide (p tau) = true
      simp only [decide_eq_true_eq]
    · change p lam ↔ decide (p lam) = true
      simp only [decide_eq_true_eq]
    · change p (Coordinates.pi * lam) ↔ decide (p (Coordinates.pi * lam)) = true
      simp only [decide_eq_true_eq]
    · change p xi ↔ false = true
      simp only [hx, Bool.false_eq_true]
    · change p (Coordinates.pi * xi) ↔ false = true
      simp only [hpx, Bool.false_eq_true]
    · change p (tau * lam * xi) ↔ decide (p (tau * lam * xi)) = true
      simp only [decide_eq_true_eq]
  refine ⟨b, fun k a => ?_⟩
  have ht := f.map_isConj (elementaryWord_isConj k a)
  change p (elementaryWord k a) ↔ _
  rw [show p (elementaryWord k a) ↔ p (localRepresentative (elementaryClass k a)) from
    ⟨fun h => h.trans ht.symm, fun h => h.trans ht⟩, hc]
  simp [selectedCodes]

private theorem fusionProduct_coordinates (k : Fin 4) (b : Fin 4 → Bool)
    (hsel : ∀ a : BaseCode, IsConj (D.a10NoncentralInvolution e)
      (D.a10ModelEmbedding e (elementaryWord k a)) ↔ a ∈ selectedCodes k b) :
    let := ambientElementary_isElementaryAbelian D e k
    fusionProduct (ambientElementary D e k) (D.a10NoncentralInvolution e) =
      ambientWordIso D e k (Multiplicative.ofAdd (∑ a ∈ selectedCodes k b, a)) := by
  classical
  let := ambientElementary_isElementaryAbelian D e k
  let := Fintype.ofFinite (ambientElementary D e k)
  let v := ambientWordIso D e k
  dsimp only
  unfold fusionProduct
  dsimp only
  rw [ofAdd_sum, map_prod]
  symm
  rw [← Finset.prod_ite_mem_eq]
  apply Fintype.prod_equiv v.toEquiv
  intro a
  change (if a.toAdd ∈ selectedCodes k b then v a else 1) =
    if IsConj (D.a10NoncentralInvolution e) (D.a10ModelEmbedding e (elementaryWord k a.toAdd))
      then v a else 1
  rw [hsel]
  split_ifs <;> rfl

omit [Finite G] in
private theorem fusionCard_coordinates (k : Fin 4) (b : Fin 4 → Bool)
    (hsel : ∀ a : BaseCode, IsConj (D.a10NoncentralInvolution e)
      (D.a10ModelEmbedding e (elementaryWord k a)) ↔ a ∈ selectedCodes k b) :
    (fusedElements (ambientElementary D e k) (D.a10NoncentralInvolution e)).ncard =
      (selectedCodes k b).card := by
  classical
  rw [← Nat.card_coe_set_eq]
  calc
    _ = Nat.card (selectedCodes k b) := Nat.card_congr
      ((Equiv.subtypeEquiv (ambientWordIso D e k).toEquiv (fun a => (hsel a.toAdd).symm)).symm)
    _ = _ := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]

private theorem pi_word (k : Fin 4) : elementaryWord k (1, 0, 0, 0) = Coordinates.pi := by
  revert k
  decide +kernel

private theorem zero_word (k : Fin 4) : elementaryWord k 0 = 1 := by
  revert k
  decide +kernel

private theorem conjugate_pi_eq_of_M_map_le
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hxi : IsConj D.z (D.a10ModelEmbedding e xi))
    (hpiXi : IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * xi)))
    (g : G) (hg : (ambientElementary D e 0).map (MulAut.conj g).toMonoidHom ≤
      ambientSylow D e) : g * D.z * g⁻¹ = D.z := by
  obtain ⟨b, hb⟩ := mu_selection D e hfusion hxi hpiXi
  let M := ambientElementary D e 0
  let := ambientElementary_isElementaryAbelian D e 0
  obtain ⟨k, hk⟩ := ambient_elementary_sixteen D e
    (M.map (MulAut.conj g).toMonoidHom) hg
    (IsElementaryAbelian.map (MulAut.conj g).toMonoidHom)
    (by rw [card_map_of_injective (MulAut.conj g).injective]; exact ambientElementary_card D e 0)
  let := ambientElementary_isElementaryAbelian D e k
  have hcard : (selectedCodes k b).card = 6 := by
    rw [← fusionCard_coordinates D e k b (hb k), ← hk,
      fusedElements_map_conj_card, fusionCard_coordinates D e 0 b (hb 0)]
    exact (selected_M b).1
  let v : M ≃* ambientElementary D e k :=
    (M.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr hk)
  have hv (a : M) : IsConj (D.a10NoncentralInvolution e) (v a : G) ↔
      IsConj (D.a10NoncentralInvolution e) (a : G) := by
    have h : IsConj (a : G) (v a : G) := isConj_iff.mpr ⟨g, rfl⟩
    exact ⟨fun h' => h'.trans h.symm, fun h' => h'.trans h⟩
  have hp := fusionProduct_transport M (ambientElementary D e k) v
    (D.a10NoncentralInvolution e) hv
  rw [fusionProduct_coordinates D e 0 b (hb 0),
    fusionProduct_coordinates D e k b (hb k), (selected_M b).2] at hp
  have he := congrArg (fun a : ambientElementary D e k => (a : G)) hp
  change g * D.a10ModelEmbedding e (elementaryWord 0 (1, 0, 0, 0)) * g⁻¹ =
    D.a10ModelEmbedding e (elementaryWord k (∑ a ∈ selectedCodes k b, a)) at he
  rw [pi_word, D.a10ModelEmbedding_central e] at he
  rcases selected_six_sum k b hcard with hs | hs
  · rw [hs, zero_word, map_one] at he
    have hz : D.z = 1 := (MulAut.conj g).injective (he.trans (map_one (MulAut.conj g)).symm)
    exact (D.z_ne_one hz).elim
  · rwa [hs, pi_word, D.a10ModelEmbedding_central e] at he

private theorem M_weakly_closed
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hxi : IsConj D.z (D.a10ModelEmbedding e xi))
    (hpiXi : IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * xi)))
    (g : G) (hg : (ambientElementary D e 0).map (MulAut.conj g).toMonoidHom ≤
      ambientSylow D e) :
    (ambientElementary D e 0).map (MulAut.conj g).toMonoidHom = ambientElementary D e 0 := by
  have hc : g ∈ D.centralizer := mem_centralizer_singleton_iff.mpr
    (mul_inv_eq_iff_eq_mul.mp (conjugate_pi_eq_of_M_map_le D e hfusion hxi hpiXi g hg))
  exact mem_normalizer_iff_map_conj_eq.mp (centralizer_le_normalizer_M D e hc)

private theorem M_normalizer_eq
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hxi : IsConj D.z (D.a10ModelEmbedding e xi))
    (hpiXi : IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * xi))) :
    normalizer (ambientElementary D e 0 : Set G) = D.centralizer := by
  apply le_antisymm ?_ (centralizer_le_normalizer_M D e)
  intro g hg
  apply mem_centralizer_singleton_iff.mpr
  apply mul_inv_eq_iff_eq_mul.mp
  apply conjugate_pi_eq_of_M_map_le D e hfusion hxi hpiXi
  have he : (ambientElementary D e 0).map (MulAut.conj g).toMonoidHom =
      ambientElementary D e 0 := mem_normalizer_iff_map_conj_eq.mp hg
  rw [he]
  exact ambientElementary_le_ambientSylow D e 0

omit [Finite G] in
private theorem M_le_xi_centralizer : ambientElementary D e 0 ≤
    centralizer ({D.a10ModelEmbedding e xi} : Set G) := by
  let := ambientElementary_isElementaryAbelian D e 0
  have hx : D.a10ModelEmbedding e xi ∈ ambientElementary D e 0 :=
    mem_map_of_mem _ (elementaryGenerators_mem 0 3)
  intro y hy
  exact mem_centralizer_singleton_iff.mpr (setLike_mul_comm hy hx)

omit [Finite G] in
private theorem xi_local_centralizer_card :
    Nat.card (D.centralizer ⊓ centralizer ({D.a10ModelEmbedding e xi} : Set G) : Subgroup G) = 96 := by
  have he : (centralizer ({xi} : Set H)).map (D.a10ModelEmbedding e) =
      D.centralizer ⊓ centralizer ({D.a10ModelEmbedding e xi} : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(e.symm y).property, mem_centralizer_singleton_iff.mpr ?_⟩
      simpa only [map_mul] using congrArg (D.a10ModelEmbedding e)
        (mem_centralizer_singleton_iff.mp hy)
    · rintro ⟨hx, hc⟩
      obtain ⟨y, rfl⟩ := (show x ∈ (D.a10ModelEmbedding e).range by
        rwa [D.a10ModelEmbedding_range e])
      refine ⟨y, mem_centralizer_singleton_iff.mpr ?_, rfl⟩
      apply D.a10ModelEmbedding_injective e
      simpa only [map_mul] using mem_centralizer_singleton_iff.mp hc
  rw [← he, card_map_of_injective (D.a10ModelEmbedding_injective e)]
  exact involution_centralizer_cards.2.2.2.2.2.1

private theorem exists_xi_overgroup
    (hxi : IsConj D.z (D.a10ModelEmbedding e xi)) :
    ∃ R : Subgroup G, Nat.card R = 64 ∧ ambientElementary D e 0 ≤ R ∧
      R ≤ centralizer ({D.a10ModelEmbedding e xi} : Set G) := by
  let C := centralizer ({D.a10ModelEmbedding e xi} : Set G)
  let M := ambientElementary D e 0
  have hMC : M ≤ C := M_le_xi_centralizer D e
  have hM : Nat.card (M.subgroupOf C) = 2 ^ 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hMC).toEquiv, ambientElementary_card]
    norm_num
  have hd : 2 ^ 6 ∣ Nat.card C := by
    rw [centralizer_card_of_isConj D hxi]
    norm_num
  obtain ⟨R, hR, hMR⟩ := Sylow.exists_subgroup_card_pow_prime_le 2 hd
    (M.subgroupOf C) hM (show 4 ≤ 6 by decide)
  refine ⟨R.map C.subtype, ?_, ?_, map_subtype_le _⟩
  · rw [card_map_of_injective C.subtype_injective, hR]
    norm_num
  · change M ≤ R.map C.subtype
    rw [← map_subgroupOf_eq_of_le hMC]
    exact map_mono hMR

/-- Held 2.7: the two xi choices cannot both fuse with pi under pi--mu nonfusion. -/
public theorem xi_separation_of_nonfusion [IsSimpleGroup G]
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e)) :
    ¬ (IsConj D.z (D.a10ModelEmbedding e xi) ∧
      IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * xi))) := by
  rintro ⟨hxi, hpiXi⟩
  obtain ⟨R, hR, hMR, hRC⟩ := exists_xi_overgroup D e hxi
  have hRN := le_normalizer_of_isPGroup_of_weakly_closed (ambientSylow D e)
    (ambientElementary D e 0) R (M_weakly_closed D e hfusion hxi hpiXi)
    (IsPGroup.of_card (p := 2) (n := 6) (by rw [hR]; norm_num)) hMR
  rw [M_normalizer_eq D e hfusion hxi hpiXi] at hRN
  have hd := card_dvd_of_le (le_inf hRN hRC)
  rw [hR, xi_local_centralizer_card D e] at hd
  norm_num at hd

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion
