module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.OmegaGeometry.KernelAction.Inner

/-!
# Realizing the factor-preserving Suzuki pair action

Restrict each literal factor marking to the aligned root preimage. Perfectness
of the component permits faithful descent of its automorphisms, and odd outer
index realizes each two-action by a root element. The second restriction uses
conjugation by the actual moving element retained in PairFactors. Multiplying
the commuting representatives realizes the entire orbit action inside T₀.
If the actor squares to one, genuine involution lifts give a square-one
representative in T₀ as well.

Source: Aschbacher–Smith, the paired Suzuki step of 13.6.6, printed p.927;
the earlier lifting input is I.2.2(4), printed pp.409–411. The elementary
center and lifting inputs remain explicit, including for Sz(8) covers.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups Theory.GroupTheory
noncomputable section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
variable {G : Type*} [Group G] {T K : Subgroup G} {v : G}

private def factorCover [Group.IsPerfect K] {m : ℕ}
    (e : (K ⧸ center K) ≃* SuzukiMatrixGroup m) :
    PerfectCentralCovering.Cover K (SuzukiMatrixGroup m) where
  toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
  isPerfect := inferInstance
  ker_le_center := by
    intro k hk
    apply (QuotientGroup.eq_one_iff k).mp
    exact e.injective (hk.trans e.map_one.symm)

private theorem factorCover_ker [Group.IsPerfect K] {m : ℕ}
    (e : (K ⧸ center K) ≃* SuzukiMatrixGroup m) :
    (factorCover e).toMonoidHom.ker = center K := by
  ext k
  change e (QuotientGroup.mk' (center K) k) = 1 ↔ k ∈ center K
  rw [← e.map_one, e.injective.eq_iff]
  exact QuotientGroup.eq_one_iff k

private theorem factorCover_lift [Group.IsPerfect K] {m : ℕ}
    (e : (K ⧸ center K) ≃* SuzukiMatrixGroup m)
    (hlift : ∀ q : K ⧸ center K, q ^ 2 = 1 →
      ∃ k : K, k ^ 2 = 1 ∧ QuotientGroup.mk' (center K) k = q)
    (q : SuzukiMatrixGroup m) (hq : q ^ 2 = 1) :
    ∃ k : K, k ^ 2 = 1 ∧ (factorCover e).toMonoidHom k = q := by
  obtain ⟨k, hk, he⟩ := hlift (e.symm q) (by rw [← map_pow, hq, map_one])
  refine ⟨k, hk, ?_⟩
  change e (QuotientGroup.mk' (center K) k) = q
  rw [he, e.apply_symm_apply]

private theorem conjugated_normalizer {d : Marking T K v} (c : PairFactors d)
    (x : Tv T v) (hn : (x : G) ∈ normalizer (K : Set G)) :
    (c.moving : G)⁻¹ * (x : G) * (c.moving : G) ∈ normalizer (K : Set G) := by
  have hfix := mem_normalizer_iff_map_conj_eq.mp hn
  have hsecond : (x : G) ∈ normalizer
      (K.map (MulAut.conj (c.moving : G)).toMonoidHom : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rcases c.permutation x with h | h
    · exact h.2
    · have he : K.map (MulAut.conj (c.moving : G)).toMonoidHom = K :=
        h.1.symm.trans hfix
      exact (c.moved (mem_normalizer_iff_map_conj_eq.mpr he)).elim
  rw [← map_equiv_normalizer_eq K (MulAut.conj (c.moving : G))] at hsecond
  obtain ⟨y, hy, he⟩ := hsecond
  have hg : (c.moving : G)⁻¹ * (x : G) * (c.moving : G) = y := by
    rw [← he]
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply,
      mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  rwa [hg]

private theorem map_conj {A B : Type*} [Group A] [Group B]
    (f : A →* B) (x y : A) : f (MulAut.conj x y) = MulAut.conj (f x) (f y) := by
  simp only [MulAut.conj_apply, map_mul, map_inv]

variable [Finite G]

/-- Factor-preserving two-actions on the literal component pair are realized inside T₀.
For square-one actors the representing element can be chosen square-one. -/
theorem PairFactors.normalizing_action_realization {d : Marking T K v} (c : PairFactors d)
    (P : Sylow 2 (Gv v)) (hP : (P : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hKG : K ≤ Gv v) (hK : IsComponent (Gv v) (K.subgroupOf (Gv v)))
    [IsElementaryAbelian 2 (center K)]
    (hlift : ∀ q : K ⧸ center K, q ^ 2 = 1 →
      ∃ k : K, k ^ 2 = 1 ∧ QuotientGroup.mk' (center K) k = q)
    (ha : ((Tv T v).subgroupOf (orbit T K v)).map d.quotientMap ≤
      (SuzukiRootSubgroup d.parameter).prod (SuzukiRootSubgroup d.parameter))
    (x : Tv T v) (hn : (x : G) ∈ normalizer (K : Set G)) :
    ∃ a : orbit T K v, (a : G) ∈ Tv T v ∧ orbitAction T K v x = MulAut.conj a ∧
      ((x : G) ^ 2 = 1 → a ^ 2 = 1) := by
  let : IsQuasisimple (K.subgroupOf (Gv v)) := hK.2
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKG).toMonoidHom) (subgroupOfEquivOfLe hKG).surjective
  let := c.orbit_center_elementary hKG hK
  have hR : IsPGroup 2 (Tv T v) := hP ▸ P.isPGroup'.map (Gv v).subtype
  have hpre := d.aligned_preimage_eq P hP hKG (IsElementaryAbelian.isPGroup 2 _) ha
  have hp₁ : (SuzukiRootSubgroup d.parameter).comap (factorCover c.firstEquiv).toMonoidHom =
      (Tv T v).subgroupOf K := by
    ext k
    have he := SetLike.ext_iff.mp hpre (firstEmbedding T K v k)
    change (d.quotientMap (firstEmbedding T K v k) ∈
      (SuzukiRootSubgroup d.parameter).prod (SuzukiRootSubgroup d.parameter)) ↔ _ at he
    rw [c.first_eq] at he
    change (c.firstEquiv (QuotientGroup.mk' (center K) k) ∈ SuzukiRootSubgroup d.parameter ∧
      (1 : SuzukiMatrixGroup d.parameter) ∈ SuzukiRootSubgroup d.parameter) ↔ (k : G) ∈ Tv T v at he
    change c.firstEquiv (QuotientGroup.mk' (center K) k) ∈ SuzukiRootSubgroup d.parameter ↔
      (k : G) ∈ Tv T v
    simpa only [one_mem, and_true] using he
  have hp₂ : (SuzukiRootSubgroup d.parameter).comap (factorCover c.secondEquiv).toMonoidHom =
      (Tv T v).subgroupOf K := by
    ext k
    have he := SetLike.ext_iff.mp hpre (secondEmbedding T K v c.moving k)
    change (d.quotientMap (secondEmbedding T K v c.moving k) ∈
      (SuzukiRootSubgroup d.parameter).prod (SuzukiRootSubgroup d.parameter)) ↔ _ at he
    rw [c.second_eq] at he
    change ((1 : SuzukiMatrixGroup d.parameter) ∈ SuzukiRootSubgroup d.parameter ∧
      c.secondEquiv (QuotientGroup.mk' (center K) k) ∈ SuzukiRootSubgroup d.parameter) ↔
      (c.moving : G) * (k : G) * (c.moving : G)⁻¹ ∈ Tv T v at he
    have hc : (c.moving : G) * (k : G) * (c.moving : G)⁻¹ ∈ Tv T v ↔ (k : G) ∈ Tv T v :=
      ((mem_normalizer_iff.mp ((Tv T v).le_normalizer c.moving.property)) (k : G)).symm
    exact (show c.secondEquiv (QuotientGroup.mk' (center K) k) ∈ SuzukiRootSubgroup d.parameter ↔
      (c.moving : G) * (k : G) * (c.moving : G)⁻¹ ∈ Tv T v from
        by simpa only [one_mem, true_and] using he).trans hc
  obtain ⟨k, hk, hak, hk2⟩ := KernelAction.cover_actor (Tv T v) K hR d.parameter d.positive
    (factorCover c.firstEquiv) (factorCover_ker c.firstEquiv) hp₁
    (factorCover_lift c.firstEquiv hlift) x x.property hn
  let z : G := (c.moving : G)⁻¹ * (x : G) * (c.moving : G)
  have hz : z ∈ Tv T v := (Tv T v).mul_mem
    ((Tv T v).mul_mem ((Tv T v).inv_mem c.moving.property) x.property) c.moving.property
  have hzn := conjugated_normalizer c x hn
  obtain ⟨l, hl, hal, hl2⟩ := KernelAction.cover_actor (Tv T v) K hR d.parameter d.positive
    (factorCover c.secondEquiv) (factorCover_ker c.secondEquiv) hp₂
    (factorCover_lift c.secondEquiv hlift) z hz hzn
  let a := firstEmbedding T K v k * secondEmbedding T K v c.moving l
  have hx₁ (s : K) : orbitAction T K v x (firstEmbedding T K v s) =
      MulAut.conj a (firstEmbedding T K v s) := by
    change _ = MulAut.conj (firstEmbedding T K v k * secondEmbedding T K v c.moving l) _
    rw [map_mul, MulAut.mul_apply]
    have hfix : MulAut.conj (secondEmbedding T K v c.moving l) (firstEmbedding T K v s) =
        firstEmbedding T K v s := by
      rw [MulAut.conj_apply]
      rw [(c.commute_factors hKG hK s l).symm.eq, mul_inv_cancel_right]
    rw [hfix]
    apply Subtype.ext
    have hh := congrArg (fun y : K => (y : G)) (DFunLike.congr_fun hak s)
    change (x : G) * (s : G) * (x : G)⁻¹ = (k : G) * (s : G) * (k : G)⁻¹
    exact hh
  have hx₂ (s : K) : orbitAction T K v x (secondEmbedding T K v c.moving s) =
      MulAut.conj a (secondEmbedding T K v c.moving s) := by
    change _ = MulAut.conj (firstEmbedding T K v k * secondEmbedding T K v c.moving l) _
    rw [map_mul, MulAut.mul_apply, ← map_conj]
    have hfix : MulAut.conj (firstEmbedding T K v k)
        (secondEmbedding T K v c.moving (MulAut.conj l s)) =
        secondEmbedding T K v c.moving (MulAut.conj l s) := by
      rw [MulAut.conj_apply]
      rw [(c.commute_factors hKG hK k (MulAut.conj l s)).eq, mul_inv_cancel_right]
    rw [hfix]
    apply Subtype.ext
    have hh := congrArg Subtype.val (DFunLike.congr_fun hal s)
    change z * (s : G) * z⁻¹ = (l : G) * (s : G) * (l : G)⁻¹ at hh
    have ht := congrArg (MulAut.conj (c.moving : G)) hh
    change (x : G) * ((c.moving : G) * (s : G) * (c.moving : G)⁻¹) * (x : G)⁻¹ =
      (c.moving : G) * ((l : G) * (s : G) * (l : G)⁻¹) * (c.moving : G)⁻¹
    simpa [z, MulAut.conj_apply, mul_assoc] using ht
  refine ⟨a, (Tv T v).mul_mem hk
    ((Tv T v).mul_mem ((Tv T v).mul_mem c.moving.property hl)
      ((Tv T v).inv_mem c.moving.property)), ?_, ?_⟩
  · apply MulEquiv.ext
    intro y
    obtain ⟨s, t, rfl⟩ := c.factorization hKG hK y
    rw [map_mul, map_mul, hx₁, hx₂]
  · intro hx2
    have hz2 : z ^ 2 = 1 := by
      have hh := congrArg (MulAut.conj (c.moving : G)⁻¹) hx2
      simpa only [map_pow, MulAut.conj_apply, inv_inv, mul_one, inv_mul_cancel] using hh
    change (firstEmbedding T K v k * secondEmbedding T K v c.moving l) ^ 2 = 1
    rw [(c.commute_factors hKG hK k l).mul_pow, ← map_pow, ← map_pow,
      hk2 hx2, hl2 hz2, map_one, map_one, mul_one]
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
