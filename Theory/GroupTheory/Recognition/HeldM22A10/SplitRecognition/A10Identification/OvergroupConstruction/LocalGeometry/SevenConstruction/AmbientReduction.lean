module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootGeometry
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootActions
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.Group

/-!
# Removing the inverted root factor from Held's crossing centralizer

Given the internal root-centralizer factor W and a compatible labeling of
its symmetric extension, an element centralizing both `uv` and `mu'` lies
in W: its cyclic factor is simultaneously of order dividing three and two.
This proves that the full ambient crossing centralizer is isomorphic to
the even permutations centralizing two disjoint marked transpositions.
The same internal factorization proves the parity-dependent action on `uv`.

These are conditional source reductions. The root geometry and the compatible
labeling remain explicit hypotheses; no existence or recognition is asserted.
Source: Held (1969), Lemmas 5.4–5.5 and the crossing calculation in 5.11,
DOI 10.1215/ijm/1256053756, pp.237–239.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (L : Source.SixLocalData D e) (R : RootGeometry D e L)

public theorem W_le_root_centralizer : R.W ≤ centralizer ({L.u * L.v} : Set G) := by
  rw [R.centralizer_root]
  exact le_sup_right

public theorem centralizer_root_mu'_le_W :
    centralizer ({L.u * L.v, mu' D e} : Set G) ≤ R.W := by
  intro y hy
  have hr : y ∈ centralizer ({L.u * L.v} : Set G) :=
    centralizer_le (by simp) hy
  have hs : Commute (mu' D e) y := hy _ (by simp)
  have hn : zpowers (L.u * L.v) ≤ normalizer (R.W : Set G) := by
    apply zpowers_le.mpr
    apply centralizer_le_normalizer (R.W : Set G)
    intro w hw
    exact mem_centralizer_singleton_iff.mp (W_le_root_centralizer D e L R hw)
  rw [R.centralizer_root] at hr
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hn] at hr
  obtain ⟨z, hz, w, hw, rfl⟩ := hr
  let f := MulAut.conj (mu' D e)
  have hfz : f z = z⁻¹ := by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hz
    rw [map_zpow]
    have hfroot : f (L.u * L.v) = (L.u * L.v)⁻¹ := by
      simpa only [f, MulAut.conj_apply, coordinate_inv D e 2 (by decide)] using
        mu'_root D e L
    rw [hfroot, inv_zpow]
  have hfw : f w ∈ R.W :=
    (mem_normalizer_iff.mp R.mu'_normalizes w).mp hw
  have hfix : f (z * w) = z * w := by
    change mu' D e * (z * w) * (mu' D e)⁻¹ = _
    rw [hs.eq, mul_inv_cancel_right]
  have heq : z⁻¹ * f w = z * w := by rw [← hfz, ← map_mul, hfix]
  have hzsq : z * z = f w * w⁻¹ := by
    calc
      _ = z * (z⁻¹ * f w) * w⁻¹ := by rw [heq]; group
      _ = _ := by group
  have hz2 : z ^ 2 = 1 := by
    rw [pow_two]
    exact disjoint_def.mp R.root_disjoint (mul_mem hz hz)
      (hzsq ▸ R.W.mul_mem hfw (R.W.inv_mem hw))
  have hz3 : z ^ 3 = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    simpa only [root_order D e L] using orderOf_dvd_of_mem_zpowers hz
  have hz1 : z = 1 := by
    simpa only [pow_succ, hz2, one_mul] using hz3
  change z * w ∈ R.W
  rw [hz1, one_mul]
  exact hw

public theorem root_triple_eq_W_pair :
    centralizer ({L.u * L.v, mu' D e, xi D e} : Set G) =
      R.W ⊓ centralizer ({mu' D e, xi D e} : Set G) := by
  apply le_antisymm
  · intro y hy
    exact ⟨centralizer_root_mu'_le_W D e L R (centralizer_le
      (by
        intro a ha
        rcases ha with rfl | rfl
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)) hy),
      centralizer_le (by simp) hy⟩
  · intro y hy a ha
    rcases ha with rfl | rfl | rfl
    · exact (mem_centralizer_singleton_iff.mp
        (W_le_root_centralizer D e L R hy.1)).symm
    · exact hy.2 _ (by simp)
    · exact hy.2 _ (by simp)

variable (M : SevenMarking D e L R)

public theorem evenPairCentralizer_map : evenPairCentralizer.map M.embedding =
    R.W ⊓ centralizer ({mu' D e, xi D e} : Set G) := by
  apply le_antisymm
  · rintro y ⟨p, hp, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← M.even_range]
      exact ⟨p, hp.1, rfl⟩
    · intro a ha
      rcases ha with rfl | rfl
      · rw [← M.mark_mu', ← map_mul, ← map_mul, hp.2 _ (by simp)]
      · rw [← M.mark_xi, ← map_mul, ← map_mul, hp.2 _ (by simp)]
  · intro y hy
    obtain ⟨p, hp, rfl⟩ := (show y ∈ (alternatingGroup (Fin 7)).map M.embedding by
      rw [M.even_range]; exact hy.1)
    refine ⟨p, ⟨hp, ?_⟩, rfl⟩
    intro a ha
    apply M.injective
    simp only [map_mul]
    rcases ha with rfl | rfl
    · rw [M.mark_mu']; exact hy.2 _ (by simp)
    · rw [M.mark_xi]; exact hy.2 _ (by simp)

public theorem root_action (p : Perm (Fin 7)) :
    M.embedding p * (L.u * L.v) * (M.embedding p)⁻¹ =
      if Perm.sign p = 1 then L.u * L.v else (L.u * L.v)⁻¹ := by
  have heven (q : Perm (Fin 7)) (hq : Perm.sign q = 1) :
      M.embedding q * (L.u * L.v) * (M.embedding q)⁻¹ = L.u * L.v := by
    have hW : M.embedding q ∈ R.W := by
      rw [← M.even_range]
      exact ⟨q, Perm.mem_alternatingGroup.mpr hq, rfl⟩
    rw [mem_centralizer_singleton_iff.mp (W_le_root_centralizer D e L R hW),
      mul_inv_cancel_right]
  by_cases hp : Perm.sign p = 1
  · rw [if_pos hp]
    exact heven p hp
  · rw [if_neg hp]
    have hpneg : Perm.sign p = -1 := (Int.units_eq_one_or _).resolve_left hp
    have hq : Perm.sign (swap 0 1 * p) = 1 := by
      rw [Perm.sign_mul, Perm.sign_swap (by decide), hpneg, neg_mul_neg, one_mul]
    have hfix := heven (swap 0 1 * p) hq
    have heq : M.embedding p = mu' D e * M.embedding (swap 0 1 * p) := by
      rw [← M.mark_mu', ← map_mul, ← mul_assoc, Equiv.swap_mul_self, one_mul]
    rw [heq]
    calc
      _ = mu' D e * (M.embedding (swap 0 1 * p) * (L.u * L.v) *
          (M.embedding (swap 0 1 * p))⁻¹) * (mu' D e)⁻¹ := by group
      _ = (L.u * L.v)⁻¹ := by
        rw [hfix, coordinate_inv D e 2 (by decide), mu'_root D e L]

public noncomputable def crossingToEvenPair : Source.crossingCentralizer D e L ≃*
    evenPairCentralizer :=
  (crossingToRoot D e L).trans ((MulEquiv.subgroupCongr
    (root_triple_eq_W_pair D e L R)).trans
      ((MulEquiv.subgroupCongr (evenPairCentralizer_map D e L R M).symm).trans
        (evenPairCentralizer.equivMapOfInjective M.embedding M.injective).symm))

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction
