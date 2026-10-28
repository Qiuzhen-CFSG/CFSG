module

public import Stellmacher.PushingUp.AmalgamGraph
-- Intentional internal implementation split: reuse the private pullback and
-- neighbor parametrization proofs without enlarging the shared public boundary.
import all Stellmacher.PushingUp.AmalgamGraph

/-!
# Characteristic kernels for an arbitrary amalgamated subgroup

For the actual free amalgam `M *_S Hol(S)`, a subgroup of the edge group
invariant under both vertex factors pulls back to a characteristic subgroup
of `S` whose image is normal in `M`. The hypothesis excluding such nontrivial
characteristic subgroups therefore gives a faithful graph action. No Sylow
hypothesis on `S`, or finiteness hypothesis on `M`, is used in these results.

At the M-vertex, fixing all neighbors is exactly membership in the normal
core of `S` in `M`: the neighbor indexed by `m` is fixed by `x` precisely when
`m*x*m⁻¹` belongs to `S`. At the holomorph vertex the neighborhood kernel is
the whole embedded `S`, since `S` is normal in its holomorph. These comparisons
use the existing finite-factor neighbor parametrizations.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*,
Hypothesis 2.0 and Lemma 2.1(ii)--(iii), printed pp.854--855. These are the
characteristic-subgroup and local-kernel steps for the holomorph construction;
no tree acyclicity, rank-one recognition, or MS classification is asserted.
-/

public section

namespace Stellmacher.PushingUp.AmalgamGraph

open Subgroup

universe u
variable {M : Type u} [Group M] (S : Subgroup M)

/-- The characteristic-subgroup hypothesis excludes a common invariant
subgroup of the edge group, for arbitrary `S ≤ M`. -/
theorem no_nontrivial_common_invariant_of_characteristic
    (hP : ∀ K : Subgroup S, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map S.subtype).Normal)
    (N : Subgroup (FreeAmalgam S)) (hNS : N ≤ Sbar S)
    (hNM : IsInvariantBy N (Mbar S)) (hNH : IsInvariantBy N (Hbar S)) :
    N = ⊥ := by
  let K := N.comap (embedS S)
  have hKchar : K.Characteristic := comap_embedS_characteristic S N hNH
  have hKMnormal : (N.comap (embedM S)).Normal := comap_embedM_normal S N hNM
  have hKmap : K.map S.subtype = N.comap (embedM S) :=
    map_comap_embedS_subtype_eq_comap_embedM S N hNS
  have hKbot : K = ⊥ := by
    by_contra hne
    exact hP K hKchar hne (hKmap ▸ hKMnormal)
  apply le_bot_iff.mp
  intro n hn
  obtain ⟨s, rfl⟩ := hNS hn
  have hs : s ∈ K := hn
  have hsone : s = 1 := by simpa only [hKbot, mem_bot] using hs
  change embedS S s = 1
  rw [hsone, map_one]

/-- The actual coset graph action is faithful under the characteristic
hypothesis, with no Sylow requirement on the amalgamated subgroup. -/
theorem actionKernel_eq_bot_of_characteristic
    (hP : ∀ K : Subgroup S, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map S.subtype).Normal) : actionKernel S = ⊥ := by
  have hKM : actionKernel S ≤ Mbar S := by
    rw [← stabilizer_m_base S]
    exact fun _ hk => hk (mVertex S 1)
  have hKH : actionKernel S ≤ Hbar S := by
    rw [← stabilizer_h_base S]
    exact fun _ hk => hk (hVertex S 1)
  have hKS : actionKernel S ≤ Sbar S := by
    rw [← Mbar_inf_Hbar S]
    exact le_inf hKM hKH
  have hKN := actionKernel_normal S
  exact no_nontrivial_common_invariant_of_characteristic S hP (actionKernel S) hKS
    (fun k _ n hn => hKN.conj_mem n hn k)
    (fun k _ n hn => hKN.conj_mem n hn k)

private theorem embedM_mem_Hbar_iff (x : M) : embedM S x ∈ Hbar S ↔ x ∈ S := by
  constructor
  · intro hx
    have hxS : embedM S x ∈ Sbar S := by
      rw [← Mbar_inf_Hbar S]
      exact ⟨⟨x, rfl⟩, hx⟩
    obtain ⟨s, hs⟩ := hxS
    have hsx : (s : M) = x := embedM_injective S
      ((DFunLike.congr_fun (embedM_comp_subtype S) s).trans hs)
    exact hsx ▸ s.property
  · intro hx
    have hs : embedM S x ∈ Sbar S :=
      ⟨⟨x, hx⟩, (DFunLike.congr_fun (embedM_comp_subtype S) ⟨x, hx⟩).symm⟩
    exact (Mbar_inf_Hbar S).symm ▸ hs |>.2

private theorem mem_map_conj_inv_iff {G : Type*} [Group G]
    (A : Subgroup G) (x g : G) :
    g ∈ A.map (MulAut.conj x⁻¹).toMonoidHom ↔ x * g * x⁻¹ ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [mul_assoc] using ha
  · intro hg
    exact ⟨x * g * x⁻¹, hg, by simp [mul_assoc]⟩

/-- The first-neighborhood kernel at the M-vertex pulls back to the actual
normal core of the specified subgroup in `M`. -/
theorem neighborhoodKernel_m_base_comap_eq_normalCore [Finite M] :
    (neighborhoodKernel S (mVertex S 1)).comap (embedM S) = S.normalCore := by
  ext x
  change embedM S x ∈ neighborhoodKernel S (mVertex S 1) ↔
    ∀ m : M, m * x * m⁻¹ ∈ S
  constructor
  · intro hx m
    have hfix := hx.2 _ (neighborFromM S 1 m).property
    change embedM S x ∈ stabilizer S (hVertex S (embedM S m * 1)) at hfix
    rw [mul_one, stabilizer_hVertex, mem_map_conj_inv_iff] at hfix
    rw [← map_inv, ← map_mul, ← map_mul] at hfix
    exact (embedM_mem_Hbar_iff S _).mp hfix
  · intro hx
    refine ⟨?_, ?_⟩
    · rw [stabilizer_m_base]
      exact ⟨x, rfl⟩
    · intro e he
      obtain ⟨m, hm⟩ := neighborFromM_surjective S 1 ⟨e, he⟩
      have hme := congrArg Subtype.val hm
      change hVertex S (embedM S m * 1) = e at hme
      rw [← hme, mul_one, stabilizer_hVertex, mem_map_conj_inv_iff]
      rw [← map_inv, ← map_mul, ← map_mul]
      exact (embedM_mem_Hbar_iff S _).mpr (hx m)

private theorem Sbar_invariant_Hbar : IsInvariantBy (Sbar S) (Hbar S) := by
  rintro _ ⟨h, rfl⟩ _ ⟨s, rfl⟩
  let A : Subgroup (Holomorph S) := (SemidirectProduct.inl : S →* Holomorph S).range
  have hA : A.Normal := by
    dsimp only [A]
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  have hc : h * SemidirectProduct.inl s * h⁻¹ ∈ A :=
    hA.conj_mem _ ⟨s, rfl⟩ h
  obtain ⟨t, ht⟩ := hc
  refine ⟨t, ?_⟩
  calc
    embedS S t = embedH S (SemidirectProduct.inl t) :=
      (DFunLike.congr_fun (embedH_comp_inl S) t).symm
    _ = embedH S (h * SemidirectProduct.inl s * h⁻¹) := congrArg (embedH S) ht
    _ = embedH S h * embedS S s * (embedH S h)⁻¹ := by
      have hs : embedH S (SemidirectProduct.inl s) = embedS S s :=
        DFunLike.congr_fun (embedH_comp_inl S) s
      rw [map_mul, map_mul, map_inv, hs]

/-- Normality of `S` in its holomorph identifies the entire first-neighborhood
kernel at the holomorph vertex with the embedded edge group. -/
theorem neighborhoodKernel_h_base_eq_Sbar [Finite M] :
    neighborhoodKernel S (hVertex S 1) = Sbar S := by
  apply le_antisymm
  · intro n hn
    rw [← base_edge_stabilizer S]
    exact ⟨hn.2 _ (adjacent_symm S (base_adjacent S)), hn.1⟩
  · intro n hn
    have hnH : n ∈ Hbar S := ((Mbar_inf_Hbar S).symm ▸ hn).2
    refine ⟨by rwa [stabilizer_h_base], ?_⟩
    intro e he
    obtain ⟨h, hh⟩ := neighborFromH_surjective S 1 ⟨e, he⟩
    have hhe := congrArg Subtype.val hh
    change mVertex S (embedH S h * 1) = e at hhe
    rw [← hhe, mul_one, stabilizer_mVertex, mem_map_conj_inv_iff]
    have hc := Sbar_invariant_Hbar S (embedH S h) ⟨h, rfl⟩ n hn
    exact ((Mbar_inf_Hbar S).symm ▸ hc).1

end Stellmacher.PushingUp.AmalgamGraph
