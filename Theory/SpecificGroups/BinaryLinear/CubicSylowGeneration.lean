module

public import Theory.SpecificGroups.BinaryLinear.OrderedResidualConjugators
public import Theory.SpecificGroups.BinaryLinear.OrderedFlagGeneration
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.FullFlagSylow

/-!
# Index-three overgroups in binary linear groups

A minimal parabolic differs from the complete flag stabilizer at one cut.
The omitted two-coordinate block has three cosets: the identity, the adjacent
swap, and a lower transvection suffice to clear its lower pivot. The index
is odd and nontrivial, so it is exactly three. The minimal parabolics generate
the full linear group and each is preserved by every inner automorphism
preserving the original Sylow subgroup.

This supplies the binary-linear index calculation in the terminal construction
of Aschbacher--Smith 12.9.1, printed pp.863--864 of `refs/quasithin.pdf`.
It does not assert that an arbitrary Sylow-normalizing automorphism is inner.
-/

public section

open Subgroup
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
open BinaryLinear.OrderedResidualConjugators

namespace BinaryLinear.CubicSylowGeneration

private theorem mem_cutSpace_iff {m : ℕ} (b : Basis m) (i : Fin m)
    (v : Space (m + 1)) : v ∈ cutSpace b i ↔
      ∀ r : Fin (m + 1), i.val < r.val → b.repr v r = 0 := by
  rw [cutSpace, Module.Basis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_ofPred_eq]
  constructor
  · intro h r hr
    by_contra hv
    exact (Nat.not_le_of_gt hr) (h r hv)
  · intro h r hr
    by_contra hle
    exact hr (h r (Nat.lt_of_not_ge hle))

private theorem parabolic_column_support {m : ℕ} (b : Basis m) (i : Fin m)
    (g : LinearGroup (m + 1)) (hg : g ∈ minimalParabolic b i)
    (r : Fin (m + 1)) (hr : i.val + 1 < r.val) :
    b.repr (g (b i.castSucc)) r = 0 := by
  let j : Fin m := ⟨i.val + 1, by have := r.isLt; omega⟩
  have hj : j ∈ ({i}ᶜ : Set (Fin m)) := by
    change j ≠ i
    intro he
    have hh := congrArg Fin.val he
    change i.val + 1 = i.val at hh
    omega
  have hv := (mem_cutStabilizer_maps b {i}ᶜ g).mp hg j hj (b i.castSucc)
    ((basis_mem_cutSpace b j _).mpr (by change i.val ≤ i.val + 1; omega))
  exact (mem_cutSpace_iff b j _).mp hv r hr

private theorem borel_of_pivot {m : ℕ} (b : Basis m) (i : Fin m)
    (g : LinearGroup (m + 1)) (hg : g ∈ minimalParabolic b i)
    (hp : b.repr (g (b i.castSucc)) i.succ = 0) :
    g ∈ cutStabilizer b Set.univ := by
  rw [mem_cutStabilizer_maps]
  intro j _ v hv
  by_cases hji : j = i
  · subst j
    have hle : cutSpace b i ≤ (cutSpace b i).comap g.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, rfl⟩
      change k.val ≤ i.val at hk
      change g (b k) ∈ cutSpace b i
      by_cases hki : k.val = i.val
      · have he : k = i.castSucc := Fin.ext hki
        subst k
        apply (mem_cutSpace_iff b i _).mpr
        intro r hr
        by_cases hrs : r = i.succ
        · subst r; exact hp
        · exact parabolic_column_support b i g hg r (by
            have hne : r.val ≠ i.val + 1 := fun h => hrs (Fin.ext h)
            omega)
      · let j : Fin m := ⟨k.val, by have := i.isLt; omega⟩
        have hj : j ∈ ({i}ᶜ : Set (Fin m)) := by
          change j ≠ i
          exact fun he => hki (congrArg Fin.val he)
        have hmem := (mem_cutStabilizer_maps b {i}ᶜ g).mp hg j hj (b k)
          ((basis_mem_cutSpace b j k).mpr le_rfl)
        exact (cutSpace_mono b (show j ≤ i from hk)) hmem
    exact hle hv
  · exact (mem_cutStabilizer_maps b {i}ᶜ g).mp hg j hji v hv

private theorem root_repr {m : ℕ} (b : Basis m)
    (r s : Fin (m + 1)) (hrs : r ≠ s) (v : Space (m + 1)) (t : Fin (m + 1)) :
    b.repr (root b r s hrs v) t = b.repr v t + if t = r then b.repr v s else 0 := by
  have he : root b r s hrs = transvection (b r) (b.coord s) (by simp [hrs]) := by
    apply b.ext'
    intro j
    rw [root_basis]
    change (if j = s then b j + b r else b j) = b j + b.coord s (b j) • b r
    by_cases h : j = s <;> simp [h, Module.Basis.coord_apply]
  rw [he]
  change b.repr (v + b.coord s v • b r) t = _
  simp [Module.Basis.coord_apply, Finsupp.single_apply, eq_comm]

private theorem swap_repr {m : ℕ} (b : Basis m) (i : Fin m)
    (v : Space (m + 1)) (t : Fin (m + 1)) :
    b.repr (adjacentSwap b i v) t = b.repr v (Equiv.swap i.castSucc i.succ t) := by
  let f := (b.coord t).comp (adjacentSwap b i).toLinearMap
  let h := b.coord (Equiv.swap i.castSucc i.succ t)
  have he : f = h := by
    apply b.ext
    intro j
    simp only [f, h, LinearMap.comp_apply, LinearEquiv.coe_coe, adjacentSwap_basis,
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    have he : j = Equiv.swap i.castSucc i.succ t ↔ Equiv.swap i.castSucc i.succ j = t :=
      Equiv.swap_apply_eq_iff.symm
    simp only [he]
  exact LinearMap.congr_fun he v

private theorem three_representatives {m : ℕ} (b : Basis m) (i : Fin m) :
    ∃ r : Fin 3 → minimalParabolic b i, ∀ g : minimalParabolic b i,
      ∃ k, (r k : LinearGroup (m + 1)) * g.val ∈ cutStabilizer b Set.univ := by
  let s : minimalParabolic b i := ⟨adjacentSwap b i, adjacentSwap_mem_minimalParabolic b i⟩
  let l : minimalParabolic b i := ⟨root b i.succ i.castSucc (by simp [Fin.ext_iff]),
    root_mem_minimalParabolic b i _ _ _ (Or.inr ⟨rfl,rfl⟩)⟩
  refine ⟨![1, s, l], ?_⟩
  intro g
  by_cases hz : b.repr (g.val (b i.castSucc)) i.succ = 0
  · refine ⟨0, ?_⟩
    simpa using borel_of_pivot b i g.val g.property hz
  · by_cases hx : b.repr (g.val (b i.castSucc)) i.castSucc = 0
    · refine ⟨1, ?_⟩
      apply borel_of_pivot b i _ (s * g).property
      change b.repr (adjacentSwap b i (g.val (b i.castSucc))) i.succ = 0
      rw [swap_repr, Equiv.swap_apply_right]
      exact hx
    · refine ⟨2, ?_⟩
      have hp := root_repr b i.succ i.castSucc (by simp [Fin.ext_iff])
        (g.val (b i.castSucc)) i.succ
      rw [if_pos rfl] at hp
      have h1 : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
      rw [h1 _ hz, h1 _ hx, show (1 + 1 : ZMod 2) = 0 by decide] at hp
      exact borel_of_pivot b i _ (l * g).property hp

/-- A binary minimal parabolic has index three over its complete flag stabilizer. -/
theorem minimalParabolic_index {m : ℕ} (b : Basis m) (i : Fin m) :
    (cutStabilizer b Set.univ).relIndex (minimalParabolic b i) = 3 := by
  let _ : Finite (LinearGroup (m + 1)) :=
    Finite.of_injective (fun g : LinearGroup (m + 1) => (g : Space (m + 1) → Space (m + 1)))
      DFunLike.coe_injective
  let B := cutStabilizer b Set.univ
  let P := minimalParabolic b i
  have hBP : B ≤ P := (cutStabilizer_le_iff b Set.univ {i}ᶜ).mpr (Set.subset_univ _)
  obtain ⟨r,hr⟩ := three_representatives b i
  let f : Fin 3 → P ⧸ B.subgroupOf P := fun k => QuotientGroup.mk (r k)⁻¹
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k,hk⟩ := hr g
    refine ⟨k, ?_⟩
    apply QuotientGroup.eq.mpr
    change ((r k)⁻¹)⁻¹ * g ∈ B.subgroupOf P
    rw [inv_inv]
    exact hk
  have hle : B.relIndex P ≤ 3 := by
    change Nat.card (P ⧸ B.subgroupOf P) ≤ 3
    simpa using Nat.card_le_card_of_surjective f hf
  have hne : B.relIndex P ≠ 1 := by
    intro he
    have hs := (relIndex_eq_one.mp he) (adjacentSwap_mem_minimalParabolic b i)
    exact (adjacentSwap_mem_cutStabilizer b Set.univ i).mp hs (Set.mem_univ _)
  obtain ⟨S,hBS⟩ := (fullFlag_isPGroup b).exists_le_sylow
  obtain ⟨c,hc⟩ := sylow_eq_cutStabilizer S
  have hS : (S : Subgroup (LinearGroup (m + 1))) = B := by
    rw [hc]
    exact cutStabilizer_eq_of_fullFlag_le b c Set.univ (hc ▸ hBS)
  have hodd : ¬ 2 ∣ B.relIndex P := by
    rw [← hS]
    exact (S.subtype (hS ▸ hBP)).not_dvd_index
  have hpos : 0 < B.relIndex P := Nat.pos_of_ne_zero index_ne_zero_of_finite
  change B.relIndex P = 3
  omega

/-- Cubic overgroups fixed by all Sylow-preserving inner automorphisms generate. -/
theorem sylow_inner_invariant_cubic_generation {m : ℕ} (hm : 1 ≤ m)
    (S : Sylow 2 (LinearGroup (m + 1))) (M : Subgroup (LinearGroup (m + 1)))
    (hlocal : ∀ J : Subgroup (LinearGroup (m + 1)),
      (S : Subgroup (LinearGroup (m + 1))) ≤ J → (S : Subgroup _).relIndex J = 3 →
      (∀ a : MulAut (LinearGroup (m + 1)), a ∈ MulAut.innerSubgroup _ →
        (S : Subgroup _).map a.toMonoidHom = S → J.map a.toMonoidHom = J) → J ≤ M) :
    M = ⊤ := by
  obtain ⟨b,hb⟩ := sylow_eq_cutStabilizer S
  apply top_unique
  rw [← iSup_minimalParabolic_eq_top hm b]
  apply iSup_le
  intro i
  apply hlocal (minimalParabolic b i)
  · rw [hb]
    exact (cutStabilizer_le_iff b Set.univ {i}ᶜ).mpr (Set.subset_univ _)
  · rw [hb]
    exact minimalParabolic_index b i
  · rintro a ⟨g,rfl⟩ ha
    rw [hb] at ha
    exact inner_fixes_minimalParabolic b g ha i

end BinaryLinear.CubicSylowGeneration
