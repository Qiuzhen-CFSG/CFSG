module

public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.InvariantSubspaces
public import Theory.SpecificGroups.BinaryLinear.CubicPairNormalizers.CoreAbsorption.Elementary
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Coordinates for successive binary parabolic residuals

The residual at a node is taken inside its literal minimal flag stabilizer
and then embedded in the full linear group. Adjacent basis swaps belong to
these stabilizers. A cubic actor on the two-dimensional diagonal block and
the root groups incident with that block belong to the two-residual, by
the cubic commutator identities. Their explicit generated subgroup is a
lower bound for the residual. The companion `RootJoins` module proves
successive generation for these explicit subgroups. Identifying them with
the full residual is a separate obligation.

The shared root interface permits the residual calculation and the
calculation of successive joins to be proved independently. In particular
it does not replace the rank-one residual C₃ by the whole Levi S₃.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.8.10(5), printed p.854 (PDF p.871), `refs/quasithin.pdf`.
The swap calculation adapts the private proof in
`InvariantNodeActions.FlagGeometry.InvariantSubspaces`.
-/

@[expose] public section

open Subgroup
namespace BinaryLinear.OrderedResidualConjugators
open OuterCyclic InvariantNodeActions
open scoped commutatorElement

/-- The embedded O² of the actual minimal parabolic. -/
noncomputable def nodeResidual {m : ℕ} (b : Basis m) (i : Fin m) :
    Subgroup (LinearGroup (m + 1)) :=
  (pResidual 2 (minimalParabolic b i)).map (minimalParabolic b i).subtype

/-- The first r embedded residuals, with zero-based node labels. -/
noncomputable def initialResiduals {m : ℕ} (b : Basis m) (r : ℕ) :
    Subgroup (LinearGroup (m + 1)) :=
  ⨆ i : Fin m, ⨆ (_ : i.val < r), nodeResidual b i

/-- Swap the two coordinates straddling the omitted cut. -/
noncomputable def adjacentSwap {m : ℕ} (b : Basis m) (i : Fin m) :
    LinearGroup (m + 1) := b.equiv b (Equiv.swap i.castSucc i.succ)

@[simp] theorem adjacentSwap_basis {m : ℕ} (b : Basis m) (i : Fin m)
    (k : Fin (m + 1)) :
    adjacentSwap b i (b k) = b (Equiv.swap i.castSucc i.succ k) :=
  Module.Basis.equiv_apply _ _ _ _

theorem adjacentSwap_mem_cutStabilizer {m : ℕ} (b : Basis m)
    (cuts : Set (Fin m)) (i : Fin m) :
    adjacentSwap b i ∈ cutStabilizer b cuts ↔ i ∉ cuts := by
  classical
  constructor
  · intro h hi
    have hv := ((mem_cutStabilizer b cuts _).mp h i hi (b i.castSucc)).mpr
      ((basis_mem_cutSpace b i _).mpr le_rfl)
    rw [adjacentSwap_basis, Equiv.swap_apply_left, basis_mem_cutSpace] at hv
    simp at hv
  · intro hi
    rw [mem_cutStabilizer_maps]
    intro j hj v hv
    have hji : j ≠ i := fun he => hi (he ▸ hj)
    have hle : cutSpace b j ≤ (cutSpace b j).comap (adjacentSwap b i).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, rfl⟩
      change adjacentSwap b i (b k) ∈ cutSpace b j
      rw [adjacentSwap_basis, basis_mem_cutSpace]
      by_cases hki : k = i.castSucc
      · subst k
        rw [Equiv.swap_apply_left]
        simp only [Fin.val_succ]
        have : j.val ≠ i.val := fun h => hji (Fin.ext h)
        change i.val ≤ j.val at hk
        omega
      · by_cases hks : k = i.succ
        · subst k
          rw [Equiv.swap_apply_right]
          simp only [Fin.val_castSucc]
          change i.val + 1 ≤ j.val at hk
          omega
        · rw [Equiv.swap_apply_of_ne_of_ne hki hks]
          exact hk
    exact hle hv

theorem adjacentSwap_mem_minimalParabolic {m : ℕ} (b : Basis m) (i : Fin m) :
    adjacentSwap b i ∈ minimalParabolic b i := by
  exact (adjacentSwap_mem_cutStabilizer b {i}ᶜ i).mpr (by simp)

@[simp] theorem adjacentSwap_inv {m : ℕ} (b : Basis m) (i : Fin m) :
    (adjacentSwap b i)⁻¹ = adjacentSwap b i := by
  apply inv_eq_of_mul_eq_one_left
  apply b.ext'
  intro k
  change adjacentSwap b i (adjacentSwap b i (b k)) = b k
  simp only [adjacentSwap_basis, Equiv.swap_apply_self]

/-- The root adding coordinate s into coordinate r in the marked basis. -/
noncomputable def root {m : ℕ} (b : Basis m) (r s : Fin (m + 1)) (hrs : r ≠ s) :
    LinearGroup (m + 1) :=
  MulAut.conj b.equivFun.symm
    (CubicPairNormalizers.CoreAbsorption.root r s hrs 1)

/-- A cubic actor on a marked pair of coordinates. -/
noncomputable def cubic {m : ℕ} (b : Basis m) (r s : Fin (m + 1)) (hrs : r ≠ s) :
    LinearGroup (m + 1) := root b r s hrs * root b s r hrs.symm

theorem cubic_cube {m : ℕ} (b : Basis m) (r s : Fin (m + 1)) (hrs : r ≠ s) :
    cubic b r s hrs ^ 3 = 1 := by
  have h := congrArg (MulAut.conj b.equivFun.symm)
    (CubicPairNormalizers.CoreAbsorption.cubic_cube r s hrs)
  simpa only [map_pow, map_one, CubicPairNormalizers.CoreAbsorption.cubic,
    map_mul, cubic, root] using h

theorem root_basis {m : ℕ} (b : Basis m) (r s : Fin (m + 1)) (hrs : r ≠ s)
    (k : Fin (m + 1)) :
    root b r s hrs (b k) = if k = s then b k + b r else b k := by
  classical
  change b.equivFun.symm
    (CubicPairNormalizers.CoreAbsorption.root r s hrs 1 (b.equivFun (b k))) = _
  have he : b.equivFun (b k) = Pi.single k 1 := by
    ext j
    simp [Pi.single_apply, eq_comm]
  rw [he]
  have hr : CubicPairNormalizers.CoreAbsorption.root r s hrs 1 (Pi.single k 1) =
      if k = s then Pi.single k 1 + Pi.single r 1 else Pi.single k 1 := by
    ext j
    by_cases hk : k = s <;> simp [CubicPairNormalizers.CoreAbsorption.root_apply,
      Pi.single_apply, hk, eq_comm]
  rw [hr]
  split_ifs <;> simp [map_add, Module.Basis.equivFun_symm_apply]

/-- A root preserves the partial flag exactly when its source and target
respect every retained cut. Only the sufficient direction is needed here. -/
theorem root_mem_cutStabilizer {m : ℕ} (b : Basis m) (cuts : Set (Fin m))
    (r s : Fin (m + 1)) (hrs : r ≠ s)
    (h : ∀ j ∈ cuts, s.val ≤ j.val → r.val ≤ j.val) :
    root b r s hrs ∈ cutStabilizer b cuts := by
  rw [mem_cutStabilizer_maps]
  intro j hj v hv
  have hle : cutSpace b j ≤ (cutSpace b j).comap (root b r s hrs).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, hk, rfl⟩
    change root b r s hrs (b k) ∈ cutSpace b j
    rw [root_basis]
    split_ifs with hks
    · subst k
      exact (cutSpace b j).add_mem ((basis_mem_cutSpace b j s).mpr hk)
        ((basis_mem_cutSpace b j r).mpr (h j hj hk))
    · exact (basis_mem_cutSpace b j k).mpr hk
  exact hle hv

/-- Roots above the diagonal and the one allowed lower simple root lie in
the minimal parabolic. -/
theorem root_mem_minimalParabolic {m : ℕ} (b : Basis m) (i : Fin m)
    (r s : Fin (m + 1)) (hrs : r ≠ s)
    (h : r.val < s.val ∨ (r = i.succ ∧ s = i.castSucc)) :
    root b r s hrs ∈ minimalParabolic b i := by
  apply root_mem_cutStabilizer
  intro j hj hsj
  rcases h with h | ⟨rfl, rfl⟩
  · omega
  · have hji : j ≠ i := by simpa using hj
    have hne : j.val ≠ i.val := fun he => hji (Fin.ext he)
    change i.val ≤ j.val at hsj
    change i.val + 1 ≤ j.val
    omega

/-- The incident roots go into or out of the two-dimensional Levi block.
Neither simple root inside that block is included. -/
def Incident {m : ℕ} (i : Fin m) (r s : Fin (m + 1)) : Prop :=
  (r.val < i.val ∧ (s = i.castSucc ∨ s = i.succ)) ∨
    ((r = i.castSucc ∨ r = i.succ) ∧ i.val + 1 < s.val)

/-- Explicit generators, independent of the abstract residual operation. -/
noncomputable def nodeGenerators {m : ℕ} (b : Basis m) (i : Fin m) :
    Set (LinearGroup (m + 1)) :=
  {cubic b i.castSucc i.succ (by simp [Fin.ext_iff])} ∪
    {g | ∃ (r s : Fin (m + 1)) (hrs : r ≠ s), Incident i r s ∧ g = root b r s hrs}

noncomputable def rootNode {m : ℕ} (b : Basis m) (i : Fin m) :
    Subgroup (LinearGroup (m + 1)) := closure (nodeGenerators b i)

noncomputable def initialRootNodes {m : ℕ} (b : Basis m) (r : ℕ) :
    Subgroup (LinearGroup (m + 1)) :=
  ⨆ i : Fin m, ⨆ (_ : i.val < r), rootNode b i

private theorem marked_root_mem_residual {m : ℕ} (b : Basis m)
    (c : Fin (m + 1) → ℕ) (P : Subgroup (LinearGroup (m + 1)))
    (hP : ∀ r s (hrs : r ≠ s), c r ≤ c s → root b r s hrs ∈ P)
    (r s : Fin (m + 1)) (hrs : r ≠ s) (hcross : c r < c s)
    (hpartner : (∃ k, k ≠ r ∧ c k = c r) ∨ (∃ k, k ≠ s ∧ c k = c s)) :
    root b r s hrs ∈ (pResidual 2 P).map P.subtype := by
  let : Finite (LinearGroup (m + 1)) := Finite.of_injective
    (fun g : LinearGroup (m + 1) => (g : Space (m + 1) → Space (m + 1)))
    DFunLike.coe_injective
  let e : MulAut (LinearGroup (m + 1)) := MulAut.conj b.equivFun.symm
  have hh := CubicPairNormalizers.CoreAbsorption.root_mem_residual c
    (P.comap e.toMonoidHom) (fun r s hrs hle => hP r s hrs hle)
    r s hrs hcross hpartner
  have hm := mem_map_of_mem e.toMonoidHom hh
  rw [map_embedded_pResidual,
    map_comap_eq_self_of_surjective e.surjective] at hm
  exact hm

private def nodeLabel {m : ℕ} (i : Fin m) (r : Fin (m + 1)) : ℕ :=
  if r.val = i.val + 1 then i.val else r.val

private theorem nodeLabel_le {m : ℕ} (i : Fin m) (r s : Fin (m + 1))
    (hrs : r ≠ s) (h : nodeLabel i r ≤ nodeLabel i s) :
    r.val < s.val ∨ (r = i.succ ∧ s = i.castSucc) := by
  have hne : r.val ≠ s.val := fun he => hrs (Fin.ext he)
  by_cases hr : r.val = i.val + 1
  · by_cases hs : s.val = i.val
    · exact Or.inr ⟨Fin.ext hr, Fin.ext hs⟩
    · left
      simp only [nodeLabel, hr, ↓reduceIte] at h
      split_ifs at h <;> omega
  · left
    simp only [nodeLabel, hr, ↓reduceIte] at h
    split_ifs at h <;> omega

/-- The odd-order diagonal actor belongs to O², not merely to the parabolic. -/
theorem cubic_mem_nodeResidual {m : ℕ} (b : Basis m) (i : Fin m) :
    cubic b i.castSucc i.succ (by simp [Fin.ext_iff]) ∈ nodeResidual b i := by
  have hi : i.castSucc ≠ i.succ := by simp [Fin.ext_iff]
  let P := minimalParabolic b i
  let x : P := ⟨cubic b i.castSucc i.succ hi, P.mul_mem
    (root_mem_minimalParabolic b i _ _ hi (Or.inl (by simp)))
    (root_mem_minimalParabolic b i _ _ hi.symm (Or.inr ⟨rfl, rfl⟩))⟩
  refine mem_map.mpr ⟨x, mem_pResidual_of_orderOf_coprime ?_, rfl⟩
  exact (by decide : Nat.Coprime 2 3).of_dvd_right
    (orderOf_dvd_of_pow_eq_one (show x ^ 3 = 1 from
      Subtype.ext (cubic_cube b _ _ hi)))

/-- Cubic commutators absorb each incident root into the actual residual. -/
theorem incident_root_mem_nodeResidual {m : ℕ} (b : Basis m) (i : Fin m)
    (r s : Fin (m + 1)) (hrs : r ≠ s) (h : Incident i r s) :
    root b r s hrs ∈ nodeResidual b i := by
  apply marked_root_mem_residual b (nodeLabel i) (minimalParabolic b i)
    (fun r s hrs hle => root_mem_minimalParabolic b i r s hrs (nodeLabel_le i r s hrs hle))
  · rcases h with ⟨hri, rfl | rfl⟩ | ⟨rfl | rfl, his⟩ <;>
      simp only [nodeLabel, Fin.val_castSucc, Fin.val_succ] <;>
      split_ifs <;> omega
  · have hi : i.castSucc ≠ i.succ := by simp [Fin.ext_iff]
    rcases h with ⟨hri, rfl | rfl⟩ | ⟨rfl | rfl, his⟩
    · exact Or.inr ⟨i.succ, hi.symm, by simp [nodeLabel]⟩
    · exact Or.inr ⟨i.castSucc, hi, by simp [nodeLabel]⟩
    · exact Or.inl ⟨i.succ, hi.symm, by simp [nodeLabel]⟩
    · exact Or.inl ⟨i.castSucc, hi, by simp [nodeLabel]⟩

/-- The explicit root subgroup is a proved lower bound for O²(Pᵢ). -/
theorem rootNode_le_nodeResidual {m : ℕ} (b : Basis m) (i : Fin m) :
    rootNode b i ≤ nodeResidual b i := by
  apply (closure_le _).mpr
  rintro g (hg | ⟨r, s, hrs, h, rfl⟩)
  · rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact cubic_mem_nodeResidual b i
  · exact incident_root_mem_nodeResidual b i r s hrs h

theorem initialRootNodes_le_initialResiduals {m : ℕ} (b : Basis m) (r : ℕ) :
    initialRootNodes b r ≤ initialResiduals b r := by
  exact iSup_mono fun i => iSup_mono fun _ => rootNode_le_nodeResidual b i

end BinaryLinear.OrderedResidualConjugators
