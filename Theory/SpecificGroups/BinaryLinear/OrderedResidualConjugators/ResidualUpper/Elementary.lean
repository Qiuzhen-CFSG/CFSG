module

public import Theory.SpecificGroups.BinaryLinear.OrderedResidualConjugators.RootJoins
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.FullFlagSylow
public import Theory.GroupTheory.PResidual.NormalClosureCover

/-!
# The elementary subgroup of a binary minimal parabolic

The cubic actor and incident roots form a normal subgroup of the group
of allowed elementary matrices. Bridge roots are commutators of incident
roots; the elementary conjugation identities then prove relative normality.
The elementary group is the join of this subgroup with the upper root
subgroup. The latter lies in the full flag stabilizer and is a two-group,
so the two-residual of the elementary group lies in the explicit root node.

Identifying the elementary group with the literal minimal flag stabilizer
is a separate generation statement. No ambient normality is asserted.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.8.10(5), printed p.854 (PDF p.871), `refs/quasithin.pdf`.
-/

@[expose] public section

open Subgroup
namespace BinaryLinear.OrderedResidualConjugators.ResidualUpper
open OuterCyclic InvariantNodeActions
open scoped commutatorElement

private theorem root_chain {m : ℕ} (b : Basis m) (r k s : Fin (m + 1))
    (hrk : r ≠ k) (hrs : r ≠ s) (hks : k ≠ s) :
    root b r k hrk * root b k s hks * root b r k hrk =
      root b r s hrs * root b k s hks := by
  have h : CubicPairNormalizers.CoreAbsorption.root r k hrk 1 *
      CubicPairNormalizers.CoreAbsorption.root k s hks 1 *
      CubicPairNormalizers.CoreAbsorption.root r k hrk 1 =
      CubicPairNormalizers.CoreAbsorption.root r s hrs 1 *
      CubicPairNormalizers.CoreAbsorption.root k s hks 1 := by
    ext v t
    simp only [LinearEquiv.mul_apply, CubicPairNormalizers.CoreAbsorption.root_apply, mul_one]
    by_cases htr : t = r <;> by_cases htk : t = k <;>
      simp [htr, htk, hrk, hrk.symm, hrs.symm, hks.symm] <;> ring_nf <;>
      simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, add_zero]
  simpa only [map_mul, root] using congrArg (MulAut.conj b.equivFun.symm) h

private theorem root_commute {m : ℕ} (b : Basis m) (r s a c : Fin (m + 1))
    (hrs : r ≠ s) (hac : a ≠ c) (hsa : s ≠ a) (hcr : c ≠ r) :
    Commute (root b r s hrs) (root b a c hac) := by
  have h : Commute (CubicPairNormalizers.CoreAbsorption.root r s hrs 1)
      (CubicPairNormalizers.CoreAbsorption.root a c hac 1) := by
    change _ * _ = _ * _
    ext v t
    simp only [LinearEquiv.mul_apply, CubicPairNormalizers.CoreAbsorption.root_apply, mul_one]
    by_cases htr : t = r <;> by_cases hta : t = a <;>
      simp [htr, hta, hsa, hcr] <;> ring
  exact h.map (MulAut.conj b.equivFun.symm).toMonoidHom

private theorem root_square {m : ℕ} (b : Basis m) (r s : Fin (m + 1)) (hrs : r ≠ s) :
    root b r s hrs * root b r s hrs = 1 := by
  nth_rw 1 [← root_inv b r s hrs]
  exact inv_mul_cancel _

private theorem root_commutator {m : ℕ} (b : Basis m) (r k s : Fin (m + 1))
    (hrk : r ≠ k) (hrs : r ≠ s) (hks : k ≠ s) :
    ⁅root b r k hrk, root b k s hks⁆ = root b r s hrs := by
  rw [commutatorElement_def, root_inv, root_inv, root_chain]
  rw [mul_assoc, root_square, mul_one]

private theorem cubic_mem {m : ℕ} (b : Basis m) (i : Fin m) :
    cubic b i.castSucc i.succ (by simp [Fin.ext_iff]) ∈ rootNode b i :=
  subset_closure (Or.inl rfl)

private theorem incident_mem {m : ℕ} (b : Basis m) (i : Fin m)
    (r s : Fin (m + 1)) (hrs : r ≠ s) (h : Incident i r s) :
    root b r s hrs ∈ rootNode b i :=
  subset_closure (Or.inr ⟨r, s, hrs, h, rfl⟩)

/-- The missing bridge roots are commutators of two incident roots. -/
theorem bridge_root_mem {m : ℕ} (b : Basis m) (i : Fin m)
    (r s : Fin (m + 1)) (hrs : r ≠ s) (hr : r.val < i.val)
    (hs : i.val + 1 < s.val) : root b r s hrs ∈ rootNode b i := by
  have hrk : r ≠ i.castSucc := by intro he; have := congrArg Fin.val he; simp at this; omega
  have hks : i.castSucc ≠ s := by intro he; have := congrArg Fin.val he; simp at this; omega
  rw [← root_commutator b r i.castSucc s hrk hrs hks, commutatorElement_def]
  have h₁ := incident_mem b i r i.castSucc hrk (Or.inl ⟨hr, Or.inl rfl⟩)
  have h₂ := incident_mem b i i.castSucc s hks (Or.inr ⟨Or.inl rfl, hs⟩)
  exact (rootNode b i).mul_mem ((rootNode b i).mul_mem
    ((rootNode b i).mul_mem h₁ h₂) ((rootNode b i).inv_mem h₁))
    ((rootNode b i).inv_mem h₂)

private theorem crossing_mem {m : ℕ} (b : Basis m) (i : Fin m)
    (r s : Fin (m + 1)) (hrs : r ≠ s)
    (h : (r.val < i.val ∧ i.val ≤ s.val) ∨
      (r.val ≤ i.val + 1 ∧ i.val + 1 < s.val)) :
    root b r s hrs ∈ rootNode b i := by
  by_cases hs : s.val ≤ i.val + 1
  · apply incident_mem b i r s hrs
    refine Or.inl ⟨by omega, ?_⟩
    have hh : s.val = i.val ∨ s.val = i.val + 1 := by omega
    exact hh.elim (fun he => Or.inl (Fin.ext he)) (fun he => Or.inr (Fin.ext he))
  · by_cases hr : r.val < i.val
    · exact bridge_root_mem b i r s hrs hr (by omega)
    · apply incident_mem b i r s hrs
      refine Or.inr ⟨?_, by omega⟩
      have hh : r.val = i.val ∨ r.val = i.val + 1 := by omega
      exact hh.imp (fun he => Fin.ext he) (fun he => Fin.ext he)

private theorem root_conj_incident_mem {m : ℕ} (b : Basis m) (i : Fin m)
    (r s a c : Fin (m + 1)) (hrs : r ≠ s) (hac : a ≠ c)
    (hallow : r.val < s.val ∨ (r = i.succ ∧ s = i.castSucc))
    (hinc : Incident i a c) :
    root b r s hrs * root b a c hac * (root b r s hrs)⁻¹ ∈ rootNode b i := by
  have hi := incident_mem b i a c hac hinc
  have ha : (r.val < s.val ∨ (r.val = i.val + 1 ∧ s.val = i.val)) := by
    simpa only [Fin.ext_iff, Fin.val_succ, Fin.val_castSucc] using hallow
  have hc : (a.val < i.val ∧ (c.val = i.val ∨ c.val = i.val + 1)) ∨
      ((a.val = i.val ∨ a.val = i.val + 1) ∧ i.val + 1 < c.val) := by
    simpa only [Incident, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc] using hinc
  rw [root_inv]
  by_cases hsa : s = a
  · subst a
    have hrc : r ≠ c := by intro he; have := congrArg Fin.val he; omega
    rw [root_chain b r s c hrs hrc hac]
    apply (rootNode b i).mul_mem _ hi
    exact crossing_mem b i r c hrc (by omega)
  · by_cases hcr : c = r
    · subst c
      have has : a ≠ s := Ne.symm hsa
      have he : root b r s hrs * root b a r hac * root b r s hrs =
          root b a s has * root b a r hac := by
        have hh := root_chain b a r s hac has hrs
        have hc₂ := root_commute b r s a s hrs has hsa hrs.symm
        calc
          _ = root b r s hrs * (root b a r hac * root b r s hrs * root b a r hac) *
              root b a r hac := by simp only [mul_assoc, root_square, mul_one]
          _ = root b r s hrs * (root b a s has * root b r s hrs) *
              root b a r hac := by rw [hh]
          _ = root b a s has * root b a r hac := by
            rw [← mul_assoc, hc₂.eq]
            simp only [mul_assoc]
            rw [← mul_assoc (root b r s hrs), root_square, one_mul]
      rw [he]
      exact (rootNode b i).mul_mem (crossing_mem b i a s has (by omega)) hi
    · have hh := root_commute b r s a c hrs hac hsa hcr
      rw [hh.eq, mul_assoc, root_square, mul_one]
      exact hi

private theorem root_conj_cubic_mem {m : ℕ} (b : Basis m) (i : Fin m)
    (r s : Fin (m + 1)) (hrs : r ≠ s)
    (hallow : r.val < s.val ∨ (r = i.succ ∧ s = i.castSucc)) :
    root b r s hrs * cubic b i.castSucc i.succ (by simp [Fin.ext_iff]) *
      (root b r s hrs)⁻¹ ∈ rootNode b i := by
  have hi : i.castSucc ≠ i.succ := by simp [Fin.ext_iff]
  have hcinv := (rootNode b i).inv_mem (cubic_mem b i)
  simp only [cubic, mul_inv_rev, root_inv] at hcinv
  rcases hallow with hlt | ⟨rfl, rfl⟩
  · by_cases hcross : (r.val < i.val ∧ i.val ≤ s.val) ∨
        (r.val ≤ i.val + 1 ∧ i.val + 1 < s.val)
    · exact (rootNode b i).mul_mem ((rootNode b i).mul_mem
        (crossing_mem b i r s hrs hcross) (cubic_mem b i))
        ((rootNode b i).inv_mem (crossing_mem b i r s hrs hcross))
    · by_cases hblock : r.val = i.val ∧ s.val = i.val + 1
      · have hr : r = i.castSucc := Fin.ext hblock.1
        have hs : s = i.succ := Fin.ext hblock.2
        subst r s
        simpa only [cubic, root_inv, ← mul_assoc, root_square, one_mul] using hcinv
      · have hr₁ : r ≠ i.castSucc := by intro he; have := congrArg Fin.val he; simp at this; omega
        have hr₂ : r ≠ i.succ := by intro he; have := congrArg Fin.val he; simp at this; omega
        have hs₁ : s ≠ i.castSucc := by intro he; have := congrArg Fin.val he; simp at this; omega
        have hs₂ : s ≠ i.succ := by intro he; have := congrArg Fin.val he; simp at this; omega
        have hc := (root_commute b r s i.castSucc i.succ hrs hi hs₁ hr₂.symm).mul_right
          (root_commute b r s i.succ i.castSucc hrs hi.symm hs₂ hr₁.symm)
        change Commute (root b r s hrs) (cubic b i.castSucc i.succ hi) at hc
        rw [hc.eq, mul_inv_cancel_right]
        exact cubic_mem b i
  · simpa only [cubic, root_inv, mul_assoc, root_square, mul_one] using hcinv

private theorem involution_mem_normalizer_closure {G : Type*} [Group G]
    (S : Set G) (g : G) (hg : g⁻¹ = g)
    (h : ∀ x ∈ S, g * x * g⁻¹ ∈ closure S) :
    g ∈ normalizer (closure S : Set G) := by
  have hh : closure S ≤ (closure S).comap (MulAut.conj g).toMonoidHom :=
    (closure_le _).mpr h
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => hh hx
  · intro hx
    have ht := hh hx
    change g * (g * x * g⁻¹) * g⁻¹ ∈ closure S at ht
    have hg2 : g * g = 1 := by nth_rw 1 [← hg]; exact inv_mul_cancel g
    rw [hg, ← mul_assoc, ← mul_assoc, hg2, one_mul, mul_assoc, hg2, mul_one] at ht
    exact ht

/-- Every allowed elementary matrix normalizes the explicit residual subgroup. -/
theorem root_mem_normalizer {m : ℕ} (b : Basis m) (i : Fin m)
    (r s : Fin (m + 1)) (hrs : r ≠ s)
    (hallow : r.val < s.val ∨ (r = i.succ ∧ s = i.castSucc)) :
    root b r s hrs ∈ normalizer (rootNode b i : Set (LinearGroup (m + 1))) := by
  apply involution_mem_normalizer_closure (nodeGenerators b i) _ (root_inv b r s hrs)
  rintro g (hg | ⟨a, c, hac, hinc, rfl⟩)
  · rw [Set.mem_singleton_iff] at hg
    subst g
    exact root_conj_cubic_mem b i r s hrs hallow
  · exact root_conj_incident_mem b i r s a c hrs hac hallow hinc

/-- Elementary generators respecting all cuts other than the marked one. -/
noncomputable def elementaryParabolic {m : ℕ} (b : Basis m) (i : Fin m) :
    Subgroup (LinearGroup (m + 1)) :=
  closure {g | ∃ (r s : Fin (m + 1)) (hrs : r ≠ s),
    (r.val < s.val ∨ (r = i.succ ∧ s = i.castSucc)) ∧ g = root b r s hrs}

/-- The subgroup generated by all upper elementary matrices. -/
noncomputable def upperRoots {m : ℕ} (b : Basis m) :
    Subgroup (LinearGroup (m + 1)) :=
  closure {g | ∃ (r s : Fin (m + 1)) (hrs : r ≠ s),
    r.val < s.val ∧ g = root b r s hrs}

theorem elementaryParabolic_le {m : ℕ} (b : Basis m) (i : Fin m) :
    elementaryParabolic b i ≤ minimalParabolic b i := by
  apply (closure_le _).mpr
  rintro _ ⟨r, s, hrs, hallow, rfl⟩
  exact root_mem_minimalParabolic b i r s hrs hallow

theorem rootNode_le_elementaryParabolic {m : ℕ} (b : Basis m) (i : Fin m) :
    rootNode b i ≤ elementaryParabolic b i := by
  have hr (r s : Fin (m + 1)) (hrs : r ≠ s)
      (h : r.val < s.val ∨ (r = i.succ ∧ s = i.castSucc)) :
      root b r s hrs ∈ elementaryParabolic b i := subset_closure ⟨r, s, hrs, h, rfl⟩
  apply (closure_le _).mpr
  rintro g (hg | ⟨r, s, hrs, hinc, rfl⟩)
  · rw [Set.mem_singleton_iff] at hg
    rw [hg, cubic]
    exact (elementaryParabolic b i).mul_mem
      (hr _ _ _ (Or.inl (by simp))) (hr _ _ _ (Or.inr ⟨rfl, rfl⟩))
  · apply hr r s hrs
    left
    simp only [Incident, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc] at hinc
    omega

theorem upperRoots_le_elementaryParabolic {m : ℕ} (b : Basis m) (i : Fin m) :
    upperRoots b ≤ elementaryParabolic b i := by
  apply (closure_le _).mpr
  rintro _ ⟨r, s, hrs, hlt, rfl⟩
  exact subset_closure ⟨r, s, hrs, Or.inl hlt, rfl⟩

/-- The elementary parabolic normalizes the cubic-and-root subgroup. -/
theorem elementaryParabolic_le_normalizer {m : ℕ} (b : Basis m) (i : Fin m) :
    elementaryParabolic b i ≤ normalizer (rootNode b i : Set (LinearGroup (m + 1))) := by
  apply (closure_le _).mpr
  rintro _ ⟨r, s, hrs, hallow, rfl⟩
  exact root_mem_normalizer b i r s hrs hallow

/-- Normality is relative to the elementary parabolic, not ambient GL. -/
theorem rootNode_normal_elementaryParabolic {m : ℕ} (b : Basis m) (i : Fin m) :
    ((rootNode b i).subgroupOf (elementaryParabolic b i)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (rootNode_le_elementaryParabolic b i)).mpr
    (elementaryParabolic_le_normalizer b i)

/-- The lower simple root is recovered from the cubic and upper simple root. -/
theorem elementaryParabolic_eq_sup {m : ℕ} (b : Basis m) (i : Fin m) :
    elementaryParabolic b i = rootNode b i ⊔ upperRoots b := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨r, s, hrs, hallow, rfl⟩
    rcases hallow with hlt | ⟨rfl, rfl⟩
    · exact (le_sup_right : upperRoots b ≤ rootNode b i ⊔ upperRoots b)
        (subset_closure ⟨r, s, hrs, hlt, rfl⟩)
    · let H := rootNode b i ⊔ upperRoots b
      have hu : root b i.castSucc i.succ hrs.symm ∈ H :=
        (le_sup_right : upperRoots b ≤ H)
          (subset_closure ⟨_, _, _, by simp, rfl⟩)
      have hc : cubic b i.castSucc i.succ hrs.symm ∈ H :=
        (le_sup_left : rootNode b i ≤ H) (cubic_mem b i)
      change root b i.succ i.castSucc hrs ∈ H
      simpa only [cubic, inv_mul_cancel_left] using H.mul_mem (H.inv_mem hu) hc
  · exact sup_le (rootNode_le_elementaryParabolic b i) (upperRoots_le_elementaryParabolic b i)

theorem upperRoots_le_fullFlag {m : ℕ} (b : Basis m) :
    upperRoots b ≤ cutStabilizer b Set.univ := by
  apply (closure_le _).mpr
  rintro _ ⟨r, s, hrs, hlt, rfl⟩
  apply root_mem_cutStabilizer
  intro j _ hsj
  omega

theorem upperRoots_isPGroup {m : ℕ} (b : Basis m) : IsPGroup 2 (upperRoots b) :=
  (fullFlag_isPGroup b).of_injective (inclusion (upperRoots_le_fullFlag b))
    (inclusion_injective _)

/-- The quotient of the elementary parabolic by the explicit residual is a two-group. -/
theorem elementaryParabolic_residual_le {m : ℕ} (b : Basis m) (i : Fin m) :
    (pResidual 2 (elementaryParabolic b i)).map (elementaryParabolic b i).subtype ≤
      rootNode b i := by
  let K := elementaryParabolic b i
  let W := (rootNode b i).subgroupOf K
  let U := (upperRoots b).subgroupOf K
  let : W.Normal := rootNode_normal_elementaryParabolic b i
  have hsup : W ⊔ U = ⊤ := by
    apply map_injective K.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (rootNode_le_elementaryParabolic b i),
      map_subgroupOf_eq_of_le (upperRoots_le_elementaryParabolic b i),
      ← MonoidHom.range_eq_map, range_subtype]
    exact (elementaryParabolic_eq_sup b i).symm
  have hp : IsPGroup 2 (K ⧸ W) :=
    isPGroup_quotient_of_sup_eq_top W U (upperRoots_isPGroup b).comap_subtype hsup
  have hle : pResidual 2 K ≤ W := sInf_le ⟨inferInstance, hp⟩
  rintro _ ⟨x, hx, rfl⟩
  exact hle hx

/-- Residual recognition reduced to elementary generation of the actual flag stabilizer. -/
theorem nodeResidual_le_of_elementary_generation {m : ℕ} (b : Basis m) (i : Fin m)
    (hgen : minimalParabolic b i ≤ elementaryParabolic b i) :
    nodeResidual b i ≤ rootNode b i := by
  have he := le_antisymm hgen (elementaryParabolic_le b i)
  unfold nodeResidual
  rw [he]
  exact elementaryParabolic_residual_le b i

end BinaryLinear.OrderedResidualConjugators.ResidualUpper
