module
public import Theory.Representation.SLHigherNaturalFirstCohomology.Elementary

/-!
# Generating flag pairs for the binary classical upper bound

The actual coordinate flags with omitted simple roots `{0,2}` and `{1}`
in dimension four, or `{0,3}` and `{1,2}` in dimension five, generate SL.
Upper transvections lie in both stabilizers. The omitted dimensions supply
all negative simple root groups, and the three-index elementary matrix
relation supplies every remaining negative root group. Gaussian elimination
then gives the whole special linear group.

Flag stabilization is defined by the zero entries below each cut, in both
the matrix and its inverse. `preservesCut_iff` identifies this condition with
the actual action on the coordinate subspace. The canonical binary SL-to-PSL
isomorphism transports the flags into the projective model. Transport to a
subgroup `L` and adjoining `T` gives an explicit generating family when
`L ⊔ T = ⊤`.

This supplies the generation part of the flag route to Aschbacher--Smith,
*The Classification of Quasithin Groups*, E.1.14(1), printed p.214, citing
Aschbacher (1982), Lemma 4.7. It does not assert an E-generation bound.
Compatibility with the ambient Sylow subgroup, graph automorphisms, and the
local quotient bounds remain separate proof obligations.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.BinaryUpper
open Matrix
open Representation.OneCohomology.SLHigherNatural
abbrev SL (d : ℕ) := Matrix.SpecialLinearGroup (Fin d) (ZMod 2)

def PreservesCut {d : ℕ} (k : ℕ) (g : SL d) : Prop :=
  ∀ i j : Fin d, k ≤ i.val → j.val < k → g.val i j = 0

private theorem preservesCut_one (d k : ℕ) : PreservesCut k (1 : SL d) := by
  intro i j hi hj
  have hij : i ≠ j := by intro h; subst j; omega
  simp [hij]

private theorem preservesCut_mul {d k : ℕ} {g h : SL d}
    (hg : PreservesCut k g) (hh : PreservesCut k h) : PreservesCut k (g * h) := by
  intro i j hi hj
  change (g.val * h.val) i j = 0
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hl : l.val < k
  · rw [hg i l hi hl, zero_mul]
  · rw [hh l j (Nat.le_of_not_gt hl) hj, mul_zero]

/-- The entry condition is exactly preservation of the coordinate subspace
spanned by the first `k` standard vectors, for the actual column action. -/
theorem preservesCut_iff {d : ℕ} (k : ℕ) (g : SL d) :
    PreservesCut k g ↔ ∀ v : Fin d → ZMod 2,
      (∀ j : Fin d, k ≤ j.val → v j = 0) →
      ∀ i : Fin d, k ≤ i.val → (g.val.mulVec v) i = 0 := by
  constructor
  · intro hg v hv i hi
    change ∑ j, g.val i j * v j = 0
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j.val < k
    · rw [hg i j hi hj, zero_mul]
    · rw [hv j (Nat.le_of_not_gt hj), mul_zero]
  · intro hg i j hi hj
    have hv : ∀ l : Fin d, k ≤ l.val → (Pi.single j (1 : ZMod 2) : Fin d → ZMod 2) l = 0 := by
      intro l hl
      have hlj : l ≠ j := by intro h; subst l; omega
      simp [Ne.symm hlj]
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hg _ hv i hi

/-- The stabilizer of the coordinate subspaces of the dimensions in `cuts`. -/
def flagStabilizer (d : ℕ) (cuts : Set ℕ) : Subgroup (SL d) where
  carrier := {g | ∀ k ∈ cuts, PreservesCut k g ∧ PreservesCut k g⁻¹}
  one_mem' := by intro k _; simpa using And.intro (preservesCut_one d k) (preservesCut_one d k)
  mul_mem' := by
    intro g h hg hh k hk
    exact ⟨preservesCut_mul (hg k hk).1 (hh k hk).1,
      by simpa using preservesCut_mul (hh k hk).2 (hg k hk).2⟩
  inv_mem' := by intro g hg k hk; simpa using (hg k hk).symm

/-- The parabolic obtained by omitting the dimensions `r + 1` for roots in `J`. -/
def parabolic (d : ℕ) (J : Set ℕ) : Subgroup (SL d) :=
  flagStabilizer d {k | 0 < k ∧ k < d ∧ k - 1 ∉ J}

private theorem preservesCut_transvection {d : ℕ} (i j : Fin d) (hij : i ≠ j)
    (c : ZMod 2) (k : ℕ) (hcut : j.val < k → i.val < k) :
    PreservesCut k (SpecialLinearGroup.transvection hij c) := by
  intro r s hr hs
  have hrs : r ≠ s := by intro h; subst s; omega
  have hentry : ¬ (r = i ∧ s = j) := by rintro ⟨rfl, rfl⟩; have := hcut hs; omega
  simp only [SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply,
    if_neg hrs, zero_add, Matrix.single_apply]
  split_ifs with h
  · exact False.elim (hentry ⟨h.1.symm, h.2.symm⟩)
  · rfl

/-- A transvection belongs to a flag stabilizer whenever it crosses none of its cuts. -/
theorem transvection_mem_flag {d : ℕ} (cuts : Set ℕ) (i j : Fin d) (hij : i ≠ j)
    (c : ZMod 2) (hcut : ∀ k ∈ cuts, j.val < k → i.val < k) :
    SpecialLinearGroup.transvection hij c ∈ flagStabilizer d cuts := by
  intro k hk
  refine ⟨preservesCut_transvection i j hij c k (hcut k hk), ?_⟩
  rw [SpecialLinearGroup.transvection_inv]
  exact preservesCut_transvection i j hij (-c) k (hcut k hk)

/-- Every standard flag stabilizer contains the upper root groups. -/
theorem upper_mem_parabolic {d : ℕ} (J : Set ℕ) (i j : Fin d) (hij : i < j)
    (c : ZMod 2) : SpecialLinearGroup.transvection (ne_of_lt hij) c ∈ parabolic d J := by
  apply transvection_mem_flag
  intro k _ hj
  have := hij
  omega

/-- The negative simple root group is present precisely at an omitted flag dimension. -/
theorem simpleLower_mem_parabolic {d : ℕ} (J : Set ℕ) (i j : Fin d)
    (hij : i.val = j.val + 1) (hj : j.val ∈ J) (c : ZMod 2) :
    SpecialLinearGroup.transvection (show i ≠ j by intro h; subst j; omega) c ∈
      parabolic d J := by
  apply transvection_mem_flag
  intro k hk hjk
  by_contra h
  have hkval : k = j.val + 1 := by omega
  exact hk.2.2 (by simpa [hkval] using hj)

/-- Upper root groups and all negative simple root groups generate binary SL. -/
theorem eq_top_of_root_groups {d : ℕ} [Nontrivial (Fin d)] (H : Subgroup (SL d))
    (hu : ∀ (i j : Fin d) (hij : i < j) (c : ZMod 2),
      SpecialLinearGroup.transvection (ne_of_lt hij) c ∈ H)
    (hl : ∀ (i j : Fin d) (hij : i.val = j.val + 1) (c : ZMod 2),
      SpecialLinearGroup.transvection (show i ≠ j by intro h; subst j; omega) c ∈ H) :
    H = ⊤ := by
  have hlow : ∀ (n : ℕ) (i j : Fin d) (hji : j < i), i.val - j.val = n →
      ∀ c : ZMod 2, SpecialLinearGroup.transvection (ne_of_gt hji) c ∈ H := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i j hji hn c
      by_cases he : i.val = j.val + 1
      · exact hl i j he c
      · let k : Fin d := ⟨i.val - 1, by omega⟩
        have hik : i.val = k.val + 1 := by dsimp [k]; omega
        have hkj : j < k := by dsimp [k]; omega
        have hki : i ≠ k := by intro he; have := congrArg Fin.val he; omega
        have hkH := ih (k.val - j.val) (by dsimp [k]; omega) k j hkj rfl (1 : ZMod 2)
        have hiH := hl i k hik c
        have heq := transvection_chain hki (ne_of_gt hkj) (ne_of_gt hji) c (1 : ZMod 2)
        rw [mul_one] at heq
        have hp := H.mul_mem hiH hkH
        rw [heq] at hp
        exact (H.mul_mem_cancel_left hkH).mp ((H.mul_mem_cancel_right hiH).mp hp)
  apply top_unique
  intro g _
  apply transvection_induction (fun g => g ∈ H) ?_ (fun _ _ => H.mul_mem) g
  intro i j hij c
  rcases lt_or_gt_of_ne hij with h | h
  · exact hu i j h c
  · exact hlow (i.val - j.val) i j h rfl c

/-- Two standard flags generate when their omitted simple roots cover the diagram. -/
theorem parabolic_sup_eq_top {d : ℕ} [Nontrivial (Fin d)] (J K : Set ℕ)
    (hcover : ∀ r : ℕ, r + 1 < d → r ∈ J ∨ r ∈ K) :
    parabolic d J ⊔ parabolic d K = ⊤ := by
  apply eq_top_of_root_groups
  · intro i j hij c
    exact (show parabolic d J ≤ parabolic d J ⊔ parabolic d K from le_sup_left)
      (upper_mem_parabolic J i j hij c)
  · intro i j hij c
    rcases hcover j.val (by omega) with h | h
    · exact (show parabolic d J ≤ parabolic d J ⊔ parabolic d K from le_sup_left)
        (simpleLower_mem_parabolic J i j hij h c)
    · exact (show parabolic d K ≤ parabolic d J ⊔ parabolic d K from le_sup_right)
        (simpleLower_mem_parabolic K i j hij h c)

/-- The two diagram-orbit parabolics for the graph automorphism of SL₄(2). -/
theorem four_flag_pair_generates :
    parabolic 4 {0, 2} ⊔ parabolic 4 {1} = ⊤ := by
  apply parabolic_sup_eq_top
  intro r hr
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- The two diagram-orbit parabolics for the graph automorphism of SL₅(2). -/
theorem five_flag_pair_generates :
    parabolic 5 {0, 3} ⊔ parabolic 5 {1, 2} = ⊤ := by
  apply parabolic_sup_eq_top
  intro r hr
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega
abbrev PSL (d : ℕ) := Matrix.ProjectiveSpecialLinearGroup (Fin d) (ZMod 2)

/-- The same flag subgroup in the actual projective group, using the canonical
binary quotient isomorphism. -/
noncomputable def projectiveParabolic (d : ℕ) (J : Set ℕ) : Subgroup (PSL d) :=
  (parabolic d J).map
    (Representation.OneCohomology.SLHigherNatural.binaryProjectiveEquiv d).toMonoidHom

/-- Canonical transport of the generating flag pair to PSL. -/
theorem projectiveParabolic_sup_eq_top {d : ℕ} [Nontrivial (Fin d)] (J K : Set ℕ)
    (hcover : ∀ r : ℕ, r + 1 < d → r ∈ J ∨ r ∈ K) :
    projectiveParabolic d J ⊔ projectiveParabolic d K = ⊤ := by
  rw [projectiveParabolic, projectiveParabolic, ← Subgroup.map_sup,
    parabolic_sup_eq_top J K hcover]
  exact Subgroup.map_top_of_surjective _
    (Representation.OneCohomology.SLHigherNatural.binaryProjectiveEquiv d).surjective

variable {G : Type*} [Group G]

/-- The transported flag subgroup together with the specified ambient Sylow
subgroup. Local analysis must prove the bounds for this actual join. -/
noncomputable def ambientFlag {d : ℕ} (L T : Subgroup G) (e : L ≃* PSL d)
    (J : Set ℕ) : Subgroup G :=
  (projectiveParabolic d J).map (L.subtype.comp e.symm.toMonoidHom) ⊔ T

theorem le_ambientFlag {d : ℕ} (L T : Subgroup G) (e : L ≃* PSL d) (J : Set ℕ) :
    T ≤ ambientFlag L T e J := le_sup_right

/-- Generation survives transport to the simple subgroup and adjoining `T`.
No normalization or automorphism classification is assumed in this identity. -/
theorem ambientFlag_sup_eq_top {d : ℕ} [Nontrivial (Fin d)]
    (L T : Subgroup G) (e : L ≃* PSL d) (hLT : L ⊔ T = ⊤) (J K : Set ℕ)
    (hcover : ∀ r : ℕ, r + 1 < d → r ∈ J ∨ r ∈ K) :
    ambientFlag L T e J ⊔ ambientFlag L T e K = ⊤ := by
  have hr : (⊤ : Subgroup (PSL d)).map (L.subtype.comp e.symm.toMonoidHom) = L := by
    rw [← Subgroup.map_map, Subgroup.map_top_of_surjective _ e.symm.surjective]
    ext x
    constructor
    · rintro ⟨y, _, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  unfold ambientFlag
  rw [sup_sup_sup_comm, sup_idem, ← Subgroup.map_sup,
    projectiveParabolic_sup_eq_top J K hcover, hr, hLT]

/-- The two end nodes of the binary linear diagram. -/
def outerRoots (d : ℕ) : Set ℕ := {0, d - 2}

/-- The nodes strictly between the two end nodes. -/
def middleRoots (d : ℕ) : Set ℕ := {r | 0 < r ∧ r + 2 < d}

/-- The explicit pair of ambient overgroups used for the binary upper bound.
For `d = 4` its flags have dimensions `{2}` and `{1,3}`; for `d = 5`
the dimensions are `{2,3}` and `{1,4}`. -/
noncomputable def binaryFlagFamily {d : ℕ} (L T : Subgroup G) (e : L ≃* PSL d) :
    Set (Subgroup G) :=
  {ambientFlag L T e (outerRoots d), ambientFlag L T e (middleRoots d)}

/-- Every member of the explicit flag family contains `T`. -/
theorem le_of_mem_binaryFlagFamily {d : ℕ} (L T : Subgroup G) (e : L ≃* PSL d)
    {H : Subgroup G} (hH : H ∈ binaryFlagFamily L T e) : T ≤ H := by
  rcases hH with rfl | hH
  · exact le_ambientFlag L T e _
  · obtain rfl := hH
    exact le_ambientFlag L T e _

/-- The explicit flag family generates the ambient group whenever `G = LT`.
The isomorphism must still be chosen compatibly with `T` to obtain local bounds. -/
theorem binaryFlagFamily_generates {d : ℕ} [Nontrivial (Fin d)]
    (L T : Subgroup G) (e : L ≃* PSL d) (hLT : L ⊔ T = ⊤) :
    sSup (binaryFlagFamily L T e) = ⊤ := by
  rw [binaryFlagFamily, sSup_pair]
  apply ambientFlag_sup_eq_top L T e hLT
  intro r hr
  simp only [outerRoots, middleRoots, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_ofPred_eq]
  omega

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.BinaryUpper
