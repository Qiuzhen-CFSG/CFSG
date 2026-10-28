module

public import Theory.SpecificGroups.SymplecticFour.Flag
public import Theory.Representation.TwoDimensionalOddOrder
public import Theory.Quasithin
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# An invariant isotropic subspace for every symplectic two-local

For a nonidentity two-subgroup Q in characteristic two, take the radical of
its common fixed space. Its orthogonal complement is nonzero because the
natural matrix action is faithful. A nonzero fixed vector on that complement
lies in the radical. The normalizer preserves both the fixed space and its
orthogonal complement, hence preserves this nonzero totally isotropic space.
In dimension four the space has dimension at most two.

This is the fixed-space step of the symplectic parabolic coverage argument
used for the converse of Aschbacher–Smith, Theorem 0.1.2(1), printed pp.3–4
(repeated as Theorem 0.1.1(1), printed pp.481–482).
-/

@[expose] public section
noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.TwoLocalCover
variable {F : Type*} [Field F]

/-- The displayed symplectic form is alternating in every characteristic. -/
theorem form_alternating : (form F).IsAlt := by
  intro x
  simp [form_apply, mul_comm]

/-- The displayed symplectic form is nondegenerate. -/
theorem form_nondegenerate : (form F).Nondegenerate := by
  have hleft : (form F).SeparatingLeft := by
    intro x hx
    funext i
    cases i with
    | inl i =>
      have h := hx (Pi.single (.inr i) 1)
      simpa [form_apply, Pi.single_apply] using h
    | inr i => simpa using hx (e i)
  refine ⟨hleft, ?_⟩
  intro x hx
  apply hleft x
  intro y
  exact form_alternating.eq_iff.mpr (hx y)

/-- The common fixed space in the actual natural matrix action. -/
def fixedSpace (Q : Subgroup (Sp F)) : Submodule F (Vector F) :=
  { carrier := {x | ∀ q ∈ Q, q • x = x}
    zero_mem' := by intro q hq; exact map_zero (toLinear q)
    add_mem' := by
      intro x y hx hy q hq
      change toLinear q (x + y) = x + y
      rw [map_add, toLinear_apply, toLinear_apply, hx q hq, hy q hq]
    smul_mem' := by
      intro a x hx q hq
      change toLinear q (a • x) = a • x
      rw [map_smul, toLinear_apply, hx q hq] }

@[simp] theorem mem_fixedSpace (Q : Subgroup (Sp F)) (x : Vector F) :
    x ∈ fixedSpace Q ↔ ∀ q ∈ Q, q • x = x := by
  rfl

/-- The radical of the common fixed space, as an ambient subspace. -/
def fixedRadical (Q : Subgroup (Sp F)) : Submodule F (Vector F) :=
  fixedSpace Q ⊓ (form F).orthogonal (fixedSpace Q)

private theorem normalizer_le_fixedSpace_stabilizer (Q : Subgroup (Sp F)) :
    Subgroup.normalizer (Q : Set (Sp F)) ≤ stabilizer (fixedSpace Q) := by
  intro g hg
  rw [mem_stabilizer_iff]
  intro x hx
  rw [mem_fixedSpace] at hx ⊢
  intro q hq
  have hq' : g⁻¹ * q * g ∈ Q := (Subgroup.mem_normalizer_iff''.mp hg q).mp hq
  have h := congrArg (g • ·) (hx _ hq')
  simpa only [mul_smul, smul_inv_smul] using h

private theorem stabilizer_le_orthogonal_stabilizer (W : Submodule F (Vector F)) :
    stabilizer W ≤ stabilizer ((form F).orthogonal W) := by
  intro g hg
  rw [mem_stabilizer_iff]
  intro x hx y hy
  have hy' : g⁻¹ • y ∈ W := (mem_stabilizer_iff W g⁻¹).mp
    ((stabilizer W).inv_mem hg) y hy
  have h := preserves_form g (g⁻¹ • y) x
  rw [smul_inv_smul] at h
  exact h.trans (hx _ hy')

/-- Normalizing Q preserves the radical of its common fixed space. -/
theorem normalizer_le_fixedRadical_stabilizer (Q : Subgroup (Sp F)) :
    Subgroup.normalizer (Q : Set (Sp F)) ≤ stabilizer (fixedRadical Q) := by
  intro g hg
  have hfix := normalizer_le_fixedSpace_stabilizer Q hg
  have horth := stabilizer_le_orthogonal_stabilizer (fixedSpace Q) hfix
  rw [mem_stabilizer_iff] at hfix horth ⊢
  intro x hx
  exact ⟨hfix x hx.1, horth x hx.2⟩

private theorem fixedSpace_ne_top (Q : Subgroup (Sp F)) (hQ : Q ≠ ⊥) :
    fixedSpace Q ≠ ⊤ := by
  intro h
  apply hQ
  apply le_antisymm _ bot_le
  change ∀ q ∈ Q, q = 1
  intro q hq
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  have hx : Pi.single j (1 : F) ∈ fixedSpace Q := by rw [h]; trivial
  have he := congrFun ((mem_fixedSpace Q _).mp hx q hq) i
  simpa [smul_eq_mulVec, Matrix.mulVec_single, Pi.single_apply, Matrix.one_apply] using he

/-- The fixed-space radical is totally isotropic. -/
theorem fixedRadical_isotropic (Q : Subgroup (Sp F))
    (x y : Vector F) (hx : x ∈ fixedRadical Q) (hy : y ∈ fixedRadical Q) :
    form F x y = 0 := hy.2 x hx.1

/-- Total isotropy in symplectic four-space bounds the dimension by two. -/
theorem finrank_le_two_of_isotropic (W : Submodule F (Vector F))
    (hW : ∀ x ∈ W, ∀ y ∈ W, form F x y = 0) : Module.finrank F W ≤ 2 := by
  have hle : W ≤ (form F).orthogonal W := fun x hx y hy => hW y hy x hx
  have h := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal form_nondegenerate] at h
  have hdim : Module.finrank F (Vector F) = 4 := by simp [Vector]
  rw [hdim] at h
  omega

variable [Finite F] [CharP F 2]

/-- A nonidentity two-subgroup has a nonzero fixed-space radical. -/
theorem fixedRadical_ne_bot (Q : Subgroup (Sp F)) (hQ : Q ≠ ⊥)
    (hp : IsPGroup 2 Q) : fixedRadical Q ≠ ⊥ := by
  let W := (form F).orthogonal (fixedSpace Q)
  have hd : 0 < Module.finrank F W := by
    rw [LinearMap.BilinForm.finrank_orthogonal form_nondegenerate]
    exact Nat.sub_pos_of_lt (Submodule.finrank_lt (fixedSpace_ne_top Q hQ))
  let : Nontrivial W := Module.nontrivial_of_finrank_pos hd
  let ρ : Representation F Q (Vector F) := (Representation.symplecticNatural 2).comp Q.subtype
  have hW : ∀ q : Q, W ≤ W.comap (ρ q) := by
    intro q x hx
    have hn : (q : Sp F) ∈ Subgroup.normalizer (Q : Set (Sp F)) :=
      Subgroup.le_normalizer q.property
    have hs := stabilizer_le_orthogonal_stabilizer (fixedSpace Q)
      (normalizer_le_fixedSpace_stabilizer Q hn)
    exact (mem_stabilizer_iff W q).mp hs x hx
  have hc : ringChar F = 2 := ringChar.eq F 2
  obtain ⟨v, hv, hfix⟩ := Representation.pGroup_fix_nonzero_vector
    (F := F) (by omega) (by rwa [hc]) (ρ.subrepresentation W hW)
  have hvfix : v.val ∈ fixedSpace Q := by
    rw [mem_fixedSpace]
    intro q hq
    exact congrArg Subtype.val (hfix ⟨q, hq⟩)
  intro hbot
  have hvzero : v.val = 0 := by
    have hm : v.val ∈ fixedRadical Q := ⟨hvfix, v.property⟩
    rwa [hbot, Submodule.mem_bot] at hm
  exact hv (Subtype.ext hvzero)

/-- Every two-local stabilizes an actual nonzero totally isotropic subspace.
No local structure or coverage hypothesis enters this construction. -/
theorem twoLocal_stabilizes_isotropic (M : Subgroup (Sp F)) (hM : IsTwoLocal M) :
    ∃ W : Submodule F (Vector F), W ≠ ⊥ ∧ Module.finrank F W ≤ 2 ∧
      (∀ x ∈ W, ∀ y ∈ W, form F x y = 0) ∧ M ≤ stabilizer W := by
  obtain ⟨Q, hQ, hp, rfl⟩ := hM
  refine ⟨fixedRadical Q, fixedRadical_ne_bot Q hQ hp, ?_, ?_,
    normalizer_le_fixedRadical_stabilizer Q⟩
  · exact finrank_le_two_of_isotropic _ (fun x hx y hy => fixedRadical_isotropic Q x y hx hy)
  · exact fun x hx y hy => fixedRadical_isotropic Q x y hx hy

end Theory.SpecificGroups.SymplecticFour.TwoLocalCover
