module

public import Theory.GroupTheory.PGroup.NormalizedSylowConjugation
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

/-!
# A Sylow bound from TI subgroups and small displacements

Let a finite group M act faithfully by automorphisms on a finite group V.
Suppose W is nontrivial and its distinct M-translates intersect trivially.
If every displacement of a Sylow p-subgroup P lies in Z ≤ W and one
translate of W is disjoint from W, then |P| ≤ |Z|. No commutativity or
normality of W in V is required.

The actors whose displacements lie in W form the kernel of the action of
its stabilizer on the right cosets of W. Conjugation transports these
kernels, and disjoint subgroups give disjoint kernels by faithfulness.
Sylow conjugacy inside the stabilizer of a disjoint translate therefore
makes its intersection with P trivial. TI then makes the P-orbit of any
nonidentity element of that translate free. All its displacements lie in Z,
so the displacement function embeds P into Z.

This is the finite action argument used to exclude the covered Suzuki
configuration under the genuine ambient hypotheses preceding the
Goldschmidt–O'Nan application in Aschbacher–Smith 16.5.1, printed p.1194
of the combined manuscript of 1 March 2004. Construction of those ambient
hypotheses and the covered exclusion itself remain with the source theorem.
-/

@[expose] public section

open Subgroup
open scoped Pointwise

namespace Theory.GroupAction.TISylowDisplacement

variable {M V : Type*} [Group M] [Group V] [MulDistribMulAction M V]

/-- The actors preserving each right coset W * v. -/
def cosetKernel (W : Subgroup V) : Subgroup M where
  carrier := {a | ∀ v : V, (a • v) * v⁻¹ ∈ W}
  one_mem' := by intro v; simp
  mul_mem' := by
    intro a b ha hb v
    have hh := W.mul_mem (ha (b • v)) (hb v)
    simpa only [mul_smul, mul_assoc, inv_mul_cancel_left] using hh
  inv_mem' := by
    intro a ha v
    have hh := W.inv_mem (ha (a⁻¹ • v))
    simpa only [smul_inv_smul, mul_inv_rev, inv_inv] using hh

/-- An actor preserving every right coset of W stabilizes W itself. -/
theorem cosetKernel_le_stabilizer (W : Subgroup V) :
    cosetKernel (M := M) W ≤ MulAction.stabilizer M W := by
  intro a ha
  rw [MulAction.mem_stabilizer_iff]
  apply le_antisymm
  · rintro v ⟨w, hw, rfl⟩
    change a • w ∈ W
    have hh := W.mul_mem (ha w) hw
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh
  · intro v hv
    refine ⟨a⁻¹ • v, ?_, smul_inv_smul a v⟩
    change a⁻¹ • v ∈ W
    have hh := W.mul_mem ((cosetKernel (M := M) W).inv_mem ha v) hv
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh

/-- Conjugating an actor transports its displacement bound to the translated subgroup. -/
theorem conjugate_mem_cosetKernel (W : Subgroup V) (g : M) {a : M}
    (ha : a ∈ cosetKernel (M := M) W) :
    g * a * g⁻¹ ∈ cosetKernel (M := M) (g • W) := by
  intro v
  have hh := Subgroup.smul_mem_pointwise_smul _ g W (ha (g⁻¹ • v))
  simpa only [mul_smul, smul_mul', smul_inv', smul_inv_smul] using hh

/-- The displacement condition is equivalent under conjugation and subgroup translation. -/
theorem conjugate_mem_cosetKernel_iff (W : Subgroup V) (g a : M) :
    g * a * g⁻¹ ∈ cosetKernel (M := M) (g • W) ↔ a ∈ cosetKernel (M := M) W := by
  constructor
  · intro ha
    have hh := conjugate_mem_cosetKernel (g • W) g⁻¹ ha
    simpa only [inv_smul_smul, inv_inv, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel_right, inv_mul_cancel, mul_one] using hh
  · exact conjugate_mem_cosetKernel W g

/-- The subgroup stabilizer normalizes the kernel of its action on right cosets. -/
theorem stabilizer_le_normalizer_cosetKernel (W : Subgroup V) :
    MulAction.stabilizer M W ≤ Subgroup.normalizer (cosetKernel (M := M) W : Set M) := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg
  apply Subgroup.mem_normalizer_iff.mpr
  intro a
  have hh := (conjugate_mem_cosetKernel_iff W g a).symm
  rwa [hg] at hh

/-- Faithfulness makes the displacement kernels of disjoint subgroups disjoint. -/
theorem disjoint_cosetKernel [FaithfulSMul M V] (W U : Subgroup V)
    (hWU : Disjoint W U) :
    Disjoint (cosetKernel (M := M) W) (cosetKernel (M := M) U) := by
  apply Subgroup.disjoint_def.mpr
  intro a haW haU
  apply eq_of_smul_eq_smul (α := V)
  intro v
  have hh := Subgroup.disjoint_def.mp hWU (haW v) (haU v)
  simpa only [one_smul] using mul_inv_eq_one.mp hh


/-- A Sylow subgroup whose displacements lie in W meets the stabilizer of a disjoint translate trivially. -/
theorem inf_stabilizer_eq_bot_of_disjoint_translate
    [Finite M] [FaithfulSMul M V] {p : ℕ} [Fact p.Prime]
    (P : Sylow p M) (W : Subgroup V)
    (hP : (P : Subgroup M) ≤ cosetKernel (M := M) W)
    (g : M) (hdisj : Disjoint W (g • W)) :
    (P : Subgroup M) ⊓ MulAction.stabilizer M (g • W) = ⊥ := by
  let K : Subgroup M := MulAction.stabilizer M (g • W)
  let Q : Sylow p M := g • P
  have hQ : (Q : Subgroup M) ≤ cosetKernel (M := M) (g • W) := by
    change (P : Subgroup M).map (MulAut.conj g).toMonoidHom ≤ _
    rintro a ⟨b, hb, rfl⟩
    exact conjugate_mem_cosetKernel W g (hP hb)
  have hQK : (Q : Subgroup M) ≤ K := hQ.trans (cosetKernel_le_stabilizer _)
  obtain ⟨c, hc, hconj⟩ := IsPGroup.exists_conj_le_sylow_of_normalized
    Q K ((P : Subgroup M) ⊓ K) (hQK.trans K.le_normalizer)
    P.isPGroup'.to_inf_left inf_le_right
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro a ha
  have hca : c * a * c⁻¹ ∈ cosetKernel (M := M) (g • W) :=
    hQ (hconj (Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom ha))
  have hcn := stabilizer_le_normalizer_cosetKernel (g • W) hc
  have haD : a ∈ cosetKernel (M := M) (g • W) :=
    (Subgroup.mem_normalizer_iff.mp hcn a).mpr hca
  exact Subgroup.disjoint_def.mp (disjoint_cosetKernel W (g • W) hdisj) (hP ha.1) haD

/-- An actor fixing a nonidentity element of a TI subgroup stabilizes that subgroup. -/
theorem fixed_mem_stabilizer_of_ti (W : Subgroup V)
    (hTI : ∀ a : M, a • W = W ∨ Disjoint W (a • W))
    {a : M} {w : V} (hw : w ∈ W) (hne : w ≠ 1) (hfix : a • w = w) :
    a ∈ MulAction.stabilizer M W := by
  rcases hTI a with he | hd
  · exact MulAction.mem_stabilizer_iff.mpr he
  · apply False.elim
    apply hne
    apply Subgroup.disjoint_def.mp hd hw
    refine ⟨w, hw, ?_⟩
    exact hfix

/-- The same fixed-element criterion holds for every translate of the TI subgroup. -/
theorem fixed_translate_mem_stabilizer_of_ti (W : Subgroup V)
    (hTI : ∀ a : M, a • W = W ∨ Disjoint W (a • W))
    (g : M) {a : M} {w : V} (hw : w ∈ g • W) (hne : w ≠ 1)
    (hfix : a • w = w) : a ∈ MulAction.stabilizer M (g • W) := by
  obtain ⟨x, hx, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists w g W).mp hw
  have hxn : x ≠ 1 := by intro he; simp [he] at hne
  have hxf : (g⁻¹ * a * g) • x = x := by
    simp only [mul_smul, hfix, inv_smul_smul]
  have hmem := fixed_mem_stabilizer_of_ti W hTI hx hxn hxf
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  refine ⟨g⁻¹ * a * g, hmem, ?_⟩
  change g * (g⁻¹ * a * g) * g⁻¹ = a
  group

/-- The Sylow displacement function at a nonidentity element of a disjoint translate is injective into Z. -/
theorem card_le_of_ti_displacement
    [Finite M] [Finite V] [FaithfulSMul M V] {p : ℕ} [Fact p.Prime]
    (P : Sylow p M) (W Z : Subgroup V) (hW : W ≠ ⊥) (hZW : Z ≤ W)
    (hTI : ∀ a : M, a • W = W ∨ Disjoint W (a • W))
    (hdisp : ∀ a ∈ (P : Subgroup M), ∀ v : V, (a • v) * v⁻¹ ∈ Z)
    (g : M) (hdisj : Disjoint W (g • W)) : Nat.card P ≤ Nat.card Z := by
  have hPD : (P : Subgroup M) ≤ cosetKernel (M := M) W :=
    fun a ha v => hZW (hdisp a ha v)
  have hinf := inf_stabilizer_eq_bot_of_disjoint_translate P W hPD g hdisj
  obtain ⟨w, hw, hne⟩ := W.bot_or_exists_ne_one.resolve_left hW
  have hgw : g • w ∈ g • W := Subgroup.smul_mem_pointwise_smul w g W hw
  have hgn : g • w ≠ 1 := by
    intro he
    apply hne
    have hh := congrArg (fun x : V => g⁻¹ • x) he
    simpa only [inv_smul_smul, smul_one] using hh
  have hfree (a : M) (ha : a ∈ (P : Subgroup M)) (hfix : a • (g • w) = g • w) : a = 1 := by
    have hm : a ∈ (P : Subgroup M) ⊓ MulAction.stabilizer M (g • W) :=
      ⟨ha, fixed_translate_mem_stabilizer_of_ti W hTI g hgw hgn hfix⟩
    rw [hinf] at hm
    exact Subgroup.mem_bot.mp hm
  let d : P → Z := fun a => ⟨((a : M) • (g • w)) * (g • w)⁻¹, hdisp a a.property _⟩
  apply Nat.card_le_card_of_injective d
  intro a b hab
  have he : (a : M) • (g • w) = (b : M) • (g • w) :=
    mul_right_cancel (congrArg Subtype.val hab)
  have hfix : ((b : M)⁻¹ * (a : M)) • (g • w) = g • w := by
    rw [mul_smul, he, inv_smul_smul]
  have hone := hfree ((b : M)⁻¹ * (a : M))
    ((P : Subgroup M).mul_mem ((P : Subgroup M).inv_mem b.property) a.property) hfix
  exact Subtype.ext (inv_mul_eq_one.mp hone).symm


/-- The explicit automorphism-homomorphism interface for the TI Sylow displacement bound. -/
theorem card_le_of_faithful_automorphisms
    {M V : Type*} [Group M] [Finite M] [Group V] [Finite V]
    {p : ℕ} [Fact p.Prime]
    (ρ : M →* MulAut V) (hρ : Function.Injective ρ)
    (P : Sylow p M) (W Z : Subgroup V) (hW : W ≠ ⊥) (hZW : Z ≤ W)
    (hTI : ∀ a : M, W.map (ρ a).toMonoidHom = W ∨ Disjoint W (W.map (ρ a).toMonoidHom))
    (hdisp : ∀ a ∈ (P : Subgroup M), ∀ v : V, ρ a v * v⁻¹ ∈ Z)
    (g : M) (hdisj : Disjoint W (W.map (ρ g).toMonoidHom)) :
    Nat.card P ≤ Nat.card Z := by
  let : MulDistribMulAction M V := MulDistribMulAction.compHom V ρ
  let : FaithfulSMul M V := ⟨by
    intro a b h
    apply hρ
    ext v
    exact h v⟩
  exact card_le_of_ti_displacement P W Z hW hZW hTI hdisp g hdisj

end Theory.GroupAction.TISylowDisplacement
