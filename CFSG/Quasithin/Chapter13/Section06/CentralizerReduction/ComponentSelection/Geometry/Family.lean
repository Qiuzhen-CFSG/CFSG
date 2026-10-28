module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.ModuleMarking
public import Theory.Representation.BinaryPermutation.FiveAction

/-!
# The nonsingular-vector family in the A₅ centralizer reduction

Use the minus-type quadratic form on the actual even-weight five-point
module. For each vector u the subgroup V_u is the ambient image of u's
polar hyperplane. This definition moves the singular seed with the vector;
it does not reuse the original fixed z in every centralizer.

The source fusion condition says that ambient conjugation between vectors
preserves their quadratic value. The remaining model calculation must
identify the distinguished polar hyperplane with ⟨z^{L_v}⟩ and prove that
the hyperplanes indexed by its nonsingular vectors generate V.

Source: Aschbacher–Smith, combined manuscript, printed pp.879 and 928,
13.2.6(2) and the reduction preceding 13.6.8.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open Subgroup
open BinaryPermutation.FiveCentralizerGeometry
variable {G : Type*} [Group G] {L V : Subgroup G}

/-- The polar hyperplane, in the concrete binary A₅ module. -/
def modelPerp (u : Space) : Subgroup (Multiplicative Space) :=
  (BinaryPermutation.FiveGeometry.form.polarBilin u).ker.toAddSubgroup.toSubgroup

/-- The actual ambient subgroup corresponding to u's polar hyperplane. -/
def vectorPerp (s : A5Module.Marking L V) (u : Space) : Subgroup G :=
  (modelPerp u).map s.map

/-- The family appearing immediately before 13.6.8. -/
def nonsingularFamily (s : A5Module.Marking L V) : Set (Subgroup G) :=
  {W | ∃ u : Space, s.map (Multiplicative.ofAdd u) ∈
      Vv L (A5Module.markedZ s) (A5Module.markedV s) ∧
    BinaryPermutation.FiveGeometry.form u ≠ 0 ∧ W = vectorPerp s u}

/-- The quadratic-value part of the genuine fusion assertion 13.2.6(2).
It includes zero harmlessly; group conjugation fixes the identity. -/
def FusionPreservesForm (s : A5Module.Marking L V) : Prop :=
  ∀ (g : G) (u w : Space),
    MulAut.conj g (s.map (Multiplicative.ofAdd u)) = s.map (Multiplicative.ofAdd w) →
      BinaryPermutation.FiveGeometry.form u = BinaryPermutation.FiveGeometry.form w

@[simp] theorem mem_modelPerp (u x : Space) :
    Multiplicative.ofAdd x ∈ modelPerp u ↔
      BinaryPermutation.FiveGeometry.form.polarBilin u x = 0 := Iff.rfl

theorem vectorPerp_le (s : A5Module.Marking L V) (u : Space) : vectorPerp s u ≤ V := by
  exact (map_le_range _ _).trans s.range_eq.le

/-- Every member is an actual subgroup of the given module. -/
theorem nonsingularFamily_le (s : A5Module.Marking L V) :
    sSup (nonsingularFamily s) ≤ V := by
  apply sSup_le
  rintro W ⟨u, _, _, rfl⟩
  exact vectorPerp_le s u

/-- Fusion preserving quadratic values also preserves the polar pairing
whenever both vectors and their conjugates lie in the actual module. -/
theorem polar_eq_of_conjugates (s : A5Module.Marking L V) (hf : FusionPreservesForm s)
    (g : G) (u x w y : Space)
    (hu : MulAut.conj g (s.map (Multiplicative.ofAdd u)) = s.map (Multiplicative.ofAdd w))
    (hx : MulAut.conj g (s.map (Multiplicative.ofAdd x)) = s.map (Multiplicative.ofAdd y)) :
    BinaryPermutation.FiveGeometry.form.polarBilin u x =
      BinaryPermutation.FiveGeometry.form.polarBilin w y := by
  have hadd : MulAut.conj g (s.map (Multiplicative.ofAdd (u + x))) =
      s.map (Multiplicative.ofAdd (w + y)) := by
    change MulAut.conj g (s.map (Multiplicative.ofAdd u * Multiplicative.ofAdd x)) =
      s.map (Multiplicative.ofAdd w * Multiplicative.ofAdd y)
    rw [map_mul, map_mul, hu, hx, map_mul]
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  rw [hf g (u + x) (w + y) hadd, hf g u w hu, hf g x y hx]

private theorem map_conj_vectorPerp_le (s : A5Module.Marking L V)
    (hf : FusionPreservesForm s) (g : G) (hg : g ∈ normalizer (V : Set G))
    (u w : Space)
    (hu : MulAut.conj g (s.map (Multiplicative.ofAdd u)) = s.map (Multiplicative.ofAdd w)) :
    (vectorPerp s u).map (MulAut.conj g).toMonoidHom ≤ vectorPerp s w := by
  rintro a ⟨b, ⟨x, hx, rfl⟩, rfl⟩
  have hxV : s.map x ∈ V := s.range_eq.le ⟨x, rfl⟩
  have hyV : MulAut.conj g (s.map x) ∈ V := (mem_normalizer_iff.mp hg _).mp hxV
  obtain ⟨y, hy⟩ := s.range_eq.ge hyV
  refine ⟨y, ?_, hy⟩
  have hp := polar_eq_of_conjugates s hf g u x.toAdd w y.toAdd hu hy.symm
  change BinaryPermutation.FiveGeometry.form.polarBilin w y.toAdd = 0
  exact hp.symm.trans hx

/-- Actual conjugation transport of the polar family under N_G(V).
This uses fusion and the module map; it makes no fixed-L equivariance claim. -/
theorem vectorPerp_conjugate (s : A5Module.Marking L V)
    (hf : FusionPreservesForm s) (g : G) (hg : g ∈ normalizer (V : Set G))
    (u w : Space)
    (hu : MulAut.conj g (s.map (Multiplicative.ofAdd u)) = s.map (Multiplicative.ofAdd w)) :
    (vectorPerp s u).map (MulAut.conj g).toMonoidHom = vectorPerp s w := by
  apply le_antisymm (map_conj_vectorPerp_le s hf g hg u w hu)
  have hinv : MulAut.conj g⁻¹ (s.map (Multiplicative.ofAdd w)) =
      s.map (Multiplicative.ofAdd u) := by
    rw [← hu]
    change g⁻¹ * (g * _ * g⁻¹) * g⁻¹⁻¹ = _
    group
  have hb := map_mono (f := (MulAut.conj g).toMonoidHom)
    (map_conj_vectorPerp_le s hf g⁻¹ ((normalizer (V : Set G)).inv_mem hg) w u hinv)
  rw [map_map] at hb
  have hc : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      MonoidHom.id G := by
    ext a
    change g * (g⁻¹ * a * g⁻¹⁻¹) * g⁻¹ = a
    group
  rwa [hc, Subgroup.map_id] at hb

/-- Once the model identifies V_v with v's polar hyperplane, the earlier
identity M_v = C_{N_G(V)}(v) supplies its relative normalizer action. -/
theorem Mv_normalizes_Vv_of_perp (s : A5Module.Marking L V)
    (hf : FusionPreservesForm s) (M : Subgroup G)
    (hM : Mv M (A5Module.markedV s) ≤ normalizer (V : Set G))
    (hperp : Vv L (A5Module.markedZ s) (A5Module.markedV s) = vectorPerp s v) :
    Mv M (A5Module.markedV s) ≤
      normalizer (Vv L (A5Module.markedZ s) (A5Module.markedV s) : Set G) := by
  intro g hg
  rw [hperp, mem_normalizer_iff_map_conj_eq]
  apply vectorPerp_conjugate s hf g (hM hg) v v
  change g * A5Module.markedV s * g⁻¹ = A5Module.markedV s
  rw [mem_centralizer_singleton_iff.mp hg.2]
  simp [mul_assoc]

/-- The proper local-overgroup conclusion of 13.6.8 follows directly
from the counterexample and the earlier normalizer identity for M_v. -/
theorem Mv_lt_Gv_of_failure (M V : Subgroup G) (v : G)
    (hM : Mv M v ≤ normalizer (V : Set G))
    (hfailure : ¬ Gv v ≤ normalizer (V : Set G)) : Mv M v < Gv v := by
  exact lt_of_le_of_ne inf_le_right (fun he => hfailure (he ▸ hM))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
end
