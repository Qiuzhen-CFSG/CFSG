module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeCentralizer
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Automorphisms.Compatibility
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.Ambient

/-!
# The original code hexad under the full M22 actor

The two faithful conjugation models identify the degree-24 pair stabilizer
with the degree-22 design automorphisms. Their actions agree on the actual
undeleted coordinates. Consequently the stabilizer of a marked hexad code
vector is the full design hexad stabilizer, including its outer actors.

This is the model bridge used by the original LT action in Aschbacher--Smith
8.2.10--11, printed pp.721--722, with the code of H.13, printed p.395.
-/

@[expose] public noncomputable section
open Subgroup Sporadic.Mathieu
open Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise
namespace MathieuCode.NormalizedShadowRows

/-- The conjugation identification retains the original inner M22 marking. -/
def pairDesignEquiv : MathieuCode.m22PairStabilizer ≃* m22DesignAut :=
  m22PairStabilizerEquivAut.trans M22ValueBound.Concrete.designAutEquiv.symm

@[simp] theorem pairDesignEquiv_inner (g : M22) :
    pairDesignEquiv (m22ToPairStabilizer g) = M22ValueBound.Concrete.inclusion g := by
  apply M22ValueBound.Concrete.designAutEquiv.injective
  change M22ValueBound.Concrete.designAutEquiv
    (M22ValueBound.Concrete.designAutEquiv.symm (m22PairStabilizerEquivAut
      (m22ToPairStabilizer g))) = _
  rw [MulEquiv.apply_symm_apply, m22PairStabilizerEquivAut_inner,
    M22ValueBound.Concrete.designAutEquiv_inclusion]

/-- The conjugation identification agrees on every undeleted coordinate. -/
theorem pairDesignEquiv_coordinate (g : MathieuCode.m22PairStabilizer) (i : Fin 22) :
    g.val • m22Coordinates i = m22Coordinates ((pairDesignEquiv g).val i) := by
  let s := pairDesignEquiv g
  have he : m22PairStabilizerEquivAut g = m22DesignAutToAut s :=
    (M22ValueBound.Concrete.designAutEquiv.apply_symm_apply
      (m22PairStabilizerEquivAut g)).symm
  have hn : g.val • m22Coordinates i ∉ MathieuCode.m22Pair := by
    intro h
    have hp := (MulAction.mem_stabilizer_finset.mp g.property (m22Coordinates i)).mp h
    exact (by decide +kernel : ∀ i : Fin 22, m22Coordinates i ∉ MathieuCode.m22Pair) i hp
  have hcoords : ∀ x : Fin 24, x = 0 ∨ x = 9 ∨ ∃ j, m22Coordinates j = x := by
    decide +kernel
  obtain h0 | h9 | ⟨j, hj⟩ := hcoords (g.val • m22Coordinates i)
  · exact (hn (by simp [h0, MathieuCode.m22Pair])).elim
  · exact (hn (by simp [h9, MathieuCode.m22Pair])).elim
  rw [← hj]
  congr 1
  by_contra hji
  have hpre : s.val⁻¹ j ≠ i := by
    intro h
    exact hji (by simpa using congrArg s.val h)
  obtain ⟨l, hli, hlpre⟩ := Fin.exists_ne_and_ne_of_two_lt i (s.val⁻¹ j) (by decide)
  obtain ⟨k, hki, hkp⟩ := (MulAction.is_two_pretransitive_iff.mp m22_isTwoPretransitive)
    hpre.symm hli.symm
  have hc := m22PairStabilizerEquivAut_apply g k
  rw [he] at hc
  have hm := eq_mul_inv_iff_mul_eq.mp hc
  have hh := congrArg (fun x : M24 => x • m22Coordinates i) hm
  have hact (a : M22) (b : Fin 22) :
      m22Embedding a • m22Coordinates b = m22Coordinates (a • b) := m22Embedding_apply a b
  simp only [mul_smul, hact, hki, ← hj] at hh
  have hjfix : m22DesignAutToAut s k • j = j := m22Coordinates.injective hh
  change (m22DesignAutToAut s k).val j = j at hjfix
  rw [m22DesignAutToAut_apply_perm] at hjfix
  change s.val (k.val (s.val⁻¹ j)) = j at hjfix
  have hfix : k • (s.val⁻¹ j) = s.val⁻¹ j := by
    change k.val (s.val⁻¹ j) = s.val⁻¹ j
    apply s.val.injective
    simpa using hjfix
  exact hlpre (hkp.symm.trans hfix)

/-- The full pair actor fixes the code vector exactly when its literal
design permutation preserves the same hexad. -/
theorem outer_code_hexad_vector_fixed_iff {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (g : MathieuCode.m22PairStabilizer) :
    m22OuterCodeRepresentation g (m22HexadVector hB) = m22HexadVector hB ↔
      pairDesignEquiv g ∈ MulAction.stabilizer m22DesignAut B := by
  constructor
  · intro hg
    have hh := (SectionAction.octadVector_fixed_iff (m22Octad hB) g.val).mp
      (congrArg Subtype.val hg)
    apply MulAction.mem_stabilizer_finset'.mpr
    intro i hi
    have hm := MulAction.mem_stabilizer_finset'.mp hh
      ((mem_m22AugmentedOctad B (m22Coordinates i)).mpr (Or.inr (Or.inr ⟨i,hi,rfl⟩)))
    change g.val • m22Coordinates i ∈ m22AugmentedOctad B at hm
    rw [pairDesignEquiv_coordinate, mem_m22AugmentedOctad] at hm
    rcases hm with hm | hm | ⟨j,hj,hji⟩
    · exact False.elim ((by decide +kernel : ∀ j : Fin 22, m22Coordinates j ≠ 0) _ hm)
    · exact False.elim ((by decide +kernel : ∀ j : Fin 22, m22Coordinates j ≠ 9) _ hm)
    · change (pairDesignEquiv g).val i ∈ B
      exact (m22Coordinates.injective hji) ▸ hj
  · intro hg
    apply Subtype.ext
    apply (SectionAction.octadVector_fixed_iff (m22Octad hB) g.val).mpr
    apply MulAction.mem_stabilizer_finset'.mpr
    intro i hi
    rcases (mem_m22AugmentedOctad B i).mp hi with rfl | rfl | ⟨j,hj,rfl⟩
    · have hp := MulAction.mem_stabilizer_finset'.mp g.property
        (by simp [MathieuCode.m22Pair] : (0 : Fin 24) ∈ MathieuCode.m22Pair)
      have he : g.val • (0 : Fin 24) = 0 ∨ g.val • (0 : Fin 24) = 9 := by
        simpa [MathieuCode.m22Pair] using hp
      exact (mem_m22AugmentedOctad B _).mpr (he.imp_right Or.inl)
    · have hp := MulAction.mem_stabilizer_finset'.mp g.property
        (by simp [MathieuCode.m22Pair] : (9 : Fin 24) ∈ MathieuCode.m22Pair)
      have he : g.val • (9 : Fin 24) = 0 ∨ g.val • (9 : Fin 24) = 9 := by
        simpa [MathieuCode.m22Pair] using hp
      exact (mem_m22AugmentedOctad B _).mpr (he.imp_right Or.inl)
    · rw [pairDesignEquiv_coordinate]
      exact (mem_m22AugmentedOctad B _).mpr (Or.inr (Or.inr
        ⟨(pairDesignEquiv g) • j,MulAction.mem_stabilizer_finset'.mp hg hj,rfl⟩))

end MathieuCode.NormalizedShadowRows
