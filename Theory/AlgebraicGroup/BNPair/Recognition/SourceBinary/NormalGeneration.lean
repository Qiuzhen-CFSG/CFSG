module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.SplitCore
public import Theory.GroupTheory.PResidual.PrimeTo
public import Theory.GroupTheory.SylowNormalClosure
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.IsPerfect

/-!
# Normal generation by the unipotent subgroup

Let B = U(B ∩ N) be a split Tits system of characteristic two. Any
normal subgroup containing U, together with the actual torus B ∩ N,
generates the whole group. Consequently the normal closure of U has
abelian quotient of odd order in the finite case, and is precisely
O^{2′}(X), the residual with prime-to-two quotient.

The key argument uses the rank-one nontriviality axiom: a subgroup
containing B and normalized by N contains every simple Bruhat cell,
hence is the whole group. Normality and the torus normality apply this
to V(B ∩ N). Perfect subgroups lie in the resulting normal closure,
as does every two-subgroup. Thus two perfect factors and a two-subgroup
which generate X prove normal generation by U without an added
normal-generation hypothesis.

This is an elementary reduction toward the Fong–Seitz invocation in
DGS, Groups and Graphs, Part II, pp.80–81 and224. It does not establish
irreducibility, the full minimal configuration left implicit there,
or the seven-row recognition theorem. The split conventions are those
of GLS3, §2.5, in refs/KGroup/GLS3/Chapter2Ca2.tex.
-/

public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary
variable {X : Type*} [Group X] {T : TitsSystem (X := X)}

private theorem eq_top_of_borel_le_of_N_normalizes (A : Subgroup X)
    (hB : T.B ≤ A) (hN : T.N ≤ normalizer (A : Set X)) : A = ⊤ := by
  rw [T.subgroup_eq_standardParabolic_simpleIndices A hB]
  apply le_antisymm le_top
  rw [← T.standardParabolic_S]
  apply T.standardParabolic_mono
  intro s hs
  apply (T.mem_simpleIndices_iff _ _).mpr
  refine ⟨hs, ?_⟩
  obtain ⟨n, b, hn, hb, hcell⟩ := T.exists_rankOne_witness hs
  have hconj : (n : X) * b * (n : X)⁻¹ ∈ A :=
    (mem_normalizer_iff.mp (hN n.property) b).mp (hB hb)
  have hsq : ((n : X) ^ 2) ∈ A :=
    hB (T.representative_sq_mem_intersection hs n hn).1
  have hw : (n : X) * b * (n : X) ∈ A := by
    have := A.mul_mem hconj hsq
    simpa only [pow_two, mul_assoc, inv_mul_cancel_left] using this
  exact T.bruhatCell_subset_of_mem A hB hcell hw

namespace SplitData
variable (d : SplitData T)

/-- An ambient normal overgroup of U is supplemented by the actual torus. -/
theorem normal_sup_torus (V : Subgroup X) [V.Normal] (hU : d.U ≤ V) :
    V ⊔ (T.B ⊓ T.N) = ⊤ := by
  apply eq_top_of_borel_le_of_N_normalizes
  · calc
      T.B = d.U ⊔ (T.B ⊓ T.N) := d.factorization.symm
      _ ≤ V ⊔ (T.B ⊓ T.N) := sup_le_sup hU le_rfl
  · have hVN : T.N ≤ normalizer (V : Set X) := by
      rw [normalizer_eq_top]
      exact le_top
    have hHN : T.N ≤ normalizer ((T.B ⊓ T.N : Subgroup X) : Set X) :=
      (normal_subgroupOf_iff_le_normalizer inf_le_right).mp T.intersection_normal
    exact (le_inf hVN hHN).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- The normal closure of the specified U, without replacing its marking.
The body is exposed so clients can retain this literal normal closure. -/
@[expose] def unipotentClosure : Subgroup X := normalClosure (d.U : Set X)

/-- Relate the named subgroup to the literal normal-closure construction. -/
theorem unipotentClosure_eq_normalClosure :
    d.unipotentClosure = normalClosure (d.U : Set X) := rfl

instance unipotentClosure_normal : d.unipotentClosure.Normal :=
  normalClosure_normal

/-- The actual torus supplements the unipotent normal closure. -/
theorem unipotentClosure_sup_torus : d.unipotentClosure ⊔ (T.B ⊓ T.N) = ⊤ :=
  d.normal_sup_torus _ le_normalClosure

/-- The quotient by the unipotent normal closure is abelian. -/
theorem commutator_le_unipotentClosure : _root_.commutator X ≤ d.unipotentClosure :=
  Normal.commutator_le_of_self_sup_commutative_eq_top d.unipotentClosure_sup_torus d.abelian

/-- Commutativity on the literal quotient carrier. -/
theorem unipotentClosure_quotient_commutative : IsMulCommutative (X ⧸ d.unipotentClosure) :=
  Normal.quotient_commutative_iff_commutator_le.mpr d.commutator_le_unipotentClosure

/-- The normal closure has odd index; finiteness is needed only here. -/
theorem unipotentClosure_index_coprime [Finite X] : Nat.Coprime 2 d.unipotentClosure.index :=
  (Nat.prime_two.coprime_iff_not_dvd.mpr d.index_not_two).coprime_dvd_right
    (index_dvd_of_le le_normalClosure)

/-- The normal closure is O^{2′}(X), rather than the two-residual O²(X). -/
theorem unipotentClosure_eq_primeToResidual [Finite X] :
    d.unipotentClosure = primeToResidual 2 X := by
  apply le_antisymm
  · apply normalClosure_le_normal
    intro x hx
    obtain ⟨n, hn⟩ := d.isTwo ⟨x, hx⟩
    exact mem_primeToResidual_of_pow (congrArg Subtype.val hn)
  · exact primeToResidual_le _ d.unipotentClosure_index_coprime

/-- Perfect subgroups disappear in the abelian quotient. -/
theorem perfect_subgroup_le_unipotentClosure (A : Subgroup X) [Group.IsPerfect A] :
    A ≤ d.unipotentClosure := by
  calc
    A = ⁅A, A⁆ := A.commutator_eq_self.symm
    _ ≤ _root_.commutator X := commutator_mono le_top le_top
    _ ≤ d.unipotentClosure := d.commutator_le_unipotentClosure

/-- Every two-subgroup lies in the normal closure of the actual Sylow U. -/
theorem two_subgroup_le_unipotentClosure [Finite X] (P : Subgroup X)
    (hP : IsPGroup 2 P) : P ≤ d.unipotentClosure :=
  hP.le_normalClosure_sylow d.sylow

/-- Perfect factors and a two-subgroup eliminate the odd abelian quotient. -/
theorem unipotentClosure_eq_top_of_generation [Finite X]
    (A : Fin 2 → Subgroup X) (P : Subgroup X)
    (hA : ∀ i, Group.IsPerfect (A i)) (hP : IsPGroup 2 P)
    (hgen : A 0 ⊔ A 1 ⊔ P = ⊤) : d.unipotentClosure = ⊤ := by
  apply top_unique
  rw [← hgen]
  apply sup_le
  · apply sup_le
    · let := hA 0
      exact d.perfect_subgroup_le_unipotentClosure _
    · let := hA 1
      exact d.perfect_subgroup_le_unipotentClosure _
  · exact d.two_subgroup_le_unipotentClosure _ hP

end SplitData
end Theory.AlgebraicGroup.TitsSystem.SourceBinary
