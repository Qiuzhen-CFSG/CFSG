module

public import Theory.SpecificGroups.SymplecticFour.BorelActionGeometry.InnerAction
public import Theory.GroupTheory.FiniteParabolicTransfer

/-!
# Aligning Sylow centers in the symplectic matrix model

Sylow conjugacy aligns an arbitrary Sylow subgroup with the standard
unipotent group and its normalizer with the Borel. A p-subgroup centralizing
a Sylow p-subgroup lies in its center, by Sylow maximality applied to their
commuting product.

These are intrinsic support for Aschbacher–Smith E.6.8(2), printed
pp.247–248 (PDF pp.258–259 of refs/quasithin.pdf).
-/

public section

open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.BorelActionGeometry.DisplacementRealization
variable {Q : Type*} [Group Q] {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
theorem align_sylow [Finite Q] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 0 < n)
    (e₀ : Q ≃* Sp F) (S : Sylow 2 Q) :
    ∃ e : Q ≃* Sp F, (S : Subgroup Q).map e.toMonoidHom = unipotent ∧
      (normalizer (S : Set Q)).map e.toMonoidHom = borel := by
  let P := S.mapSurjective (f := e₀.toMonoidHom) e₀.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Sp F) P (unipotentSylow hF hn)
  let e := e₀.trans (MulAut.conj g)
  have hS : (S : Subgroup Q).map e.toMonoidHom = unipotent := by
    change (S : Subgroup Q).map ((MulAut.conj g).toMonoidHom.comp e₀.toMonoidHom) = _
    rw [← map_map]
    exact congrArg (fun R : Sylow 2 (Sp F) => (R : Subgroup (Sp F))) hg
  refine ⟨e, hS, ?_⟩
  calc
    _ = normalizer (((S : Subgroup Q).map e.toMonoidHom) : Set (Sp F)) :=
      map_normalizer_eq_of_bijective (S : Subgroup Q) e.bijective
    _ = borel := by rw [hS]; exact borel_eq_normalizer_unipotent.symm

theorem pGroup_le_sylow_center {p : ℕ} (S : Sylow p Q) (A : Subgroup Q)
    (hA : IsPGroup p A) (hc : A ≤ centralizer (S : Set Q)) :
    A ≤ (center S).map (S : Subgroup Q).subtype := by
  have hAS : A ≤ (S : Subgroup Q) := by
    apply sup_eq_right.mp
    exact S.is_maximal' (hA.to_sup_of_normal_right' S.isPGroup'
      (hc.trans (centralizer_le_normalizer _))) le_sup_right
  intro a ha
  refine ⟨⟨a, hAS ha⟩, mem_center_iff.mpr ?_, rfl⟩
  intro s
  exact Subtype.ext (mem_centralizer_iff.mp (hc ha) s s.property)

end Theory.SpecificGroups.SymplecticFour.BorelActionGeometry.DisplacementRealization
