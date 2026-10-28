module
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.MarkedParabolicPair

/-!
# Actual symplectic residual marks under automorphisms

An automorphism fixing the standard Sylow fixes either parabolic residual
exactly when it preserves the diagram. The forward direction uses the
inner-field description and the Borel normalizer; the reverse direction
recovers the parabolic as the normalizer of its residual. An arbitrary
diagram-moving automorphism sends each residual to the opposite conjugacy
class, by transporting the actual solvable residual of its parabolic.

These statements retain the point and plane subgroup images and are used
in the marked Sp₄ alternative of Aschbacher–Smith 2.4.23(5), printed
pp.537–538 of the combined manuscript.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- For a Sylow-preserving automorphism, preserving either actual local
factor is equivalent to preserving the diagram. -/
theorem preservesDiagram_iff_local_map {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (a : MulAut (Sp F)) (hU : unipotent.map a.toMonoidHom = unipotent)
    (D : Subgroup (Sp F)) (hD : D = pointLocal ∨ D = planeLocal) :
    PreservesDiagram a ↔ D.map a.toMonoidHom = D := by
  constructor
  · intro ha
    have hh := local_pair_map_of_unipotent_map hF hn a ha hU
    rcases hD with rfl | rfl
    · exact hh.1
    · exact hh.2
  · intro hfix
    have hq : 2 < Nat.card F := by
      rw [hF]
      exact (show 2 ^ 1 < 2 ^ n from Nat.pow_lt_pow_right (by decide) hn)
    apply preservesDiagram_of_one_parabolic_class hq a
    rcases hD with rfl | rfl
    · left
      have hP : pointParabolic.map a.toMonoidHom = pointParabolic := by
        rw [← pointLocal_normalizer hF hn,map_equiv_normalizer_eq,hfix]
      refine ⟨1,?_⟩
      have h1 : (MulAut.conj (1 : Sp F)).toMonoidHom = MonoidHom.id _ := by
        ext g : 1
        simp
      rw [h1,map_id]
      exact hP
    · right
      have hP : planeParabolic.map a.toMonoidHom = planeParabolic := by
        rw [← planeLocal_normalizer hF hn,map_equiv_normalizer_eq,hfix]
      refine ⟨1,?_⟩
      have h1 : (MulAut.conj (1 : Sp F)).toMonoidHom = MonoidHom.id _ := by
        ext g : 1
        simp
      rw [h1,map_id]
      exact hP

omit [CharP F 2] in
private theorem map_embedded_residual (a : MulAut (Sp F)) (P : Subgroup (Sp F)) :
    ((solvableResidual P).map P.subtype).map a.toMonoidHom =
      (solvableResidual (P.map a.toMonoidHom)).map (P.map a.toMonoidHom).subtype := by
  let e := P.equivMapOfInjective a.toMonoidHom a.injective
  have hh := congrArg (fun D => D.map (P.map a.toMonoidHom).subtype)
    (map_solvableResidual_eq e.toMonoidHom e.surjective)
  rw [map_map] at hh
  rw [map_map]
  convert hh using 1
  congr 1

/-- A diagram-moving automorphism takes the point local to the plane local
conjugacy class and the plane local to the point local conjugacy class. -/
theorem moving_local_opposite_classes {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (a : MulAut (Sp F)) (ha : ¬ PreservesDiagram a) :
    (∃ g : Sp F, pointLocal.map a.toMonoidHom = planeLocal.map (MulAut.conj g).toMonoidHom) ∧
    (∃ g : Sp F, planeLocal.map a.toMonoidHom = pointLocal.map (MulAut.conj g).toMonoidHom) := by
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (show 2 ^ 1 < 2 ^ n from Nat.pow_lt_pow_right (by decide) hn)
  have aux (P Q D E : Subgroup (Sp F))
      (hp : P = pointParabolic ∨ P = planeParabolic)
      (hopp : (P = pointParabolic ∧ Q = planeParabolic) ∨
        (P = planeParabolic ∧ Q = pointParabolic))
      (hd : (solvableResidual P).map P.subtype = D)
      (he : (solvableResidual Q).map Q.subtype = E) :
      ∃ g : Sp F, D.map a.toMonoidHom = E.map (MulAut.conj g).toMonoidHom := by
    obtain ⟨Q',hQ',g,hg⟩ := map_parabolic_eq_conjugate hq a P hp
    have hsame : Q' ≠ P := by
      intro hsame
      rw [hsame] at hg
      apply ha
      apply preservesDiagram_of_one_parabolic_class hq a
      rcases hp with rfl | rfl
      · exact Or.inl ⟨g,hg⟩
      · exact Or.inr ⟨g,hg⟩
    have hQ : Q' = Q := by
      rcases hopp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
        rcases hQ' with heq | heq
      · exact (hsame heq).elim
      · exact heq
      · exact heq
      · exact (hsame heq).elim
    rw [hQ] at hg
    refine ⟨g,?_⟩
    rw [← hd,← he,map_embedded_residual,map_embedded_residual,hg]
  exact ⟨aux _ _ _ _ (Or.inl rfl) (Or.inl ⟨rfl,rfl⟩)
    (pointParabolic_solvableResidual_eq hF hn) (planeParabolic_solvableResidual_eq hF hn),
    aux _ _ _ _ (Or.inr rfl) (Or.inr ⟨rfl,rfl⟩)
    (planeParabolic_solvableResidual_eq hF hn) (pointParabolic_solvableResidual_eq hF hn)⟩
end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms