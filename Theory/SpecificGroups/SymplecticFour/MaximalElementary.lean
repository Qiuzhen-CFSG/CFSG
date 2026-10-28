module
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.Placement
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ParabolicCores
/-!
# Elementary subgroups of maximum order in symplectic four-space

An elementary subgroup of order q cubed fills one of the two parabolic
radicals after Sylow conjugation. Both radicals are self-centralizing in
the nonbinary symplectic group, so the same holds for the original subgroup.
The distance-two MS application uses this to identify the entire opposite
kernel image with its secondary image, retaining the original kernel.

Source: Meierfrankenfeld--Stellmacher (1993), (3.6), printed p.871; the
standard parabolic calculations are in `LocalStructure.ParabolicCores`.
-/

public section
open Subgroup Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair
namespace Theory.SpecificGroups.SymplecticFour.MaximalElementary
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- Maximum order turns elementary placement into equality with a radical. -/
theorem conjugate_radical {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0 < n)
    (A : Subgroup (Sp F)) [IsElementaryAbelian 2 A]
    (hc : Nat.card A = Nat.card F ^ 3) :
    ∃ g : Sp F, A.map (MulAut.conj g).toMonoidHom = pointRadicalAmbient ∨
      A.map (MulAut.conj g).toMonoidHom = planeRadicalAmbient := by
  obtain ⟨g,hg | hg⟩ := elementary_conjugate_radical hF hn A
  · refine ⟨g,Or.inl (eq_of_le_of_card_ge hg ?_)⟩
    change Nat.card (SymplecticConjugatePair.pointRadical (F := F)) ≤ _
    rw [card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective,hc,card_pointRadical]
  · refine ⟨g,Or.inr ?_⟩
    have he := eq_of_le_of_card_ge hg (show Nat.card (SymplecticConjugatePair.planeRadical (F := F)) ≤
        Nat.card (A.map (MulAut.conj g).toMonoidHom) by
      rw [card_map_of_injective (MulAut.conj g).injective,hc,card_planeRadical])
    exact he

/-- Every elementary subgroup of order q cubed is self-centralizing. -/
theorem selfCentralizing {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (A : Subgroup (Sp F)) [IsElementaryAbelian 2 A]
    (hc : Nat.card A = Nat.card F ^ 3) : centralizer (A : Set (Sp F)) ≤ A := by
  obtain ⟨g,hg⟩ := conjugate_radical hF (by omega) A hc
  have hself : centralizer (A.map (MulAut.conj g).toMonoidHom : Set (Sp F)) ≤
      A.map (MulAut.conj g).toMonoidHom := by
    rcases hg with hg | hg
    · rw [hg]; exact pointRadicalAmbient_selfCentralizing hF hn
    · rw [hg]; exact planeRadicalAmbient_selfCentralizing hF hn
  intro x hx
  have hgx : (MulAut.conj g) x ∈ centralizer
      (A.map (MulAut.conj g).toMonoidHom : Set (Sp F)) := by
    rintro y ⟨z,hz,rfl⟩
    exact (map_mul (MulAut.conj g) z x).symm.trans
      ((congrArg (MulAut.conj g) (hx z hz)).trans (map_mul (MulAut.conj g) x z))
  obtain ⟨y,hy,he⟩ := hself hgx
  exact (MulAut.conj g).injective he ▸ hy
end Theory.SpecificGroups.SymplecticFour.MaximalElementary
