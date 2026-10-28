module
public import Theory.SpecificGroups.SymplecticFour.Sylow
public import Mathlib.GroupTheory.Sylow

/-!
# Sylow normalizers inside marked symplectic parabolics

A full point or plane parabolic contains the normalizer of each ambient
Sylow two-subgroup it contains. Conjugate the parabolic to its standard
matrix form, then conjugate its Sylow subgroup internally to the standard
unipotent group. The latter's normalizer is the flag Borel.

This retains the supplied subgroup and its original conjugation marking.
Source: Aschbacher--Smith C.2.7, pp.145--147, and the parabolic inspection
in original 15.2.23, p.1116; refs/quasithin.pdf.
-/

public section
open Subgroup
open scoped Pointwise

private theorem normalizer_le_of_common_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S Q : Sylow p G) (P : Subgroup G)
    (hSP : (S : Subgroup G) ≤ P) (hQP : (Q : Subgroup G) ≤ P)
    (hN : normalizer (S : Set G) ≤ P) : normalizer (Q : Set G) ≤ P := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq P (S.subtype hSP) (Q.subtype hQP)
  have he : (g : G) • S = Q :=
    Sylow.subtype_injective ((S.smul_subtype hSP g).symm.trans hg)
  have hm : (S : Subgroup G).map (MulAut.conj (g : G)).toMonoidHom = Q :=
    congrArg Sylow.toSubgroup he
  have hn : (normalizer (S : Set G)).map (MulAut.conj (g : G)).toMonoidHom =
      normalizer (Q : Set G) := by
    change (normalizer ((S : Subgroup G) : Set G)).map _ = _
    rw [map_equiv_normalizer_eq,hm]
    rfl
  rw [←hn]
  rintro x ⟨y,hy,rfl⟩
  exact P.mul_mem (P.mul_mem g.property (hN hy)) (P.inv_mem g.property)

namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F]

/-- Every full maximal parabolic containing Q also contains its ambient normalizer. -/
theorem normalizer_le_marked_parabolic {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (Q : Sylow 2 (Sp F)) (P : Subgroup (Sp F))
    (hQP : (Q : Subgroup (Sp F)) ≤ P)
    (hP : ∃ g : Sp F, P.map (MulAut.conj g).toMonoidHom = pointParabolic ∨
      P.map (MulAut.conj g).toMonoidHom = planeParabolic) :
    normalizer (Q : Set (Sp F)) ≤ P := by
  obtain ⟨g,hg⟩ := hP
  let a := MulAut.conj g
  let Q' := Q.mapSurjective (f := a.toMonoidHom) a.surjective
  have hQ' : (Q' : Subgroup (Sp F)) ≤ P.map a.toMonoidHom := map_mono hQP
  have hU : unipotent ≤ P.map a.toMonoidHom := by
    rcases hg with hg | hg
    · rw [hg]; exact unipotent_le_borel.trans inf_le_left
    · rw [hg]; exact unipotent_le_borel.trans inf_le_right
  have hB : normalizer (unipotent (F := F) : Set (Sp F)) ≤ P.map a.toMonoidHom := by
    rw [←borel_eq_normalizer_unipotent]
    rcases hg with hg | hg
    · rw [hg]; exact inf_le_left
    · rw [hg]; exact inf_le_right
  have hh := normalizer_le_of_common_sylow (unipotentSylow hF hn) Q'
    (P.map a.toMonoidHom) hU hQ' hB
  intro x hx
  apply (mem_map_iff_mem (f := a.toMonoidHom) a.injective).mp
  apply hh
  change a x ∈ normalizer (((Q : Subgroup (Sp F)).map a.toMonoidHom) : Set (Sp F))
  rw [←map_equiv_normalizer_eq]
  exact mem_map_of_mem a.toMonoidHom hx
end Theory.SpecificGroups.SymplecticFour
