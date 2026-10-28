module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers.CentralizerGeometry.Alignment.BorelCocycle
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers.CentralizerGeometry.Standard

/-!
# Aligning graph-field-stable symplectic Sylow subgroups

Ordinary Sylow conjugacy gives a matrix `g` carrying the standard unipotent
subgroup to the supplied invariant Sylow subgroup. Invariance makes
`g⁻¹ * a(g)` a cocycle in its actual Borel normalizer. The local Borel descent
writes this as `b * a(b)⁻¹`, so `g * b` is fixed by `a` and still carries the
standard unipotent subgroup to that same Sylow subgroup.

The resulting fixed conjugator discharges the alignment premise of
`Standard.geometry_at_aligned_sylow`, giving both the Sylow intersection
with the fixed subgroup and generation of the whole symplectic group.

Source: the symplectic swapping branch of Aschbacher--Smith E.1.14(1),
printed p.214, with the actual graph-field fixed group of 16.1.4(7),
printed p.1171 of `refs/quasithin.pdf`. The ambient centralizer assembly
remains in the parent `CentralizerGeometry` module.
-/

public section
open Subgroup Theory.SpecificGroups.SymplecticFour
open DiagramAutomorphisms GraphFieldFixedResidual
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers.CentralizerGeometry.Alignment
open BorelCocycle
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private lemma map_conj_mul {G : Type*} [Group G] (H : Subgroup G) (x y : G) :
    H.map (MulAut.conj (x * y)).toMonoidHom =
      (H.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext g
  simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    MulAut.conj_apply]
  group

private lemma map_conj_aut {G : Type*} [Group G] (H : Subgroup G) (a : MulAut G) (x : G) :
    (H.map (MulAut.conj x).toMonoidHom).map a.toMonoidHom =
      (H.map a.toMonoidHom).map (MulAut.conj (a x)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext g
  simp [MulAut.conj_apply]

/-- Every supplied graph-field-stable Sylow subgroup is a conjugate of the
standard unipotent subgroup by an element of the actual fixed group. -/
theorem exists_fixed_conjugator (m : ℕ) (hF : Nat.card F = 2 ^ (2 * m + 1))
    (S : Sylow 2 (Sp F))
    (hS : (S : Subgroup (Sp F)).map (graphFieldAut m).toMonoidHom = S) :
    ∃ k : Sp F, k ∈ (graphFieldAut m).fixedSubgroup ∧
      unipotent.map (MulAut.conj k).toMonoidHom = (S : Subgroup (Sp F)) := by
  let a := graphFieldAut (F := F) m
  have haa (x : Sp F) : a (a x) = x :=
    congrArg (fun t : MulAut (Sp F) => t x) (graphFieldAut_sq m hF)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Sp F) (unipotentSylow hF (by omega)) S
  have hg' : unipotent.map (MulAut.conj g).toMonoidHom = (S : Subgroup (Sp F)) :=
    congrArg (fun T : Sylow 2 (Sp F) => (T : Subgroup (Sp F))) hg
  have hag : unipotent.map (MulAut.conj (a g)).toMonoidHom =
      (S : Subgroup (Sp F)) := by
    rw [← graphFieldAut_map_unipotent m, ← map_conj_aut, hg', hS]
  let c := g⁻¹ * a g
  have hcB : c ∈ borel := by
    rw [borel_eq_normalizer_unipotent, mem_normalizer_iff_map_conj_eq]
    change unipotent.map (MulAut.conj (g⁻¹ * a g)).toMonoidHom = unipotent
    rw [map_conj_mul, hag, ← hg', ← map_conj_mul, inv_mul_cancel]
    have hid : (MulAut.conj (1 : Sp F)).toMonoidHom = MonoidHom.id (Sp F) := by
      ext x
      simp
    rw [hid, Subgroup.map_id]
  have hcc : c * a c = 1 := by
    dsimp [c]
    rw [map_mul, map_inv, haa]
    group
  obtain ⟨b, hb, hcb⟩ := borel_cocycle_coboundary m hF c hcB hcc
  change c = b * (a b)⁻¹ at hcb
  refine ⟨g * b, ?_, ?_⟩
  · rw [MulAut.mem_fixedSubgroup]
    change a (g * b) = g * b
    rw [map_mul]
    have he : a g = g * c := by dsimp [c]; group
    rw [he, hcb]
    group
  · rw [map_conj_mul]
    have hb' : unipotent.map (MulAut.conj b).toMonoidHom = unipotent :=
      mem_normalizer_iff_map_conj_eq.mp (borel_eq_normalizer_unipotent (F := F) ▸ hb)
    rw [hb', hg']

/-- The standard matrix geometry holds at every supplied invariant Sylow,
with no alignment assumption. The relative subgroup and join use the literal
fixed subgroup of the specified graph-field automorphism. -/
theorem geometry_at_stable_sylow (m : ℕ) (hm : 0 < m)
    (hF : Nat.card F = 2 ^ (2 * m + 1)) (S : Sylow 2 (Sp F))
    (hstable : (S : Subgroup (Sp F)).map (graphFieldAut m).toMonoidHom = S) :
    (∃ R : Sylow 2 (graphFieldAut (F := F) m).fixedSubgroup,
      (R : Subgroup (graphFieldAut (F := F) m).fixedSubgroup) =
        (S : Subgroup (Sp F)).subgroupOf (graphFieldAut m).fixedSubgroup) ∧
      (graphFieldAut (F := F) m).fixedSubgroup ⊔ (S : Subgroup (Sp F)) = ⊤ := by
  obtain ⟨k, hk, hS⟩ := exists_fixed_conjugator m hF S hstable
  exact Standard.geometry_at_aligned_sylow m hm hF S k hk hS

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers.CentralizerGeometry.Alignment
