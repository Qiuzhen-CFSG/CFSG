module
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.CartanFixedPoints.Quotient
public import Theory.SpecificGroups.PSL2.CartanPanelFixedPoints
public import Theory.SpecificGroups.DihedralSolvable

/-!
# The perfect linear constructor on original local panels

The concrete even PSL₂ theorem is transported through the actual field/model
isomorphism of the source constructor. Applying the two-core quotient adapter
gives the two fixed cosets in the original F.1.1 local Borel action, with the
caller's supplied odd complement. The dihedral source constructor is separately
excluded by its proved solvability and the perfectness hypothesis.

Source: Aschbacher--Smith, printed pp.259--260, F.1.1 and F.1.3(1).
-/

public section
namespace CFSG.Quasithin.ChapterF.Source
open Theory.CartanPanel

/-- The perfect linear constructor uses the caller's actual finite field and isomorphism. -/
theorem perfect_sylow_two_fixed_cosets_linear {M : Type*} [Group M] [Group.IsPerfect M]
    (n : ℕ) (_hn : 0 < n) (hmodel : ClassicalGroup.IsPSL M 2 (2 ^ n))
    (T : Sylow 2 M) : SylowHasTwoFixedCosets T := by
  obtain ⟨F, hF, hf, hcard, ⟨e⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : Finite M := Finite.of_injective e e.injective
  let P := T.mapSurjective (f := e.toMonoidHom) e.surjective
  apply sylow_transport e.symm P T _
    (Theory.PSL2.CartanPanel.perfect_sylow_two_fixed_cosets P)
  exact (Subgroup.map_symm_eq_iff_map_eq _).mpr rfl

/-- The dihedral constructor is incompatible with the perfect-model hypothesis. -/
theorem not_perfect_dihedral_model {M : Type*} [Group M]
    (e : M ≃* DihedralGroup 5) : ¬ Group.IsPerfect M := by
  intro hp
  let : Group.IsPerfect M := hp
  let : Group.IsPerfect (DihedralGroup 5) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact Group.IsPerfect.not_isSolvable (DihedralGroup 5)
    (GLS3.Chapter5.dihedralGroup_isSolvable 5)

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
/-- The original F.1.1 local Borel in the perfect linear quotient branch,
with the supplied complement and the original left-coset action. -/
theorem HypothesisF11.borel_two_fixed_cosets_linear (h : HypothesisF11 L S)
    (i : Fin 2) (hp : Group.IsPerfect (L i)) (n : ℕ) (hn : 0 < n)
    (hmodel : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2 ^ n))
    (D : Subgroup (L i)) (hD : D ≤ (borel (L i) S).subgroupOf (L i))
    (hodd : Nat.Coprime 2 (Nat.card D))
    (hdis : Disjoint ((S ⊓ L i).subgroupOf (L i)) D)
    (hsup : (S ⊓ L i).subgroupOf (L i) ⊔ D = (borel (L i) S).subgroupOf (L i)) :
    ∃ d ∈ D, ∃ β : (L i) ⧸ (borel (L i) S).subgroupOf (L i),
      β ≠ QuotientGroup.mk 1 ∧ ∀ ω : (L i) ⧸ (borel (L i) S).subgroupOf (L i),
        d • ω = ω ↔ ω = QuotientGroup.mk 1 ∨ ω = β := by
  let : Finite (L i) := h.finite_local i
  let : Group.IsPerfect (L i) := hp
  obtain ⟨T, hT⟩ := h.sylow i
  have hTi : (S ⊓ L i).subgroupOf (L i) = (T : Subgroup (L i)) := by
    rw [← hT]
    exact Subgroup.comap_map_eq_self_of_injective (L i).subtype_injective _
  exact localBorel_two_fixed_of_quotient (L i) S T hT
    (perfect_sylow_two_fixed_cosets_linear n hn hmodel _) D hD hodd
    (hTi ▸ hdis) (hTi ▸ hsup)
end CFSG.Quasithin.ChapterF.Source
