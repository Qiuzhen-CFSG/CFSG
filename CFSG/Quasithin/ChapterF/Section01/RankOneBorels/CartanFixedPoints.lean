module
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.CartanFixedPoints.Linear
public import Theory.SpecificGroups.Suzuki.CartanPanelFixedPoints
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.CartanFixedPoints.Unitary

/-!
# Cartan fixed points for the original local Borels

All five perfect rank-one quotient branches of F.1.1 are proved on the
original local group and its intrinsic Borel cosets. The caller supplies its actual
odd complement; projection preserves its full complement data, and the
concrete model theorems remove the fixed-point premises. The quotient
adapter retains the original representatives and the chosen model map.

Perfectness excludes the dihedral constructor and the small linear, Suzuki
and unitary parameters. The unitary proof uses the fixed-field torus and
regular root action, retaining the actual special-to-projective scalar kernel.
Source: Aschbacher--Smith, printed pp.259--260, Hypothesis F.1.1 and F.1.3(1),
with the Suzuki fixed-pair calculation from Huppert--Blackburn III, XI.3.10.
-/

public section
namespace CFSG.Quasithin.ChapterF.Source
open Theory.CartanPanel BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The original F.1.1 local Borel, in the perfect Suzuki quotient branch,
has a sharp fixed-pair element in the caller's actual odd complement. -/
theorem HypothesisF11.borel_two_fixed_cosets_suzuki (h : HypothesisF11 L S)
    (i : Fin 2) (hp : Group.IsPerfect (L i)) (m : ℕ)
    (e : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (D : Subgroup (L i)) (hD : D ≤ (borel (L i) S).subgroupOf (L i))
    (hodd : Nat.Coprime 2 (Nat.card D))
    (hdis : Disjoint ((S ⊓ L i).subgroupOf (L i)) D)
    (hsup : (S ⊓ L i).subgroupOf (L i) ⊔ D = (borel (L i) S).subgroupOf (L i)) :
    ∃ d ∈ D, ∃ β : (L i) ⧸ (borel (L i) S).subgroupOf (L i),
      β ≠ QuotientGroup.mk 1 ∧ ∀ ω : (L i) ⧸ (borel (L i) S).subgroupOf (L i),
        d • ω = ω ↔ ω = QuotientGroup.mk 1 ∨ ω = β := by
  let : Finite (L i) := h.finite_local i
  let : Group.IsPerfect (L i) := hp
  let : Group.IsPerfect (SuzukiMatrixGroup m) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨T, hT⟩ := h.sylow i
  have hTi : (S ⊓ L i).subgroupOf (L i) = (T : Subgroup (L i)) := by
    rw [← hT]
    exact Subgroup.comap_map_eq_self_of_injective (L i).subtype_injective _
  exact localBorel_two_fixed_of_model (L i) S T hT e
    (suzuki_perfect_sylow_two_fixed_cosets m _) D hD hodd
    (hTi ▸ hdis) (hTi ▸ hsup)

/-- Every perfect rank-one source model has a sharp Cartan element on its
Sylow-normalizer cosets, in every supplied odd complement. All five source
constructors are covered; their small nonperfect cases are excluded by proof. -/
theorem IsRankOneModel.perfect_sylow_two_fixed_cosets {M : Type*} [Group M]
    [Group.IsPerfect M] (h : IsRankOneModel M) (T : Sylow 2 M) :
    SylowHasTwoFixedCosets T := by
  cases h with
  | linear n hn hm => exact perfect_sylow_two_fixed_cosets_linear n hn hm T
  | suzuki m hm =>
    obtain ⟨e⟩ := hm
    let : Finite M := Finite.of_injective e e.injective
    let : Group.IsPerfect (SuzukiMatrixGroup m) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    let P := T.mapSurjective (f := e.toMonoidHom) e.surjective
    apply sylow_transport e.symm P T _ (suzuki_perfect_sylow_two_fixed_cosets m P)
    exact (Subgroup.map_symm_eq_iff_map_eq _).mpr rfl
  | projective_unitary n hn hm => exact perfect_sylow_two_fixed_cosets_psu n hn hm T
  | special_unitary n hn hm => exact perfect_sylow_two_fixed_cosets_su n hn hm T
  | dihedral hm => exact (not_perfect_dihedral_model hm.some inferInstance).elim

/-- The original F.1.1 local Borel action, with the actual supplied odd
complement. The two-core quotient and all five concrete model alternatives
are discharged, so no additional fixed-point premise remains. -/
theorem HypothesisF11.borel_two_fixed_cosets (h : HypothesisF11 L S)
    (i : Fin 2) (hp : Group.IsPerfect (L i))
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
    ((h.quotient i).perfect_sylow_two_fixed_cosets _) D hD hodd
    (hTi ▸ hdis) (hTi ▸ hsup)

end CFSG.Quasithin.ChapterF.Source
