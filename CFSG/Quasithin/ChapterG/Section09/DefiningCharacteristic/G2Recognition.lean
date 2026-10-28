module

public import CFSG.Quasithin.ChapterG.Section09.Basic
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.Models
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.OrbitBounds

/-!
# Reductions for the genuine G₂ alternative of G.9.3

The target module is the scalar restriction of the trace-zero octonion quotient,
with a separate restriction to the actual commutator subgroup. Perfectness
identifies these two actions away from the binary field. A recognized action
has binary degree `6*n`; the original actor inequality then gives `3*n-1 ≤ m`.
An actual component isomorphism transfers an automorphism-rank bound to that
same actor, giving the representation threshold `6*n+2`.

`OrbitBounds` excludes repeated Frobenius blocks and the next basic degrees.
It is only the arithmetic step: construction of the G₂ restricted modules,
exhaustivity and Frobenius descent, and recognition of degree-six actions of
G₂(2)′ are still required. The automorphism-rank estimate is also an explicit
input to the transfer below; its existing owner is the even G₂ rank development.
These reductions do not assert the completed source theorem.

Source: Aschbacher--Smith, G.9.3(10), printed pp.354,356--357; GLS3,
2.8.6, 2.8.8 and 2.8.10(g).
-/

public noncomputable section

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition

attribute [local instance] ZMod.algebra

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Away from the binary endpoint, perfectness identifies the full and derived
natural actions through their actual inclusion. -/
theorem derivedNaturalBinary_quasiequivalent (hq : 2 < Nat.card F) :
    Quasiequivalent (derivedNaturalBinary F) (naturalBinary F) := by
  let : Group.IsPerfect (Atlas.G2.Model F) := Atlas.G2.isPerfect hq
  let e : commutator (Atlas.G2.Model F) ≃* Atlas.G2.Model F :=
    (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans Subgroup.topEquiv
  exact ⟨e, LinearEquiv.refl (ZMod 2) _, fun _ _ => rfl⟩

section Dimension
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  {σ : Representation (ZMod 2) D V} {n : ℕ}

/-- An actual intertwining equivalence, not a group-family identification,
transfers the binary dimension of the natural module. -/
theorem degree_of_natural (hF : Nat.card F = 2 ^ n)
    (hσ : Quasiequivalent σ (naturalBinary F)) :
    Module.finrank (ZMod 2) V = 6 * n := by
  obtain ⟨_, f, _⟩ := hσ
  exact f.finrank_eq.trans (naturalBinary_degree F hF)

/-- The same dimension transport for the derived action includes G₂(2)′. -/
theorem degree_of_derived_natural (hF : Nat.card F = 2 ^ n)
    (hσ : Quasiequivalent σ (derivedNaturalBinary F)) :
    Module.finrank (ZMod 2) V = 6 * n := by
  obtain ⟨_, f, _⟩ := hσ
  exact f.finrank_eq.trans (naturalBinary_degree F hF)
end Dimension

universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
  {A L : Subgroup G} {m n : ℕ}

omit [CharP F 2] in
/-- The rank estimate on the actual full model bounds the original actor and
therefore the degree of its irreducible component module. -/
theorem actor_bound_of_model_rank (h : ComponentHypothesis K ρ A L L m)
    (e : L ≃* Atlas.G2.Model F)
    (hr : primeRank 2 (MulAut (Atlas.G2.Model F)) ≤ 3 * n) :
    m ≤ 3 * n ∧ Module.finrank (ZMod 2) V ≤ 6 * n + 2 := by
  let : Representation.IsIrreducible (ρ.comp L.subtype) := h.irreducible
  have hm : m ≤ primeRank 2 (MulAut L) := h.toSetup.rank_le_automorphisms (by
    rw [Subgroup.normalizer_eq_top_iff.mpr h.normal_H]
    exact le_top)
  rw [Theory.GroupTheory.primeRank_equiv 2 (MulAut.congr e)] at hm
  have hb := hm.trans hr
  exact ⟨hb, by have := h.degree_le; omega⟩

/-- Once the full natural action is recognized, its degree and the lower actor
bound are forced without enlarging or replacing the actor. -/
theorem parameters_of_natural (h : Setup ρ A m) (hF : Nat.card F = 2 ^ n)
    (hρ : Quasiequivalent (ρ.comp L.subtype) (naturalBinary F)) :
    Module.finrank (ZMod 2) V = 6 * n ∧ 3 * n - 1 ≤ m := by
  have hd := degree_of_natural hF hρ
  exact ⟨hd, by have := h.degree_le; omega⟩

/-- The source derived-group conclusion retains the original actor, including
the binary endpoint once its degree-six recognition has been established. -/
theorem parameters_of_derived_natural (h : Setup ρ A m) (hF : Nat.card F = 2 ^ n)
    (hρ : Quasiequivalent (ρ.comp L.subtype) (derivedNaturalBinary F)) :
    Module.finrank (ZMod 2) V = 6 * n ∧ 3 * n - 1 ≤ m := by
  have hd := degree_of_derived_natural hF hρ
  exact ⟨hd, by have := h.degree_le; omega⟩

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition
