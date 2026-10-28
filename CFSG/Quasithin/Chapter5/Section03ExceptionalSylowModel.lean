module

public import CFSG.Quasithin.Chapter5.Section03ExceptionalSylowModel.Abelian

/-!
# The marked exceptional Sylow model for §5.3.7

The concrete model is UT₃(F₄) extended by its field involution, constructed in
`Matrix.PSL3Four.SylowModel`. This module transports its markings into an
ambient group through an actual isomorphism onto a subgroup. No ambient
centralizer or recognition conclusion is part of the transport data.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, §5.3.7,
printed pp. 660--661 (PDF pp. 677--678).
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.Chapter5.Section03ExceptionalSylowModel

open Matrix.PSL3Four

universe u
variable {G : Type u} [Group G]

/-- An actual copy of the Sylow model in an ambient group. The remaining
markings are images under this isomorphism, so compatibility is retained. -/
structure MarkedCopy (G : Type u) [Group G] where
  carrier : Subgroup G
  equiv : SylowModel.T ≃* carrier

namespace MarkedCopy

variable (m : MarkedCopy G)

def embedding : SylowModel.T →* G := m.carrier.subtype.comp m.equiv.toMonoidHom

theorem embedding_injective : Function.Injective m.embedding :=
  Subtype.val_injective.comp m.equiv.injective

def S : Subgroup G := SylowModel.S.map m.embedding
def V₁ : Subgroup G := SylowModel.V₁.map m.embedding
def V₂ : Subgroup G := SylowModel.V₂.map m.embedding
def Z : Subgroup G := SylowModel.Z.map m.embedding
def Q : Subgroup G := SylowModel.Q.map m.embedding
def z : G := m.embedding SylowModel.z

/-- Every marked subgroup is transported by a group isomorphism, not just an
equality of orders. -/
def subgroupEquiv (A : Subgroup SylowModel.T) : A ≃* A.map m.embedding :=
  A.equivMapOfInjective m.embedding m.embedding_injective

theorem card_carrier : Nat.card m.carrier = 128 := by
  rw [← Nat.card_congr m.equiv.toEquiv, SylowModel.card_T]

theorem card_S : Nat.card m.S = 64 := by
  rw [S, ← Nat.card_congr (m.subgroupEquiv SylowModel.S).toEquiv, SylowModel.card_S]

theorem card_V₁ : Nat.card m.V₁ = 16 := by
  rw [V₁, ← Nat.card_congr (m.subgroupEquiv SylowModel.V₁).toEquiv, SylowModel.card_V₁]

theorem card_V₂ : Nat.card m.V₂ = 16 := by
  rw [V₂, ← Nat.card_congr (m.subgroupEquiv SylowModel.V₂).toEquiv, SylowModel.card_V₂]

theorem card_Z : Nat.card m.Z = 4 := by
  rw [Z, ← Nat.card_congr (m.subgroupEquiv SylowModel.Z).toEquiv, SylowModel.card_Z]

instance : IsElementaryAbelian 2 m.V₁ := IsElementaryAbelian.map m.embedding
instance : IsElementaryAbelian 2 m.V₂ := IsElementaryAbelian.map m.embedding

theorem V₁_inf_V₂ : m.V₁ ⊓ m.V₂ = m.Z := by
  rw [V₁, V₂, ← Subgroup.map_inf _ _ _ m.embedding_injective, SylowModel.V₁_inf_V₂]
  rfl

theorem S_le_carrier : m.S ≤ m.carrier := by
  rintro _ ⟨a, _, rfl⟩
  exact (m.equiv a).property

theorem centralizer_Z : Subgroup.centralizer (m.Z : Set G) ⊓ m.carrier = m.S := by
  apply le_antisymm
  · rintro a ⟨hc, ha⟩
    let b : SylowModel.T := m.equiv.symm ⟨a, ha⟩
    have hb : m.embedding b = a := congrArg Subtype.val (m.equiv.apply_symm_apply ⟨a, ha⟩)
    have hbc : b ∈ Subgroup.centralizer (SylowModel.Z : Set SylowModel.T) := by
      intro c hcZ
      apply m.embedding_injective
      simpa only [map_mul, hb] using hc (m.embedding c) ⟨c, hcZ, rfl⟩
    rw [SylowModel.centralizer_Z] at hbc
    exact ⟨b, hbc, hb⟩
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨?_, (m.equiv a).property⟩
    have hc : a ∈ Subgroup.centralizer (SylowModel.Z : Set SylowModel.T) := by
      rwa [SylowModel.centralizer_Z]
    rintro _ ⟨b, hb, rfl⟩
    simpa only [map_mul] using congrArg m.embedding (hc b hb)

theorem z_ne_one : m.z ≠ 1 := by
  intro h
  apply SylowModel.z_ne_one
  apply m.embedding_injective
  simpa only [map_one, z] using h

theorem z_sq : m.z ^ 2 = 1 := by
  rw [z, ← map_pow, SylowModel.z_sq, map_one]

theorem z_mem_Z : m.z ∈ m.Z := ⟨SylowModel.z, SylowModel.z_mem_Z, rfl⟩

end MarkedCopy
end CFSG.Quasithin.Chapter5.Section03ExceptionalSylowModel
