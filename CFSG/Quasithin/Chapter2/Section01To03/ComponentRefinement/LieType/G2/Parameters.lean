module

public import Theory.AtlasPort.LinearGroups.G2.LieParabolicSetup
public import Theory.PGroupCore

/-!
# Model and parabolic coordinates for the G₂ branch

These are concrete inputs for the two-parabolic calculation in
Aschbacher–Smith 2.3.9(7), printed p.526, with exactly the G₂ model
alternatives in 1.1.5(3)(a),(b), printed pp.501–502.

The model map keeps the binary derived subgroup and the arbitrary central
two-covers of G₂(4). Pullback parabolics retain their embedding in L and
invariance under N_S(L). The Sylow marking is for S intersected with L.
The overgroups are generated with all of S; S need not normalize L.

No field of the coordinate structure asserts a block classification,
HeOver membership, or the desired exclusion. Geometry and block analysis
can therefore use this interface independently before final assembly.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2

open Subgroup

/-- Exactly the two G₂ model alternatives, with the binary derived subgroup
and arbitrary central two-covers retained. -/
def IsModelCase (L : Type*) [Group L] : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (n : ℕ),
    1 ≤ n ∧ Nat.card F = 2 ^ n ∧
      Nonempty (L ≃* commutator (Atlas.G2.Model F))) ∨
  (center L = pCore 2 L ∧ pCore 2 L ≠ ⊥ ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = 4 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.G2.Model F))

variable {G : Type*} [Group G]

/-- Geometric data for the invariant-parabolic branch. Its fields concern
the concrete model, Sylow intersection and normalizer action; no block
classification, HeOver condition or exclusion is assumed. -/
structure ParabolicCoordinates (L S : Subgroup G) where
  field : Type
  fieldInstance : Field field
  finiteField : Finite field
  characteristic : CharP field 2
  exponent : ℕ
  exponent_pos : 1 ≤ exponent
  field_card : Nat.card field = 2 ^ exponent
  modelMap : L →* Atlas.G2.Model field
  model_range : modelMap.range = commutator (Atlas.G2.Model field)
  model_kernel : modelMap.ker = ⊥ ∨
    (Nat.card field = 4 ∧ modelMap.ker = center L ∧
      center L = pCore 2 L ∧ pCore 2 L ≠ ⊥)
  sylow_image : (S.subgroupOf L).map modelMap =
    Atlas.G2.unipotent ⊓ commutator (Atlas.G2.Model field)
  first_invariant : S ⊓ normalizer (L : Set G) ≤ normalizer
    (((Atlas.G2.LieParabolicSetup.parabolic₁.comap modelMap).map L.subtype) : Set G)
  second_invariant : S ⊓ normalizer (L : Set G) ≤ normalizer
    (((Atlas.G2.LieParabolicSetup.parabolic₂.comap modelMap).map L.subtype) : Set G)

attribute [instance] ParabolicCoordinates.fieldInstance ParabolicCoordinates.finiteField
  ParabolicCoordinates.characteristic

namespace ParabolicCoordinates

variable {L S : Subgroup G} (d : ParabolicCoordinates L S)

/-- The pullback of the genuine first parabolic, as a subgroup of G. -/
def first : Subgroup G :=
  (Atlas.G2.LieParabolicSetup.parabolic₁.comap d.modelMap).map L.subtype

/-- The pullback of the genuine second parabolic, as a subgroup of G. -/
def second : Subgroup G :=
  (Atlas.G2.LieParabolicSetup.parabolic₂.comap d.modelMap).map L.subtype

def firstOvergroup : Subgroup G := d.first ⊔ S
def secondOvergroup : Subgroup G := d.second ⊔ S

theorem firstOvergroup_le : d.firstOvergroup ≤ L ⊔ S :=
  sup_le_sup (map_subtype_le _) le_rfl

theorem secondOvergroup_le : d.secondOvergroup ≤ L ⊔ S :=
  sup_le_sup (map_subtype_le _) le_rfl

end ParabolicCoordinates

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2

end
