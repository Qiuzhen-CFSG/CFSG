module

public import Theory.GroupTheory.PResidual.Defs
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Theory.ElementaryAbelian.Basic

/-!
# Short groups and Aschbacher blocks

These are the five clauses of Aschbacher–Smith C.1.7 (combined manuscript,
1 March 2004, printed p.123). The quotient U/C_U(L) is an actual quotient
group. Irreducibility is expressed by the interval of L-normal subgroups
between U ∩ Z(L) and U. For an elementary abelian U this is precisely the
lattice of invariant binary subspaces of that quotient. Strict containment
excludes the zero module.

The condition U ≤ Ω₁(Z(O₂(L))) is recorded as elementary abelianness and
centrality in O₂(L); U ≤ O₂(L) follows from its commutator definition.
No later structural result is included among the defining hypotheses.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterC

open Theory.GroupTheory

variable (L : Type*) [Group L]

/-- The elementary commutator layer U(L) in the short-group definition. -/
def blockU : Subgroup L := ⁅pCore 2 L, ⊤⁆

instance blockU_normal : (blockU L).Normal :=
  inferInstanceAs (⁅pCore 2 L, (⊤ : Subgroup L)⁆).Normal

/-- C_U(L), viewed intrinsically as a subgroup of U. -/
def blockFixed : Subgroup (blockU L) := (Subgroup.center L).subgroupOf (blockU L)

instance blockFixed_normal : (blockFixed L).Normal :=
  inferInstanceAs ((Subgroup.center L).subgroupOf (blockU L)).Normal

/-- The actual module quotient Ũ(L) = U(L)/C_U(L). -/
abbrev BlockModule := blockU L ⧸ blockFixed L

/-- Conjugation on U(L), with the ambient element retained in the formula. -/
def blockConjugate (l : L) (u : blockU L) : blockU L :=
  ⟨l * (u : L) * l⁻¹, (blockU_normal L).conj_mem u u.property l⟩

/-- An identification with a prescribed module. Both the quotient group
isomorphism and the intertwining of the actual conjugation action are required.
For a vector-space model use its multiplicative additive group for `V`. -/
structure BlockModuleModel {A V : Type*} [Group A] [Group V]
    (ρ : A →* MulAut V) where
  quotientIso : (L ⧸ pCore 2 L) ≃* A
  moduleIso : BlockModule L ≃* V
  intertwining : ∀ (l : L) (u : blockU L),
    moduleIso (QuotientGroup.mk' (blockFixed L) (blockConjugate L l u)) =
      ρ (quotientIso (QuotientGroup.mk' (pCore 2 L) l))
        (moduleIso (QuotientGroup.mk' (blockFixed L) u))

/-- Irreducibility of Ũ(L), expressed by the invariant-subgroup interval. -/
def BlockModuleIrreducible : Prop :=
  blockU L ⊓ Subgroup.center L < blockU L ∧
  ∀ N : Subgroup L, N.Normal → blockU L ⊓ Subgroup.center L ≤ N →
    N ≤ blockU L → N = blockU L ⊓ Subgroup.center L ∨ N = blockU L

/-- A short group, with exactly the structural hypotheses of C.1.7. -/
structure IsShort : Prop where
  finite : Finite L
  twoPerfect : IsPPerfect 2 L
  fitting : generalizedFitting L = pCore 2 L
  elementary : IsElementaryAbelian 2 (blockU L)
  central : blockU L ≤ Subgroup.centralizer (pCore 2 L : Set L)
  quotient : IsQuasisimple (L ⧸ pCore 2 L) ∨ Nat.card (L ⧸ pCore 2 L) = 3
  irreducible : BlockModuleIrreducible L

variable {G : Type*} [Group G]

/-- A block is a short subnormal subgroup of a finite ambient group. -/
structure IsBlock (K : Subgroup G) : Prop where
  finite : Finite G
  short : IsShort K
  subnormal : K.IsSubnormal

end CFSG.Quasithin.ChapterC

end
