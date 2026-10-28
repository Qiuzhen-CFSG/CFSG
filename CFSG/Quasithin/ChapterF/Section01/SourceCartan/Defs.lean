module

public import CFSG.Quasithin.ChapterF.Section01.SourceDefs
public import Theory.GroupTheory.Hall.Basic
public import Theory.GroupTheory.Hall.OddNormalProducts

/-!
# Contracts for the Cartan construction in F.1.3(5)

`CompatibleCartans` is constructed from F.1.1 by Hall theory. It asserts the
individual abelian complements, their mutual normalization and the joint
Hall complement, but does not assert joint commutativity.

`CartanQuadraticRigidity` isolates the intrinsic rank-one automorphism fact
used in the final paragraph of the source proof (printed p.260). It must be
proved for the concrete quotient models, then lifted through the two-core;
it is not an additional source hypothesis or a proved model fact.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterF.Source
open Subgroup Subgroup.OddHall
variable {G : Type*} [Group G]

/-- The compatible complements obtained before the field-automorphism argument. -/
structure CompatibleCartans (L : Fin 2 → Subgroup G) (S : Subgroup G) where
  D : Fin 2 → Subgroup G
  le_borel : ∀ i, D i ≤ borel (L i) S
  odd : ∀ i, Nat.Coprime 2 (Nat.card (D i))
  abelian : ∀ i, IsMulCommutative (D i)
  hall : ∀ i, IsHallSubgroup oddPrimes ((D i).subgroupOf (borel (L i) S))
  complement : ∀ i, ((S ⊓ L i).subgroupOf (borel (L i) S)).IsComplement'
    ((D i).subgroupOf (borel (L i) S))
  normalizes : ∀ i, D i ≤ normalizer (D (other i) : Set G)
  joint_hall : IsHallSubgroup oddPrimes ((D 0 ⊔ D 1).subgroupOf (commonBorel L S))
  joint_complement : (S.subgroupOf (commonBorel L S)).IsComplement'
    ((D 0 ⊔ D 1).subgroupOf (commonBorel L S))


/-- An odd automorphism preserving a Sylow subgroup and an odd Cartan
complement cannot act nontrivially and quadratically on that complement.
All maps here are actual group automorphisms; the condition is pointwise. -/
def CartanQuadraticRigidity (H : Type*) [Group H] : Prop :=
  ∀ (T : Sylow 2 H) (D : Subgroup H),
    D ≤ normalizer (T : Set H) →
    Nat.Coprime 2 (Nat.card D) →
    Disjoint (T : Subgroup H) D →
    (T : Subgroup H) ⊔ D = normalizer (T : Set H) →
    ∀ a : MulAut H, Odd (orderOf a) →
      (T : Subgroup H).map a.toMonoidHom = (T : Subgroup H) →
      D.map a.toMonoidHom = D →
      (∀ x ∈ D, a (a x * x⁻¹) = a x * x⁻¹) →
      ∀ x ∈ D, a x = x

end CFSG.Quasithin.ChapterF.Source
