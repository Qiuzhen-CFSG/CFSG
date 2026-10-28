module

public import Theory.GroupTheory.PCoreImage
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Abelian quotients by intrinsic prime cores

The embedded containment [B,B] ≤ Oₚ(B) is equivalent to commutativity of
the intrinsic quotient B/Oₚ(B). If a homomorphism has p-group kernel,
this containment for the image lifts to B: restrict to B and its actual
image, then pull the image core back along the resulting surjection.

This is the usual p-core extension argument. The Borel application is
Aschbacher–Smith 13.8.20, printed p.954 (PDF p.971).
-/

public section
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- Express the intrinsic abelian quotient as an ambient commutator containment. -/
theorem commutator_self_le_pCoreIn_iff (p : ℕ) (B : Subgroup G) :
    ⁅B, B⁆ ≤ B.pCoreIn p ↔ IsMulCommutative (B ⧸ pCore p B) := by
  rw [← B.map_subtype_commutator, pCoreIn,
    map_le_map_iff_of_injective B.subtype_injective]
  exact Normal.quotient_commutative_iff_commutator_le.symm

/-- An abelian quotient by the image core lifts across a p-group kernel. -/
theorem commutator_self_le_pCoreIn_of_map {p : ℕ} [Fact p.Prime]
    [Finite G] [Finite H] (f : G →* H) (hk : IsPGroup p f.ker)
    (B : Subgroup G) (h : ⁅B.map f, B.map f⁆ ≤ (B.map f).pCoreIn p) :
    ⁅B, B⁆ ≤ B.pCoreIn p := by
  rw [← B.map_subtype_commutator, pCoreIn,
    map_le_map_iff_of_injective B.subtype_injective]
  have hk' : IsPGroup p (f.subgroupMap B).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  rw [← (f.subgroupMap B).comap_pCore_of_ker_isPGroup
    (f.subgroupMap_surjective B) hk', ← map_le_iff_le_comap,
    _root_.map_commutator_eq,
    MonoidHom.range_eq_top_of_surjective _ (f.subgroupMap_surjective B)]
  exact Normal.quotient_commutative_iff_commutator_le.mp
    ((commutator_self_le_pCoreIn_iff p _).mp h)

end Subgroup
