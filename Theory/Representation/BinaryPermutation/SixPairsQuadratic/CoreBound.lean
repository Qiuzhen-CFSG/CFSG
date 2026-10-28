module
public import Theory.Representation.HexacodeAction.PairCore
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Normal two-subgroups of even pair stabilizers

All pair stabilizers in A₆ are conjugate to the standard duad stabilizer,
whose two-core has order four. Consequently a two-subgroup of S₆ contained
in A₆, fixing a pair and normalized by its even stabilizer has order at most
four. This formulation retains the literal permutation image for transport
from faithful hexacode actors.

Source: Aschbacher–Smith, 13.8.21(2), printed p.956, the E₄ parabolic core.
-/

public section
open Subgroup
namespace BinaryPermutation.SixPairsQuadratic
open Theory.SpecificGroups.SymmetricSix

private theorem pair_fix_iff (s : Pair) (g : Equiv.Perm (Fin 6)) :
    pairPerm g s = s ↔ g • s.val = s.val := by
  rw [Subtype.ext_iff]
  change s.val.map g.toEmbedding = s.val ↔ s.val.image g = s.val
  simp only [Finset.map_eq_image,Equiv.coe_toEmbedding]

theorem even_pair_stabilizer_core_card (s : Pair) :
    Nat.card (pCore 2 (MulAction.stabilizer (alternatingGroup (Fin 6)) s.val)) = 4 := by
  let t : Pair := ⟨{0,1},by decide⟩
  obtain ⟨g,hg⟩ := exists_even_pair_transport s t
  have he : (pair 0 1) = g • s.val := by
    have hh := congrArg Subtype.val hg
    change s.val.map g.val.toEmbedding = {0,1} at hh
    change {0,1} = s.val.image g.val
    simpa only [Finset.map_eq_image,Equiv.coe_toEmbedding] using hh.symm
  let e : MulAction.stabilizer (alternatingGroup (Fin 6)) s.val ≃* a6DuadStabilizer :=
    MulAction.stabilizerEquivStabilizer he
  have hc : (pCore 2 (MulAction.stabilizer (alternatingGroup (Fin 6)) s.val)).map e.toMonoidHom =
      pCore 2 a6DuadStabilizer := pCore_map_iso 2 e
  have hh := card_map_of_injective (f := e.toMonoidHom) e.injective
    (K := pCore 2 (MulAction.stabilizer (alternatingGroup (Fin 6)) s.val))
  rw [hc,a6DuadCore_card] at hh
  exact hh.symm

theorem even_pair_normal_two_card_le_four (s : Pair) (Q : Subgroup (Equiv.Perm (Fin 6)))
    (hQ : IsPGroup 2 Q) (heven : Q ≤ alternatingGroup (Fin 6))
    (hfix : ∀ g ∈ Q, pairPerm g s = s)
    (hn : ∀ g : Equiv.Perm (Fin 6), Equiv.Perm.sign g = 1 → pairPerm g s = s →
      ∀ x ∈ Q, g * x * g⁻¹ ∈ Q) : Nat.card Q ≤ 4 := by
  let P := MulAction.stabilizer (alternatingGroup (Fin 6)) s.val
  let N := Q.subgroupOf (alternatingGroup (Fin 6))
  have hNP : N ≤ P := by
    intro x hx
    exact (pair_fix_iff s x.val).mp (hfix x hx)
  have hnorm : P ≤ normalizer (N : Set (alternatingGroup (Fin 6))) := by
    apply le_normalizer_iff.mpr
    intro g hg x hx
    exact hn g g.property ((pair_fix_iff s g.val).mpr hg) x hx
  have hcore : N ≤ P.pCoreIn 2 :=
    le_pCoreIn_of_normalizes hQ.comap_subtype hNP hnorm
  calc
    Nat.card Q = Nat.card N := (Nat.card_congr (subgroupOfEquivOfLe heven).toEquiv).symm
    _ ≤ Nat.card (P.pCoreIn 2) := Nat.card_le_card_of_injective _ (inclusion_injective hcore)
    _ = Nat.card (pCore 2 P) := card_map_of_injective P.subtype_injective
    _ = 4 := even_pair_stabilizer_core_card s
end BinaryPermutation.SixPairsQuadratic
