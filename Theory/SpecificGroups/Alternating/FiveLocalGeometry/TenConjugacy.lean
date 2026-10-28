module
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.PentagonNormalizer

/-!
# Conjugacy of order-ten subgroups in A₅

An order-ten subgroup has a normal Sylow five-subgroup and equals its
normalizer in A₅, whose order is ten. Sylow conjugacy therefore conjugates
any two such subgroups. This aligns the dihedral markings inside the
literal J₂ pointwise edge fixers in *Sporadic Groups*, 47.10, pp.266–267.
-/

public section
open Subgroup
namespace alternatingGroup.FiveLocalGeometry
variable {H : Type*} [Group H] [Finite H]
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem ten_is_five_normalizer (e : H ≃* A5)
    (B : Subgroup H) (hB : Nat.card B = 10) :
    ∃ P : Sylow 5 H, normalizer (P : Set H) = B := by
  let S : Sylow 5 B := default
  have hS : Nat.card S = 5 := by rw [S.card_eq_multiplicity, hB]; decide +kernel
  have hi : (S : Subgroup B).index = 2 := by
    have h := (S : Subgroup B).card_mul_index
    rw [hS, hB] at h
    omega
  let : (S : Subgroup B).Normal := normal_of_index_eq_two hi
  let P0 := (S : Subgroup B).map B.subtype
  have hP : Nat.card P0 = 5 := by rw [card_map_of_injective B.subtype_injective, hS]
  have hH : Nat.card H = 60 := (Nat.card_congr e.toEquiv).trans card
  let P : Sylow 5 H := Sylow.ofCard P0 (by rw [hP, hH]; decide +kernel)
  have hle : B ≤ normalizer (P0 : Set H) := by
    have hn := (S : Subgroup B).le_normalizer_map B.subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hn
    exact hn
  have hn : Nat.card (normalizer (P0 : Set H)) = 10 := by
    rw [← card_map_of_injective (f := e.toMonoidHom) e.injective, map_equiv_normalizer_eq]
    exact five_normalizer_card _ (by rw [card_map_of_injective e.injective, hP])
  exact ⟨P, (eq_of_le_of_card_ge hle (by rw [hn, hB])).symm⟩

/-- Any two order-ten subgroups in an actual A₅ are conjugate inside that A₅. -/
theorem ten_subgroups_conjugate (e : H ≃* A5)
    (B D : Subgroup H) (hB : Nat.card B = 10) (hD : Nat.card D = 10) :
    ∃ g : H, B.map (MulAut.conj g).toMonoidHom = D := by
  obtain ⟨P, hP⟩ := ten_is_five_normalizer e B hB
  obtain ⟨Q, hQ⟩ := ten_is_five_normalizer e D hD
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P Q
  have he := congrArg (fun R : Sylow 5 H => (R : Subgroup H)) hg
  change (P : Subgroup H).map (MulAut.conj g).toMonoidHom = (Q : Subgroup H) at he
  refine ⟨g, ?_⟩
  rw [← hP, ← hQ]
  change (normalizer ((P : Subgroup H) : Set H)).map (MulAut.conj g).toMonoidHom =
    normalizer ((Q : Subgroup H) : Set H)
  rw [map_equiv_normalizer_eq, he]
end alternatingGroup.FiveLocalGeometry
