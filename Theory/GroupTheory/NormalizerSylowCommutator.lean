module
public import Theory.GroupTheory.CyclicSylowAction
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Derived subgroups of two-subgroups in a normalizer

If the derived subgroup of one Sylow two-subgroup of N(Z) centralizes Z,
then the same holds for every two-subgroup of N(Z). Embed the subgroup
in a Sylow subgroup, conjugate within N(Z), and use N(Z)-invariance of C(Z).

Source application: Aschbacher–Smith, original 2.4.21, printed p.536.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A derived-centralizer bound on one Sylow subgroup of a normalizer holds
for every two-subgroup of that normalizer. -/
theorem normalizer_commutator_le_of_sylow_derived
    (Z S : Subgroup G)
    (P : Sylow 2 (normalizer (Z : Set G)))
    (hP : (P : Subgroup (normalizer (Z : Set G))).map
      (normalizer (Z : Set G)).subtype = S)
    (hSC : ⁅S,S⁆≤centralizer (Z : Set G))
    (I : Subgroup G) (hI : IsPGroup 2 I) (hIN : I≤normalizer (Z : Set G)) :
    ⁅I,I⁆≤centralizer (Z : Set G) := by
  let N := normalizer (Z : Set G)
  let J := I.subgroupOf N
  obtain ⟨Q,hJQ⟩ := (hI.comap_subtype (K := N)).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq N P Q
  have hQP : (Q : Subgroup N).map N.subtype = S.conjBy (g:G) := by
    rw [←hg]
    change ((P : Subgroup N).map (MulAut.conj g).toMonoidHom).map N.subtype = _
    rw [←hP]
    change ((P : Subgroup N).map (MulAut.conj g).toMonoidHom).map N.subtype =
      ((P : Subgroup N).map N.subtype).map (MulAut.conj (g:G)).toMonoidHom
    rw [map_map,map_map]
    rfl
  have hIP : I≤S.conjBy (g:G) := by
    rw [←hQP,←map_subgroupOf_eq_of_le hIN]
    exact map_mono hJQ
  have hCN : (g:G)∈normalizer (centralizer (Z : Set G) : Set G) :=
    normalizer_le_normalizer_centralizer Z g.property
  calc
    ⁅I,I⁆ ≤ ⁅S.conjBy (g:G),S.conjBy (g:G)⁆ := commutator_mono hIP hIP
    _ = (⁅S,S⁆).map (MulAut.conj (g:G)).toMonoidHom := (map_commutator _ _ _).symm
    _ ≤ (centralizer (Z : Set G)).map (MulAut.conj (g:G)).toMonoidHom := map_mono hSC
    _ = centralizer (Z : Set G) := mem_normalizer_iff_map_conj_eq.mp hCN
end Theory.GroupTheory
