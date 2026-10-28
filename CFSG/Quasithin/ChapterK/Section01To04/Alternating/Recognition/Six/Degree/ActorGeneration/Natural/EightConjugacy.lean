module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.ElementaryPair
public import Theory.Representation.BinaryOffender.ElementaryConjugateBudget.Transport

/-!
# Fusion of elementary eight-groups in Aut(A₆)

The marked Sylow classification gives two elementary eight-groups, exchanged
by a specified Sylow element. Sylow conjugacy therefore fuses all elementary
eight-groups in the actual automorphism carrier. This permits transport of
a single two-conjugate generation calculation.

Source: the group-generation bound used for Aschbacher–Smith K.1.1, printed
p.452 / PDF p.463, citing GM02 Theorem 6.2 and Table 6.3. This is an intrinsic
generation calculation, not the full representation-theoretic conclusion.
-/

public section

open Subgroup AlternatingSix.ShadowLocal
open scoped Pointwise
namespace CFSG.Quasithin.ChapterK.Alternating.SixDegreeReduction.ActorGenerationProof.NaturalProof

private theorem local_eight_conjugacy (P : Sylow 2 AutA6) (E F : Subgroup P)
    [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 F]
    (hE : Nat.card E = 8) (hF : Nat.card F = 8) :
    ∃ g : P, E.map (MulAut.conj g).toMonoidHom = F := by
  rcases ElementaryPair.elementary_eight_cases P E hE with rfl | rfl <;>
    rcases ElementaryPair.elementary_eight_cases P F hF with rfl | rfl
  · exact ⟨1, by rw [map_one]; exact Subgroup.map_id _⟩
  · exact ⟨Identification.sylowEquiv P Holomorph.rotation, ElementaryPair.rotation_conjugates P⟩
  · exact ⟨Identification.sylowEquiv P Holomorph.rotation, ElementaryPair.rotation_conjugates_one P⟩
  · exact ⟨1, by rw [map_one]; exact Subgroup.map_id _⟩

theorem eight_conjugacy (E F : Subgroup AutA6)
    [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 F]
    (hE : Nat.card E = 8) (hF : Nat.card F = 8) :
    ∃ g : AutA6, E.map (MulAut.conj g).toMonoidHom = F := by
  obtain ⟨Q,hEQ⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  obtain ⟨P,hFP⟩ := (IsElementaryAbelian.isPGroup 2 F).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq AutA6 Q P
  have hQP : (Q : Subgroup AutA6).map (MulAut.conj g).toMonoidHom = P := by
    exact congrArg (fun R : Sylow 2 AutA6 => (R : Subgroup AutA6)) hg
  let E' := E.map (MulAut.conj g).toMonoidHom
  have hEP : E' ≤ P := by
    rw [← hQP]
    exact Subgroup.map_mono hEQ
  let : IsElementaryAbelian 2 E' := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (E'.subgroupOf (P : Subgroup AutA6)) := IsElementaryAbelian.subgroupOf hEP
  let : IsElementaryAbelian 2 (F.subgroupOf (P : Subgroup AutA6)) := IsElementaryAbelian.subgroupOf hFP
  have hcE : Nat.card (E'.subgroupOf (P : Subgroup AutA6)) = 8 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEP).toEquiv,
      Subgroup.card_map_of_injective (MulAut.conj g).injective, hE]
  have hcF : Nat.card (F.subgroupOf (P : Subgroup AutA6)) = 8 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hFP).toEquiv, hF]
  obtain ⟨k,hk⟩ := local_eight_conjugacy P _ _ hcE hcF
  have hm := congrArg (Subgroup.map (P : Subgroup AutA6).subtype) hk
  rw [map_subgroupOf_eq_of_le hFP] at hm
  have heq : (E'.subgroupOf (P : Subgroup AutA6)).map
      ((P : Subgroup AutA6).subtype.comp (MulAut.conj k).toMonoidHom) =
      (E'.subgroupOf (P : Subgroup AutA6)).map
      ((MulAut.conj (k : AutA6)).toMonoidHom.comp (P : Subgroup AutA6).subtype) := rfl
  rw [map_map, heq, ← map_map, map_subgroupOf_eq_of_le hEP] at hm
  refine ⟨(k : AutA6) * g, ?_⟩
  rw [← hm]
  change E.map (MulAut.conj ((k : AutA6) * g)).toMonoidHom =
    (E.map (MulAut.conj g).toMonoidHom).map (MulAut.conj (k : AutA6)).toMonoidHom
  rw [map_map]
  congr 1

end CFSG.Quasithin.ChapterK.Alternating.SixDegreeReduction.ActorGenerationProof.NaturalProof
