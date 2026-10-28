module
public import Theory.SpecificGroups.SL2.TwoCoreBorel
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Two-cores of solvable Sylow intersections in binary SL₂ covers

A solvable overgroup of a full Sylow two-subgroup in a two-group cover
of binary SL₂ is proper and lies in its Sylow normalizer. Its two-core
is therefore exactly that Sylow subgroup. For a subnormal embedded cover,
this identifies the two-core of its intersection with a solvable ambient
Sylow overgroup. Characteristicity then controls the relative normalizer.

The quotient homomorphism and the prescribed Sylow subgroup are retained.
The source application is the exchanged PSL₂(16) pair in Aschbacher–Smith
14.6.15, printed pp.1033–1034, before the module comparison.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {A F : Type*} [Group A] [Finite A] [Field F] [Finite F] [CharP F 2]

/-- A solvable full-Sylow overgroup has precisely the prescribed Sylow as two-core. -/
theorem solvable_sylow_overgroup_core
    (q : A →* SL(2,F)) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (hns : ¬ Group.IsSolvable SL(2,F)) (P : Sylow 2 A)
    (B : Subgroup A) [Group.IsSolvable B] (hPB : (P : Subgroup A) ≤ B) :
    B.pCoreIn 2 = (P : Subgroup A) := by
  have hb : B ≠ ⊤ := by
    intro he
    have hs : Group.IsSolvable (⊤ : Subgroup A) := he ▸ inferInstanceAs (Group.IsSolvable B)
    let := hs
    let : Group.IsSolvable A := Group.isSolvable_of_surjective
      (f := (topEquiv (G := A)).toMonoidHom) (topEquiv (G := A)).surjective
    exact hns (Group.isSolvable_of_surjective hq)
  have hn := proper_overgroup_le_sylow_normalizer_of_two_kernel q hq P
    (hk.le_sylow_of_normal P) B hPB hb
  apply le_antisymm
  · simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hPB] using
      B.pCoreIn_le_sylow (P.subtype hPB)
  · exact le_pCoreIn_of_normalizes P.isPGroup' hPB hn

variable {G : Type*} [Group G] [Finite G]
/-- The same two-core identity for the literal intersection with a subnormal cover. -/
theorem solvable_intersection_core
    (T : Sylow 2 G) (K H : Subgroup G) (hK : K.IsSubnormal)
    (q : K →* SL(2,F)) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (hns : ¬ Group.IsSolvable SL(2,F)) [Group.IsSolvable H]
    (hTH : (T : Subgroup G) ≤ H) :
    (K ⊓ H).pCoreIn 2 = K ⊓ (T : Subgroup G) := by
  obtain ⟨P,hP⟩ := T.exists_subgroupOf_eq_of_subnormal K hK
  let B := H.subgroupOf K
  let f : B →* H := (K.subtype.comp B.subtype).codRestrict H (fun x => x.property)
  let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
    (f := f) (by
      intro x y he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : H => (z : G)) he)
  have hPB : (P : Subgroup K) ≤ B := by
    rw [hP]
    exact fun x hx => hTH hx
  have hc := congrArg (Subgroup.map K.subtype)
    (solvable_sylow_overgroup_core q hq hk hns P B hPB)
  rw [map_pCoreIn_of_injective 2 _ _ K.subtype_injective,
    subgroupOf_map_subtype, hP, subgroupOf_map_subtype] at hc
  simpa only [inf_comm] using hc

/-- The full relative normalizer in the solvable Sylow overgroup preserves
its actual component Sylow intersection. -/
theorem solvable_intersection_normalizer
    (T : Sylow 2 G) (K H : Subgroup G) (hK : K.IsSubnormal)
    (q : K →* SL(2,F)) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (hns : ¬ Group.IsSolvable SL(2,F)) [Group.IsSolvable H]
    (hTH : (T : Subgroup G) ≤ H) :
    H ⊓ normalizer (K : Set G) ≤ normalizer ((K ⊓ (T : Subgroup G) : Subgroup G) : Set G) := by
  rw [←solvable_intersection_core T K H hK q hq hk hns hTH]
  exact ((le_inf inf_le_right (inf_le_left.trans H.le_normalizer)).trans
    inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image (K ⊓ H) (pCore 2 (K ⊓ H : Subgroup G)))

end Matrix.SpecialLinearGroup
