module
public import Theory.GroupTheory.SubnormalOddCoreAction

/-!
# Subnormal odd-core action in a supplied overgroup

The subnormal odd-core action criterion applies to elementary A and K
inside a supplied subgroup U: A is normal in U and K is subnormal in U,
while the quotient order and core/center centralization conditions are
stated using the original ambient incarnations of A and K.

The intrinsic copy K.subgroupOf U is equivalent to K. The two-core map
identity transports its quotient and core, and central elements map into
the corresponding ambient core center. Reflect both commutators through
the injective inclusion of U, apply the intrinsic action criterion, and
map its conclusion back to the original ambient group.

This is the intrinsic-to-ambient transport for the two subnormal action
applications in Stellmacher (6.4), Journal of Algebra 190 (1997), p.32;
`refs/latex/stellmacher-n-group.tex`. The supplied overgroup is not
identified with the entire ambient group.
-/

namespace Subgroup

public theorem commutator_eq_bot_of_subnormal_odd_core_action_in
    {G : Type*} [Group G] [Finite G] (A K U : Subgroup G)
    [IsElementaryAbelian 2 A] (hAU : A ≤ U) (hKU : K ≤ U)
    (hAn : (A.subgroupOf U).Normal) (hKn : (K.subgroupOf U).IsSubnormal)
    (hodd : Odd (Nat.card (K ⧸ pCore 2 K)))
    (hcore : ⁅A, (pCore 2 K).map K.subtype⁆ = ⊥)
    (hcenter : ⁅(center ((pCore 2 K).map K.subtype)).map
      ((pCore 2 K).map K.subtype).subtype, K⁆ = ⊥) :
    ⁅A, K⁆ = ⊥ := by
  let AU := A.subgroupOf U
  let KU := K.subgroupOf U
  let Q := (pCore 2 KU).map KU.subtype
  let Qa := (pCore 2 K).map K.subtype
  let e : KU ≃* K := subgroupOfEquivOfLe hKU
  have hQmap : Q.map U.subtype = Qa := by
    dsimp [Q, Qa]
    rw [← pCore_map_iso 2 e, map_map, map_map]
    rfl
  have hcenterMap : ((center Q).map Q.subtype).map U.subtype ≤
      (center Qa).map Qa.subtype := by
    rintro _ ⟨z, ⟨zQ, hzQ, rfl⟩, rfl⟩
    have hzQa : ((zQ : U) : G) ∈ Qa := hQmap.le (mem_map_of_mem U.subtype zQ.property)
    refine mem_map.mpr ⟨⟨zQ, hzQa⟩, ?_, rfl⟩
    rw [mem_center_iff]
    intro y
    obtain ⟨yU, hyU, hy⟩ := mem_map.mp (hQmap.ge y.property)
    have hh := (mem_center_iff.mp hzQ) ⟨yU, hyU⟩
    apply Subtype.ext
    have hm := congrArg (fun t : Q => ((t : U) : G)) hh
    change (yU : G) * ((zQ : U) : G) = ((zQ : U) : G) * (yU : G) at hm
    change (yU : G) = (y : G) at hy
    rwa [hy] at hm
  have hcenterU : ⁅(center Q).map Q.subtype, KU⁆ = ⊥ := by
    apply (map_eq_bot_iff_of_injective (H := ⁅(center Q).map Q.subtype, KU⁆)
      (f := U.subtype) U.subtype_injective).mp
    rw [map_commutator, map_subgroupOf_eq_of_le hKU]
    exact bot_unique ((commutator_mono hcenterMap le_rfl).trans_eq hcenter)
  have hcoreU : ⁅AU, Q⁆ = ⊥ := by
    apply (map_eq_bot_iff_of_injective (H := ⁅AU, Q⁆)
      (f := U.subtype) U.subtype_injective).mp
    rw [map_commutator, map_subgroupOf_eq_of_le hAU, hQmap]
    exact hcore
  have hoddU : Odd (Nat.card (KU ⧸ pCore 2 KU)) := by
    rw [Nat.card_congr (QuotientGroup.congr (pCore 2 KU) (pCore 2 K) e
      (pCore_map_iso 2 e)).toEquiv]
    exact hodd
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : IsElementaryAbelian 2 AU := IsElementaryAbelian.subgroupOf hAU
  let _ : AU.Normal := hAn
  have hb := commutator_eq_bot_of_subnormal_odd_core_action AU KU hKn hoddU hcoreU hcenterU
  have hm := congrArg (map U.subtype) hb
  rwa [map_commutator, map_subgroupOf_eq_of_le hAU, map_subgroupOf_eq_of_le hKU,
    map_bot] at hm

end Subgroup
