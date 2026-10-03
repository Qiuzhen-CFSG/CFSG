module
public import Stellmacher.DihedralThreePowerCoreQuotient
public import Stellmacher.SL2FrattiniUniqueMaximal
public import Mathlib.GroupTheory.Frattini

/-!
# Ordinary dihedral quotient from a nested SL2 Frattini quotient

Let G be finite and solvable with nontrivial two-core. If the quotient
by its two-core, followed by the Frattini quotient, is SL2(2), then the
ordinary quotient G/O2(G) is dihedral with rotation order a power of three.

The core quotient has trivial two-core. Its Frattini subgroup is nilpotent;
a nontrivial Sylow two-subgroup there would be characteristic and hence
normal in the whole quotient. Consequently the Frattini subgroup has odd
order. Its quotient map is therefore injective on the Sylow two-subgroup,
whose image in SL2(2) has order two. This proves the actual Sylow/core
relative index two. The nested SL2 theorem supplies unique maximal
containment, and the existing dihedral recognition theorem applies to
the composite nested quotient map.

Source: Stellmacher (3.3) and (3.6), as used in the final step of (6.3),
Journal of Algebra 190 (1997), pp.21--23 and31,
refs/latex/stellmacher-n-group.tex. The nested quotient is preserved, and
no faithful-action quotient is substituted for the ordinary core quotient.
-/

namespace Stellmacher

public theorem dihedral_three_power_core_quotient_of_nested
    {G : Type*} [Group G] [Finite G]
    (hsolv : Group.IsSolvable G) (S : Sylow 2 G) (hcore : pCore 2 G ≠ ⊥)
    (hA : IsSL2Two ((G ⧸ pCore 2 G) ⧸ frattini (G ⧸ pCore 2 G))) :
    ∃ n : ℕ, Nonempty ((G ⧸ pCore 2 G) ≃* DihedralGroup (3 ^ n)) := by
  classical
  let Q := pCore 2 G
  let X := G ⧸ Q
  let q : G →* X := QuotientGroup.mk' Q
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective Q
  let F := frattini X
  let Y := X ⧸ F
  let r : X →* Y := QuotientGroup.mk' F
  have hr : Function.Surjective r := QuotientGroup.mk'_surjective F
  let T : Sylow 2 X := S.mapSurjective hq
  let U : Sylow 2 Y := T.mapSurjective hr
  have hXcore : pCore 2 X = ⊥ := by
    have hm := pCore_map_mk'_eq_of_normal_isPGroup
      (G := G) (p := 2) Q (pCore_isPGroup (p := 2) (G := G))
    have hb : (pCore 2 G).map q = ⊥ := (Subgroup.map_eq_bot_iff _).mpr
      (show pCore 2 G ≤ q.ker from (QuotientGroup.ker_mk' Q).symm.le)
    exact hm.symm.trans hb
  have hFodd : ¬ 2 ∣ Nat.card F := by
    let P : Sylow 2 F := default
    have hn : (P : Subgroup F).Normal :=
      Group.IsNilpotent.sylow_normal (show Group.IsNilpotent F from frattini_nilpotent) 2 P
    let _ : (P : Subgroup F).Characteristic := Sylow.characteristic_of_normal P hn
    have hmap : (P : Subgroup F).map F.subtype ≤ pCore 2 X :=
      le_sSup ⟨inferInstance, P.isPGroup'.map F.subtype⟩
    have hPbot : (P : Subgroup F) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ F.subtype_injective).mp
        (le_bot_iff.mp (hmap.trans_eq hXcore))
    intro hdvd
    exact P.ne_bot_of_dvd_card hdvd hPbot
  have hTF : (T : Subgroup X) ⊓ F = ⊥ := by
    rcases (T.isPGroup'.to_le (show (T : Subgroup X) ⊓ F ≤ T from inf_le_left)).card_eq_or_dvd
      with hc | hd
    · exact Subgroup.card_eq_one.mp hc
    · exact (hFodd (hd.trans (Subgroup.card_dvd_of_le inf_le_right))).elim
  have hrT : Function.Injective (r.comp (T : Subgroup X).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply bot_unique
    intro t ht
    have htF : (t : X) ∈ F := (QuotientGroup.eq_one_iff (N := F) _).mp ht
    have hone : (t : X) ∈ (T : Subgroup X) ⊓ F := ⟨t.property, htF⟩
    rw [hTF] at hone
    exact Subtype.ext hone
  have hUcard : Nat.card U = 2 := by
    rw [U.card_eq_multiplicity, SectionOne.RankOneThreeGroupAssembly.isSL2Two_card hA]
    have hf : Nat.factorization 6 2 = 1 := by
      change Nat.factorization (3 * 2) 2 = 1
      rw [Nat.factorization_mul (by decide) (by decide)]
      norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
    simp [hf]
  have hTcard : Nat.card T = 2 := by
    have hTrange : (r.comp (T : Subgroup X).subtype).range = (U : Subgroup Y) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rfl
    have hc := Nat.card_congr (MonoidHom.ofInjective hrT).toEquiv
    rw [hTrange] at hc
    exact hc.trans hUcard
  have hidx : (pCore 2 G).relIndex (S : Subgroup G) = 2 := by
    change Q.relIndex (S : Subgroup G) = 2
    rw [← QuotientGroup.ker_mk' Q, Subgroup.relIndex_ker]
    exact hTcard
  exact dihedral_three_power_core_quotient hsolv S hcore
    (isUniqueMaximalContaining_of_sl2Two_frattini S hA) hidx (r.comp q) (hr.comp hq) hA

end Stellmacher

