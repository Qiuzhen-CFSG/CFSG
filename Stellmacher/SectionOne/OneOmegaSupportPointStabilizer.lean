module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Basic
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Mathlib.Tactic

/-!
# Four-point odd supports and their point stabilizers

For a faithful Section One action, an odd-core subgroup with displacement
of order four has order three and hence belongs to the source's omega
family. If such a factor lies in the three-core, every element fixing a
specified nonidentity vector of its support normalizes the factor.

Coprime splitting makes the odd subgroup faithful on its four-element
support. It therefore embeds in the six-element automorphism group of a
Klein four; oddness and nontrivial support force order three. For the
stabilizer statement, the vector belongs to both the factor's support and
its conjugate's support. The pairwise disjointness theorem from (1.4)
forces these two factors to coincide. The supplied three-core containment
is essential and retained explicitly.

These results supply the support-invariance step in Stellmacher (10.1),
printed p.63, the first support case preceding (13). The graph consumer
proves the required three-core containment using (3.3).
-/

namespace Stellmacher.SectionOne
open Subgroup
open scoped IsMulCommutative
universe u

public theorem oneOmega_of_odd_four_support
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (hyp : Hypotheses G V) (R : Subgroup G) (hR : R ≤ oddCore G)
    (hfour : Nat.card (commutatorAction R V) = 4) :
    oneOmega (G := G) (V := V) R := by
  classical
  let U := commutatorAction R V
  let _ : IsInvariant R V U := commutatorAction_isInvariant
  let _ : IsElementaryAbelian 2 U := RankOneThreeGroupAssembly.isElementaryAbelian_subgroup U
  have hUfour : Nat.card U = 4 := hfour
  let _ : Nontrivial U := (Finite.one_lt_card_iff_nontrivial).mp (by rw [hUfour]; decide)
  let _ : IsKleinFour U := ⟨hUfour, IsElementaryAbelian.exponent_eq_prime⟩
  have hodd : Odd (Nat.card R) := Nat.coprime_two_left.mp
    ((pPrimeCore_coprime_card (p := 2) (G := G)).of_dvd_right (card_dvd_of_le hR))
  have hcop : Nat.Coprime (Nat.card R) (Nat.card V) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hn]
    exact hodd.coprime_two_right.pow_right n
  have hsplit := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (G := V) (A := R) (Group.isSolvable_of_comm fun x y => mul_comm x y) hcop inferInstance
  let f : R →* MulAut U := MulDistribMulAction.toMulAut R U
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply bot_unique
    intro r hr
    have hfixU (v : U) : r • v = v := by
      have hh := DFunLike.congr_fun hr v
      exact hh
    have hfixV (v : V) : (r : G) • v = v := by
      have hv : v ∈ FixedPoints.subgroup R V ⊔ U := by
        rw [hsplit.sup_eq_top]
        exact mem_top v
      obtain ⟨c, hc, d, hd, rfl⟩ := mem_sup_of_normal_left.mp hv
      have hcfix := ((FixedPoints.mem_subgroup (M := R) (a := c)).mp hc) r
      have hdfix := congrArg Subtype.val (hfixU ⟨d, hd⟩)
      change (r : G) • c = c at hcfix
      change (r : G) • d = d at hdfix
      rw [smul_mul', hcfix, hdfix]
    have hker : (r : G) ∈ fixingSubgroup G (Set.univ : Set V) :=
      (mem_fixingSubgroup_iff G).mpr (fun v _ => hfixV v)
    rw [hyp.action_faithful] at hker
    exact Subtype.ext hker
  have hdiv : Nat.card R ∣ 6 := by
    simpa only [IsKleinFour.card_mulAut] using card_dvd_of_injective f hinj
  have hthree : Nat.card R = 3 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp
      (hodd.coprime_two_right.dvd_of_dvd_mul_left hdiv) with hone | hthree
    · have hbot := card_eq_one.mp hone
      have hUbot : commutatorAction R V = ⊥ := by
        apply bot_unique
        rw [commutatorAction_eq_closure, Subgroup.closure_le]
        rintro v ⟨r, w, rfl⟩
        have hr : (r : G) = 1 := hbot ▸ r.property
        change w⁻¹ * (r : G) • w ∈ (⊥ : Subgroup V)
        simp [hr]
      rw [hUbot, card_bot] at hfour
      omega
    · exact hthree
  exact ⟨hR, hthree, hfour⟩

public theorem oneOmega_point_stabilizer_le_normalizer
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (hyp : Hypotheses G V) (R : Subgroup G)
    (hR : oneOmega (G := G) (V := V) R) (hcore : R ≤ pCore 3 G)
    (v : V) (hv : v ∈ commutatorAction R V) (hne : v ≠ 1) :
    MulAction.stabilizer G v ≤ normalizer (R : Set G) := by
  intro g hg
  have hRconj : oneOmega (G := G) (V := V) (R.conjBy g) :=
    RankOneThreeGroupAssembly.oneOmega_conjBy R hR g
  have hcoreconj : R.conjBy g ≤ pCore 3 G := by
    rintro x ⟨r, hr, rfl⟩
    exact (inferInstance : (pCore 3 G).Normal).conj_mem r (hcore hr) g
  have hvconj : v ∈ commutatorAction (R.conjBy g) V := by
    rw [← RankOneThreeGroupAssembly.commutatorAction_conjBy R g]
    exact ⟨v, hv, hg⟩
  have hsame : R = R.conjBy g := by
    by_contra hnot
    exact hne (Subgroup.disjoint_def.mp
      (omega_pair_action_disjoint hyp hR hRconj hnot hcore hcoreconj le_rfl) hv hvconj)
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  exact hsame.symm

end Stellmacher.SectionOne
