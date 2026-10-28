module
public import Theory.GroupAction.NoOrderFortyOnSixteen

public import Theory.Mathieu.M23.QuasithinGeometry.SylowTwoLocals.Coverage
public import Theory.Mathieu.M23.QuasithinGeometry.SylowTwoLocals.TripleSolvable.PointComparison
public import Theory.Mathieu.M22.Properties.QuinticSylowOvergroups
public import Theory.GroupTheory.TwoPrimeSolvable
public import Theory.GroupTheory.SolvableSmallOddCore
public import Theory.GroupTheory.TwoLocalCoreObstruction

/-!
# Quintic Sylow overgroups in the native M₂₃ carrier

A two-five overgroup of a full Sylow two-subgroup with nontrivial five-part
would have order 640. Burnside solvability and the small odd-core theorem
give a nontrivial two-core. Native maximal two-local coverage places it in
a heptad or triple stabilizer. The heptad quotient would have order forty
and act faithfully on its actual sixteen-element translation kernel. The
triple action has two-group image, hence fixes a point; the native M₂₂
point-stabilizer equivalence then contradicts its three-free Sylow bound.

All normality is relative to the named local subgroup, and all permutation
and kernel actions use the original design carriers. No new maximal-subgroup
classification or simplicity certification is assumed.
Source: Aschbacher–Smith 15.1.21(ii), 15.1.22(5), pp.1098–1100;
GLS3 Table 5.3d for the native heptad and triple stabilizers.
-/

public section
open Subgroup MulAction Theory.GroupTheory
open scoped Pointwise
namespace Sporadic.Mathieu.M23QuinticSylow
open M23Geometry M23Geometry.SylowTwoLocals

private theorem heptad_action_injective : Function.Injective heptadConjugation := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top
    (by simp : 5 ≤ Nat.card (Fin 7)) (N := heptadConjugation.ker) with he | he
  · exact he
  · have hall (u : heptadKernel) : u = 1 := by
      apply (heptadConjugation_cycle_fixed_iff u).mp
      have hc : heptadConjugation AlternatingSection.c = 1 := by
        change AlternatingSection.c ∈ heptadConjugation.ker
        rw [he]
        trivial
      exact DFunLike.congr_fun hc u
    have hs : Subsingleton heptadKernel := ⟨fun x y => (hall x).trans (hall y).symm⟩
    have hc := Nat.card_eq_one_iff_unique.mpr ⟨hs, ⟨1⟩⟩
    rw [heptadKernel_card] at hc
    omega

private theorem heptad_no_order640 (P : Sylow 2 heptadStabilizer)
    (H : Subgroup heptadStabilizer) (hPH : (P : Subgroup _) ≤ H)
    (hc : Nat.card H = 640) : False := by
  let f := heptadAlternatingAction
  have hk : f.ker = heptadKernel := heptadAlternatingAction_ker
  have hkc : Nat.card f.ker = 16 := hk ▸ heptadKernel_card
  have hkp : IsPGroup 2 f.ker := IsPGroup.of_card (hkc.trans (by decide : 16 = 2^4))
  have hkh : f.ker ≤ H := (hkp.le_sylow_of_normal P).trans hPH
  have hh := (f.ker.subgroupOf H).card_mul_index
  change Nat.card (f.ker.subgroupOf H) * f.ker.relIndex H = _ at hh
  rw [relIndex_ker,Nat.card_congr (subgroupOfEquivOfLe hkh).toEquiv,hkc,hc] at hh
  have hI : Nat.card (H.map f) = 40 := by omega
  exact Theory.GroupAction.card_ne_forty_of_faithful_sixteen
    (heptadConjugation.comp (H.map f).subtype)
    (heptad_action_injective.comp (H.map f).subtype_injective) heptadKernel_card hI

private theorem m22_no_order640 (H : Subgroup M22) (hc : Nat.card H = 640) : False := by
  let P : Sylow 2 H := Classical.choice inferInstance
  let Q := (P : Subgroup H).map H.subtype
  have hQ : Nat.card Q = 128 := by
    rw [card_map_of_injective H.subtype_injective,Sylow.card_eq_multiplicity,hc]
    decide +kernel
  let R : Sylow 2 M22 := Sylow.ofCard Q (by rw [hQ,m22_order]; decide +kernel)
  have hh := M22QuinticSylow.card_eq_128 R H (map_subtype_le _)
    (by rw [hc]; decide) (by rw [hc]; decide)
  omega

private theorem triple_no_order640 (H : Subgroup tripleStabilizer)
    (hc : Nat.card H = 640) : False := by
  let F : Finset (Fin 23) := {0,1,2}
  let f : H →* Equiv.Perm F := {
    toFun g := g.val.val.val.subtypePerm (MulAction.mem_stabilizer_finset.mp g.val.property)
    map_one' := by ext x; rfl
    map_mul' := by intros; ext x; rfl }
  have hF : Nat.card F = 3 := by rw [Nat.card_eq_fintype_card]; decide
  have hI : IsPGroup 2 f.range := by
    have h6 : Nat.card f.range ∣ 6 := by
      have hh := f.range.card_subgroup_dvd_card
      rw [Nat.card_perm,hF] at hh
      exact hh
    have h640 : Nat.card f.range ∣ 640 := by
      rw [←hc,←index_ker]
      exact f.ker.index_dvd_card
    have h2 : Nat.card f.range ∣ 2 := by
      simpa using Nat.dvd_gcd h6 h640
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h2
    · exact IsPGroup.of_card (h1.trans (by decide : 1 = 2^0))
    · exact IsPGroup.of_card (h2.trans (by decide : 2 = 2^1))
  obtain ⟨x,hx⟩ := hI.nonempty_fixed_point_of_prime_not_dvd_card F (by rw [hF]; decide)
  let k : H →* stabilizer M23 (x.val : Fin 23) := {
    toFun g := ⟨g.val.val, congrArg Subtype.val (hx ⟨f g, ⟨g,rfl⟩⟩)⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hki : Function.Injective k := by
    intro a b hab
    have hh : a.val.val = b.val.val :=
      congrArg (fun z : stabilizer M23 x.val => (z : M23)) hab
    exact Subtype.ext (Subtype.ext hh)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M23 x.val (9 : Fin 23)
  let e : stabilizer M23 x.val ≃* M22 :=
    (MulAction.stabilizerEquivStabilizer hg.symm).trans m23EquivM22PointStabilizer.symm
  let r := e.toMonoidHom.comp k
  have hri : Function.Injective r := e.injective.comp hki
  apply m22_no_order640 r.range
  exact (Nat.card_congr (MonoidHom.ofInjective hri).toEquiv).symm.trans hc

private theorem twoCore_ne_bot (H : Subgroup M23) (hc : Nat.card H = 640) :
    pCore 2 H ≠ ⊥ := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hprime (q : ℕ) (hq : q.Prime) (hd : q ∣ Nat.card H) : q = 2 ∨ q = 5 := by
    rw [hc,show 640 = 2^7 * 5 from rfl] at hd
    rcases hq.dvd_mul.mp hd with h2 | h5
    · exact .inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2))
    · exact .inr ((Nat.prime_dvd_prime_iff_eq hq (by decide)).mp h5)
  have hs := isSolvable_of_prime_dvd_card_eq_two_or_prime H (by decide : Nat.Prime 5) hprime
  let P : Sylow 5 H := Classical.choice inferInstance
  have hP : Nat.card P = 5 := by rw [Sylow.card_eq_multiplicity,hc]; decide +kernel
  have hsmall : Nat.card (pCore 5 H) ≤ 5^1 := by
    have hh := card_le_of_le ((pCore_isPGroup (p := 5) (G := H)).le_sylow_of_normal P)
    simpa only [hP,pow_one] using hh
  apply twoCore_ne_bot_of_solvable_small_odd_core (p := 5) (d := 1) (t := 7)
    (by decide) hs hprime hsmall (by rw [hc]; decide)
  intro n hn
  interval_cases n <;> norm_num [Fin.prod_univ_succ]

/-- There is no subgroup of order 640 in the native degree-23 Mathieu group. -/
private theorem no_subgroup_order640 (P : Sylow 2 M23) (H : Subgroup M23)
    (hPH : (P : Subgroup M23) ≤ H) (hc : Nat.card H = 640) : False := by
  obtain ⟨N,hN,hHN⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot H (twoCore_ne_bot H hc)
  obtain ⟨i,⟨e⟩⟩ := sylow_maximal_twoLocal_coverage P N hN (hPH.trans hHN)
  let Q := (P.subtype (hPH.trans hHN)).mapSurjective (f := e.toMonoidHom) e.surjective
  let X := (H.subgroupOf N).map e.toMonoidHom
  have hQX : (Q : Subgroup _) ≤ X := map_mono (comap_mono hPH)
  have hX : Nat.card X = 640 := by
    rw [card_map_of_injective e.injective,Nat.card_congr (subgroupOfEquivOfLe hHN).toEquiv,hc]
  fin_cases i
  · exact heptad_no_order640 Q X hQX hX
  · exact triple_no_order640 X hX

/-- A native M₂₃ overgroup of a full Sylow two-subgroup cannot have
order divisible by five and supported only at two and five. -/
theorem not_five_of_two_five_sylow_overgroup (P : Sylow 2 M23) (H : Subgroup M23)
    (hPH : (P : Subgroup M23) ≤ H) (a b : ℕ)
    (hc : Nat.card H ∣ 2^a * 5^b) : ¬5 ∣ Nat.card H := by
  intro h5
  have hP : Nat.card P = 128 := by rw [Sylow.card_eq_multiplicity,m23_order]; decide +kernel
  have h128 : 128 ∣ Nat.card H := hP ▸ card_dvd_of_le hPH
  have hlo : 640 ∣ Nat.card H :=
    (by decide : Nat.Coprime 128 5).mul_dvd_of_dvd_of_dvd h128 h5
  have hcop : Nat.Coprime 15939 (Nat.card H) :=
    ((((by decide : Nat.Coprime 15939 2).pow_right a).mul_right
      ((by decide : Nat.Coprime 15939 5).pow_right b))).of_dvd_right hc
  have hhi : Nat.card H ∣ 640 := by
    have hh := H.card_subgroup_dvd_card
    rw [m23_order,show 10200960 = 640 * 15939 from rfl] at hh
    exact hcop.symm.dvd_mul_right.mp hh
  exact no_subgroup_order640 P H hPH (Nat.dvd_antisymm hhi hlo)

end Sporadic.Mathieu.M23QuinticSylow
