module

public import Theory.SpecificGroups.Alternating.TwoThreeCycles
public import Theory.GroupTheory.DihedralPresentation
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Mathlib.GroupTheory.Sylow
public import Theory.Quasithin.Rank
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Subgroup obstructions for the alternating group on six letters

The two disjoint three-cycles obstruct embeddings in groups of three-rank
at most one. Two explicit double transpositions generate a two-subgroup
with noncommuting involutions; Sylow conjugacy therefore excludes embeddings
in any finite group whose Sylow two-subgroup has commuting involutions.

These are intrinsic subgroup arguments for the rank-one families in the
inspection of Aschbacher–Smith, E.6.23, printed p.254, combined manuscript
of 1 March 2004. A perfect fixed component lies in the derived fixed group. At order 360,
a fixed A₆ fills the group and forces the automorphism to be identity.
No automorphism classification is assumed.
-/

public section

open Subgroup Theory.GroupTheory
namespace alternatingGroup.SixSubgroupObstructions

theorem card_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

theorem not_injective_of_three_rank_le_one {G : Type*} [Group G] [Finite G]
    (hr : primeRank 3 G ≤ 1) (f : (alternatingGroup (Fin 6)) →* G) : ¬ Function.Injective f := by
  intro hf
  have hh := (primeRank_le_of_injective 3 f hf).trans hr
  change primeRank 3 (alternatingGroup (Fin 6)) ≤ 1 at hh
  have hl := alternatingGroup.TwoThreeCycles.two_le_primeRank (n := 6) (by decide)
  omega

private def x : (alternatingGroup (Fin 6)) := ⟨Equiv.swap 0 1 * Equiv.swap 4 5, by change Equiv.Perm.sign _ = 1; decide⟩
private def y : (alternatingGroup (Fin 6)) := ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by change Equiv.Perm.sign _ = 1; decide⟩
private theorem x_sq : x ^ 2 = 1 := by decide
private theorem y_sq : y ^ 2 = 1 := by decide
private theorem yx_four : (y * x) ^ 4 = 1 := by decide
private theorem yx_order : orderOf (y * x) = 4 := by
  exact orderOf_eq_prime_pow (p := 2) (n := 1) (by decide) yx_four

private theorem xy_not_commute : ¬ Commute x y := by
  change ¬ x * y = y * x
  decide

/-- A concrete two-subgroup of A₆ contains two noncommuting involutions. -/
theorem exists_two_subgroup_noncommuting_involutions :
    ∃ (P : Subgroup (alternatingGroup (Fin 6))), IsPGroup 2 P ∧
      ∃ a b : P, a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ ¬ Commute a b := by
  let P := closure ({x, y} : Set (alternatingGroup (Fin 6)))
  have hx : x ∈ P := subset_closure (by simp)
  have hy : y ∈ P := subset_closure (by simp)
  have hd : 4 ∣ Nat.card P := by
    have h := orderOf_dvd_natCard (⟨y * x, P.mul_mem hy hx⟩ : P)
    rwa [← Subgroup.orderOf_coe, yx_order] at h
  have hb := (closure_pair_finite_card_le_of_involutions (by decide : 0 < 4)
    x y x_sq y_sq yx_four).2
  change Nat.card P ≤ 2 * 4 at hb
  have hpos : 0 < Nat.card P := Nat.card_pos
  have hc : Nat.card P = 4 ∨ Nat.card P = 8 := by omega
  have hp : IsPGroup 2 P := by
    rcases hc with hc | hc
    · exact IsPGroup.of_card (n := 2) hc
    · exact IsPGroup.of_card (n := 3) hc
  refine ⟨P, hp, ⟨x, hx⟩, ⟨y, hy⟩, ?_, ?_, ?_⟩
  · exact Subtype.ext x_sq
  · exact Subtype.ext y_sq
  · intro h
    exact xy_not_commute (h.map P.subtype)

/-- Commuting involutions in one Sylow two-subgroup exclude an A₆ embedding. -/
theorem not_injective_of_sylow_involutions_commute {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G)
    (hP : ∀ a b : P, a ^ 2 = 1 → b ^ 2 = 1 → Commute a b)
    (f : (alternatingGroup (Fin 6)) →* G) : ¬ Function.Injective f := by
  intro hf
  obtain ⟨R, hR, a, b, ha, hb, hab⟩ := exists_two_subgroup_noncommuting_involutions
  obtain ⟨Q, hQ⟩ := (hR.map f).exists_le_sylow
  let e' : Q ≃* P := Q.equiv P
  let r : R →* P := e'.toMonoidHom.comp
    ((f.comp R.subtype).codRestrict Q (by intro z; exact hQ ⟨z, z.property, rfl⟩))
  have hi : Function.Injective r := by
    intro z w h
    apply Subtype.ext
    apply hf
    exact congrArg Subtype.val (e'.injective h)
  apply hab
  apply hi
  simpa only [map_mul] using (hP (r a) (r b)
    (by rw [← map_pow, ha, map_one]) (by rw [← map_pow, hb, map_one])).eq
variable {D : Type*} [Group D] [Finite D]

/-- A perfect subgroup of a fixed group embeds in its first derived subgroup. -/
theorem not_six_of_derived_fixed_rank (a : MulAut D)
    (hr : primeRank 3 (commutator a.fixedSubgroup) ≤ 1)
    (S : Subgroup D) (hS : IsComponentIn S a.fixedSubgroup) :
    ¬ Nonempty (S ≃* alternatingGroup (Fin 6)) := by
  rintro ⟨e⟩
  let : IsQuasisimple S := hS.quasisimple
  let f : S →* a.fixedSubgroup := inclusion hS.1
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hfc : f.range ≤ commutator a.fixedSubgroup := by
    rw [← Subgroup.commutator_eq_self (H := f.range)]
    exact commutator_mono le_top le_top
  let g : S →* commutator a.fixedSubgroup := f.codRestrict _ (fun s => hfc ⟨s, rfl⟩)
  have hg : Function.Injective g := by
    intro x y h
    exact Subtype.ext (congrArg (fun z => z.val.val) h)
  exact not_injective_of_three_rank_le_one hr (g.comp e.symm.toMonoidHom)
    (hg.comp e.symm.injective)

/-- In the order-360 endpoint, a fixed A₆ fills the group and forces the actor to be identity. -/
theorem not_six_fixed_of_card (hc : Nat.card D = 360)
    (a : MulAut D) (ha : orderOf a = 2) (S : Subgroup D)
    (hS : S ≤ a.fixedSubgroup) : ¬ Nonempty (S ≃* alternatingGroup (Fin 6)) := by
  rintro ⟨e⟩
  have htop : S = ⊤ := S.eq_top_of_card_eq ((Nat.card_congr e.toEquiv).trans (card_six.trans hc.symm))
  have hfix : a.fixedSubgroup = ⊤ := top_unique (htop ▸ hS)
  have hone : a = 1 := by
    ext x
    exact (MulAut.mem_fixedSubgroup a x).mp (by rw [hfix]; trivial)
  rw [hone, orderOf_one] at ha
  omega

end alternatingGroup.SixSubgroupObstructions
