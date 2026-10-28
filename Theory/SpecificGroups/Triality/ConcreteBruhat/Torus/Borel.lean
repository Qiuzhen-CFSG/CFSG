module
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Torus.FixedWords
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl.Basic
public import Theory.SpecificGroups.Triality.ElementaryCentralKernel
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.PGroup

/-!
# Unique Borel factorization and its descent

Normalization and disjointness give a unique positive-times-torus product in
the original split Borel. Both subgroups are graph-field invariant, so
uniqueness forces the two factors of a fixed element to be fixed. A fixed
positive element has prime-power order and therefore lies in the actual
elementary subgroup. The other elementary factor is its inverse times the
original element. Finally, injectivity of the actual elementary central
quotient preserves uniqueness. Normality is asserted only inside the Borel.

This proves the Borel factorization, the cardinality product, and the relative
index formula from the explicit split normalization and intersection inputs.
It makes no assertion about Sylow maximality or the global index of U.

Source: the proof of GLS3 2.3.4(c) and 2.3.8(a)
(`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section
open scoped Pointwise
namespace Triality.Standard.ConcreteBruhat
open Parabolics

theorem splitBorel_eq_mul_of_normalizes (P : Parameters)
    (hn : splitTorus P ≤ Subgroup.normalizer (positiveSubgroup P)) :
    (splitBorel P : Set (SplitGroup P)) =
      (positiveSubgroup P : Set (SplitGroup P)) * splitTorus P :=
  Subgroup.coe_mul_of_right_le_normalizer_left _ _ hn

theorem splitPositive_normal_in_borel_of_normalizes (P : Parameters)
    (hn : splitTorus P ≤ Subgroup.normalizer (positiveSubgroup P)) :
    ((positiveSubgroup P).subgroupOf (splitBorel P)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le (positiveSubgroup P).le_normalizer hn)

theorem existsUnique_splitBorel_factors_of_normalizes (P : Parameters)
    (hn : splitTorus P ≤ Subgroup.normalizer (positiveSubgroup P))
    (hd : Disjoint (positiveSubgroup P) (splitTorus P)) (g : splitBorel P) :
    ∃! a : positiveSubgroup P × splitTorus P, a.1.val * a.2.val = g.val := by
  have hg : g.val ∈ (positiveSubgroup P : Set (SplitGroup P)) * splitTorus P := by
    rw [← splitBorel_eq_mul_of_normalizes P hn]
    exact g.property
  obtain ⟨u, hu, t, ht, he⟩ := hg
  exact ⟨(⟨u, hu⟩, ⟨t, ht⟩), he,
    fun b hb => Subgroup.mul_injective_of_disjoint hd (hb.trans he.symm)⟩

/-- Uniqueness forces each Borel factor of a fixed matrix to be fixed. -/
theorem splitBorel_factors_fixed (P : Parameters)
    (hd : Disjoint (positiveSubgroup P) (splitTorus P))
    (u t : SplitGroup P) (hu : u ∈ positiveSubgroup P) (ht : t ∈ splitTorus P)
    (hfix : graphFieldAutomorphism P (u * t) = u * t) :
    u ∈ fixedSubgroup P ∧ t ∈ fixedSubgroup P := by
  have huF : graphFieldAutomorphism P u ∈ positiveSubgroup P := by
    rw [← positiveSubgroup_invariant P]
    exact ⟨u, hu, rfl⟩
  have htF : graphFieldAutomorphism P t ∈ splitTorus P := by
    rw [← splitTorus_invariant P]
    exact ⟨t, ht, rfl⟩
  have he : (⟨graphFieldAutomorphism P u, huF⟩, ⟨graphFieldAutomorphism P t, htF⟩) =
      ((⟨u, hu⟩, ⟨t, ht⟩) : positiveSubgroup P × splitTorus P) :=
    Subgroup.mul_injective_of_disjoint hd ((map_mul _ u t).symm.trans hfix)
  exact ⟨congrArg (fun x : positiveSubgroup P × splitTorus P => x.1.val) he,
    congrArg (fun x : positiveSubgroup P × splitTorus P => x.2.val) he⟩

/-- The split factorization descends by lifting the positive factor using its
characteristic-power order; the other elementary factor is its inverse times g. -/
theorem borel_eq_mul_of_split (P : Parameters)
    (hU : IsPGroup P.prime (positiveSubgroup P))
    (hn : splitTorus P ≤ Subgroup.normalizer (positiveSubgroup P))
    (hd : Disjoint (positiveSubgroup P) (splitTorus P)) :
    (borel P : Set (Carrier P)) = (unipotent P : Set (Carrier P)) * torus P := by
  apply Set.Subset.antisymm
  · rintro g ⟨x, hx, rfl⟩
    have hx' : elementaryInclusion P x ∈
        (positiveSubgroup P : Set (SplitGroup P)) * splitTorus P :=
      (Set.ext_iff.mp (splitBorel_eq_mul_of_normalizes P hn) (elementaryInclusion P x)).mp hx
    obtain ⟨u, hu, t, ht, he⟩ := hx'
    have hfix : graphFieldAutomorphism P (u * t) = u * t :=
      (congrArg (graphFieldAutomorphism P) he).trans (x.val.property.trans he.symm)
    have huf := (splitBorel_factors_fixed P hd u t hu ht hfix).1
    let uf : fixedSubgroup P := ⟨u, huf⟩
    have hue : uf ∈ elementarySubgroup P := by
      obtain ⟨k, hk⟩ := hU ⟨u, hu⟩
      apply mem_elementarySubgroup_of_pow P uf k
      exact Subtype.ext (congrArg (fun y : positiveSubgroup P => y.val) hk)
    let ue : ElementaryGroup P := ⟨uf, hue⟩
    let te : ElementaryGroup P := ue⁻¹ * x
    have hte : elementaryInclusion P te = t := by
      change u⁻¹ * elementaryInclusion P x = t
      exact (congrArg (fun z : SplitGroup P => u⁻¹ * z) he.symm).trans
        (inv_mul_cancel_left u t)
    refine ⟨toCarrier P ue, ⟨ue, hu, rfl⟩,
      toCarrier P te, ⟨te, ?_, rfl⟩, ?_⟩
    · change elementaryInclusion P te ∈ splitTorus P
      exact hte.symm ▸ ht
    · exact (map_mul (toCarrier P) ue te).symm.trans
        (congrArg (toCarrier P) (mul_inv_cancel_left ue x))
  · rintro _ ⟨u, hu, t, ht, rfl⟩
    exact (borel P).mul_mem (unipotent_le_borel P hu) (torus_le_borel P ht)

theorem disjoint_unipotent_torus_of_split (P : Parameters) (hp : P.prime = 2)
    (hd : Disjoint (positiveSubgroup P) (splitTorus P)) :
    Disjoint (unipotent P) (torus P) := by
  rw [disjoint_iff_inf_le]
  rintro g ⟨⟨u, hu, hug⟩, ⟨t, ht, htg⟩⟩
  have hut := ElementaryCentralKernel.toCarrier_injective P hp (hug.trans htg.symm)
  subst t
  have hu1 : elementaryInclusion P u = 1 :=
    Subgroup.mem_bot.mp ((disjoint_iff_inf_le.mp hd) ⟨hu, ht⟩)
  have hue : u = 1 := Subtype.ext (Subtype.ext hu1)
  rw [Subgroup.mem_bot, ← hug, hue, map_one]

theorem unipotent_normal_in_borel_of_split (P : Parameters)
    (hn : splitTorus P ≤ Subgroup.normalizer (positiveSubgroup P)) :
    ((unipotent P).subgroupOf (borel P)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff (unipotent_le_borel P)).mpr
  intro u b hu hb
  obtain ⟨x, hx, rfl⟩ := hu
  obtain ⟨y, hy, rfl⟩ := hb
  refine ⟨y * x * y⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  change elementaryInclusion P (y * x * y⁻¹) ∈ positiveSubgroup P
  have hconj := (Subgroup.normal_subgroupOf_iff (show positiveSubgroup P ≤ splitBorel P from
    le_sup_left)).mp (splitPositive_normal_in_borel_of_normalizes P hn) _ _ hx hy
  simpa only [map_mul, map_inv] using hconj

def borelEquivOfSplit (P : Parameters) (hp : P.prime = 2)
    (hU : IsPGroup P.prime (positiveSubgroup P))
    (hn : splitTorus P ≤ Subgroup.normalizer (positiveSubgroup P))
    (hd : Disjoint (positiveSubgroup P) (splitTorus P)) :
    unipotent P × torus P ≃ borel P := by
  let f : unipotent P × torus P → borel P := fun a =>
    ⟨a.1.val * a.2.val,
      (borel P).mul_mem (unipotent_le_borel P a.1.property) (torus_le_borel P a.2.property)⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b h
    exact Subgroup.mul_injective_of_disjoint (disjoint_unipotent_torus_of_split P hp hd)
      (congrArg Subtype.val h)
  · intro g
    have hg : g.val ∈ (unipotent P : Set (Carrier P)) * torus P := by
      rw [← borel_eq_mul_of_split P hU hn hd]
      exact g.property
    obtain ⟨u, hu, t, ht, he⟩ := hg
    exact ⟨(⟨u, hu⟩, ⟨t, ht⟩), Subtype.ext he⟩

theorem borel_relIndex_eq_card_torus_of_split (P : Parameters) (hp : P.prime = 2)
    (hU : IsPGroup P.prime (positiveSubgroup P))
    (hn : splitTorus P ≤ Subgroup.normalizer (positiveSubgroup P))
    (hd : Disjoint (positiveSubgroup P) (splitTorus P)) :
    (unipotent P).relIndex (borel P) = Nat.card (torus P) := by
  have he := Nat.card_congr (borelEquivOfSplit P hp hU hn hd)
  rw [Nat.card_prod] at he
  have hc := Subgroup.card_mul_index ((unipotent P).subgroupOf (borel P))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (unipotent_le_borel P)).toEquiv] at hc
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := unipotent P)) (hc.trans he.symm)

end Triality.Standard.ConcreteBruhat
