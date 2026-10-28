module
public import Theory.SpecificGroups.PSL3Four.OuterThreeStructure
public import Theory.SpecificGroups.PSL3.CartanActions.ResidualInner
public import Theory.SpecificGroups.PSL3.CartanActions.ActorCoverage
public import Theory.GroupTheory.SelfCentralizingOuter
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Theory.FieldTheory.FiniteAutomorphismOrder

/-!
# Graph actors selected from an outer four-group

For PSL₃(4), a four-group in the outer group injects into the quotient by
diagonal automorphisms: diagonal classes have cube one. That quotient has
order at most four, so the injection is onto and its graph class has an
actual lift in the supplied actor. The lift differs from inverse transpose
by an explicit GL₃ conjugation.

The supplement theorem keeps the original normal subgroup and chosen
supplement. Perfect central descent then lifts the relation to the full
special-linear component, including its scalar center.

Source: Aschbacher–Smith 12.6.31(1) and the first paragraph of 12.6.32,
printed p.837; GLS3, Theorem 2.5.12 and §2.7 for the outer structure.
-/
public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3Four.OuterGraphSelection
open Matrix.PSL3.OuterSolvable
variable {E : Type*} [Field E] [Finite E]

private theorem full_coverage (hE : Nat.card E = 4) : standard E = ⊤ :=
  standard_eq_top_of_two_power_card E (m := 2) (by decide) hE

private theorem diagonal_normal (hE : Nat.card E = 4) : (innerDiagonal E).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← full_coverage hE]
  exact standard_le_normalizer_innerDiagonal

private theorem diagonal_index_dvd_four (hE : Nat.card E = 4) :
    (innerDiagonal E).index ∣ 4 := by
  let := diagonal_normal hE
  let q := QuotientGroup.mk' (innerDiagonal E)
  let f := q.comp (Matrix.PSL3.OuterSolvable.fieldAction E)
  let g := q (graph E)
  have hgen : f.range ⊔ zpowers g = ⊤ := by
    have h := congrArg (Subgroup.map q) (full_coverage hE)
    rw [standard,Subgroup.map_sup,Subgroup.map_sup,QuotientGroup.map_mk'_self,bot_sup_eq,
      MonoidHom.map_zpowers,←MonoidHom.range_comp,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
    exact h
  have hc : ∀ σ (z : zpowers g), Commute (f σ) ((zpowers g).subtype z) := by
    intro σ ⟨z,hz⟩
    obtain ⟨n,rfl⟩ := hz
    exact ((field_commute_graph σ).map q).zpow_right n
  let φ := f.noncommCoprod (zpowers g).subtype hc
  have hs : Function.Surjective φ := by
    apply MonoidHom.range_eq_top.mp
    exact (MonoidHom.noncommCoprod_range f (zpowers g).subtype hc).trans
      (by rw [range_subtype]; exact hgen)
  have hg : Nat.card (zpowers g) ∣ 2 := by
    rw [Nat.card_zpowers]
    apply orderOf_dvd_of_pow_eq_one
    change q (graph E) ^ 2 = 1
    rw [←map_pow,graph_sq,map_one]
  have hh := card_dvd_of_surjective φ hs
  rw [Nat.card_prod,FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two
    (show Nat.card E = 2 ^ 2 from hE)] at hh
  exact hh.trans (Nat.mul_dvd_mul (dvd_refl 2) hg)

/-- Select an actual graph actor from any action with a four-group outer image. -/
theorem exists_graph_of_kleinFour_outer_range {A : Type*} [Group A]
    (hE : Nat.card E = 4) (ρ : A →* MulAut PSL(3,E))
    (hQ : IsKleinFour ((QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,E))).comp ρ).range) :
    ∃ a : A, ∃ c : GL (Fin 3) E, ρ a = linearConj E c * graph E := by
  let := diagonal_normal hE
  let q := QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,E))
  let d := QuotientGroup.mk' (innerDiagonal E)
  let Q := (q.comp ρ).range
  let _ : IsKleinFour Q := hQ
  let l : MulAut.Outer PSL(3,E) →* (MulAut PSL(3,E) ⧸ innerDiagonal E) :=
    QuotientGroup.lift (MulAut.innerSubgroup PSL(3,E)) d (by
      intro a ha
      exact (QuotientGroup.eq_one_iff _).mpr (inner_le_innerDiagonal E ha))
  let f := l.comp Q.subtype
  have hi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    obtain ⟨a,ha⟩ := x.property
    have he : q (ρ a) = (x : MulAut.Outer PSL(3,E)) := ha
    have hd : d (ρ a) = 1 := by
      change l (x : MulAut.Outer PSL(3,E)) = 1 at hx
      rw [←he] at hx
      exact hx
    obtain ⟨c,hc⟩ := (QuotientGroup.eq_one_iff _).mp hd
    have h3 : (x : MulAut.Outer PSL(3,E)) ^ 3 = 1 := by
      rw [←he,←hc,←map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr
        (Matrix.PSL3.CartanActions.ResidualInner.linearConj_cube_inner c)
    have h2 : (x : MulAut.Outer PSL(3,E)) ^ 2 = 1 := by
      simpa only [pow_two,Subgroup.coe_mul,Subgroup.coe_one] using
        congrArg Subtype.val (IsKleinFour.mul_self x)
    apply Subtype.ext
    change (x : MulAut.Outer PSL(3,E)) = 1
    simpa only [pow_succ,h2,one_mul] using h3
  have hs : Function.Surjective f :=
    (hi.bijective_of_nat_card_le (by
      rw [IsKleinFour.card_four (G := Q)]
      exact Nat.le_of_dvd (by decide) (diagonal_index_dvd_four hE))).2
  obtain ⟨x,hx⟩ := hs (d (graph E))
  obtain ⟨a,ha⟩ := x.property
  have he : d (ρ a) = d (graph E) := by
    change l (x : MulAut.Outer PSL(3,E)) = _ at hx
    rw [←ha] at hx
    exact hx
  have hc : ρ a * (graph E)⁻¹ ∈ innerDiagonal E := by
    apply (QuotientGroup.eq_one_iff _).mp
    change d (ρ a * (graph E)⁻¹) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  obtain ⟨c,hc⟩ := hc
  exact ⟨a,c,(mul_inv_eq_iff_eq_mul.mp hc.symm)⟩
end Matrix.PSL3Four.OuterGraphSelection

namespace Matrix.PSL3Four.OuterGraphSelection
open Matrix.PSL3.OuterSolvable
variable {E : Type*} [Field E] [Finite E]

/-- Select the graph actor in a specified supplement of the original normal subgroup. -/
theorem exists_graph_of_normal_supplement {J : Type*} [Group J]
    (hE : Nat.card E = 4) (N P : Subgroup J) [N.Normal] [Group.IsPerfect N] [IsKleinFour (J ⧸ N)]
    (e : N ⧸ center N ≃* PSL(3,E)) (hc : centralizer (N : Set J) ≤ N)
    (hgen : N ⊔ P = ⊤) :
    ∃ t : P, ∃ c : GL (Fin 3) E,
      MulAut.centralQuotientAction e (MulAut.conjNormal (t : J)) =
        linearConj E c * graph E := by
  let f := (MulAut.centralQuotientOuter e).comp (MulAut.outerAction N)
  have hi : Function.Injective f :=
    MulAut.centralQuotientOuter_comp_outerAction_injective N e hc
  let π := (QuotientGroup.mk' N).comp P.subtype
  have hs : Function.Surjective π := by
    apply MonoidHom.range_eq_top.mp
    change ((QuotientGroup.mk' N).comp P.subtype).range = ⊤
    rw [MonoidHom.range_comp,Subgroup.range_subtype]
    have hh := congrArg (Subgroup.map (QuotientGroup.mk' N)) hgen
    rwa [Subgroup.map_sup,QuotientGroup.map_mk'_self,bot_sup_eq,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
  let ρ := (MulAut.centralQuotientAction e).comp
    ((MulAut.conjNormal : J →* MulAut N).comp P.subtype)
  let q := QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,E))
  have he : q.comp ρ = f.comp π := by ext t; rfl
  have hr : (q.comp ρ).range = f.range := by
    rw [he,MonoidHom.range_comp,MonoidHom.range_eq_top.mpr hs,
      ←MonoidHom.range_eq_map]
  let er := MonoidHom.ofInjective hi
  have hQ : IsKleinFour f.range := {
    card_four := (Nat.card_congr er.toEquiv).symm.trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv er).symm.trans IsKleinFour.exponent_two }
  exact exists_graph_of_kleinFour_outer_range hE ρ (hr.symm ▸ hQ)
end Matrix.PSL3Four.OuterGraphSelection

namespace Matrix.PSL3Four.OuterGraphSelection
open Matrix.PSL3.OuterSolvable
variable {E : Type*} [Field E] [Finite E]

/-- The same supplement has a literal graph action on the full special-linear component. -/
theorem exists_full_graph_of_normal_supplement {J : Type*} [Group J]
    (hE : Nat.card E = 4) (N P : Subgroup J) [N.Normal] [Group.IsPerfect N] [IsKleinFour (J ⧸ N)]
    (e : N ≃* SL(3,E)) (hc : centralizer (N : Set J) ≤ N)
    (hgen : N ⊔ P = ⊤) :
    ∃ t : P, ∃ c : GL (Fin 3) E,
      MulAut.congr e (MulAut.conjNormal (t : J)) = linearConjSL E c * graphSL E := by
  let q : N ⧸ center N ≃* PSL(3,E) := QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro x hx
      exact ⟨e.symm x,((centerCongr e).symm ⟨x,hx⟩).property,e.apply_symm_apply x⟩)
  obtain ⟨t,c,ht⟩ := exists_graph_of_normal_supplement hE N P q hc hgen
  have hcongr : centerAction E (MulAut.congr e (MulAut.conjNormal (t : J))) =
      MulAut.centralQuotientAction q (MulAut.conjNormal (t : J)) := by
    ext x
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (center SL(3,E)) x
    obtain ⟨n,rfl⟩ := e.surjective y
    change centerAction E (MulAut.congr e (MulAut.conjNormal (t : J)))
      (QuotientGroup.mk (e n)) =
      MulAut.centralQuotientAction q (MulAut.conjNormal (t : J))
        (q (QuotientGroup.mk' (center N) n))
    rw [centerAction_mk,MulAut.centralQuotientAction_apply]
    change QuotientGroup.mk (e (MulAut.conjNormal (t : J) (e.symm (e n)))) = _
    rw [e.symm_apply_apply]
    rfl
  refine ⟨t,c,?_⟩
  apply Matrix.PSL3.CartanActions.ActorCoverage.centerAction_injective E
  rw [map_mul,hcongr,ht]
  rfl
end Matrix.PSL3Four.OuterGraphSelection
