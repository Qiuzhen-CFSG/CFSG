module
public import CFSG.Quasithin.ChapterI.Section06To08.UniqueFixedSource
public import Theory.GroupTheory.UniqueFixedCosetQuotient
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# The nonbinary perfect-action contradiction in F.4.42

A perfect subgroup of the local stabilizer acts transitively on the nonzero
vectors of the normal elementary module. If the marked vector fixes a
unique ambient coset, all nonzero vectors do. For a proper stabilizer I.8.5
makes its induced action solvable, forcing the perfect subgroup to act
trivially. This contradicts an orbit with more than one nonzero vector.

This is the first unitary quotient step of Aschbacher–Smith F.4.42,
printed p.295. The ambient fixed-coset premise remains explicit.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.UnitarySource
variable {G : Type*} [Group G] [Finite G]

/-- I.8.5 excludes a proper stabilizer of a nonbinary perfect vector orbit. -/
theorem eq_top_of_perfect_orbit
    (V M P : Subgroup G) [IsElementaryAbelian 2 V] [(V.subgroupOf M).Normal]
    [Group.IsPerfect P] (hVM : V ≤ M) (hPM : P ≤ M) (hcard : 2 < Nat.card V)
    (z : G) (hz : z ∈ V)
    (horbit : ∀ v ∈ V, v ≠ 1 → ∃ a ∈ P, a*z*a⁻¹ = v)
    (hfix : ∃! q : G ⧸ M, z • q = q) : M = ⊤ := by
  by_contra hproper
  have hVne : V ≠ ⊥ := by
    intro he
    rw [he,Nat.card_unique] at hcard
    omega
  have hfixV : ∀ v ∈ V, v ≠ 1 → ∃! q : G ⧸ M, v • q = q := by
    intro v hv hv1
    obtain ⟨a,_,he⟩ := horbit v hv hv1
    exact UniqueFixedCoset.unique_of_isConj hfix (isConj_iff.mpr ⟨a,he⟩)
  let : Group.IsSolvable (M ⧸ centralizer (V.subgroupOf M : Set M)) :=
    ChapterI.Section06To08.lemma_I_8_5_automizer V M hVM hVne hproper hfixV
  let : Group.IsPerfect (P.subgroupOf M) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hPM).symm.toMonoidHom)
    (subgroupOfEquivOfLe hPM).symm.surjective
  have hPC := le_of_isPerfect_of_solvable_quotient (P.subgroupOf M)
    (centralizer (V.subgroupOf M : Set M))
  obtain ⟨v,hv1,hvz⟩ := ENat.exists_ne_ne_of_three_le (α := V)
    (by rw [ENat.card_eq_coe_natCard]; exact_mod_cast (by omega : 3 ≤ Nat.card V))
    1 ⟨z,hz⟩
  obtain ⟨a,ha,he⟩ := horbit v.val v.property (fun hh => hv1 (Subtype.ext hh))
  have hh := hPC (show (⟨a,hPM ha⟩ : M) ∈ P.subgroupOf M from ha)
    (⟨z,hVM hz⟩ : M) hz
  have hc : z*a = a*z := congrArg Subtype.val hh
  apply hvz
  apply Subtype.ext
  rw [←he,←hc,mul_inv_cancel_right]

end CFSG.Quasithin.ChapterF.UnitarySource
