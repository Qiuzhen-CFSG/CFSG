module
public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic

/-!
# Normal two-subgroups in linear Borel supplements

In characteristic two, a two-subgroup of the matrix Borel lies in its
abelian root group. If a subgroup supplements a two-subgroup in the Borel,
its normal two-subgroups therefore have images invariant under the entire
Borel. Root irreducibility makes every nontrivial such image the whole root.
An explicit transvection sends any nonbase Borel coset to any other; the
same conclusion transfers to any action with the marked Borel stabilizer.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, the rank-one action in 5.1 and the proof of 6.8(a), p.123.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F]

/-- Upper roots act transitively on the Borel cosets other than the Borel itself. -/
theorem root_moves_nonbase_cosets (a b : SL(2,F))
    (ha : a ∉ rankOneBorel F) (hb : b ∉ rankOneBorel F) :
    ∃ u ∈ upperUnipotent F, b⁻¹ * u * a ∈ rankOneBorel F := by
  have ha0 : a.val 1 0 ≠ 0 := fun hz => ha ((mem_rankOneBorel_iff a).mpr hz)
  have hb0 : b.val 1 0 ≠ 0 := fun hz => hb ((mem_rankOneBorel_iff b).mpr hz)
  let t := b.val 0 0 / b.val 1 0 - a.val 0 0 / a.val 1 0
  refine ⟨transvection zero_ne_one t, (mem_upperUnipotent F _).mpr ⟨t,rfl⟩, ?_⟩
  rw [mem_rankOneBorel_iff]
  simp [adjugate_fin_two, mul_apply, vecMul, dotProduct, Fin.sum_univ_two, transvection_coe]
  dsimp [t]
  field_simp
  ring

variable [Finite F] [CharP F 2]
private theorem two_subgroup_le_root (A : Subgroup SL(2,F))
    (hp : IsPGroup 2 A) (hA : A ≤ rankOneBorel F) : A ≤ upperUnipotent F := by
  have hh := hp.inf_normalizer_sylow (upperUnipotentSylow F 2)
  change A ⊓ rankOneBorel F = A ⊓ upperUnipotent F at hh
  rw [inf_eq_left.mpr hA] at hh
  exact hh.le.trans inf_le_right

omit [Finite F] [CharP F 2] in
private theorem root_centralizes_subgroup (A : Subgroup SL(2,F))
    (hA : A ≤ upperUnipotent F) : upperUnipotent F ≤ normalizer (A : Set SL(2,F)) := by
  apply le_normalizer_iff.mpr
  intro u hu a ha
  obtain ⟨s,rfl⟩ := (mem_upperUnipotent F u).mp hu
  obtain ⟨t,rfl⟩ := (mem_upperUnipotent F a).mp (hA ha)
  have hc : transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one s *
      transvection zero_ne_one t = transvection zero_ne_one t * transvection zero_ne_one s := by
    rw [← transvection_add, ← transvection_add, add_comm]
  simpa only [hc, mul_inv_cancel_right] using ha

variable {J : Type*} [Group J]
/-- A normal two-subgroup of a Borel supplement either vanishes in the
linear quotient or maps onto the entire root group. -/
theorem normal_two_image_of_borel_supplement (q : J →* SL(2,F))
    (hq : Function.Surjective q) (D S A : Subgroup J)
    (hsup : D ⊔ S = (rankOneBorel F).comap q)
    (hS : IsPGroup 2 S) (hA : IsPGroup 2 A) (hAD : A ≤ D)
    (hn : D ≤ normalizer (A : Set J)) (hne : ¬ A ≤ q.ker) :
    A.map q = upperUnipotent F := by
  have hD : D.map q ≤ rankOneBorel F := (map_le_iff_le_comap).mpr
    (le_sup_left.trans hsup.le)
  have hS' : S.map q ≤ upperUnipotent F := two_subgroup_le_root _ (hS.map q)
    ((map_le_iff_le_comap).mpr (le_sup_right.trans hsup.le))
  have hA' : A.map q ≤ upperUnipotent F := two_subgroup_le_root _ (hA.map q)
    ((map_mono hAD).trans hD)
  apply eq_upperUnipotent_of_normalized _ hA'
    (fun hz => hne ((map_eq_bot_iff A).mp hz))
  have hgen : D.map q ⊔ S.map q = rankOneBorel F := by
    rw [← Subgroup.map_sup, hsup, map_comap_eq_self_of_surjective hq]
  rw [← hgen]
  exact sup_le ((map_mono hn).trans (A.le_normalizer_map q))
    (hS'.trans (root_centralizes_subgroup _ hA'))

variable {Ω : Type*} [MulAction J Ω]
omit [Finite F] [CharP F 2] in
/-- Full root image supplies transitivity on the nonbase points of an orbit
whose marked stabilizer is the preimage of the actual matrix Borel. -/
theorem moves_of_root_image (q : J →* SL(2,F)) (A : Subgroup J)
    (hA : upperUnipotent F ≤ A.map q) (o x y : Ω)
    (hb : MulAction.stabilizer J o = (rankOneBorel F).comap q)
    (hx : x ≠ o) (hy : y ≠ o)
    (hox : ∃ a : J, a • o = x) (hoy : ∃ b : J, b • o = y) :
    ∃ g ∈ A, g • x = y := by
  obtain ⟨a,rfl⟩ := hox
  obtain ⟨b,rfl⟩ := hoy
  have ha : q a ∉ rankOneBorel F := by
    intro ha
    apply hx
    change a ∈ MulAction.stabilizer J o
    rwa [hb]
  have hc : q b ∉ rankOneBorel F := by
    intro hc
    apply hy
    change b ∈ MulAction.stabilizer J o
    rwa [hb]
  obtain ⟨u,hu,he⟩ := root_moves_nonbase_cosets (q a) (q b) ha hc
  obtain ⟨g,hg,rfl⟩ := hA hu
  have hfix : b⁻¹ * g * a ∈ MulAction.stabilizer J o := by
    rw [hb]
    change q (b⁻¹ * g * a) ∈ rankOneBorel F
    simpa only [map_mul, map_inv] using he
  refine ⟨g,hg,?_⟩
  have hh := congrArg (fun z : Ω => b • z) hfix
  simpa only [mul_smul, smul_inv_smul] using hh
end Matrix.SpecialLinearGroup
