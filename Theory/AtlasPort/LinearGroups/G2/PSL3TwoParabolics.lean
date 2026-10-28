module

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Quotient
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Quotient
public import Theory.SpecificGroups.PSL3Two.EmbeddingObstructions
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import BenderSuzuki.External.Huppert.II.theorem_8_27

/-!
# PSL₃(2) cannot embed in an even G₂ parabolic or involution centralizer

The scalar characters of both full parabolics vanish on the perfect binary
linear-three group. The remaining local actions have five-root two-group
kernels and image SL₂. Simplicity makes a faithful PSL₃(2) action faithful
on that quotient, contradicting its noncommuting Sylow involutions.
The octonion normalizer-cover theorem then places each involution centralizer
in a conjugate parabolic. This argument concerns actual subgroups, and does
not identify a Levi quotient with an ordinary component.

Source: Aschbacher--Smith, proof of 15.3.38, printed p.1137, using the
characteristic-two families of Theorem C and Remark A.2.4, p.33.
The octonion model and root calculations are from the licensed ATLAS port;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Atlas.G2.PSL3TwoObstructions
open LieParabolicSetup
local instance : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
local instance : Group.IsPerfect Matrix.PSL3Two.PSL := Atlas.psl_perfect 3 (by decide)

private theorem character_trivial {A : Type*} [CommGroup A]
    (f : Matrix.PSL3Two.PSL →* A) (x : Matrix.PSL3Two.PSL) : f x = 1 := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  exact congrArg Subtype.val (Subsingleton.elim (f.rangeRestrict x) 1)

private theorem injective_comp_of_two_kernel {G H : Type*} [Group G] [Finite G] [Group H]
    (r : G →* H) (hr : IsPGroup 2 r.ker) (j : Matrix.PSL3Two.PSL →* G)
    (hj : Function.Injective j) : Function.Injective (r.comp j) := by
  rcases (inferInstance : (r.comp j).ker.Normal).eq_bot_or_eq_top with hb | ht
  · exact (r.comp j).ker_eq_bot_iff.mp hb
  · let k : Matrix.PSL3Two.PSL →* r.ker := j.codRestrict r.ker (by
      intro x
      have hx : x ∈ (r.comp j).ker := ht ▸ mem_top x
      exact hx)
    have hk : Function.Injective k := fun x y h => hj (congrArg Subtype.val h)
    let : Group.IsNilpotent r.ker := hr.isNilpotent
    exact (Group.IsPerfect.not_isSolvable Matrix.PSL3Two.PSL
      (Group.isSolvable_of_isSolvable_injective (f := k) hk)).elim

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem not_injective_SL (j : Matrix.PSL3Two.PSL →* SL(2,F)) :
    ¬ Function.Injective j := by
  intro hj
  let := Fintype.ofFinite F
  obtain ⟨n, _, hn⟩ := FiniteField.card F 2
  let P : Sylow 2 PSL(2,F) := default
  obtain ⟨d⟩ := BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive
    (show Nat.card F = 2 ^ (n : ℕ) by simpa only [Nat.card_eq_fintype_card] using hn) P
  exact Matrix.PSL3Two.not_injective_of_sylow_involutions_commute P
    (fun a b _ _ => d.symm.injective (by simp only [map_mul]; exact mul_comm _ _))
    (RankOneFieldAutomorphisms.slEquivPSL.toMonoidHom.comp j)
    (RankOneFieldAutomorphisms.slEquivPSL.injective.comp hj)

/-- The short local group admits no binary linear-three subgroup. -/
theorem not_injective_local₁ (j : Matrix.PSL3Two.PSL →* local₁ (F := F)) :
    ¬ Function.Injective j := by
  intro hj
  apply not_injective_SL (shortSLHom.comp j)
  apply injective_comp_of_two_kernel shortSLHom _ j hj
  rw [shortSLHom_ker]
  exact radical₁_isTwoGroup.comap_subtype

/-- The long rank-one quotient also excludes a binary linear-three subgroup. -/
theorem not_injective_local₂ (j : Matrix.PSL3Two.PSL →* local₂ (F := F)) :
    ¬ Function.Injective j := by
  intro hj
  apply not_injective_SL (longSLHom.comp j)
  apply injective_comp_of_two_kernel longSLHom _ j hj
  rw [longSLHom_ker]
  exact radical₂_isTwoGroup.comap_subtype

/-- Perfectness removes the determinant character of the full short parabolic. -/
theorem not_injective_parabolic₁ (j : Matrix.PSL3Two.PSL →* parabolic₁ (F := F)) :
    ¬ Function.Injective j := by
  intro hj
  let k := (MulEquiv.subgroupCongr parabolic₁_eq_shortPlaneStabilizer).toMonoidHom.comp j
  have hlocal (x : Matrix.PSL3Two.PSL) : (j x).val ∈ local₁ (F := F) := by
    rw [local₁_eq_shortSpecial]
    exact ⟨k x, show shortDet (k x) = 1 from congrArg Units.val
      (character_trivial (shortDet.toHomUnits.comp k) x), rfl⟩
  let l := (parabolic₁.subtype.comp j).codRestrict local₁ hlocal
  exact not_injective_local₁ l (fun x y h => hj (Subtype.ext (congrArg (fun z : local₁ (F := F) => z.val) h)))

/-- Perfectness removes the point-scalar character of the full long parabolic. -/
theorem not_injective_parabolic₂ (j : Matrix.PSL3Two.PSL →* parabolic₂ (F := F)) :
    ¬ Function.Injective j := by
  intro hj
  let k := (MulEquiv.subgroupCongr (parabolic_eq_pointStabilizer (F := F))).toMonoidHom.comp j
  have hlocal (x : Matrix.PSL3Two.PSL) : (j x).val ∈ local₂ (F := F) := by
    rw [local₂_eq_fixingFirstVector]
    have hx : k x ∈ (lineScalarHom (K := F)).ker :=
      character_trivial (lineScalarHom.comp k) x
    rwa [lineScalarHom_kernel] at hx
  let l := (parabolic₂.subtype.comp j).codRestrict local₂ hlocal
  exact not_injective_local₂ l (fun x y h => hj (Subtype.ext (congrArg (fun z : local₂ (F := F) => z.val) h)))

/-- Involution centralizers in the actual octonion model contain no PSL₃(2). -/
theorem not_injective_involution_centralizer (x : Model F) (hx : orderOf x = 2)
    (j : Matrix.PSL3Two.PSL →* centralizer ({x} : Set (Model F))) :
    ¬ Function.Injective j := by
  intro hj
  have hne : zpowers x ≠ ⊥ := by
    rw [ne_eq, zpowers_eq_bot]
    intro he
    rw [he, orderOf_one] at hx
    omega
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1) (by
    simpa only [Nat.card_zpowers, pow_one] using hx)
  have hc : centralizer ({x} : Set (Model F)) ≤ normalizer (zpowers x : Set (Model F)) := by
    rw [zpowers_eq_closure, ← centralizer_closure {x}]
    exact centralizer_le_normalizer _
  obtain ⟨g, hg⟩ := EvenLocal.NormalizerCover.normalizer_conjugate_le_parabolic
    (zpowers x) hne hp
  let k := (MulAut.conj g).toMonoidHom.comp ((centralizer ({x} : Set (Model F))).subtype.comp j)
  have hk : Function.Injective k := (MulAut.conj g).injective.comp (Subtype.val_injective.comp hj)
  rcases hg with h | h
  · let l := k.codRestrict parabolic₁ (fun z => h ⟨(j z).val, hc (j z).property, rfl⟩)
    exact not_injective_parabolic₁ l (fun a b he => hk (congrArg Subtype.val he))
  · let l := k.codRestrict parabolic₂ (fun z => h ⟨(j z).val, hc (j z).property, rfl⟩)
    exact not_injective_parabolic₂ l (fun a b he => hk (congrArg Subtype.val he))
end Atlas.G2.PSL3TwoObstructions
