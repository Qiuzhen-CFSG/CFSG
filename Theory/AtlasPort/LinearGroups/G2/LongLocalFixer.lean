module

public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.SylowFixers
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.AutomorphismDescription
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# Faithfulness of restriction to the second G₂ local subgroup

An automorphism fixing the second local subgroup fixes the positive Sylow
subgroup. The proved inner-field description makes it conjugation by a
Sylow element. This element lies in the highest-root subgroup, and the long
Weyl generator in the local subgroup exchanges that root with a distinct
root. Unique positive-root coordinates force its parameter to vanish.

Faithful action on a perfect group's central quotient gives the same result
for every perfect central cover, with the literal marked subgroup image.
This supplies the G₂(4) local calculation in Aschbacher–Smith 10.2.9,
printed pp.750–751, using the standard parabolics of F.1.12.
-/

public section
open Subgroup
namespace Atlas.G2.LieParabolicSetup
open LieAutomorphismExtensions EvenInvolutionGeometry
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Restriction to the second local subgroup detects every automorphism. -/
theorem local₂_fixer_eq_one (hq : 2 < Nat.card F) (a : MulAut (Model F))
    (hfix : ∀ x ∈ local₂, a x = x) : a = 1 := by
  obtain ⟨g, hg, he⟩ := fixing_standard_sylow_inner
    (semilinearAction_bijective hq).2 a
    (fun x hx => hfix x (unipotent_le_local₂ hx))
  have hc : g ∈ highestRoot := by
    rw [← unipotent_center]
    refine ⟨⟨g, hg⟩, mem_center_iff.mpr ?_, rfl⟩
    intro x
    apply Subtype.ext
    have hh := hfix x.val (unipotent_le_local₂ x.property)
    rw [he, MulAut.conj_apply] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  obtain ⟨t, ht⟩ := hc
  change rootA t.toAdd = g at ht
  have hR := hfix weylR (show (weylR : Model F) ∈ local₂ from
    mem_sup_right (subset_closure (Set.mem_singleton _)))
  rw [he, ← ht, MulAut.conj_apply] at hR
  have hroots : rootB t.toAdd = rootA t.toAdd := by
    rw [← weylR_rootA, (mul_inv_eq_iff_eq_mul.mp hR).symm, mul_inv_cancel_right]
  have hp : unipotentProduct ![0,t.toAdd,0,0,0,0] =
      unipotentProduct ![t.toAdd,0,0,0,0,0] := by
    simpa [unipotentProduct] using hroots
  have ht0 : t.toAdd = 0 := by
    simpa using (congrFun (unipotentProduct_injective hp) 0).symm
  rw [he, ← ht, ht0, rootA_zero, map_one]

/-- The actual marked second local subgroup determines automorphisms of
every perfect central cover. -/
theorem perfect_cover_local₂_fixer_eq_one
    {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (hq : 2 < Nat.card F) (e : (K ⧸ center K) ≃* Model F) (B : Subgroup K)
    (hB : B.map (e.toMonoidHom.comp (QuotientGroup.mk' (center K))) = local₂)
    (a : MulAut K) (hfix : ∀ b ∈ B, a b = b) : a = 1 := by
  apply MulAut.centralQuotientAction_injective e
  rw [map_one]
  apply local₂_fixer_eq_one hq
  intro x hx
  rw [← hB] at hx
  obtain ⟨b, hb, rfl⟩ := hx
  change MulAut.centralQuotientAction e a
    (e (QuotientGroup.mk' (center K) b)) = e (QuotientGroup.mk' (center K) b)
  rw [MulAut.centralQuotientAction_apply, hfix b hb]

end Atlas.G2.LieParabolicSetup
