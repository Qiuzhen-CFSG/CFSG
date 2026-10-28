module
public import ABG.ChapterII.Section1.FocalGenerators
public import ABG.ChapterII.Section1.WreathedUFrattiniAction
public import Theory.GroupTheory.SpecificGroups.KleinFourAutDifference

/-!
# High base automizer generates wreathed local fusion

For the actual base U in a finite wreathed fusion frame, automizer order six
makes the normalizer fusion subgroup exactly U inside the chosen Sylow subgroup.
Thus U lies in its ambient focal subgroup. This formalizes the base derived
subgroup assertion in Alperin--Brauer--Gorenstein, Chapter II, Section 1,
Proposition 2, article p.12 (`page-013.tex`, second proof paragraph).

The normalizer induces every automorphism of the Klein four Frattini quotient.
Every element of that quotient is an automorphism difference x inverse times
f(x). Lift x to U and f to the actual normalizer to realize the difference
as a normalizer fusion generator. Consequently the preimage in U of the
local fusion subgroup surjects onto the Frattini quotient. Frattini
nongeneration makes that preimage all of U. Normalizer invariance gives
the reverse containment. The argument uses the existing fusion subgroup
definition and retains all subgroup inclusions.
-/

namespace ABG.Wreathed
variable {G : Type*} [Group G] [Finite G]

/-- An automizer of order six makes the entire wreathed base a local focal subgroup. -/
public theorem u_normalizerFusionSubgroup_eq
    (S : Sylow 2 G) (n : ℕ) (U V : Subgroup G)
    (hf : WreathedFusionFrame S n U V) (hindex : automizerIndex U = 6) :
    normalizerFusionSubgroup (S : Subgroup G) U = U.subgroupOf S := by
  let := (u_frattini_action S n U V hf).1
  have hfull := u_frattini_action_surjective S n U V hf hindex
  let K := normalizerFusionSubgroup (S : Subgroup G) U
  let j : U →* S := Subgroup.inclusion hf.2.1
  let L := K.comap j
  let q := QuotientGroup.mk' (frattini U)
  have hmap : L.map q = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨x, f, hx⟩ := IsKleinFour.exists_mulAut_difference z
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (frattini U) x
    obtain ⟨g, hg⟩ := hfull f
    let v := U.normalizerMonoidHom g u
    refine ⟨u⁻¹ * v, ?_, ?_⟩
    · change j (u⁻¹ * v) ∈ K
      apply Subgroup.subset_closure
      refine ⟨j u, j v, (g : G)⁻¹,
        (Subgroup.normalizer (U : Set G)).inv_mem g.property, u.property, ?_, ?_⟩
      · change ((g : G)⁻¹)⁻¹ * (u : G) * (g : G)⁻¹ = (v : G)
        simp only [inv_inv]
        rfl
      · simp only [map_mul, map_inv]
    · have hqv : q v = f (q u) := by
        have hh := DFunLike.congr_fun hg (q u)
        change (Subgroup.quotientAut (frattini U) (U.normalizerMonoidHom g)) (q u) = _ at hh
        simpa only [q, Subgroup.quotientAut_apply_mk] using hh
      rw [map_mul, map_inv, hqv]
      exact hx
  have hsup : L ⊔ frattini U = ⊤ := by
    have hh := congrArg (Subgroup.comap q) hmap
    simpa only [Subgroup.comap_map_eq, q, QuotientGroup.ker_mk', Subgroup.comap_top] using hh
  have hL : L = ⊤ := frattini_nongenerating hsup
  apply le_antisymm (normalizerFusionSubgroup_le _ _)
  intro z hz
  let u : U := ⟨z, hz⟩
  have hu : u ∈ L := hL ▸ Subgroup.mem_top u
  exact hu
end ABG.Wreathed
