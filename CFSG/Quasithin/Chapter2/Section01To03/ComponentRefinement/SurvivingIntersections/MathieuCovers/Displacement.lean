module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuCovers.Source

/-!
# Forced displacement of a normal two-subgroup in the source Γ₀ geometry

If H normalizes a nontrivial two-subgroup D, Γ₀ maximality makes the
original S Sylow in N_G(D). Consequently T ∩ N_G(D) is exactly S.
The normalizer condition in T then produces an element normalizing S
but moving D. This uses the original Γ₀ hypotheses alone, without the
earlier structural or block-classification inputs.

The component-kernel application retains H-normalization of L explicitly.
Neither component subnormality nor characteristicness in S ∩ L is promoted
to that hypothesis, or to characteristicness in S.

Source: Aschbacher–Smith 2.3.7(2,4) and 2.3.9(3), printed pp.523,525.
-/

public section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
variable {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The full Γ₀ selection pins down the intersection of the kernel normalizer
with the selected ambient Sylow, whenever H normalizes that kernel. -/
theorem MathieuSourceSetup.normalizer_inf_T
    (c : MathieuSourceSetup H L M S z) (D : Subgroup G)
    (hD : D ≠ ⊥) (hp : IsPGroup 2 D) (hHD : H ≤ normalizer (D : Set G)) :
    (c.T : Subgroup G) ⊓ normalizer (D : Set G) = (S : Subgroup H).map H.subtype := by
  let N := normalizer (D : Set G)
  have hcore : twoCore N ≠ ⊥ := Chapter1.mem_H_of_isTwoLocal ⟨D, hD, hp, rfl⟩
  have hg := gammaZero_overgroup c.gamma hHD hcore
  have hNgamma : N ∈ Chapter2.gamma (Chapter1.He G) M :=
    hg.1.elim (fun a => a.1.1) (fun a => a.1)
  obtain ⟨P, hP⟩ := (gamma_sylow_transport hNgamma S
    ((map_subtype_le _).trans hHD) hg.2.1 (c.sylow_lt.le.trans c.sylow_le)).1
  have he := inf_eq_sylow_map P c.T.isPGroup' (hP.symm ▸ c.sylow_lt.le)
  exact he.trans hP

/-- There is actual displacement already in N_T(S), not just somewhere
in T. This is a conclusion of Γ₀ maximality and the p-group normalizer condition. -/
theorem MathieuSourceSetup.exists_displacing_sylow_normalizer
    (c : MathieuSourceSetup H L M S z) (D : Subgroup G)
    (hD : D ≠ ⊥) (hp : IsPGroup 2 D) (hHD : H ≤ normalizer (D : Set G)) :
    ∃ g ∈ (c.T : Subgroup G),
      g ∈ normalizer ((S : Subgroup H).map H.subtype : Set G) ∧
      g ∉ normalizer (D : Set G) := by
  let A := (S : Subgroup H).map H.subtype
  let : Group.IsNilpotent (c.T : Subgroup G) := c.T.isPGroup'.isNilpotent
  have hproper : A.subgroupOf (c.T : Subgroup G) < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro he
    exact c.sylow_lt.not_ge (subgroupOf_eq_top.mp he)
  obtain ⟨g, hg, hgn⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent _ hproper)
  have hgN : (g : G) ∈ normalizer (A : Set G) := by
    rw [← subgroupOf_normalizer_eq c.sylow_lt.le] at hg
    exact hg
  refine ⟨g, g.property, hgN, ?_⟩
  intro hgD
  have hm : (g : G) ∈ (c.T : Subgroup G) ⊓ normalizer (D : Set G) :=
    ⟨g.property, hgD⟩
  rw [c.normalizer_inf_T D hD hp hHD] at hm
  exact hgn hm

/-- The actual covering kernel is displaced if the component is normalized
by H. No intrinsic Sylow property supplies the absent ambient invariance. -/
theorem MathieuSourceSetup.twoCore_displacement
    (c : MathieuSourceSetup H L M S z)
    (hHL : H ≤ normalizer (L : Set G)) (hk : pCore 2 L ≠ ⊥) :
    ∃ g ∈ (c.T : Subgroup G),
      g ∈ normalizer ((S : Subgroup H).map H.subtype : Set G) ∧
      g ∉ normalizer (twoCore L : Set G) := by
  apply c.exists_displacing_sylow_normalizer (twoCore L)
  · exact fun he => hk ((map_eq_bot_iff_of_injective _ L.subtype_injective).mp he)
  · exact pCore_isPGroup.map L.subtype
  · exact hHL.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))

end CFSG.Quasithin.Chapter2.ComponentRefinement
end
