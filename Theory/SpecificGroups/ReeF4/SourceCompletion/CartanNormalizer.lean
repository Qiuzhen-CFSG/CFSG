module
public import Theory.SpecificGroups.ReeF4.SmallCompletion.Cartan
public import Theory.SpecificGroups.ReeF4.SmallCompletion.TorusAction

/-!
# The full Cartan normalizer in the positive-parameter Ree group

Write a Cartan-normalizing element in the unique fixed Bruhat normal form
u n v. Comparing its left and right products by a Cartan element forces u
to centralize the entire Cartan. The positive centralizer is trivial, so
u=1. Then v normalizes the Cartan inside the positive subgroup, hence v=1.
Thus the full normalizer is precisely the root-word normalizer, at every
positive parameter including q=8.

This is the native normalizer calculation needed when aligning compatible
parabolic actions in the source 5.3.2 extension argument. It makes no claim
that arbitrary local actions already act on the complete Ree group.
Source: GLS3 2.3.4 and Table 2.4; Aschbacher–Smith F.4.3,10,16,
printed pp.274,279,282 (`refs/quasithin.pdf`).
-/

public noncomputable section
namespace ReeF4.SourceCompletion
open Subgroup Parabolics LargeLocalSeeds SectionGeometry.BNPair
open CentralCovers.OddPrimary.Order

private theorem words_normalize_torus (m : ℕ) :
    normalizerWords m ≤ normalizer (fixedTorus m : Set (Model m)) := by
  have hn := borel_inf_normalizerWords_normal m
  rw [borel_inf_normalizerWords] at hn
  exact (normal_subgroupOf_iff_le_normalizer (fixedTorus_le_normalizerWords m)).mp hn

/-- At every positive parameter the full Cartan normalizer is the actual
root-word normalizer. -/
theorem normalizer_fixedTorus_eq_words {m : ℕ} (hm : 0 < m) :
    normalizer (fixedTorus m : Set (Model m)) = normalizerWords m := by
  apply le_antisymm ?_ (words_normalize_torus m)
  intro g hg
  obtain ⟨⟨n,u,v⟩,hform⟩ := (normalFormMap_bijective m).2 g
  change u.val * n.val * v.val = g at hform
  have hT : fixedTorus m ≤ normalizer (unipotent m : Set (Model m)) :=
    (fixedTorus_le_borel m).trans (borel_le_unipotent_normalizer m)
  have huC : u.val ∈ centralizer (fixedTorus m : Set (Model m)) := by
    intro t ht
    let s := g⁻¹*t*g
    have hs : s ∈ fixedTorus m := by
      simpa only [s,inv_inv] using
        (mem_normalizer_iff.mp ((normalizer (fixedTorus m : Set (Model m))).inv_mem hg) t).mp ht
    have hu' : t*u.val*t⁻¹ ∈ unipotent m :=
      (mem_normalizer_iff.mp (hT ht) u.val).mp u.property
    have hv' : s⁻¹*v.val*s ∈ fixedRightUnipotent (n.val*s) := by
      constructor
      · change toSplitGroup m (s⁻¹*v.val*s) ∈ splitUnipotent m
        have hvU : v.val ∈ unipotent m := v.property.1
        have hh := (mem_normalizer_iff.mp (hT ((fixedTorus m).inv_mem hs)) v.val).mp hvU
        simpa only [inv_inv, unipotent, Subgroup.mem_comap, toSplitGroup_apply] using hh
      · change toSplitGroup m (n.val*s) * toSplitGroup m (s⁻¹*v.val*s) *
          (toSplitGroup m (n.val*s))⁻¹ ∈ LocalBlockInput.splitNegativeUnipotent m
        have he : (n.val*s)*(s⁻¹*v.val*s)*(n.val*s)⁻¹ = n.val*v.val*n.val⁻¹ := by group
        simp only [←map_inv,←map_mul]
        rw [he,map_mul,map_mul,map_inv]
        exact v.property.2
    have hv'' : v.val ∈ fixedRightUnipotent (t*n.val) := by
      rw [fixedRightUnipotent_torus_mul ht]
      exact v.property
    let x : Σ a : normalizerWords m, unipotent m × fixedRightUnipotent a.val :=
      ⟨⟨t*n.val,mul_mem (fixedTorus_le_normalizerWords m ht) n.property⟩,
        ⟨t*u.val*t⁻¹,hu'⟩,⟨v.val,hv''⟩⟩
    let y : Σ a : normalizerWords m, unipotent m × fixedRightUnipotent a.val :=
      ⟨⟨n.val*s,mul_mem n.property (fixedTorus_le_normalizerWords m hs)⟩,
        u,⟨s⁻¹*v.val*s,hv'⟩⟩
    have he : normalFormMap m x = normalFormMap m y := by
      change (t*u.val*t⁻¹)*(t*n.val)*v.val = u.val*(n.val*s)*(s⁻¹*v.val*s)
      have hgs : g*s=t*g := by dsimp [s]; group
      rw [←hform] at hgs
      calc
        _ = t*(u.val*n.val*v.val) := by group
        _ = (u.val*n.val*v.val)*s := hgs.symm
        _ = _ := by group
    have hleft := congrArg (fun z : Σ a : normalizerWords m,
      unipotent m × fixedRightUnipotent a.val => z.2.1.val)
        ((normalFormMap_bijective m).1 he)
    change t*u.val*t⁻¹=u.val at hleft
    exact (mul_inv_eq_iff_eq_mul.mp hleft)
  have hu1 : u.val=1 := mem_bot.mp
    ((SmallCompletion.unipotent_inf_centralizer_fixedTorus m hm).le ⟨u.property,huC⟩)
  have hvN : v.val ∈ normalizer (fixedTorus m : Set (Model m)) := by
    have hv := (normalizer (fixedTorus m : Set (Model m))).mul_mem
      (inv_mem (words_normalize_torus m n.property)) hg
    rw [←hform,hu1,one_mul,inv_mul_cancel_left] at hv
    exact hv
  have hv1 : v.val=1 := mem_bot.mp
    ((SmallCompletion.unipotent_inf_normalizer_fixedTorus m hm).le ⟨v.property.1,hvN⟩)
  rw [←hform,hu1,hv1,one_mul,mul_one]
  exact n.property

end ReeF4.SourceCompletion
