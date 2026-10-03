module

public import Stellmacher.Recognition.SimpleInvolutionFusion
public import ABG.ChapterII.Section1.CentricFusionRelation

/-!
# A centric normalizer moving an involution

Every involution in a Sylow two-subgroup of a finite nonsolvable simple group
is moved by the normalizer of some centric Huppert-extremal subgroup containing
it. Both the original and moved involutions lie in this subgroup of the Sylow.

Otherwise every centric normalizer step preserves the relation
`R x y := (x = z → y = z)`. The centric fusion relation theorem extends this
to ambient conjugacy, contradicting the existence of a distinct conjugate of
`z` in the Sylow subgroup. No Sylow-centrality or N₂ hypothesis is required.

Sources: GLS2, Chapter D, 16.13; GLS4, printed p.94, Lemmas 18.7–18.8.
The fusion transport is supplied by ABG, Chapter II §1.
-/

namespace Stellmacher.Recognition

open BenderSuzuki.External BenderSuzuki.PFchapter1section1

/-- Some centric extremal normalizer moves the given involution within its
subgroup of the Sylow two-subgroup. -/
public theorem exists_centric_extremal_normalizer_moves_involution
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G) (z : S) (hz : orderOf z = 2) :
    ∃ D : Subgroup G, HuppertExtremal S D ∧
      subgroupCentralizerIn (S : Subgroup G) D ≤ D ∧
      D ≤ (S : Subgroup G) ∧ (z : G) ∈ D ∧
      ∃ g : G, g ∈ Subgroup.normalizer (D : Set G) ∧
        g⁻¹ * (z : G) * g ∈ D ∧ g⁻¹ * (z : G) * g ≠ (z : G) := by
  classical
  by_contra hnone
  let R : S → S → Prop := fun x y => x = z → y = z
  have hrefl : ∀ x, R x x := fun _ hx => hx
  have htrans : ∀ {x y w}, R x y → R y w → R x w :=
    fun hxy hyw hx => hyw (hxy hx)
  have hlocal : ∀ (D : Subgroup G), HuppertExtremal S D →
      subgroupCentralizerIn (S : Subgroup G) D ≤ D →
      ∀ g : G, g ∈ Subgroup.normalizer (D : Set G) →
      ∀ x y : S, (x : G) ∈ D → g⁻¹ * (x : G) * g = (y : G) → R x y := by
    intro D hD hc g hg x y hx hxy hxz
    subst x
    have hmem : g⁻¹ * (z : G) * g ∈ D := by
      simpa only [inv_inv] using
        (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (D : Set G)).inv_mem hg) (z : G)).1 hx
    have hfix : g⁻¹ * (z : G) * g = (z : G) := by
      by_contra hne
      exact hnone ⟨D, hD, hc, hD.1, hx, g, hg, hmem, hne⟩
    exact Subtype.ext (hxy.symm.trans hfix)
  obtain ⟨t, ht, hzt⟩ := exists_distinct_isConj_in_sylow hns S z hz
  exact ht (ABG.centric_fusion_relation S R hrefl htrans hlocal hzt rfl)

end Stellmacher.Recognition
