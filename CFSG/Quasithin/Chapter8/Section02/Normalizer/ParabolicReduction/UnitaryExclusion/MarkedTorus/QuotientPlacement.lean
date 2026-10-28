module

public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.UnitaryExclusion.GroupDeductions

/-!
# Placing a quotient normalizer inside the source local subgroup

For a member H of the genuine HStar(T,M) family, every proper overgroup
of T in H lies in H ∩ M. Applied to the preimage of a proper quotient
normalizer, this puts the whole normalizer in the image of H ∩ M.
In particular it places any constructed unitary torus there without
assuming that the torus lifts into the local subgroup.

Source: Aschbacher–Smith, Lemma 3.1.3 and the cocode paragraph of
Lemma 8.2.9, printed p.720 (combined manuscript, 1 March 2004).
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.UnitaryExclusion.MarkedTorus

variable {G : Type*} [Group G]

/-- Intrinsic form of the genuine HStar proper-overgroup property.
Here `M.subgroupOf H` is literally the intersection viewed inside H. -/
theorem proper_overgroups_of_HStar (T : Sylow 2 G) (M H : Subgroup G)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    ∀ Y : Subgroup H,
      (T.subtype hH.1.1.2 : Subgroup H) ≤ Y → Y ≠ ⊤ → Y ≤ M.subgroupOf H := by
  intro Y hTY hY
  have htop : (⊤ : Subgroup H).map H.subtype = H := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  have hlt : Y.map H.subtype < H := by
    refine lt_of_le_of_ne (map_subtype_le Y) ?_
    intro he
    exact hY (map_injective H.subtype_injective (he.trans htop.symm))
  have hTY' : (T : Subgroup G) ≤ Y.map H.subtype := by
    intro t ht
    exact ⟨⟨t, hH.1.1.2 ht⟩, hTY ht, rfl⟩
  have hYM := Chapter3.HStar.proper_overgroup_le T hH hTY' hlt
  intro y hy
  exact hYM ⟨y, hy, rfl⟩

variable {H Q : Type*} [Group H] [Group Q]

/-- A proper normalizer containing the Sylow image lies in the local image.
The hypothesis on proper overgroups is supplied by `proper_overgroups_of_HStar`. -/
theorem quotient_normalizer_le_local_image
    (T : Subgroup H) (M : Subgroup H)
    (hlocal : ∀ Y : Subgroup H, T ≤ Y → Y ≠ ⊤ → Y ≤ M)
    (q : H →* Q) (hq : Function.Surjective q) (R : Subgroup Q)
    (hT : T.map q ≤ normalizer (R : Set Q))
    (hproper : normalizer (R : Set Q) ≠ ⊤) :
    normalizer (R : Set Q) ≤ M.map q := by
  let N := normalizer (R : Set Q)
  have hpre : N.comap q ≠ ⊤ := by
    intro he
    apply hproper
    have hm := congrArg (Subgroup.map q) he
    rw [map_comap_eq_self (show N ≤ q.range from
      (MonoidHom.range_eq_top.mpr hq) ▸ le_top), map_top_of_surjective q hq] at hm
    exact hm
  have hc := hlocal (N.comap q) (map_le_iff_le_comap.mp hT) hpre
  intro x hx
  obtain ⟨y, rfl⟩ := hq x
  exact ⟨y, hc hx, rfl⟩

/-- The source application uses the actual quotient H/O₂(H) and actual
intersection H ∩ M, with no upstairs five-subgroup as an input. -/
theorem quotient_normalizer_le_intersection_image
    (T : Sylow 2 G) (M H : Subgroup G)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (R : Subgroup (H ⧸ pCore 2 H))
    (hT : (T.subtype hH.1.1.2 : Subgroup H).map (QuotientGroup.mk' (pCore 2 H)) ≤
      normalizer (R : Set (H ⧸ pCore 2 H)))
    (hproper : normalizer (R : Set (H ⧸ pCore 2 H)) ≠ ⊤) :
    normalizer (R : Set (H ⧸ pCore 2 H)) ≤
      (M.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) :=
  quotient_normalizer_le_local_image _ _ (proper_overgroups_of_HStar T M H hH)
    _ (QuotientGroup.mk'_surjective _) R hT hproper

end CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.UnitaryExclusion.MarkedTorus
