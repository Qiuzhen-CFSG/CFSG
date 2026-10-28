module

public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.SourceData
public import Theory.GroupTheory.CenterlessSupplementCentralizer

/-!
# The two centralizers in Lemma 15.4.22

The source quotient is `I/C_T(K)`. For a centerless normal Sylow supplement
`K`, its centralizer in `I` lies in `T₀`. Conversely, an element of `C_T(K)`
normalizes both selected local factors, hence belongs to `T₀`, even for the
alternate choice of either factor. Thus `C_I(K) = C_T(K)`.

The centerless normal supplement is an explicit intermediate hypothesis;
its construction and A₆ identification remain part of 15.4.22.
Source: Aschbacher–Smith, printed p.1165.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section04.Source

open Subgroup
variable {G : Type*} [Group G] {d : Geometry G} (h : LocalData d)

/-- Centralizing a subgroup containing the two selected factors forces a
T-element into the common factor normalizer. This includes both X-choices. -/
theorem LocalData.centralizer_T_le_T₀ (h : LocalData d) (i j : Bool) (K : Subgroup G)
    (hX : d.X i ≤ K) (hY : d.Y j ≤ K) :
    (d.T : Subgroup G) ⊓ centralizer (K : Set G) ≤ d.T₀ := by
  intro t ht
  have htx : t ∈ (d.T : Subgroup G) ⊓ normalizer (d.X i : Set G) :=
    ⟨ht.1, centralizer_le_normalizer _ (centralizer_le hX ht.2)⟩
  have hty : t ∈ (d.T : Subgroup G) ⊓ normalizer (d.Y j : Set G) :=
    ⟨ht.1, centralizer_le_normalizer _ (centralizer_le hY ht.2)⟩
  rw [h.normalizer_X_eq i] at htx
  rw [h.normalizer_Y_eq j] at hty
  exact ⟨htx, hty.2⟩

private theorem centralizer_restrict (H : Subgroup G) (K : Subgroup H) :
    (centralizer (K.map H.subtype : Set G)).subgroupOf H = centralizer (K : Set H) := by
  ext x
  constructor
  · intro hx k hk
    exact Subtype.ext (hx (k : G) ⟨k, hk, rfl⟩)
  · intro hx y hy
    obtain ⟨k, hk, rfl⟩ := hy
    exact congrArg Subtype.val (hx k hk)

/-- Equality of the ambient relative centralizers, proved before identifying
or transporting either quotient. -/
theorem LocalData.centralizer_I_eq_centralizer_T (i j : Bool)
    (K : Subgroup (d.I i j)) [K.Normal]
    (hgen : K ⊔ (h.sylow i j : Subgroup (d.I i j)) = ⊤)
    (hZ : center K = ⊥)
    (hX : d.X i ≤ K.map (d.I i j).subtype)
    (hY : d.Y j ≤ K.map (d.I i j).subtype) :
    d.I i j ⊓ centralizer (K.map (d.I i j).subtype : Set G) =
      (d.T : Subgroup G) ⊓ centralizer (K.map (d.I i j).subtype : Set G) := by
  have hc : centralizer (K : Set (d.I i j)) ≤ (h.sylow i j : Subgroup (d.I i j)) :=
    centralizer_le_sylow_of_centerless_supplement K (h.sylow i j) hgen hZ
  apply le_antisymm
  · intro x hx
    have hxC : (⟨x, hx.1⟩ : d.I i j) ∈ centralizer (K : Set (d.I i j)) := by
      rw [← centralizer_restrict]
      exact hx.2
    have hxT₀ : x ∈ d.T₀ := by
      rw [← h.sylow_image i j]
      exact ⟨⟨x, hx.1⟩, hc hxC, rfl⟩
    exact ⟨d.T₀_le_T hxT₀, hx.2⟩
  · intro x hx
    exact ⟨d.T₀_le_I i j (h.centralizer_T_le_T₀ i j _ hX hY hx), hx.2⟩

/-- Intrinsic quotient form of the equality. In particular the source
`C_T(K)` is normal in `I`, because the right side is a normal centralizer. -/
theorem LocalData.centralizer_T_subgroupOf_eq (i j : Bool)
    (K : Subgroup (d.I i j)) [K.Normal]
    (hgen : K ⊔ (h.sylow i j : Subgroup (d.I i j)) = ⊤)
    (hZ : center K = ⊥)
    (hX : d.X i ≤ K.map (d.I i j).subtype)
    (hY : d.Y j ≤ K.map (d.I i j).subtype) :
    (((d.T : Subgroup G) ⊓ centralizer (K.map (d.I i j).subtype : Set G)).subgroupOf
      (d.I i j)) = centralizer (K : Set (d.I i j)) := by
  rw [← h.centralizer_I_eq_centralizer_T i j K hgen hZ hX hY]
  have heq : ((d.I i j ⊓ centralizer (K.map (d.I i j).subtype : Set G)).subgroupOf
      (d.I i j)) = (centralizer (K.map (d.I i j).subtype : Set G)).subgroupOf (d.I i j) := by
    ext x
    exact and_iff_right x.property
  rw [heq, centralizer_restrict]

end CFSG.Quasithin.Chapter15.Section04.Source
