module
public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Mathlib.GroupTheory.Nilpotent

/-!
# Central-cover preimages in a unique maximal two-local

The preimage of a prime subgroup under a central extension is nilpotent.
Its characteristic Sylow subgroup lifts the whole prime subgroup and is
normalized by the preimage of its normalizer. Consequently a local subgroup
containing a uniqueness subgroup has its entire central-cover preimage in
the unique maximal two-local. Normality then descends through the literal
surjection, retaining the relative overgroup.
Source application: Aschbacher--Smith 4.4.12, printed pp.621--622.
-/

public noncomputable section
open Subgroup

namespace Subgroup
theorem exists_prime_lift_of_central_kernel {E Q : Type*} [Group E] [Finite E] [Group Q]
    {p : ℕ} [Fact p.Prime] (f : E →* Q) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (B : Subgroup Q) (hB : IsPGroup p B) :
    ∃ U : Subgroup E, IsPGroup p U ∧ U.map f = B ∧
      (normalizer (B : Set Q)).comap f ≤ normalizer (U : Set E) := by
  let : Finite Q := Finite.of_surjective f hf
  let R := B.comap f
  let g : R →* B := f.subgroupComap B
  have hg : Function.Surjective g := f.subgroupComap_surjective_of_surjective B hf
  have hgc : g.ker ≤ center R := by
    intro x hx
    have hxk : (x : E) ∈ f.ker := congrArg Subtype.val hx
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp (hc hxk) y)
  let := hB.isNilpotent
  let : Group.IsNilpotent R := Subgroup.isNilpotent_of_ker_le_center g hgc
  let P : Sylow p R := Sylow.nonempty.some
  let : (P : Subgroup R).Characteristic := P.characteristic_of_normal inferInstance
  have hPtop : (P.mapSurjective hg : Subgroup B) = ⊤ := by
    apply top_unique
    exact (hB.to_subgroup ⊤).le_sylow_of_normal _
  let U : Subgroup E := (P : Subgroup R).map R.subtype
  have hUmap : U.map f = B := by
    have hh := congrArg (Subgroup.map B.subtype) hPtop
    change ((P : Subgroup R).map g).map B.subtype = (⊤ : Subgroup B).map B.subtype at hh
    rw [map_map, ← MonoidHom.range_eq_map, range_subtype] at hh
    change (P : Subgroup R).map (f.comp R.subtype) = B at hh
    simpa only [U,map_map] using hh
  refine ⟨U,P.isPGroup'.map R.subtype,hUmap,?_⟩
  apply le_trans ?_ (normalizer_le_normalizer_characteristic_image R (P : Subgroup R))
  exact le_of_eq (comap_normalizer_eq_of_surjective B hf)

theorem central_preimage_le_of_unique_maximalTwoLocal
    {G Q : Type*} [Group G] [Finite G] [Group Q]
    {F K M : Subgroup G} (hFK : F ≤ K)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → F ≤ N → N = M)
    (q : K →* Q) (hq : Function.Surjective q) (hc : q.ker ≤ center K)
    (B P : Subgroup Q) (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    (hBP : B ≤ normalizer (P : Set Q))
    (hFB : (q.comp (inclusion hFK)).range ≤ B) : (B.comap q).map K.subtype ≤ M := by
  obtain ⟨U,hU,hUP,hN⟩ := exists_prime_lift_of_central_kernel q hq hc P hp
  have hUne : U ≠ ⊥ := fun he => hne (by simpa only [he,map_bot] using hUP.symm)
  have hUn : U.map K.subtype ≠ ⊥ := fun he => hUne
    ((map_eq_bot_iff_of_injective U K.subtype_injective).mp he)
  have hnmap := U.le_normalizer_map K.subtype
  have hFn : F ≤ normalizer (U.map K.subtype : Set G) := by
    intro x hx
    apply hnmap
    refine ⟨⟨x,hFK hx⟩,hN ?_,rfl⟩
    exact hBP (hFB ⟨⟨x,hx⟩,rfl⟩)
  have hNM := normalizer_le_of_unique_maximalTwoLocal hu (hU.map K.subtype) hUn hFn
  apply le_trans ?_ hNM
  rintro _ ⟨x,hx,rfl⟩
  exact hnmap ⟨x,hN (hBP hx),rfl⟩

theorem image_normal_in_of_preimage_normalizes
    {G Q : Type*} [Group G] [Group Q] {F K : Subgroup G} (hFK : F ≤ K)
    (q : K →* Q) (hq : Function.Surjective q) (B : Subgroup Q)
    (hFB : (q.comp (inclusion hFK)).range ≤ B)
    (hBF : (B.comap q).map K.subtype ≤ normalizer (F : Set G)) :
    ((q.comp (inclusion hFK)).range.subgroupOf B).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer hFB).mpr
  apply le_normalizer_iff.mpr
  intro b hb x hx
  obtain ⟨k,rfl⟩ := hq b
  obtain ⟨f,rfl⟩ := hx
  have hn : (k : G) ∈ normalizer (F : Set G) := hBF ⟨k,hb,rfl⟩
  have hf : (k : G) * f * (k : G)⁻¹ ∈ F := (mem_normalizer_iff.mp hn _).mp f.property
  refine ⟨⟨(k : G) * f * (k : G)⁻¹,hf⟩,?_⟩
  change q (k * inclusion hFK f * k⁻¹) = q k * q (inclusion hFK f) * (q k)⁻¹
  simp only [map_mul,map_inv]
end Subgroup

