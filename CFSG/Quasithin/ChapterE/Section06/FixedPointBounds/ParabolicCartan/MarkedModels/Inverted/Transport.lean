module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Transport
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.FixedSubgroup
/-!
# The faithful Cartan or escaping normalizer alternative

The Hall construction and ambient embedding retain the same cyclic subgroup.
If that subgroup is not faithful on the original V, select a nontrivial
odd-primary subgroup of its fixed subgroup. Its intrinsic normalizer escapes
the unique maximal subgroup, and injectivity transfers this escape to the
actual relative ambient normalizer. No earlier containment theorem is used.
Source: Aschbacher–Smith E.6.27, printed p.257.
-/
public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted
open ChapterB
universe u v
variable {X : Type u} [Group X] [Finite X] {G : Type u} [Group G] [Finite G]
omit [Finite X] [Finite G] in
theorem transport_cyclic_image {n : ℕ} {S : Sylow 2 X}
    {hP : IsMinimalParabolicOver S ⊤} (d : IntrinsicHallCartanData S hP n)
    (f : X →* G) (hf : Function.Injective f) (M U : Subgroup G)
    (hC : f.range ≤ centralizer (U : Set G))
    (hM : minimalParabolicMax S hP = M.comap f)
    (R : Sylow 2 ↥(M ⊓ centralizer (U : Set G)))
    (hR : (R : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
      (M ⊓ centralizer (U : Set G)).subtype = (S : Subgroup X).map f) :
    (transport d f hf M U hC hM R hR).witness.cyclicGroup.map
      (M ⊓ centralizer (U : Set G)).subtype = d.witness.cyclicGroup.map f := by
  let D := minimalParabolicMax S hP
  let L := M ⊓ centralizer (U : Set G)
  let g : D →* L := (f.comp D.subtype).codRestrict L (by
    intro x
    exact ⟨show x.val ∈ M.comap f from hM ▸ x.property, hC ⟨x, rfl⟩⟩)
  change ((d.witness.cyclicGroup.subgroupOf D).map g).map L.subtype = _
  rw [map_map]
  change (d.witness.cyclicGroup.subgroupOf D).map (f.comp D.subtype) = _
  rw [← map_map, map_subgroupOf_eq_of_le (d.witness.cyclic_le.trans d.hall_le)]

omit [Finite G] in
theorem alternative_of_intrinsic_escape {n : ℕ} {S : Sylow 2 X}
    {hP : IsMinimalParabolicOver S ⊤} (d : IntrinsicHallCartanData S hP n)
    (hN : ∀ (p : ℕ) (_ : Fact p.Prime) (A : Subgroup X), Odd p →
      A ≤ d.witness.cyclicGroup → IsPGroup p A → ¬normalizer (A : Set X) ≤ minimalParabolicMax S hP)
    (f : X →* G) (hf : Function.Injective f) (M U V : Subgroup G)
    (hC : f.range ≤ centralizer (U : Set G))
    (hM : minimalParabolicMax S hP = M.comap f)
    (R : Sylow 2 ↥(M ⊓ centralizer (U : Set G)))
    (hR : (R : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
      (M ⊓ centralizer (U : Set G)).subtype = (S : Subgroup X).map f) :
    ParabolicCartanAlternative V M U f.range n := by
  classical
  let d' := transport d f hf M U hC hM R hR
  have heq := transport_cyclic_image d f hf M U hC hM R hR
  by_cases hb : d.witness.cyclicGroup.map f ⊓ centralizer (V : Set G) = ⊥
  · exact Or.inl ⟨d'.witness, heq ▸ map_le_range f _, heq.symm ▸ hb⟩
  · have hne : d.witness.cyclicGroup ⊓ (centralizer (V : Set G)).comap f ≠ ⊥ := by
      intro hz
      apply hb
      apply le_antisymm _ bot_le
      rintro z ⟨⟨x,hx,rfl⟩,hc⟩
      have hx0 : x ∈ (⊥ : Subgroup X) := hz ▸ (show x ∈ d.witness.cyclicGroup ⊓
        (centralizer (V : Set G)).comap f from ⟨hx,hc⟩)
      simp only [mem_bot, (mem_bot.mp hx0), map_one]
    let :=  d.witness.cyclic
    obtain ⟨p,A,hp,ho,hA,he,hAD,hAo,_⟩ := exists_elementary_odd_in_intersection
      (Y := d.witness.cyclicGroup) (C := (centralizer (V : Set G)).comap f)
      (inferInstance) (d.witness.odd.of_dvd_nat (card_dvd_of_le d.witness.cyclic_le)) hne
    let : Fact p.Prime := ⟨hp⟩
    let :=  he
    have hAM : A ≤ M.comap f := (hAD.trans inf_le_left).trans
      (d.witness.cyclic_le.trans (hM ▸ d.hall_le))
    refine Or.inr ⟨A.map f, ?_, ?_, ?_, ?_⟩
    · exact fun hz => hA ((map_eq_bot_iff_of_injective A hf).mp hz)
    · exact le_inf (le_inf (map_le_range f A) (map_le_iff_le_comap.mpr hAM))
        (map_le_iff_le_comap.mpr (hAD.trans inf_le_right))
    · simpa only [card_map_of_injective hf] using hAo
    · intro hh
      apply hN p inferInstance A ho (hAD.trans inf_le_left) he.isPGroup
      rw [hM]
      intro x hx
      exact hh ⟨⟨x,rfl⟩, A.le_normalizer_map f (mem_map.mpr ⟨x,hx,rfl⟩)⟩
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted
