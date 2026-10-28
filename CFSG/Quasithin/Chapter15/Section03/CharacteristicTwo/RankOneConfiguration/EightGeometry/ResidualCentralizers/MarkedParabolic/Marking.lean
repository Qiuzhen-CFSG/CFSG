module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.MarkedParabolic.FixedLine

/-!
# Compatible four-block markings from the fixed-vector stabilizer

The natural actor sends the supplied Sylow subgroup onto a Sylow subgroup
of S₈. Apply the concrete fixed-vector stabilizer calculation, then relabel
the compatible star equivalence by its conjugator. The component image is
A₈ by uniqueness of its index-two subgroup. Intersecting the fixed-plane
centralizer with the component gives the even four-block stabilizer, while
Dedekind decomposition identifies its Sylow extension with the whole one.

The fixed-vector calculation is an explicit, purely model-theoretic input;
this reduction does not assume the desired ambient centralizer marking.

Source: Aschbacher–Smith, 15.3.32(4), printed pp.1132–1133.
-/

public section
open Subgroup
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.MarkedParabolic
variable {G : Type*} [Group G] [Finite G]

/-- The concrete fixed-vector calculation supplies all three compatible star markings. -/
theorem exists_marking_of_fixedVector_geometry (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hn : (c.L.subgroupOf I).Normal)
    (hjoin : I = c.L ⊔ d.S)
    (m : Parabolics.MiddleNodePermutationMarking d I c.L)
    (a : NaturalEightAction I (d.componentModule I c.L))
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hC : I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2)
    (hfixed : d.ZS ⊓ centralizer (c.L : Set G) = d.ZS ⊓ d.V₁)
    (hcard : Nat.card d.ZS = 4)
    (hfirst : Nat.card (d.ZS ⊓ d.V₁ : Subgroup G) = 2)
    (hsecond : Nat.card (d.ZS ⊓ d.V₂ : Subgroup G) = 2)
    (hinter : d.ZS ⊓ d.componentModule I c.L = d.ZS ⊓ d.V₂)
    (hgeometry : ∀ (Q : Sylow 2 (Equiv.Perm (Fin 8)))
      (v : BinaryPermutation.natural (Fin 8)), v ≠ 0 →
      (∀ g ∈ (Q : Subgroup (Equiv.Perm (Fin 8))),
        BinaryPermutation.naturalRepresentation (Fin 8) g v = v) →
      ∃ r : Equiv.Perm (Fin 8), ∀ g : Equiv.Perm (Fin 8),
        BinaryPermutation.naturalRepresentation (Fin 8) g v = v ↔
          r * g * r⁻¹ ∈ fourStabilizer) :
    ∃ b : CompatibleStarMarking d I (d.componentModule I c.L) a,
      (d.starImage I c.L).map b.equiv.toMonoidHom = alternatingGroup (Fin 8) ∧
      (d.starImage I (c.L ⊓ centralizer (d.ZS : Set G))).map b.equiv.toMonoidHom =
        fourStabilizer ⊓ alternatingGroup (Fin 8) ∧
      (d.starImage I ((c.L ⊓ centralizer (d.ZS : Set G)) ⊔ d.S)).map
        b.equiv.toMonoidHom = fourStabilizer := by
  obtain ⟨v, hv, hSfix, hfix⟩ := exists_fixedVector_centralizer d c hjoin a
    hfixed hcard hfirst hsecond hinter
  let Q := P.mapSurjective a.onto
  have hvQ : ∀ g ∈ (Q : Subgroup (Equiv.Perm (Fin 8))),
      BinaryPermutation.naturalRepresentation (Fin 8) g v = v := by
    rintro g ⟨i, hi, rfl⟩
    exact hSfix i (hP ▸ mem_map_of_mem I.subtype hi)
  obtain ⟨r, hr⟩ := hgeometry Q v hv hvQ
  let b := relabelMarking d (naturalStarMarking d c a P hP hC) r
  have hb (i : I) : b.equiv (d.starMap I i) = r * a.actor i * r⁻¹ := by
    exact b.compatible i
  have hpoint (i : I) : (i : G) ∈ centralizer (d.ZS : Set G) ↔
      b.equiv (d.starMap I i) ∈ fourStabilizer := by
    rw [hb]
    exact (hfix i).trans (hr (a.actor i))
  have hL := component_image d m b.equiv
  have hK : (d.starImage I (c.L ⊓ centralizer (d.ZS : Set G))).map b.equiv.toMonoidHom =
      fourStabilizer ⊓ alternatingGroup (Fin 8) := by
    apply le_antisymm
    · rintro g ⟨x, ⟨i, hi, rfl⟩, rfl⟩
      refine ⟨(hpoint i).mp hi.2, ?_⟩
      rw [← hL]
      exact mem_map_of_mem _ (mem_map_of_mem _ hi.1)
    · intro g hg
      have hgin : g ∈ (d.starImage I c.L).map b.equiv.toMonoidHom := hL ▸ hg.2
      obtain ⟨x, ⟨i, hi, rfl⟩, rfl⟩ := hgin
      exact mem_map_of_mem _ (mem_map_of_mem _ ⟨hi, (hpoint i).mpr hg.1⟩)
  refine ⟨b, hL, hK, ?_⟩
  rw [← fixedPlane_centralizer_decomposition d c hn hjoin]
  apply le_antisymm
  · rintro g ⟨x, ⟨i, hi, rfl⟩, rfl⟩
    exact (hpoint i).mp hi.2
  · intro g hg
    obtain ⟨x, rfl⟩ := b.equiv.surjective g
    obtain ⟨i, rfl⟩ := QuotientGroup.mk'_surjective (localActionKernel d.Z I) x
    exact mem_map_of_mem _ (mem_map_of_mem _ ⟨i.property, (hpoint i).mpr hg⟩)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.MarkedParabolic
end
