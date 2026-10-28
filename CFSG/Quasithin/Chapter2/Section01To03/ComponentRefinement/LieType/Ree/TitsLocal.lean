module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Ree.TitsLocal.Pair
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Ree.TitsLocal.InvariantOvergroups
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Ree.TitsLocal.BlockLayers.Local

/-!
# Tits endpoint local calculations

The literal inner action determines an involution projection. A constructed
marking sends it to Atlas r5 and sends S ∩ L to the certified Atlas Sylow
subgroup. The full centralizer and characteristic-normalizer identifications
give both parabolics their N_S(L)-invariance. Both overgroups belong to HeOver,
including nontriviality of their actual two-cores; the first lies in M.

The second parabolic's concrete commutator obstruction, transported through
the component-orbit coordinates, excludes short subnormal subgroups of the
second overgroup. It supplies the requested normal two-layer conclusion for
every escaping relative block. All model premises are discharged here, while
S is still allowed to permute components. The parent Ree exclusion can apply
`false_of_right_calculations` directly to the constructed data.

Source: Aschbacher–Smith 1.1.5(3)(a), pp.501–502, and 2.3.9(7), p.526.
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Ree

open Subgroup ChapterC

variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- All Tits endpoint calculations from the genuine local setup and literal
inner action. The same marking, projected involution and invariant pair serve
every conclusion; there are no additional stabilizer or coordinate premises. -/
theorem tits_exists_local_calculations
    (h : LocalSetup H L M S z) (e : L ≃* Tits.ParrottGroup)
    (α : MulAut L) (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hinner : α ∈ (MulAut.conj (G := L)).range) :
    ∃ (e' : L ≃* Tits.ParrottGroup) (t : L)
      (d : InvariantPair L ((S : Subgroup H).map H.subtype)),
      d.left = titsFirst e' ∧ d.right = titsSecond e' ∧
      IsConjugationProjection L z t ∧ orderOf t = 2 ∧
      titsAtlasEquiv e' t = Tits.atlas1600R5 ∧
      (((S : Subgroup H).map H.subtype).subgroupOf L).map
        (titsAtlasEquiv e').toMonoidHom = Tits.atlas1600SylowTwoSubgroup ∧
      d.leftOver ≤ M ∧
      d.leftOver ∈ Chapter1.HeOver G
        (((S : Subgroup H).map H.subtype : Subgroup G) : Set G) ∧
      d.rightOver ∈ Chapter1.HeOver G
        (((S : Subgroup H).map H.subtype : Subgroup G) : Set G) ∧
      z ∈ d.rightOver.pCoreIn 2 ∧
      ∀ B : Subgroup d.rightOver, IsBlock B →
        B.map d.rightOver.subtype =
          ⁅B.map d.rightOver.subtype,
            Stellmacher.elementaryAbelianMaxJ ((S : Subgroup H).map H.subtype)⁆ →
        ¬ B.map d.rightOver.subtype ≤ M → HasNoncentralTwoLayer B := by
  obtain ⟨e', t, ht, htwo, himage, hmark⟩ :=
    tits_exists_compatible_sylow_marking h e α hα hinner
  have hproj := tits_projection_of_marked_image e' ht himage
  let d := titsPairOfSylowStabilizers e' hmark
    Tits.RelativeParabolicNormalizers.first_stabilized
    Tits.RelativeParabolicNormalizers.second_stabilized
  refine ⟨e', t, d, rfl, rfl, ht, htwo, himage, hmark, ?_, ?_, ?_, ?_, ?_⟩
  · exact titsFirstOver_le_of_projection h e' hproj
  · exact titsFirstOver_mem_HeOver h e' hproj
  · exact titsSecondOver_mem_HeOver h e' hmark hproj
  · exact titsSecondOver_z_mem_core h e' hmark hproj
  · exact titsSecondOver_escaping_layers h e' d rfl

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Ree

end
