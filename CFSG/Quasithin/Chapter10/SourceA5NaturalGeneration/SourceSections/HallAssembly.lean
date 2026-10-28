module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.OmegaEntrance.Source
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.HStarSource.CubicFixedCenter
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.CubicFixedCenter
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.HallNontrivial
public import CFSG.Quasithin.Chapter3.Section01.HStarOmegaCentralizer
/-!
# The natural Hall entrance and vanishing fixed centers

The actual odd Hall subgroup is nontrivial when the generation minimum
exceeds one. Its exponent-three placement in the original orbit makes it
faithful on the Sylow omega-center. H-star minimality then identifies that
center's centralizer in H with the prescribed Sylow subgroup. Comparing the
two proved fixed-center equalities for one actual cubic Hall element forces
both original-orbit and H fixed centers to vanish.

This discharges the four entrance assumptions used by source selection,
alpha geometry and the characteristic-pair argument. Original natural
irreducibility, crossed-factor centralization and the actual Hall placement
remain the earlier source inputs, with their original maps unchanged.
Source: Aschbacher–Smith 10.2.3(4), pp.745–746.
-/
public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance hallAssemblyOriginalMovedElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
variable {F : Type*} [Field F] [CharP F 2]
local instance hallAssemblyFixedFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

theorem source_natural_fixed_centers_of_hall
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hF : Nat.card F=4) (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)))
    (hBR : B.map H.subtype ≤ localOrbit T L)
    [IsElementaryAbelian 3 (B.map H.subtype)] :
    ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥ ∧
      centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
        (T.subtype hH.1.1.2 : Subgroup H) ∧
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥ ∧
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥ := by
  have hB := source_hstar_hall_ne_bot_of_generation_large D e hn hH hlarge B hBM hHall
  have hBi : B.map H.subtype ≠ ⊥ := fun he => hB ((map_eq_bot_iff_of_injective _ H.subtype_injective).mp he)
  have hZH := source_natural_omega_commutator_ne_bot_of_three_hall
    D e hn ht htn hcross f n hi (B.map H.subtype) H hBR (map_subtype_le B) hBi
  have hfaith := source_natural_three_hall_omega_centralizer_eq_bot
    D e hn ht htn hcross f n hi (B.map H.subtype) hBR
  have hCZ := Chapter3.HStar.omega_center_centralizer_eq_sylow_of_hall hH hZH B hBM hHall hfaith
  obtain ⟨⟨b,hbB⟩,hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB
  have hbG1 : (b:G)≠1 := fun he => hb1 (Subtype.ext (Subtype.ext he))
  have hbG : (b:G) ∈ B.map H.subtype := mem_map_of_mem H.subtype hbB
  have hb3 : orderOf (b:G)=3 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (b:G) hbG) hbG1
  have hbH : orderOf b=3 := by simpa only [Subgroup.orderOf_coe] using hb3
  let bR : localOrbit T L := ⟨b,hBR hbG⟩
  have hbR : orderOf bR=3 := by simpa only [bR,Subgroup.orderOf_mk] using hb3
  have hfix := source_hstar_cubic_fixed_center D e hn hH hZH hF f n hlarge hCZ b hbH
  exact ⟨hZH,hCZ,source_hstar_natural_four_fixed_centers_eq_bot_of_cubic
    D e hn hH hZH hF f n bR hbR hfix.symm⟩
end CFSG.Quasithin.Chapter10
