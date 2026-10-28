module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SecondBlock.BaumannPlacement
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SecondBlock.CommonBaumannGeometry
/-!
# Recovering the second original component from the paired natural source

The genuine paired source and full-core movement place the common Baumann
subgroup in the original commuting component product and make it a full
Sylow there. The first natural block's cubic action gives central elementary
commutators in both conjugate Sylow factors. Their product supplies the
common-base hypothesis of the second component's C.1.17 local class,
which forces that original component to be a block in its stated ambient.
All quotient maps, the paired marker and the original component are retained.
Source: Aschbacher--Smith 10.2.3(4), printed pp.746--747.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE.ThompsonAction ChapterB ChapterB.SourceInduction
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
set_option backward.isDefEq.respectTransparency false in
theorem source_original_second_block_of_paired_linear
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsBlock (L.subgroupOf (localJoin T L)))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (A : Subgroup G) (hL : ChapterC.IsL2EvenBlock L 2)
    (hAL : A ≤ L) (hA : Nat.card A=3)
    (hAS : A ≤ normalizer (baumann (T : Subgroup G) : Set G))
    {K M : Subgroup G} (hKM : K ≤ M) (hK : (K.subgroupOf M).IsCComponent)
    (hBK : baumann (T : Subgroup G) ≤ normalizer (K : Set G))
    (hlocal : ChapterC.GlaubermanNiles.InLocalClass (inclusion
      (show baumann (T : Subgroup G) ≤ K ⊔ baumann (T : Subgroup G) from le_sup_right))) :
    let X := localJoin T L
    let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
    let U := D.moduleSubgroup.subgroupOf X
    letI := (source_parabolic_module_reduced D).normal
    letI := (source_parabolic_module_reduced D).elementary
    let C := centralizer (U : Set X)
    let q := QuotientGroup.mk' C
    let hq := QuotientGroup.mk'_surjective C
    let hk := QuotientGroup.ker_mk' C
    let α := NormalElementaryQuotient.representation U q hq hk
    let Y := offenderSubgroup α
    letI := offenderSubgroup_normal α
    ∀ (_hJ : ¬ elementaryAbelianMaxJ (S : Subgroup X) ≤ centralizer (U : Set X))
      (d : SourceTwoFactorCase (α.comp Y.subtype)) (F : BinaryField)
      (_hF : 3 < Nat.card F.Carrier) (_c : d.MarkedProduct (linearNatural F 2))
      (_hexchange : ∃ t : S.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:X ⧸ C)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:X ⧸ C)).toMonoidHom = d.first),
      ChapterC.IsBlock (K.subgroupOf M) := by
  let X := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf X
  have hU : IsPReduced 2 U := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker=C := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let := offenderSubgroup_normal α
  dsimp only
  intro hJ d F hF c hexchange
  obtain ⟨hSO,hS⟩ := source_original_baumann_in_orbit_of_source
    D e hn hb hz hH hZH hJ d F hF c hexchange
  have hclass := source_original_component_localClass_of_paired_linear D e hn hJ d F c hexchange
  have hSm : (S : Subgroup X).map X.subtype=(T : Subgroup G) := map_subgroupOf_eq_of_le le_sup_right
  have hBm := baumann_map_injective X.subtype X.subtype_injective (S : Subgroup X)
  change (baumann (S : Subgroup X)).map X.subtype=baumann ((S : Subgroup X).map X.subtype) at hBm
  rw [hSm] at hBm
  have hSL : baumann (T : Subgroup G) ≤ normalizer (L : Set G) := by
    have hh := map_mono (f := X.subtype)
      (le_normalizer_iff_commutator_le_right.mp hclass.2.1)
    rw [map_commutator,hBm,map_subgroupOf_eq_of_le
      ((le_componentOrbit L T).trans le_sup_left)] at hh
    exact le_normalizer_iff_commutator_le_right.mpr hh
  exact source_component_block_of_common_baumann_commutator hKM hK hBK hlocal
    (source_original_common_baumann_commutator D e hn hb hz hH hZH A hL hS hSO hAL hA hAS hSL)
end CFSG.Quasithin.Chapter10
