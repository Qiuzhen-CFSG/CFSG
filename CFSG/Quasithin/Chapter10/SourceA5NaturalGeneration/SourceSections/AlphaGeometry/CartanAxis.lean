module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.AlphaGeometry.Original
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.AlphaGeometry.Coordinates
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.AlphaGeometry.AxisRecognition
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.OriginalAssembly
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
/-!
# The actual alpha fixed subgroup selects an original Cartan axis

The original source places alpha in its actual module, whose selected
natural coordinates are injective after the omega-center centralizer
vanishes. A nonidentity element fixed by the actual cubic subgroup gives
a nonzero paired natural fixed vector. Kernel rigidity under the explicit
original product marking then identifies that subgroup with one of the
two literal original quotient axes of the containing Hall torus.

The HStar branch supplies the nontrivial alpha fixed subgroup; the Hall
branch supplies torus placement. No independent vector, factor alignment,
or equivariance premise remains in this consumer.

Source: Aschbacher--Smith 10.2.3(4), printed pp.746--747.
-/
public section
open Matrix Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L H : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
variable {F : Type*} [Field F] [CharP F 2]
local instance alphaAxisFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
variable
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥)
    (hF : Nat.card F = 4)
    (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
include e hn hH hZH hF f n
set_option backward.isDefEq.respectTransparency false in
theorem source_original_cartan_axis_of_alpha_fixed
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (C P : Subgroup G) (hCB : C ≤ sourceOrbitBorel T L)
    (hc : Nat.card C = 9) (hC : IsElementaryAbelian 3 C)
    (hPC : P ≤ C) (hP : Nat.card P = 3)
    (hfixed : thompsonAlpha (T : Subgroup G) ⊓ centralizer (P : Set G) ≠ ⊥) :
    let hCR : C ≤ localOrbit T L := hCB.trans ((map_subtype_le _).trans inf_le_left)
    let q := (originalA5ProductProjection D e hn ht htn).comp (inclusion hCR)
    P = ((MonoidHom.snd _ _).comp q).ker.map C.subtype ∨
      P = ((MonoidHom.fst _ _).comp q).ker.map C.subtype := by
  let A := alternatingGroup (Fin 5)
  let R := localOrbit T L
  have hCR : C ≤ R := hCB.trans ((map_subtype_le _).trans inf_le_left)
  let q := (originalA5ProductProjection D e hn ht htn).comp (inclusion hCR)
  have hpair := source_original_paired_linear_of_hstar_natural_four D e hn hH hZH hF f n
  have hJ := source_hstar_local_thompson_moves_of_omega_commutator D hH hZH
  obtain ⟨K,hK,a,m,hm,he⟩ := source_original_module_marking_of_selected_source
    D e hn ht htn hz hJ hpair
  obtain ⟨b₀⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hK
  let b : A ≃* SL(2,K.Carrier) := (Atlas.RankOneFieldAutomorphisms.slEquivPSL.trans b₀).symm
  have hcore : pCore 2 A = ⊥ := by
    apply Subgroup.map_injective (f := b.toMonoidHom) b.injective
    rw [pCore_map_iso,Subgroup.map_bot,Atlas.RankOneFieldAutomorphisms.sl_twoCore_eq_bot]
  have hi : Function.Injective q := source_a5_borel_torus_quotient_injective C hCB
    (IsPGroup.of_card (n := 2) hc) _
    ((originalA5ProductProjection_ker D e hn ht htn).symm ▸ pCore_isPGroup)
  obtain ⟨⟨x,hx⟩,hne'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hfixed
  have hne : x ≠ 1 := fun h => hne' (Subtype.ext h)
  have hαU := source_original_alpha_le_module_of_hstar_natural_four D e hn hH hZH hF f n hz
  let v : D.moduleSubgroup := ⟨x,hαU hx.1⟩
  have hv : (m v).toAdd ≠ 0 := by
    intro h
    have hh0 : m v = 1 := h
    have hh : m v = m 1 := hh0.trans m.map_one.symm
    have hh' := congrArg Subtype.val (hm.1 hh)
    exact hne hh'
  apply source_a5_cartan_axis_of_equivalent_natural_pair hcore C P q hi hc hC b a hPC hP
    (m v).toAdd hv
  intro p hp
  have hcP : (p:G)*x*(p:G)⁻¹ = x := by
    rw [hx.2 p hp,mul_inv_cancel_right]
  have hh := he (inclusion hCR p) v
  have hv' : (⟨(p:G)*v*(p:G)⁻¹,
      (mem_normalizer_iff.mp (D.orbit_normalizes_module (hCR p.property)) v).mp v.property⟩ :
      D.moduleSubgroup) = v := Subtype.ext hcP
  change (m ⟨(p:G)*v*(p:G)⁻¹,_⟩).toAdd = _ at hh
  rw [hv'] at hh
  exact hh.symm
end CFSG.Quasithin.Chapter10
