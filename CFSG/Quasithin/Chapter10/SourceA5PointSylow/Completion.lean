module
public import CFSG.Quasithin.Chapter10.SourceA5PointSylow.NaturalPoint
public import CFSG.Quasithin.Chapter10.SourceA5PointSylow.Deleted
public import CFSG.Quasithin.Chapter10.SourceA5PointSylow.OriginalOrbits
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.Alternatives
public import CFSG.Quasithin.Chapter10.SourceA5PointFixedKernel.Completion
public import CFSG.Quasithin.Chapter10.SourceA5PointFixedKernel.FixedSpan

/-!
# Point Sylow promotion for the chosen original A₅ module

The natural and deleted markings put every moved vector into a component
conjugate of the Thompson fixed subgroup. Its elementary fixed vectors
lie in the central omega subgroup of J(T), so Baum(T) fixes them. Local
Sylow saturation and Baumann weak closure then give J(C_T(v))=J(T).
The earlier Baumann normalizer containment promotes the same literal
Sylow subgroup to C_G(v).

This discharges Sylow promotion in the all-point centralizer endpoint and
the Thompson equality in the constrained FF-action consumer. All vectors
of the original central cover are retained. Chosen irreducibility, the
earlier Baumann normalizer theorem, separated-factor centralization, and
the later component inspection remain their independent source inputs.

Source: Aschbacher–Smith10.2.9(1), printed pp.750–751, and the constrained
point-component construction on printed pp.751–753.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance pointSylowCompletionElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
local instance pointSylowCompletionAlgebra : Algebra (ZMod 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1) :=
  ZMod.algebra _ 2

omit [Finite G] in
private theorem fixed_representative_of_conjugate_fixed
    (S W : Subgroup G) {v m : G} (hv : v ∈ W)
    (hm : m ∈ normalizer (W : Set G))
    (hfix : (elementaryAbelianMaxJ S).map (MulAut.conj m).toMonoidHom ≤ centralizer ({v} : Set G)) :
    (MulAut.conj m⁻¹) v ∈ W ⊓ centralizer (elementaryAbelianMaxJ S : Set G) := by
  refine ⟨(mem_normalizer_iff.mp ((normalizer (W : Set G)).inv_mem hm) v).mp hv,?_⟩
  intro j hj
  apply (MulAut.conj m).injective
  have hc : (MulAut.conj m) ((MulAut.conj m⁻¹) v) = v := by
    simp only [MulAut.conj_apply,inv_inv]; group
  simpa only [map_mul,hc,MulEquiv.coe_toMonoidHom] using
    (mem_centralizer_singleton_iff.mp (hfix (mem_map_of_mem (MulAut.conj m).toMonoidHom hj)))

theorem source_a5_thompson_fixed_representative_of_irreducible
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    {v : G} (hv : v ∈ ⁅D.fullModule,L⁆) :
    ∃ l ∈ L, (MulAut.conj l) v ∈ ⁅D.fullModule,L⁆ ⊓
      centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  rcases source_a5_original_module_alternatives_of_irreducible D e hi with
    ⟨f,⟨c⟩⟩ | ⟨_,f,⟨c⟩⟩
  · obtain ⟨l,hl⟩ := source_a5_natural_thompson_point_fixed D e f c hv
    exact ⟨(l:G)⁻¹,L.inv_mem l.property,
      fixed_representative_of_conjugate_fixed _ _ hv (c.normalized l.property) hl⟩
  · exact source_deleted_thompson_fixed_representative D
      (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))
      (f.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _))) c hv

theorem source_a5_partner_baumann_conjugate_fixed_of_irreducible
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    {t v : G} (ht : t ∈ (T : Subgroup G))
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) :
    ∃ m ∈ D.maximalLocal,
      (baumann (T : Subgroup G)).map (MulAut.conj m).toMonoidHom ≤ centralizer ({v} : Set G) :=
  source_a5_partner_baumann_conjugate_fixed_of_thompson_orbits D
    (fun _ hw => source_a5_thompson_fixed_representative_of_irreducible D e hi hw) ht hv

theorem source_a5_partner_thompson_eq_of_irreducible
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    {t v : G} (ht : t ∈ (T : Subgroup G))
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (D.maximalLocal ⊓ centralizer ({v} : Set G))) :
    elementaryAbelianMaxJ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) =
      elementaryAbelianMaxJ (T : Subgroup G) := by
  obtain ⟨m,hm,hfix⟩ := source_a5_partner_baumann_conjugate_fixed_of_irreducible D e hi ht hv
  exact source_point_thompson_eq_of_conjugate_fixed D hs
    ⟨m,hm,(map_mono (elementaryAbelianMaxJ_le_baumann _)).trans hfix⟩

theorem source_a5_partner_sylow_and_thompson_of_irreducible
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (h1021 : normalizer (baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    {t v : G} (ht : t ∈ (T : Subgroup G))
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (D.maximalLocal ⊓ centralizer ({v} : Set G))) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (centralizer ({v} : Set G)) ∧
      elementaryAbelianMaxJ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) =
        elementaryAbelianMaxJ (T : Subgroup G) :=
  source_a5_partner_sylow_and_thompson_of_thompson_orbits D h1021
    (fun _ hw => source_a5_thompson_fixed_representative_of_irreducible D e hi hw) ht hv hs

theorem source_a5_moved_point_centralizers_of_irreducible_inspection
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (h1021 : normalizer (baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hinspect : ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom, v ≠ 1 →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (centralizer ({v} : Set G)) → SourceA5PointComponentInspection D e t v) :
    ∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal := by
  apply source_a5_moved_point_centralizers_of_all_point_inspection D e ht htn hcross
    (fun v hv _ hs => (source_a5_partner_sylow_and_thompson_of_irreducible D e hi h1021 ht hv hs).1)
    hinspect

theorem source_a5_point_quasisimple_ff_action_of_irreducible_partner
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t v : G} (ht : t ∈ (T : Subgroup G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) (hvne : v ≠ 1)
    (I : Subgroup G) (hLI : L ≤ I) (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hNI : centralizer ({v} : Set G) ≤ normalizer (I : Set G))
    (hnot : ¬ IsQuasisimple I) (hout : ¬ I ≤ D.maximalLocal)
    (hCW : centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G))) :
    let S := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
    let H := I ⊔ S
    let U := (conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (S : Set G)) I).subgroupOf H
    ∃ hr : IsPReduced 2 U, letI := hr.normal; letI := hr.elementary
      IsQuasisimple ((I.subgroupOf H).map (actionMk U)) ∧
      ⁅(I.subgroupOf H).map (actionMk U),
        (elementaryAbelianMaxJ (S.subgroupOf H)).map (actionMk U)⁆ =
        (I.subgroupOf H).map (actionMk U) ∧
      IsFFModule (V := Additive U) (action U) ∧ Function.Injective (action U) ∧
      Nonempty (ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple (ActionQuotient U)) := by
  have hWV : ⁅D.fullModule,L⁆ ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  have hmapV : D.fullModule.map (MulAut.conj t).toMonoidHom = D.fullModule :=
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule
      (le_normalizer_componentOrbit L T ht))
  have hvV : v ∈ D.fullModule := hmapV ▸ map_mono hWV hv
  have hJ := source_a5_partner_thompson_eq_of_irreducible D e hi ht hv
    (hs.restrict (le_inf (inf_le_left.trans (le_normalizer_componentOrbit L T)) inf_le_right)
      inf_le_right)
  exact source_a5_point_quasisimple_ff_action_all_points D e hi hn ht hcross hvV hvne
    (hcross hv) I hLI hIX hI hNI hnot hout hCW hs hJ

end CFSG.Quasithin.Chapter10
