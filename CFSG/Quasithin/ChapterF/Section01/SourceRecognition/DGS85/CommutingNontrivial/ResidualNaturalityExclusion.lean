module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualProperImage
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.BinaryResidualFixed
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.PathBorelSylow
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.BinaryCatalogue
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.NaturalResidualDihedralExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.OppositeResidualMovement
public import Theory.Representation.SpecialLinearNatural.ProperBorelInvariant
public import Theory.Representation.BinaryConjugationSection.FixedImage

/-!
# The natural residual exclusion in DGS 8.5

Suppose the entire beta residual section is natural. The source catalogue
and dihedral exclusion recognize the alpha center and give both center
orders and the beta core commutator. The residual fixed denominator has
local displacement in the beta center: perfectness proves this for larger
fields, and odd-residual fixed generation proves it over the binary field.

The intersection with the terminal core has proper image. A full image
would force a cubic neighborhood and collapse its denominator into that
proper intersection. The literal path actor maps onto the beta Borel and
normalizes the intersection, whose proper image is therefore fixed by the
opposite Sylow. Its commutator lies in the residual fixed denominator,
contradicting movement of the nonzero terminal-central intersection.

All field sizes, source catalogue rows, actor images, quotient maps, and
denominators are retained. Source: DGS, *Groups and Graphs* (1985), 8.5,
printed p.139.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open CommutingTrivial
universe u
variable {G : Type u} [Group G] {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- At critical distance three with nonzero intersection commutator, the
whole beta residual section cannot be natural over any defining field. -/
theorem reduced_natural_residual_exclusion
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : b (Reduction.reducedFamily J S₀) = 3)
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily J S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) beta)) ≃* SL(2,F))
    (hres : NaturalResidualSection h beta e n) : False := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily J S₀
  change b Γ = 3 at hb
  change (graph Γ).dist beta a' + 1 = b Γ at hd
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let hB := Reduction.reduced_borel_core_sylow h
  let hS := Reduction.reduced_vertex_sylow h
  let hSyl := Reduction.reduced_kernel_sylow h
  let hZ := fun v => (source_Z_Q_U ht v).1
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  have hb1 : 1 < b Γ := by omega
  have hb2 : 2 < b Γ := by omega
  have hnotdi : ¬ Nonempty ((graphLocalGroup Γ a ⧸ pCore 2 (graphLocalGroup Γ a)) ≃* DihedralGroup 5) := by
    rintro ⟨ed⟩
    exact reduced_natural_residual_not_dihedral h hc hab hd hb1 hcomm (models a)
      (by omega) hF e hres ed
  obtain ⟨Mbin⟩ := (models a).binaryModel_of_not_dihedral hnotdi
  have hz := (source_critical_geometry ht d hc hab hd hb1 hcomm).2.2.1
  obtain ⟨K,_,_,_,m,hm,hK,⟨eα⟩⟩ :=
    reduced_natural_residual_alpha_model h hob hc hab hd hb1 hcomm Mbin (models a) (by omega) hF e hres
  let := Z_elementary Γ hZ a
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  obtain ⟨heq,hcQ,hcV,ρ,Tα,hact,hfaith,hnatα,Eα,hEα⟩ :=
    reduced_natural_residual_alpha_natural h hob hc hab hd hb1 hcomm Mbin (models a)
      (by omega) hF e hres hm hK eα
  obtain ⟨hca,hcb⟩ := linear_natural_neighbor_center_orders ht hB hS hab
    (core_escape_of_intersection_obstruction Γ (hob beta a hab.symm)) hz hm hK eα
    ρ hact hfaith ⟨Tα,hnatα⟩
  rw [heq] at hca hcb
  obtain ⟨mid,hbm,ham,hVm,hescmid,hpath⟩ :=
    reduced_critical_path_borel_or_dihedral h hob models hc hab hd hb hcomm e
  obtain ⟨g,hg,hgm⟩ := graphLocalGroup_transitive ht hB hS beta ⟨a,hab.symm⟩ ⟨mid,hbm⟩
  change g • a = mid at hgm
  have hcm : Nat.card (Z Γ mid) = Nat.card F ^ 2 := by
    have hh := card_map_of_injective (K := Z Γ a)
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [←Z_translate,hgm] at hh
    exact hh.trans hca
  rcases hpath with hdi | ⟨T,hT,hKpath,hfix⟩
  · obtain ⟨ed⟩ := hdi
    let el := ((graphLocalGroup Γ a).equivMapOfInjective
        (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
        (MulEquiv.subgroupCongr ((graphLocalGroup_conjugate ht g a).symm.trans (congrArg _ hgm)))
    let eqt := QuotientGroup.congr _ _ el (pCore_map_iso 2 el)
    exact hnotdi ⟨eqt.trans ed⟩
  · let L := graphLocalGroup Γ beta
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
    let A := V Γ beta 1 ⊓ Q Γ a'
    let U := V Γ a' 1
    have hUQ : U ≤ Q Γ mid := V_le_Q_of_dist_add_lt_b Γ ht.generate hZ a' mid 1
      (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr ham]; omega) (hSyl mid)
    have hUL : U ≤ L := hUQ.trans (neighbor_core_le_localGroup ht hB hS hbm)
    have hUesc := reduced_reciprocal_escape h hob models hc hab hd hb1 hcomm hne
    have hUimage := source_path_normalized_sylow_image ht U hUL hUQ hUesc
      (stabilizer_normalizes_V Γ a' 1) e T hT hKpath
    change (U.subgroupOf L).map q = T at hUimage
    have hi : (Q Γ beta).relIndex U = Nat.card F := by
      have hcard := BinaryConjugationSection.actor_image_card_eq_relIndex L (Q Γ beta) U q ?_ hUL
      · rw [hUimage] at hcard
        exact hcard.symm.trans (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 T).symm.toEquiv)
      · rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
        have hcore : (pCore 2 L).map L.subtype = Q Γ beta := graphLocalGroup_core ht beta
        rw [←hcore]
        exact (comap_map_eq_self_of_injective L.subtype_injective _).symm
    obtain ⟨hVQ,hUQa,heV,heU,_,_,hVesc⟩ := reduced_neighbor_quadratic h hSyl hc hab.symm hb2 hd
    let := heV
    let := heU
    let : Finite (V Γ beta 1) := Finite.of_injective
      (inclusion (hVQ.trans (Q_le_stabilizer Γ beta))) (inclusion_injective _)
    let A₀ := (V Γ beta 1).subgroupOf L
    let := neighborhoodIn_normal Γ beta L (sylowGenerated_le _)
    obtain ⟨hb2',σ,Tβ,hσ,hfaithβ,hnatβ,Eβ,hEβ⟩ := hres
    let := neighborhoodIn_elementary Γ ht.generate hZ hSyl beta hb2' L
    let : Algebra (ZMod 2) F := ZMod.algebra F 2
    have hcomp : σ.comp q = Representation.NormalElementaryQuotient.fixedQuotientAction A₀ (pResidual 2 L) :=
      MonoidHom.ext hσ
    obtain ⟨⟨c₀⟩,_,_⟩ := neighborhood_residual_section ht hSyl beta hb2' L
      (core_le_graphLocalGroup ht beta) (sylowGenerated_le _)
    let c := hcomp.symm ▸ c₀
    have hcW : Nat.card (Representation.NormalElementaryQuotient.FixedQuotient A₀ (pResidual 2 L)) = Nat.card F ^ 2 := by
      have hh := hnatβ.1
      rw [hh,hF,←pow_mul,Nat.mul_comm n 2]
    have hZA : Z Γ beta ≤ A := le_inf (Z_le_V Γ beta 1)
      (CommutingTrivial.Z_le_Q_of_dist_lt_b Γ hZ hSyl beta a' (by omega))
    have hHZ := (source_critical_commutator_structure ht hB d hc hab hd hb1 hcomm models).2.1 ⟨mid,ham⟩
    let : Finite (V (family (fun i => (Reduction.P₀ J S₀ i).subgroupOf (Reduction.G₀ J S₀))) beta 1) :=
      inferInstanceAs (Finite (V Γ beta 1))
    let : IsMulCommutative (V (family (fun i => (Reduction.P₀ J S₀ i).subgroupOf (Reduction.G₀ J S₀))) beta 1) :=
      heV.toIsMulCommutative
    have hproper : c.imageSpace A ≠ ⊤ := by
      by_cases hn1 : n = 1
      · have hF2 : Nat.card F = 2 := by simpa only [hn1,pow_one] using hF
        have hfixed := source_binary_residual_fixed_commutator ht hB hS hab.symm
          (core_escape_of_intersection_obstruction Γ (hob a beta hab)) hb2 hcV.le hF2 e
        exact source_residual_image_proper_of_fixed_commutator ht hB hS hbm hz hcV.le e hfixed σ c hcW A U inf_le_left hZA (fun hh => hVesc (hh.trans inf_le_right))
          (hVm.trans (Q_le_stabilizer Γ mid)) hUL (IsElementaryAbelian.isPGroup 2 U) hi
          (hUQ.trans (Q_le_stabilizer Γ mid)) hHZ hcm hcb
      · have hlarge : 3 < Nat.card F := by
          rw [hF]
          have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
          norm_num at hh
          omega
        exact source_natural_residual_image_proper ht hB hS hbm hz hcV.le hlarge e σ c hcW A U inf_le_left hZA (fun hh => hVesc (hh.trans inf_le_right))
          (hVm.trans (Q_le_stabilizer Γ mid)) hUL (IsElementaryAbelian.isPGroup 2 U) hi
          (hUQ.trans (Q_le_stabilizer Γ mid)) hHZ hcm hcb
    have hinv : ∀ t ∈ normalizer (T : Set SL(2,F)), ∀ w ∈ c.imageSpace A, σ t w ∈ c.imageSpace A := by
      intro t ht w hw
      rw [←hKpath] at ht
      obtain ⟨l,hl,rfl⟩ := ht
      have hnA : (l : Reduction.G₀ J S₀) ∈ normalizer (A : Set (Reduction.G₀ J S₀)) :=
        inf_normalizer_le_normalizer_inf ⟨c.normalized l.property,
          stabilizer_normalizes_Q Γ a' hl.2⟩
      exact c.imageSpace_apply_mem A l hnA w hw
    have hfixed := Representation.SpecialLinearTwo.proper_natural_sylow_normalizer_invariant_fixed
      σ Eβ hEβ T (c.imageSpace A) hproper hinv
    have hHker : ⁅A,U⁆ ≤ V Γ beta 1 ⊓ centralizer ((pResidual 2 L).map L.subtype : Set (Reduction.G₀ J S₀)) := by
      rw [commutator_comm]
      apply c.commutator_le_of_imageSpace_fixed U A hUL inf_le_left
      intro w hw u
      apply hfixed hw ⟨q u.val,?_⟩
      rw [←hUimage]
      exact mem_map_of_mem q u.property
    exact (source_distance_three_critical_commutator_not_residual_fixed ht hB d hob models
      hc hab hd hb hcomm hne).2 hHker
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
