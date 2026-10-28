module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerKernel
public import Theory.GroupTheory.PResidual.PointCentralizerFusion
public import CFSG.Quasithin.ChapterI.Section06To08.Basic
public import Theory.GroupAction.FourAutomorphismOrbit
/-!
# The elementary residual-centralizer TI branch

If the literal residual centralizer is elementary abelian, each of its
nonidentity elements is graph-class: its centralizer contains the A₆
residual of order 360, which cannot embed in the root centralizer of order
1152. Conjugate point-centralizer residuals then coincide, and their abelian
centralizers coincide as well. Thus every returning conjugator normalizes
the entire four-group. This proves TI and normalizer transitivity; the
three-point orbit gives an element with induced automorphism of order three.

Source: Aschbacher–Smith F.5.5, printed p.302, the elementary R₀ contradiction.
The subsequent contradiction with the two elementary-sixteen families is
retained by the final source assembly.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open GreenBook.LieModels.UnitaryFour
open ChapterI.Section06To08
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)

variable (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
include h

theorem sourceResidualCentralizer_eq_point (R : Sylow 2 (C c i)) (hR : Tf c i ≤ R) :
    sourceResidualCentralizer c i = pointResidualCentralizer 2 (Source.graphElement c i) := by
  apply eq_of_le_of_card_ge
  · intro x hx
    rw [←source_Rzero_eq_residual_centralizer c i z h R hR,
      Rzero,source_DtwoResidual_eq_centralizer_residual c i z h R hR] at hx
    exact ⟨Rimage_le_C c i R hx.1,hx.2⟩
  · have he : pointResidualCentralizer 2 (Source.graphElement c i) =
        (centralizer (pResidual 2 (C c i) : Set (C c i))).map (C c i).subtype :=
      (map_centralizer_subtype (C c i) (pResidual 2 (C c i))).symm
    rw [he,card_map_of_injective (C c i).subtype_injective,
      source_residual_centralizer_card c i z h R hR,
      sourceResidualCentralizer_card c i z h R hR]

theorem source_residualCentralizer_involution_fusion (R : Sylow 2 (C c i)) (hR : Tf c i ≤ R)
    (x : G) (hx : x∈sourceResidualCentralizer c i) (hx2 : orderOf x=2) :
    IsConj (Source.graphElement c i) x := by
  rcases source_two_involution_classes c i z h x hx2 with hz | hf
  · have hK : (pResidual 2 (C c i)).map (C c i).subtype ≤ centralizer ({x} : Set G) := by
      rw [sourceResidualCentralizer_eq_point c i z h R hR] at hx
      intro a ha
      exact mem_centralizer_singleton_iff.mpr (hx.2 a ha)
    have hcardK : Nat.card ((pResidual 2 (C c i)).map (C c i).subtype)=360 := by
      rw [card_map_of_injective (C c i).subtype_injective]
      obtain ⟨e⟩ := source_centralizer_residual_alternating c i z h R hR
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
      decide
    have hcardM : Nat.card (M c i false)=1152 := by
      change Nat.card (endpointMap c i false).range=1152
      rw [←Nat.card_congr (MonoidHom.ofInjective
        (endpointMap_injective c i h.embedding_injective false)).toEquiv]
      exact Extension.binary_point_card
    obtain ⟨g,hg⟩ := isConj_iff.mp hz
    have hcardC := Nat.card_congr
      (CentralizerSmallKernelTransport.centralizerEquiv (MulAut.conj g) (rootElement c i z)).toEquiv
    change Nat.card (centralizer ({rootElement c i z} : Set G)) =
      Nat.card (centralizer ({g*rootElement c i z*g⁻¹} : Set G)) at hcardC
    rw [hg,source_root_centralizer c i z h,hcardM] at hcardC
    have hd := card_dvd_of_le hK
    rw [hcardK,←hcardC] at hd
    norm_num at hd
  · exact hf

variable [IsElementaryAbelian 2 (sourceResidualCentralizer c i)]

theorem source_residualCentralizer_nonidentity_fusion (R : Sylow 2 (C c i)) (hR : Tf c i ≤ R)
    (x : G) (hx : x∈sourceResidualCentralizer c i) (hx1 : x≠1) :
    IsConj (Source.graphElement c i) x := by
  apply source_residualCentralizer_involution_fusion c i z h R hR x hx
  apply orderOf_eq_prime ?_ hx1
  exact congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 (sourceResidualCentralizer c i)) ⟨x,hx⟩)

theorem source_residualCentralizer_conjugator_mem_normalizer
    (R : Sylow 2 (C c i)) (hR : Tf c i ≤ R)
    (g x : G) (hx : x∈sourceResidualCentralizer c i) (hx1 : x≠1)
    (hgx : g*x*g⁻¹∈sourceResidualCentralizer c i) :
    g∈normalizer (sourceResidualCentralizer c i : Set G) := by
  have he := sourceResidualCentralizer_eq_point c i z h R hR
  let : IsMulCommutative (pointResidualCentralizer 2 (Source.graphElement c i)) :=
    he ▸ (inferInstance : IsMulCommutative (sourceResidualCentralizer c i))
  rw [he] at hx hgx ⊢
  apply pointResidualCentralizer_conjugator_mem_normalizer 2 (Source.graphElement c i)
    (fun x hx hx1 => source_residualCentralizer_nonidentity_fusion c i z h R hR x (he.symm ▸ hx) hx1)
    g x hx hx1 hgx

theorem source_residualCentralizer_isTI (R : Sylow 2 (C c i)) (hR : Tf c i ≤ R) :
    IsTISubgroup (sourceResidualCentralizer c i) := by
  apply (isTISubgroup_iff _).mpr
  intro g hg x hx hcx
  by_contra hx1
  exact hg (source_residualCentralizer_conjugator_mem_normalizer c i z h R hR g x hx hx1 hcx)

theorem source_residualCentralizer_normalizer_transitive
    (R : Sylow 2 (C c i)) (hR : Tf c i ≤ R)
    (x y : G) (hx : x∈sourceResidualCentralizer c i) (hx1 : x≠1)
    (hy : y∈sourceResidualCentralizer c i) (hy1 : y≠1) :
    ∃g∈normalizer (sourceResidualCentralizer c i : Set G),g*x*g⁻¹=y := by
  have hc := (source_residualCentralizer_nonidentity_fusion c i z h R hR x hx hx1).symm.trans
    (source_residualCentralizer_nonidentity_fusion c i z h R hR y hy hy1)
  obtain ⟨g,hg⟩ := isConj_iff.mp hc
  exact ⟨g,source_residualCentralizer_conjugator_mem_normalizer c i z h R hR g x hx hx1
    (hg.symm ▸ hy),hg⟩

theorem source_residualCentralizer_cubic_action
    (R : Sylow 2 (C c i)) (hR : Tf c i ≤ R)
    :
    ∃g:normalizer (sourceResidualCentralizer c i : Set G),
      orderOf ((sourceResidualCentralizer c i).normalizerMonoidHom g)=3 ∧
      3 ∣ orderOf (g:G) := by
  classical
  have hcard := sourceResidualCentralizer_card c i z h R hR
  let V := sourceResidualCentralizer c i
  let N := normalizer (V : Set G)
  let a := V.normalizerMonoidHom
  let J := a.range
  let x : V := ⟨Source.graphElement c i,source_graph_mem_residual_centralizer c i⟩
  have hx : x≠1 := by
    intro he
    have hG : Source.graphElement c i=1 := congrArg Subtype.val he
    have ho := source_graph_order c i h.embedding_injective
    rw [hG,orderOf_one] at ho
    omega
  have horbit : MulAction.orbit J x = ({1} : Set V)ᶜ := by
    ext y
    constructor
    · intro hy
      obtain ⟨u,rfl⟩ := MulAction.mem_orbit_iff.mp hy
      change (u : MulAut V) x≠1
      exact fun he => hx ((u : MulAut V).injective (he.trans (map_one _).symm))
    · intro hy
      have hxG : (x:G)≠1 := fun he => hx (Subtype.ext he)
      have hyG : (y:G)≠1 := fun he => hy (Subtype.ext he)
      obtain ⟨g,hg,he⟩ := source_residualCentralizer_normalizer_transitive c i z h R hR
        x y x.property hxG y.property hyG
      exact MulAction.mem_orbit_iff.mpr
        ⟨⟨a ⟨g,hg⟩,⟨⟨g,hg⟩,rfl⟩⟩,Subtype.ext he⟩
  have hc : Nat.card (MulAction.orbit J x)=3 := by
    change (MulAction.orbit J x).ncard=3
    rw [horbit,Set.ncard_compl,hcard,Set.ncard_singleton]
  have hdiv : 3∣Nat.card J := by
    have hh := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup J x)
    rw [Nat.card_prod,hc] at hh
    exact hh ▸ dvd_mul_right 3 _
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G:=J) 3 hdiv
  obtain ⟨g,hg⟩ := u.property
  have ho : orderOf (a g)=3 := by
    rw [hg]
    exact (orderOf_coe u).trans hu
  refine ⟨g,ho,?_⟩
  have hd := orderOf_map_dvd a g
  rw [ho] at hd
  exact (orderOf_coe g) ▸ hd

theorem source_residualCentralizer_cubic_moves_all
    (R : Sylow 2 (C c i)) (hR : Tf c i ≤ R)
    :
    ∃g:normalizer (sourceResidualCentralizer c i : Set G),
      orderOf ((sourceResidualCentralizer c i).normalizerMonoidHom g)=3 ∧
      ∀x∈sourceResidualCentralizer c i,x≠1 → (g:G)*x*(g:G)⁻¹≠x := by
  have hcard := sourceResidualCentralizer_card c i z h R hR
  obtain ⟨g,hg,_⟩ := source_residualCentralizer_cubic_action c i z h R hR
  refine ⟨g,hg,?_⟩
  intro x hx hx1 hc
  let V := sourceResidualCentralizer c i
  let a := V.normalizerMonoidHom g
  let v : V := ⟨x,hx⟩
  have hv : v≠1 := fun he => hx1 (congrArg Subtype.val he)
  have ha : a∈MulAction.stabilizer (MulAut V) v := Subtype.ext hc
  have hle : zpowers a ≤ MulAction.stabilizer (MulAut V) v := zpowers_le.mpr ha
  have hh := card_mulAut_subgroup_le_two_of_fixed_point hcard v hv (zpowers a)
    (fun b hb => hle hb)
  rw [Nat.card_zpowers,hg] at hh
  omega

omit [IsElementaryAbelian 2 (sourceResidualCentralizer c i)] in
/-- The literal R₀ consumer of the elementary branch. -/
theorem source_Rzero_elementary_TI_and_cubic
    (R : Sylow 2 (C c i)) (hR : Tf c i ≤ R)
    (hEA : IsElementaryAbelian 2 (Rzero c i R)) :
    IsTISubgroup (Rzero c i R) ∧
      ∃g:normalizer (Rzero c i R : Set G),
        orderOf ((Rzero c i R).normalizerMonoidHom g)=3 ∧
        ∀x∈Rzero c i R,x≠1 → (g:G)*x*(g:G)⁻¹≠x := by
  rw [source_Rzero_eq_residual_centralizer c i z h R hR] at hEA ⊢
  let := hEA
  exact ⟨source_residualCentralizer_isTI c i z h R hR,
    source_residualCentralizer_cubic_moves_all c i z h R hR⟩

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
