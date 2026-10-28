module

public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerSylow
public import Theory.GroupTheory.TwoKernelCentralizerNonfusion
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionPlaneCommutator

/-!
# The literal graph-centralizer quotient and its Sylow centralizer

In C_G(f)/⟨f⟩ the transported root still has order two. Its centralizer
is exactly the image of the chosen Sylow R: a larger preimage would fuse
the root u with fu, which belongs to the other ambient involution class.

Source: Aschbacher--Smith F.5.5, printed p.301.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)

def graphInCentralizer : C c i := ⟨Source.graphElement c i,graph_mem_C c i⟩

theorem graphInCentralizer_mem_center : graphInCentralizer c i ∈ center (C c i) := by
  apply mem_center_iff.mpr
  intro x
  exact Subtype.ext (mem_centralizer_singleton_iff.mp x.property)

instance graphCentralKernel_normal : (zpowers (graphInCentralizer c i)).Normal where
  conj_mem x hx g := by
    have hc : x ∈ center (C c i) :=
      (zpowers_le.mpr (graphInCentralizer_mem_center c i)) hx
    rw [mem_center_iff.mp hc g,mul_inv_cancel_right]
    exact hx

abbrev graphCentralQuotient := C c i ⧸ zpowers (graphInCentralizer c i)

variable [Finite G] (z : pointParabolic 1 hn) (t : G) (hf : FusionFacts c i z t)

private theorem graph_kernel_cases (hs : Source.Hypotheses c i z)
    (x : C c i) (hx : x ∈ zpowers (graphInCentralizer c i)) :
    x=1 ∨ x=graphInCentralizer c i := by
  classical
  have ho : orderOf (graphInCentralizer c i)=2 :=
    (orderOf_coe (graphInCentralizer c i)).symm.trans
      (source_graph_order c i hs.embedding_injective)
  rw [mem_zpowers_iff_mem_range_orderOf,ho] at hx
  obtain ⟨n,hnn,rfl⟩ := Finset.mem_image.mp hx
  have hn2 : n<2 := Finset.mem_range.mp hnn
  interval_cases n <;> simp

/-- The quotient by the graph involution has its literal two-element kernel. -/
theorem graph_quotient_eq_one_iff (hs : Source.Hypotheses c i z) (x : C c i) :
    QuotientGroup.mk' (zpowers (graphInCentralizer c i)) x=1 ↔
      x=1 ∨ x=graphInCentralizer c i := by
  constructor
  · intro hx
    exact graph_kernel_cases c i z hs x ((QuotientGroup.eq_one_iff x).mp hx)
  · rintro (rfl|rfl)
    · exact map_one _
    · exact (QuotientGroup.eq_one_iff _).mpr (mem_zpowers _)

include hf in
/-- The quotient centralizer at F.5.5 is the literal image of R. -/
theorem exists_graph_quotient_sylow_centralizer_with_lift (hs : Source.Hypotheses c i z)
    (R : Sylow 2 (C c i))
    (hj : centralizer ({rootElement c i z,t} : Set G)=Tcentralizer c i t) :
    ∃ u : C c i, u ∈ (R : Subgroup (C c i)) ∧
      IsConj (rootElement c i z) u.val ∧
      IsConj (Source.graphElement c i) (Source.graphElement c i*u.val) ∧
      C c i ⊓ centralizer ({u.val} : Set G)=Rimage c i R ∧
      orderOf (QuotientGroup.mk' (zpowers (graphInCentralizer c i)) u)=2 ∧
      centralizer ({QuotientGroup.mk' (zpowers (graphInCentralizer c i)) u} :
        Set (graphCentralQuotient c i)) =
        (R : Subgroup (C c i)).map (QuotientGroup.mk' (zpowers (graphInCentralizer c i))) := by
  obtain ⟨v,hvR,hzv,hfv,hC⟩ := exists_graph_centralizer_root c i z t hf R hj
  let u : C c i := ⟨v,Rimage_le_C c i R hvR⟩
  let f := graphInCentralizer c i
  let q := QuotientGroup.mk' (zpowers f)
  have huR : u ∈ (R : Subgroup (C c i)) :=
    (mem_map_iff_mem (C c i).subtype_injective).mp hvR
  have huC : centralizer ({u} : Set (C c i)) = R := by
    ext x
    have hm : x.val ∈ Rimage c i R ↔ x ∈ (R : Subgroup (C c i)) :=
      mem_map_iff_mem (C c i).subtype_injective
    rw [←hm,←hC]
    change x ∈ centralizer ({u} : Set (C c i)) ↔
      x.val ∈ C c i ∧ x.val ∈ centralizer ({v} : Set G)
    simp only [mem_centralizer_singleton_iff]
    exact ⟨fun hh => ⟨x.property,congrArg Subtype.val hh⟩,
      fun hh => Subtype.ext hh.2⟩
  have hnot : ¬ IsConj u (f*u) := by
    intro hh
    have hG := (C c i).subtype.map_isConj hh
    exact Source.graph_not_conjugate_root c i z hs (hfv.trans (hG.symm.trans hzv.symm))
  have hqC := q.map_centralizer_eq_of_two_kernel_nonfusion (by
    exact QuotientGroup.mk'_surjective _) f u
    (fun x hx => graph_kernel_cases c i z hs x ((QuotientGroup.eq_one_iff x).mp hx)) hnot
  have hu2 : u^2=1 := by
    apply Subtype.ext
    obtain ⟨g,hg⟩ := isConj_iff.mp hzv
    have hz2 : rootElement c i z^2=1 := source_root_order c i z hs ▸ pow_orderOf_eq_one _
    change v^2=1
    rw [←hg]
    change (MulAut.conj g (rootElement c i z))^2=1
    rw [←map_pow,hz2,map_one]
  have hq1 : q u≠1 := by
    intro hh
    rcases graph_kernel_cases c i z hs u ((QuotientGroup.eq_one_iff u).mp hh) with hu | hu
    · have hv1 : v=1 := congrArg Subtype.val hu
      have hz1 : rootElement c i z=1 := isConj_one_left.mp (hv1 ▸ hzv)
      have ho := source_root_order c i z hs
      rw [hz1,orderOf_one] at ho
      omega
    · have hvf : v=Source.graphElement c i := congrArg Subtype.val hu
      exact Source.graph_not_conjugate_root c i z hs (hvf ▸ hzv).symm
  refine ⟨u,huR,hzv,hfv,hC,orderOf_eq_prime (by rw [←map_pow,hu2,map_one]) hq1,?_⟩
  rw [huC] at hqC
  exact hqC.symm

include hf in
/-- The quotient centralizer at F.5.5 is the literal image of R. -/
theorem exists_graph_quotient_sylow_centralizer (hs : Source.Hypotheses c i z)
    (R : Sylow 2 (C c i))
    (hj : centralizer ({rootElement c i z,t} : Set G)=Tcentralizer c i t) :
    ∃ u : C c i, u ∈ (R : Subgroup (C c i)) ∧
      IsConj (rootElement c i z) u.val ∧
      orderOf (QuotientGroup.mk' (zpowers (graphInCentralizer c i)) u)=2 ∧
      centralizer ({QuotientGroup.mk' (zpowers (graphInCentralizer c i)) u} :
        Set (graphCentralQuotient c i)) =
        (R : Subgroup (C c i)).map (QuotientGroup.mk' (zpowers (graphInCentralizer c i))) := by
  obtain ⟨u,hu,hzu,_,_,ho,hc⟩ :=
    exists_graph_quotient_sylow_centralizer_with_lift c i z t hf hs R hj
  exact ⟨u,hu,hzu,ho,hc⟩

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
