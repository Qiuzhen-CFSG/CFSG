module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallRadius
public import Theory.GroupTheory.ClassTwoIndexTwoDerived

/-!
# Common-core transfer for the original cubic selected span

Let P be the selected orbit span at the original component vertex. Its
central quotient has order greater than four: the action kernel lies in
E, so the action image has the symmetric-six quotient and cannot act on at
most four points. This argument retains the odd kernel E/Q. Radius
centrality and the proved derived order two now imply that every subgroup
of index at most two in P has the same derived line.

The full midpoint-radius bound places I = P ∩ Q_c at index at most two
in that same P. Thus I' = P'. For the opposite core C = [Q_c,L̃_c], the
two estimates |C'| ≤ 2 and [I,C] ≤ C' would force a contradiction. Indeed,
I ∨ C is normal at c and its derived subgroup has order at most four and
is centralized by Q_c. The original normal-subgroup dichotomy makes L̃_c
centralize that subgroup. Together with the original edge action this
centralizes P' at c, contrary to its critical seed commutator.

The actual whole-core and C.1.32 applications supply the selected span,
its radius line and common-core transfer, leaving the opposite-core order
and commutator estimates explicit as an obstruction. They retain both
moving covers and the plane and Sylow alternatives. Their discharge,
the other radical branches and both final reconstructions remain required.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.10)(i)--(ii), printed pp.879--881, and the final paragraph of
(5.12), printed p.927; Aschbacher--Smith C.1.31--32, pp.135--136.
The normal-envelope argument adapts the checked natural selected-span
proof to the original cubic graph and its literal edge embeddings.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk
include h e hz hk in
/-- An action detecting the component cannot have at most four points. -/
theorem cubic_action_card_gt_four {X : Type*} [Group X] [Finite X]
    (ρ : M →* MulAut X) (hker : ρ.ker ≤ extensionKernel h) : 4 < Nat.card X := by
  have hle : (π).ker.index ≤ ρ.ker.index := index_antitone (by
    rw [CubicAction.projection_kernel]
    exact hker)
  rw [index_ker,index_ker,MonoidHom.range_eq_top.mpr
    (CubicEven.projection_surjective h e hz hk),Nat.card_congr (topEquiv : (⊤ : Subgroup S) ≃* S).toEquiv,
    Nat.card_perm,Nat.card_fin] at hle
  have hr : Nat.card ρ.range ≤ Nat.card (Equiv.Perm X) :=
    Nat.card_le_card_of_injective (fun a : ρ.range => a.val.toEquiv)
      (fun a b hab => Subtype.ext (MulEquiv.toEquiv_injective hab))
  rw [Nat.card_perm] at hr
  by_contra hn
  have hf := Nat.factorial_le (Nat.le_of_not_gt hn)
  change 720 ≤ Nat.card ρ.range at hle
  change (Nat.card X).factorial ≤ 24 at hf
  omega

include h e hz hk in
/-- Nonabelianness forces the original selected span's central index above four,
without asserting that the odd extension kernel acts trivially. -/
theorem selected_span_center_index_gt_four
    (hb : 2 < sourceDistance h) {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hnon : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥) :
    4 < (center (localZSpan Rg (p.walk.getVert 2) (alpha Rg))).index := by
  have hd : (cosetGraph Rg).dist (p.walk.getVert 2) (alpha Rg) ≤ 2 := by
    rw [SimpleGraph.dist_comm,p.dist_start (by
      have hl : p.walk.length = sourceDistance h := p.length_eq_b
      omega)]
  have hPG : localZSpan Rg (p.walk.getVert 2) (alpha Rg) ≤ stabilizer Rg (alpha Rg) :=
    (localZSpan_le_V Rg hd).trans ((sourceGeometry h).V_local _ rfl hb)
  let := finite_stabilizer Rg (alpha Rg)
  let : Finite (localZSpan Rg (p.walk.getVert 2) (alpha Rg)) :=
    Finite.of_injective (inclusion hPG) (inclusion_injective _)
  rw [index_eq_card]
  exact cubic_action_card_gt_four h e hz hk (forwardSpanCentralAction Rg (p.walk.getVert 2))
    (selected_span_central_action_kernel_le_extension h e hz hk hb p hnon)

include h e hz hk in
/-- Every subgroup of index at most two retains the selected central derived line. -/
theorem selected_span_derived_transfer
    (hb : 2 < sourceDistance h) {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hcard : Nat.card (⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ : Subgroup (FreeAmalgam Rg)) = 2)
    (A : Subgroup (FreeAmalgam Rg))
    (hA : A ≤ localZSpan Rg (p.walk.getVert 2) (alpha Rg))
    (hi : A.relIndex (localZSpan Rg (p.walk.getVert 2) (alpha Rg)) ≤ 2) :
    ⁅A,A⁆ = ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ := by
  let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
  have hd : (cosetGraph Rg).dist (p.walk.getVert 2) (alpha Rg) ≤ 2 := by
    rw [SimpleGraph.dist_comm,p.dist_start (by
      have hl : p.walk.length = sourceDistance h := p.length_eq_b
      omega)]
  have hPV : P ≤ V Rg (alpha Rg) := localZSpan_le_V Rg hd
  have hPG : P ≤ stabilizer Rg (alpha Rg) :=
    hPV.trans ((sourceGeometry h).V_local _ rfl hb)
  let := finite_stabilizer Rg (alpha Rg)
  let : Finite P := Finite.of_injective (inclusion hPG) (inclusion_injective _)
  have hc : _root_.commutator P ≤ center P := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    have hx' : (x : FreeAmalgam Rg) ∈ ⁅P,P⁆ := by
      rw [←P.map_subtype_commutator]
      exact mem_map_of_mem P.subtype hx
    exact ((commutator_mono hPV (hPV.trans (V_le_Q Rg (geometry := sourceGeometry h) rfl hb))).trans
      (radius_commutator_central h e hz hk)) hx' y (hPV y.property)
  have hcard' : Nat.card (_root_.commutator P) = 2 := by
    rw [←P.map_subtype_commutator,card_map_of_injective P.subtype_injective] at hcard
    exact hcard
  have hnon : ⁅P,P⁆ ≠ ⊥ := by
    intro he
    change Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 at hcard
    rw [he,card_bot] at hcard
    omega
  have ht := ClassTwo.commutator_eq_of_index_le_two_of_center_index_gt_four hc hcard'
    (selected_span_center_index_gt_four h e hz hk hb p hnon) (A.subgroupOf P) hi
  have hm := congrArg (Subgroup.map P.subtype) ht
  rwa [map_commutator,map_subgroupOf_eq_of_le hA,P.map_subtype_commutator] at hm

include h e hz hk in
/-- The same critical span retains its derived line in the opposite two-core. -/
theorem point_selected_common_core_derived
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hcard : Nat.card (⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ : Subgroup (FreeAmalgam Rg)) = 2) :
    let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
    (Q Rg (p.walk.getVert 2)).relIndex P ≤ 2 ∧
      ⁅P ⊓ Q Rg (p.walk.getVert 2),P ⊓ Q Rg (p.walk.getVert 2)⁆ = ⁅P,P⁆ := by
  have hb := point_image_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hb2 : 2 < sourceDistance h := by omega
  have hc : color Rg (p.walk.getVert 2) = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero] using
      (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 0) (by omega))
  have hct : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
  have hPV : P ≤ V Rg (alpha Rg) := localZSpan_le_V Rg (by
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)])
  let := finite_stabilizer Rg (alpha Rg)
  let : Finite (V Rg (alpha Rg)) := Finite.of_injective
    (inclusion ((sourceGeometry h).V_local _ rfl hb2)) (inclusion_injective _)
  have hi : (Q Rg (p.walk.getVert 2)).relIndex P ≤ 2 :=
    (relIndex_le_of_le_right hPV index_ne_zero_of_finite).trans
      (point_radius_index_le_two h e hz hk u hR rfl hc hat hct)
  refine ⟨hi,selected_span_derived_transfer h e hz hk hb2 p hcard _ inf_le_left ?_⟩
  rwa [inf_relIndex_left]

include h e hz hk in
private theorem small_normal_subgroup_fixed
    (A : Subgroup M) [A.Normal] (hcard : Nat.card A ≤ 4)
    (hQ : pCore 2 M ≤ centralizer (A : Set M)) :
    A ≤ centralizer (L.subgroupOf M : Set M) := by
  let ρ : M →* MulAut A := MulAut.conjNormal
  have hker : pCore 2 M ≤ ρ.ker := by
    intro m hm
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change m*(x : M)*m⁻¹=(x : M)
    rw [(hQ hm x x.property).symm,mul_inv_cancel_right]
  rcases normal_over_core_dichotomy h e ρ.ker hker with hsmall | hcomp
  · have hh := cubic_action_card_gt_four h e hz hk ρ hsmall
    omega
  · intro x hx m hm
    have he := congrArg (fun f : MulAut A => (f ⟨x,hx⟩ : M))
      (MonoidHom.mem_ker.mp (hcomp hm))
    change m*x*m⁻¹=x at he
    exact mul_inv_eq_iff_eq_mul.mp he

private theorem small_subgroup_fixed {F : Type*} [Group F] [Finite F]
    (A B : Subgroup F) (hn : A ≤ normalizer (B : Set F)) (hc : Nat.card B ≤ 2) :
    A ≤ centralizer (B : Set F) := by
  have hp := Nat.card_pos (α := B)
  have hh : Nat.card B = 1 ∨ Nat.card B = 2 := by omega
  rcases hh with hh | hh
  · rw [card_eq_one.mp hh]
    intro a _ b hb
    have hb1 : b = 1 := mem_bot.mp hb
    simp only [hb1,mul_one,one_mul]
  · exact hn.trans (normalizer_le_centralizer_of_card_two B hh)

include h e hz hk in
private theorem core_derived_fixed_of_two_lines
    (D : Subgroup M) (hDQ : D≤pCore 2 M)
    (hDN : Rg≤normalizer (D:Set M))
    (hDcard : Nat.card (⁅D,D⁆:Subgroup M)≤2)
    (hCcard : Nat.card (⁅⁅pCore 2 M,L.subgroupOf M⁆,⁅pCore 2 M,L.subgroupOf M⁆⁆:Subgroup M)≤2)
    (hcomm : ⁅D,⁅pCore 2 M,L.subgroupOf M⁆⁆≤⁅⁅pCore 2 M,L.subgroupOf M⁆,⁅pCore 2 M,L.subgroupOf M⁆⁆) :
    ⁅D,D⁆≤centralizer ((L.subgroupOf M):Set M) := by
  let := h.relative_normal
  let C := ⁅pCore 2 M,L.subgroupOf M⁆
  have hDn : Rg ≤ normalizer ((⁅D,D⁆ : Subgroup M) : Set M) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hDN hg)]
  have hDC : ⁅D,D⁆ ≤ centralizer (Rg : Set M) :=
    le_centralizer_iff.mp (small_subgroup_fixed _ _ hDn hDcard)
  have hCC : ⁅C,C⁆ ≤ centralizer (Rg : Set M) :=
    le_centralizer_iff.mp (small_subgroup_fixed _ _ le_normalizer_of_normal hCcard)
  let N := D⊔C
  let H := ⁅D,D⁆⊔⁅C,C⁆
  have hCQ : C≤pCore 2 M := commutator_le_left _ _
  have hDR : D≤Rg := hDQ.trans (h.relative_radical.twoCore_le)
  have hCR : C≤Rg := hCQ.trans (h.relative_radical.twoCore_le)
  have hHR : H≤centralizer (Rg:Set M) := sup_le hDC hCC
  have hHN : Rg≤normalizer (H:Set M) :=
    (le_centralizer_iff.mp hHR).trans (Subgroup.centralizer_le_normalizer _)
  have hNC : ⁅N,N⁆≤H := by
    apply commutator_sup_le_of_relative_normal Rg D C N H hHN hDR hCR
    · rw [commutator_comm]
      apply commutator_sup_le_of_relative_normal Rg D C D H hHN hDR hCR le_sup_left
      exact (by rw [commutator_comm]; exact hcomm.trans le_sup_right)
    · rw [commutator_comm]
      exact commutator_sup_le_of_relative_normal Rg D C C H hHN hDR hCR
        (hcomm.trans le_sup_right) le_sup_right
  have hNnorm : (⊤:Subgroup M)≤normalizer (N:Set M) := by
    rw [←(codisjoint_subgroupOf_sup L R).eq_top]
    apply sup_le
    · apply le_normalizer_iff_commutator_le_right.mpr
      rw [commutator_comm]
      exact (commutator_mono (sup_le hDQ hCQ) le_rfl).trans le_sup_right
    · apply le_trans (le_inf hDN (le_normalizer_of_normal (H:=C)))
        (normalizer_inf_normalizer_le_normalizer_sup D C)
  let : N.Normal := ⟨by
    intro n hn g
    exact (le_normalizer_iff.mp hNnorm g (mem_top _)) n hn⟩
  have hcardH : Nat.card H≤4 := by
    have hprod : ((⁅D,D⁆:Subgroup M):Set M)*((⁅C,C⁆:Subgroup M):Set M)=(H:Set M) :=
      (coe_mul_of_right_le_normalizer_left _ _
        (((commutator_le_left C C).trans hCR).trans
          ((le_centralizer_iff.mp hDC).trans (Subgroup.centralizer_le_normalizer _)))).symm
    let f : (⁅D,D⁆:Subgroup M)×(⁅C,C⁆:Subgroup M)→H :=
      fun x => ⟨x.1*x.2,H.mul_mem (mem_sup_left x.1.property) (mem_sup_right x.2.property)⟩
    have hf : Function.Surjective f := by
      rintro ⟨x,hx⟩
      have hx' : x∈((⁅D,D⁆:Subgroup M):Set M)*((⁅C,C⁆:Subgroup M):Set M) := hprod.symm ▸ hx
      obtain ⟨a,ha,b,hb,rfl⟩ := hx'
      exact ⟨(⟨a,ha⟩,⟨b,hb⟩),rfl⟩
    have hh := Nat.card_le_card_of_surjective f hf
    rw [Nat.card_prod] at hh
    exact hh.trans (Nat.mul_le_mul hDcard hCcard)
  have hh : ⁅N,N⁆ ≤ centralizer (L.subgroupOf M : Set M) :=
    small_normal_subgroup_fixed h e hz hk ⁅N,N⁆
      ((card_le_of_le hNC).trans hcardH)
      (le_centralizer_iff.mp ((hNC.trans hHR).trans
        (centralizer_le h.relative_radical.twoCore_le)))
  exact (commutator_mono le_sup_left le_sup_left).trans hh

include h in
private theorem opposite_edge_coordinates {c t : Vertex Rg}
    (hc : color Rg c=false) (hct : Adjacent Rg c t) :
    ∃ i : M→*FreeAmalgam Rg, Function.Injective i ∧
      (Rg).map i=Q Rg t ∧ (pCore 2 M).map i=Q Rg c ∧ (L.subgroupOf M).map i=Ltilde Rg c := by
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common Rg c t).mp hct
  · rcases hg with ⟨rfl,rfl⟩
    let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM Rg)
    refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective Rg),?_,?_,?_⟩
    · have he := Q_act Rg g (beta Rg)
      rw [Q_beta] at he
      simpa only [beta,act_hVertex,one_mul,map_map] using he.symm
    · have he := Q_act Rg g (alpha Rg)
      rw [Q_alpha Rg (h.relative_radical.isPGroup) (h.relative_radical.twoCore_le)] at he
      simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
    · have he := Ltilde_act Rg g (alpha Rg)
      rw [Ltilde_alpha,h.relative_residual] at he
      simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
  · rw [hg.1] at hc
    cases hc

include h e hz hk in
private theorem opposite_core_derived_fixed
    {c t : Vertex Rg} (hc : color Rg c=false) (hct : Adjacent Rg c t)
    (D : Subgroup (FreeAmalgam Rg)) (hDQ : D≤Q Rg c)
    (hDN : Q Rg t≤normalizer (D:Set (FreeAmalgam Rg)))
    (hDcard : Nat.card (⁅D,D⁆:Subgroup (FreeAmalgam Rg))≤2)
    (hCcard : Nat.card (⁅⁅Q Rg c,Ltilde Rg c⁆,⁅Q Rg c,Ltilde Rg c⁆⁆:Subgroup (FreeAmalgam Rg))≤2)
    (hcomm : ⁅D,⁅Q Rg c,Ltilde Rg c⁆⁆≤⁅⁅Q Rg c,Ltilde Rg c⁆,⁅Q Rg c,Ltilde Rg c⁆⁆) :
    ⁅D,D⁆≤centralizer (Ltilde Rg c:Set (FreeAmalgam Rg)) := by
  obtain ⟨i,hi,hiR,hiQ,hiL⟩ := opposite_edge_coordinates (h := h) hc hct
  let D₀ := D.comap i
  let C₀ := ⁅pCore 2 M,L.subgroupOf M⁆
  have hDm : D₀.map i=D := map_comap_eq_self (hDQ.trans (hiQ ▸ map_le_range i _))
  have hCm : C₀.map i=⁅Q Rg c,Ltilde Rg c⁆ := by rw [map_commutator,hiQ,hiL]
  have hDDm : (⁅D₀,D₀⁆:Subgroup M).map i=⁅D,D⁆ := by rw [map_commutator,hDm]
  have hCCm : (⁅C₀,C₀⁆:Subgroup M).map i=⁅⁅Q Rg c,Ltilde Rg c⁆,⁅Q Rg c,Ltilde Rg c⁆⁆ := by
    rw [map_commutator,hCm]
  have hD₀Q : D₀≤pCore 2 M := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hDm,hiQ]
  have hD₀N : Rg≤normalizer (D₀:Set M) :=
    ((map_le_iff_le_comap).mp (hiR ▸ hDN)).trans (le_normalizer_comap i)
  have hD₀card : Nat.card (⁅D₀,D₀⁆:Subgroup M)≤2 := by
    rwa [←hDDm,card_map_of_injective hi] at hDcard
  have hC₀card : Nat.card (⁅C₀,C₀⁆:Subgroup M)≤2 := by
    rwa [←hCCm,card_map_of_injective hi] at hCcard
  have hcomm₀ : ⁅D₀,C₀⁆≤⁅C₀,C₀⁆ := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [map_commutator,hDm,hCm,hCCm]
  have hh := core_derived_fixed_of_two_lines h e hz hk D₀ hD₀Q hD₀N
    hD₀card hC₀card hcomm₀
  have hm := (map_mono (f:=i) hh).trans (map_centralizer_le_centralizer_image _ _)
  change (⁅D₀,D₀⁆:Subgroup M).map i≤centralizer ((L.subgroupOf M).map i:Set (FreeAmalgam Rg)) at hm
  rwa [hDDm,hiL] at hm


include h e hz hk in
/-- The opposite-core bounds contradict the retained critical line on the same
cubic graph. Index-two transfer is proved for the literal selected span. -/
theorem point_selected_terminal_false_of_opposite_core_bounds
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hcard : Nat.card (⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ :
        Subgroup (FreeAmalgam Rg)) = 2)
    (hCcard : Nat.card (⁅⁅Q Rg (p.walk.getVert 2),Ltilde Rg (p.walk.getVert 2)⁆,
      ⁅Q Rg (p.walk.getVert 2),Ltilde Rg (p.walk.getVert 2)⁆⁆ :
        Subgroup (FreeAmalgam Rg)) ≤ 2)
    (hcross : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg) ⊓
      Q Rg (p.walk.getVert 2),
      ⁅Q Rg (p.walk.getVert 2),Ltilde Rg (p.walk.getVert 2)⁆⁆ ≤
      ⁅⁅Q Rg (p.walk.getVert 2),Ltilde Rg (p.walk.getVert 2)⁆,
        ⁅Q Rg (p.walk.getVert 2),Ltilde Rg (p.walk.getVert 2)⁆⁆) : False := by
  have hb4 := point_image_distance_eq_four h e hz hk u hR
  have hb : 2 < sourceDistance h := by omega
  have htransfer := (point_selected_common_core_derived h e hz hk u hR p hcard).2
  have hnonabelian : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥ := by
    intro hz
    rw [hz,card_bot] at hcard
    omega
  obtain ⟨_,x,hx,q,_,_,_⟩ := selected_span_conjugate_critical_path h hb p hnonabelian
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let P := localZSpan Rg c (alpha Rg)
  let D := P ⊓ Q Rg c
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcolor : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent Rg (alpha Rg) t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t := adjacent_symm Rg
    ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hQa : Q Rg t ≤ stabilizer Rg (alpha Rg) :=
    fun _ hz => hz.2 _ (adjacent_symm Rg hat)
  have hQc : Q Rg t ≤ stabilizer Rg c :=
    fun _ hz => hz.2 _ (adjacent_symm Rg hct)
  have hPN : stabilizer Rg (alpha Rg) ≤
      normalizer ((⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (localZSpan_normalized Rg c (alpha Rg) hg)]
  have hPC : ⁅P,P⁆ ≤ centralizer
      (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp (hPN.trans (normalizer_le_centralizer_of_card_two _ hcard))
  have hDN : Q Rg t ≤ normalizer (D : Set (FreeAmalgam Rg)) :=
    (le_inf (hQa.trans (localZSpan_normalized Rg c (alpha Rg)))
      (hQc.trans (Q_normalized Rg c))).trans inf_normalizer_le_normalizer_inf
  have hDcard : Nat.card (⁅D,D⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2 := by
    change Nat.card (⁅P ⊓ Q Rg c,P ⊓ Q Rg c⁆ :
      Subgroup (FreeAmalgam Rg)) ≤ 2
    rw [htransfer,hcard]
  have hfixed := opposite_core_derived_fixed h e hz hk hcolor hct D
    inf_le_right hDN hDcard hCcard hcross
  rw [htransfer] at hfixed
  have hcenter : ⁅P,P⁆ ≤ centralizer (stabilizer Rg c : Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mpr
    rw [←CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.local_residual_edge_generation Rg
      (by rw [h.relative_residual]; exact (codisjoint_subgroupOf_sup L R).eq_top) hcolor hct]
    exact sup_le (le_centralizer_iff.mp hfixed)
      (hQa.trans (le_centralizer_iff.mp hPC))
  have hcP : Z Rg c ≤ P := Z_le_localZSpan Rg _ _
  have hxP : Z Rg (act Rg x c) ≤ P := by
    rw [Z_act]
    exact (map_mono hcP).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (localZSpan_normalized Rg c (alpha Rg)
        ((stabilizer Rg (alpha Rg)).inv_mem hx)))
  exact critical_commutator_not_central h e hz hk q
    ((commutator_mono hcP hxP).trans hcenter)

include h e hz hk in
/-- The same nonabelian selected span forces failure of one of the two
opposite-core estimates required by the terminal source argument. -/
theorem point_selected_opposite_core_obstruction
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hcard : Nat.card (⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ : Subgroup (FreeAmalgam Rg)) = 2) :
    let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
    let C := ⁅Q Rg (p.walk.getVert 2),Ltilde Rg (p.walk.getVert 2)⁆
    2 < Nat.card (⁅C,C⁆ : Subgroup (FreeAmalgam Rg)) ∨
      ¬ ⁅P ⊓ Q Rg (p.walk.getVert 2),C⁆ ≤ ⁅C,C⁆ := by
  classical
  dsimp only
  by_cases hc : Nat.card (⁅⁅Q Rg (p.walk.getVert 2),Ltilde Rg (p.walk.getVert 2)⁆,
      ⁅Q Rg (p.walk.getVert 2),Ltilde Rg (p.walk.getVert 2)⁆⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2
  · exact Or.inr (fun hh => point_selected_terminal_false_of_opposite_core_bounds h e hz hk u hR p hcard hc hh)
  · exact Or.inl (Nat.lt_of_not_ge hc)

include h e hz hk in
/-- The actual selected span has the same derived line in its common-core
intersection. The two remaining opposite-core estimates cannot both hold. -/
theorem point_image_selected_common_core_obstruction
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom) :
    ∃ a', ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a',
      let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
      let I := P ⊓ Q Rg (p.walk.getVert 2)
      let C := ⁅Q Rg (p.walk.getVert 2),Ltilde Rg (p.walk.getVert 2)⁆
      Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
      ⁅P,P⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
      ⁅P,V Rg (alpha Rg)⁆ = ⁅P,P⁆ ∧
      (Q Rg (p.walk.getVert 2)).relIndex P ≤ 2 ∧
      ⁅I,I⁆ = ⁅P,P⁆ ∧
      (2 < Nat.card (⁅C,C⁆ : Subgroup (FreeAmalgam Rg)) ∨ ¬ ⁅I,C⁆ ≤ ⁅C,C⁆) := by
  obtain ⟨a',p,hcard,hcentral,hradius⟩ := point_image_selected_span_radius_line h e hz hk u hR
  have ht := point_selected_common_core_derived h e hz hk u hR p hcard
  exact ⟨a',p,hcard,hcentral,hradius,ht.1,ht.2,
    point_selected_opposite_core_obstruction h e hz hk u hR p hcard⟩

omit hk in
include h e hz in
/-- Whole-core application of the common-core transfer and opposite-core
obstruction, retaining the actual cubic projection and both moving covers. -/
theorem coreExhaustion_or_cubic_opposite_core_obstruction :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          (∀ (a a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) a a'),
            (Q Rg a).relIndex (V Rg (p.walk.getVert 2)) = 2 ∧
            (Q Rg a').relIndex (V Rg (p.walk.getVert 2)) = 2) ∧
          ∃ a', ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a',
            let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
            let I := P ⊓ Q Rg (p.walk.getVert 2)
            let C := ⁅Q Rg (p.walk.getVert 2),Ltilde Rg (p.walk.getVert 2)⁆
            Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
            ⁅P,P⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
            ⁅P,V Rg (alpha Rg)⁆ = ⁅P,P⁆ ∧
            (Q Rg (p.walk.getVert 2)).relIndex P ≤ 2 ∧
            ⁅I,I⁆ = ⁅P,P⁆ ∧
            (2 < Nat.card (⁅C,C⁆ : Subgroup (FreeAmalgam Rg)) ∨ ¬ ⁅I,C⁆ ≤ ⁅C,C⁆)) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom := by
  rcases coreExhaustion_or_cubic_radical_cases h e hz with
    hx | ⟨hk,hs,hb,hcovers,u,hpoint | hplane | hsylow⟩
  · exact Or.inl hx
  · refine Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl ?_⟩
    exact ⟨hpoint.2,hpoint.1,
      fun _ _ p => point_critical_midpoint_radius_indices h e hz hk u hpoint.2.le p,
      point_image_selected_common_core_obstruction h e hz hk u hpoint.2.le⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inl hplane)⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inr hsylow)⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application. The point-core branch retains the same
selected span and exposes the two remaining opposite-core estimates; the
plane and Sylow branches are unchanged. -/
theorem rankTwo_or_cubic_opposite_core_obstruction :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          (∀ (a a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) a a'),
            (Q Rg a).relIndex (V Rg (p.walk.getVert 2)) = 2 ∧
            (Q Rg a').relIndex (V Rg (p.walk.getVert 2)) = 2) ∧
          ∃ a', ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a',
            let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
            let I := P ⊓ Q Rg (p.walk.getVert 2)
            let C := ⁅Q Rg (p.walk.getVert 2),Ltilde Rg (p.walk.getVert 2)⁆
            Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
            ⁅P,P⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
            ⁅P,V Rg (alpha Rg)⁆ = ⁅P,P⁆ ∧
            (Q Rg (p.walk.getVert 2)).relIndex P ≤ 2 ∧
            ⁅I,I⁆ = ⁅P,P⁆ ∧
            (2 < Nat.card (⁅C,C⁆ : Subgroup (FreeAmalgam Rg)) ∨ ¬ ⁅I,C⁆ ≤ ⁅C,C⁆)) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom :=
  (coreExhaustion_or_cubic_opposite_core_obstruction h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
