module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneFixedKernel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeKernelLine
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicRemainingRadicals
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward

/-!
# Backward critical shifts in the original cubic plane branch

The full trapped radius has at most line movement on the reverse critical
kernel whenever the endpoint seed moves the backward seed outside the
starting seed. The fixed-hyperplane calculation on both permitted covers
proves this bound. Its transport uses the original cubic quotient with
kernel E, including E/Q of order three, and the entire incident central
attachment. Only the representation theorem from the natural branch is
reused; no identification of the two graphs or their radicals is made.

For the same selected switch x and both entire critical paths, conjugating
the second kernel commutator transports both entries. The transported
backward seed lies in the first trapped radius, so its nonzero commutator
is exactly the first line. Both lines centralize the selected edge kernel.
The retained generation by that edge and its x-conjugate makes the first
line central in the starting stabilizer. The switch therefore fixes it,
contradicting the previously proved joint commutator order greater than two.
This uses the two selected-edge joins, not the first-edge join normalized
by x. No whole-core normalization is inferred from that earlier selector.

The final theorem removes the trapped-pair alternative and constructs a
backward critical walk with all overlaps, retaining the same switch,
neighbor transporter and both generation identities. The Borel branch,
terminal exclusions and both whole-core reconstructions remain required.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii), (5.6)--(5.7), printed pp.866--867,917--919;
Aschbacher--Smith C.1.31--32, printed pp.135--136. The cover transport and
radius comparison adapt Natural.Exhaustion.LargeDistance.SectionFive's
CubeKernelLine and CubeKernelOrbit to the original cubic action.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Representation.NormalElementaryQuotient
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W₀" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk
local instance : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.of_le (commutator_le_left _ _)

include h e hz hk in
/-- The fixed-hyperplane comparison in the literal moved subgroup and original
quotient action; both possible central covers are retained. -/
private theorem plane_cover_large_fixed_commutator (u : S)
    (hR : (Rg).map π ≤ D.map (MulAut.conj u).toMonoidHom)
    (A P : Subgroup M) (hA : A ≤ Rg) (hP : P ≤ Rg)
    (hne : ¬ A ≤ pCore 2 M)
    (hindex : (centralizer (A : Set M)).relIndex (W₀) ≤ 2)
    (hlarge : 2 < Nat.card (⁅W₀ ⊓ centralizer (A : Set M),P⁆ : Subgroup M)) :
    ⁅W₀,P⁆ ≤
      ⁅W₀ ⊓ centralizer (A : Set M),P⁆ ⊔ ⁅W₀,A⁆ := by
  let := h.relative_normal
  let U := W₀
  let F := U ⊓ centralizer (A : Set M)
  let K := ⁅F,P⁆
  have hKU : K ≤ U := (commutator_mono inf_le_left le_rfl).trans (commutator_le_left U P)
  let : IsElementaryAbelian 2 K := IsElementaryAbelian.of_le hKU
  have hker := CubicAction.moved_projection_kernel h e hz hk
  have hsmall : fixedCodim (coverAction h e hz hk) (A.map π) ≤ 1 := by
    rw [centralizer_index_eq_fixedCodim U π (CubicEven.projection_surjective h e hz hk) hker] at hindex
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hindex
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map π) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction h e hz hk) (naturalRepresentation (Fin 6))
      (coverMap h e hz hk)
      (coverMap_surjective h e hz hk)
      (coverMap_equivariant h e hz hk) (A.map π)).trans hsmall
  have hnA : A.map π ≠ ⊥ := by
    intro he
    exact hne (two_subgroup_le_core_of_le_extensionKernel h hz A
      (h.relative_radical.isPGroup.to_le hA)
      (CubicAction.projection_kernel h e hz hk ▸ (map_eq_bot_iff A).mp he))
  obtain ⟨t,ht,hs,he⟩ := PointCoreTranspositionFixed.small_image_eq_zpowers (A.map π) hnA hnat
  have hF : subgroupSpace U F = fixedSpace (coverAction h e hz hk) (A.map π) := by
    ext v
    change ((v.toMul : M) ∈ U ∧ (v.toMul : M) ∈ centralizer (A : Set M)) ↔ _
    simp only [v.toMul.property,true_and]
    exact (mem_fixedSpace_image U π (CubicEven.projection_surjective h e hz hk) hker A v).symm
  have hK : subgroupSpace U K = subspaceCommutator (coverAction h e hz hk)
      (fixedSpace (coverAction h e hz hk) (A.map π)) (P.map π) := by
    rw [subgroupSpace_commutator U π (CubicEven.projection_surjective h e hz hk) hker F P inf_le_left,hF]
  have hU : subgroupSpace U U = ⊤ := by ext v; exact iff_of_true v.toMul.property trivial
  have hdim : 1 < Module.finrank (ZMod 2) (subgroupSpace U K) := by
    have hcard : Nat.card K = 2 ^ Module.finrank (ZMod 2) (subgroupSpace U K) := by
      calc Nat.card K = Nat.card (Additive K) := rfl
           _ = Nat.card (subgroupSpace U K) := Nat.card_congr (subgroupSpaceEquiv U K hKU).toEquiv
           _ = _ := by rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    change 2 < Nat.card K at hlarge
    rw [hcard] at hlarge
    exact (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp hlarge
  rw [hK,he] at hdim
  have hc := Natural.Exhaustion.LargeDistance.SectionFive.CubeKernelLine.model_comparison (coverAction h e hz hk) (moved_subgroup_cover_model h e hz hk) u t
    (P.map π) (by simpa only [CFSG.Quasithin.ChapterB.Offenders.SixCorePlane.cube_eq] using ((map_mono hP).trans hR))
    (by simpa only [CFSG.Quasithin.ChapterB.Offenders.SixCorePlane.cube_eq] using (((map_mono hA).trans hR) ht)) hs hdim
  rw [←he,←hK] at hc
  have hwhole (B : Subgroup M) : subgroupSpace U ⁅U,B⁆ =
      subspaceCommutator (coverAction h e hz hk) ⊤ (B.map π) := by
    rw [subgroupSpace_commutator U π (CubicEven.projection_surjective h e hz hk) hker U B le_rfl,hU]
  rw [←hwhole P,←hwhole A,←subgroupSpace_sup U hKU (commutator_le_left U A)] at hc
  intro v hv
  exact hc (show Additive.ofMul (⟨v,(commutator_le_left U P) hv⟩ : U) ∈ subgroupSpace U ⁅U,P⁆ from hv)

include h e hz hk in
private theorem embedded_plane_large_fixed_commutator {H : Type*} [Group H]
    (u : S) (hR : (Rg).map π ≤ D.map (MulAut.conj u).toMonoidHom)
    (i : M →* H) (hi : Function.Injective i)
    (A P : Subgroup H) (hA : A ≤ (Rg).map i) (hP : P ≤ (Rg).map i)
    (hne : ¬ A ≤ (pCore 2 M).map i)
    (hindex : (centralizer (A : Set H)).relIndex ((W₀).map i) ≤ 2)
    (hlarge : 2 < Nat.card (⁅(W₀).map i ⊓ centralizer (A : Set H),P⁆ : Subgroup H)) :
    ⁅(W₀).map i,P⁆ ≤
      ⁅(W₀).map i ⊓ centralizer (A : Set H),P⁆ ⊔ ⁅(W₀).map i,A⁆ := by
  have hmA : (A.comap i).map i = A := map_comap_eq_self (hA.trans (map_le_range i _))
  have hmP : (P.comap i).map i = P := map_comap_eq_self (hP.trans (map_le_range i _))
  have hAr : A.comap i ≤ Rg := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hmA]
  have hPr : P.comap i ≤ Rg := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hmP]
  have hnA : ¬ A.comap i ≤ pCore 2 M := by
    intro hh
    exact hne (hmA ▸ map_mono hh)
  have hidx : (centralizer (A.comap i : Set M)).relIndex (W₀) ≤ 2 := by
    rw [←hmA,←inf_relIndex_right,inf_comm,
      map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,inf_relIndex_left] at hindex
    exact hindex
  have hcard : 2 < Nat.card (⁅W₀ ⊓ centralizer (A.comap i : Set M),P.comap i⁆ : Subgroup M) := by
    rw [←card_map_of_injective hi,map_commutator,←map_inf_centralizer_of_injective i hi,hmA,hmP]
    exact hlarge
  have hh := map_mono (f := i) (plane_cover_large_fixed_commutator h e hz hk u hR
    (A.comap i) (P.comap i) hAr hPr hnA hidx hcard)
  simp only [Subgroup.map_sup,map_commutator,
    ←map_inf_centralizer_of_injective i hi,hmA,hmP] at hh ⊢
  exact hh
private theorem commutator_sup_of_central_attachment {H : Type*} [Group H]
    (U Z P : Subgroup H) (hN : Z ≤ normalizer (U : Set H))
    (hC : Z ≤ centralizer (P : Set H)) : ⁅U ⊔ Z,P⁆ = ⁅U,P⁆ := by
  apply le_antisymm _ (commutator_mono le_sup_left le_rfl)
  apply commutator_le.mpr
  intro x hx r hr
  have hp : x ∈ (U : Set H) * (Z : Set H) := by
    rw [←coe_mul_of_right_le_normalizer_left U Z hN]
    exact hx
  obtain ⟨w,hw,z,hz,rfl⟩ := hp
  have hzero : ⁅z,r⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr (hC hz r hr).symm
  rw [commutatorElement_mul_left_eq_conj_mul,hzero,mul_one,mul_inv_cancel,one_mul]
  exact commutator_mem_commutator hw hr

include h e hz hk in
/-- The literal full seed, including its central edge attachment, satisfies
the hyperplane comparison for every actor in the incident edge kernel. -/
private theorem plane_edge_large_fixed_commutator (u : S)
    (hR : (Rg).map π ≤ D.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex Rg} (hcol : color Rg c = false)
    (hct : Adjacent Rg c t)
    (A P : Subgroup (FreeAmalgam Rg)) (hA : A ≤ Q Rg t) (hP : P ≤ Q Rg t)
    (hne : ¬ A ≤ Q Rg c)
    (hindex : (centralizer (A : Set (FreeAmalgam Rg))).relIndex (U Rg c) ≤ 2)
    (hlarge : 2 < Nat.card (⁅Z Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)),P⁆ :
      Subgroup (FreeAmalgam Rg))) :
    ⁅Z Rg c,P⁆ ≤
      ⁅Z Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)),P⁆ ⊔ ⁅Z Rg c,A⁆ := by
  obtain ⟨i,hi,_,hiR,hiQ,hiU⟩ := remaining_edge_coordinates h e hz hcol hct
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hct
    rw [hcol] at hh
    cases he : color Rg t <;> simp_all
  have hseed : Z Rg t ≤ centralizer (Q Rg t : Set (FreeAmalgam Rg)) := by
    intro x hx
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  have hseedA := hseed.trans (centralizer_le hA)
  have hseedP := hseed.trans (centralizer_le hP)
  have hseedN : Z Rg t ≤ normalizer (U Rg c : Set (FreeAmalgam Rg)) :=
    ((adjacent_Z_le Rg hcol hct).trans (Z_le_stabilizer Rg c)).trans (U_normalized c)
  let F := U Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg))
  have heq : Z Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)) = F ⊔ Z Rg t := by
    rw [vertex_seed_eq_moving_sup_edge h e hz hcol hct,
      sup_comm (U Rg c),inf_centralizer_sup_of_centralizing _ _ _ hseedN hseedA]
    exact sup_comm _ _
  have hNF : Z Rg t ≤ normalizer (F : Set (FreeAmalgam Rg)) :=
    (le_inf hseedN (hseedA.trans (centralizer (A : Set (FreeAmalgam Rg))).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hcomm : ⁅Z Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)),P⁆ = ⁅F,P⁆ := by
    rw [heq,commutator_sup_of_central_attachment F _ P hNF hseedP]
  have hwhole (X : Subgroup (FreeAmalgam Rg)) (hX : X ≤ Q Rg t) :
      ⁅Z Rg c,X⁆ = ⁅U Rg c,X⁆ := by
    rw [vertex_seed_eq_moving_sup_edge h e hz hcol hct,
      commutator_sup_of_central_attachment _ _ X hseedN (hseed.trans (centralizer_le hX))]
  rw [hcomm] at hlarge ⊢
  rw [hwhole P hP,hwhole A hA]
  rw [←hiR] at hA hP
  rw [←hiQ] at hne
  rw [←hiU] at hindex
  have hh := embedded_plane_large_fixed_commutator h e hz hk u hR i hi A P hA hP hne hindex
  rw [hiU] at hh
  exact hh hlarge

include h e hz hk in
/-- The entire trapped part of the radius has at most line movement on the
reverse critical kernel, if the endpoint commutator escapes the starting seed. -/
private theorem plane_trapped_radius_kernel_card_le_two
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a a' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (hsmall : (Q Rg a').relIndex (Z Rg a) < 4)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hnot : ¬ ⁅Z Rg c,Z Rg a'⁆ ≤ Z Rg a) :
    Nat.card (⁅V Rg a ⊓ Q Rg (p.walk.getVert (p.walk.length-1)),
      Z Rg a' ⊓ Q Rg a⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2 := by
  have hb := distance_gt_two h e hz hk
  by_contra hcard
  have hlarge := Nat.lt_of_not_ge hcard
  let F := Z Rg a' ⊓ Q Rg a
  let v := p.walk.getVert (p.walk.length-1)
  let W := V Rg a ⊓ Q Rg v
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hev : Adjacent Rg a' v := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have hv : color Rg v = true := by
    have hh := adjacent_color_ne Rg hev
    rw [p.end_color] at hh
    cases he : color Rg v <;> simp_all
  have hpre : Q Rg (p.walk.getVert (p.walk.length-2)) ≤ Q Rg v := by
    apply Q_le_adjacent_h Rg hv
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hAv : Z Rg a ≤ Q Rg v := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.start_color)
    rw [(sourceGeometry h).distance_constant _ p.start_color,p.dist_start (Nat.sub_le _ _)]
    have he : p.walk.length = sourceDistance h := p.length_eq_b
    change p.walk.length-1 < sourceDistance h
    omega
  have hfixed : F = Z Rg a' ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
    (critical_seed_centralizer_intersection h e
      (CriticalPath.ofPair p.end_color (reverse_pair h e p))).symm
  let := finite_Z Rg a'
  let : Finite (U Rg a') := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg a')) (inclusion_injective _)
  have hindex : (centralizer (Z Rg a : Set (FreeAmalgam Rg))).relIndex
      (U Rg a') ≤ 2 := by
    have hQC : Q Rg a ≤ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg a p.start_color))
    exact ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg a') index_ne_zero_of_finite)).trans_eq
        (small_critical_indices h e hz hk p hsmall).2
  have hdist : (cosetGraph Rg).dist c a ≤ 2 := by
    have h1 : (cosetGraph Rg).dist c t=1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hct)
    have h2 : (cosetGraph Rg).dist t a=1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat))
    simpa only [h1,h2] using (cosetGraph_connected Rg).dist_triangle (u := c) (v := t) (w := a)
  have hCW : Z Rg c ≤ W := le_inf
    ((Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg hdist)) (hbad.trans hpre)
  have hlarge' : 2 < Nat.card (⁅Z Rg a' ⊓
      centralizer (Z Rg a : Set (FreeAmalgam Rg)),W⁆ : Subgroup (FreeAmalgam Rg)) := by
    rw [←hfixed,commutator_comm]
    exact hlarge
  have hcmp := plane_edge_large_fixed_commutator h e hz hk u hR.le p.end_color hev
    (Z Rg a) W hAv inf_le_right p.critical.2 hindex hlarge'
  rw [←hfixed,commutator_comm F W] at hcmp
  have hH : ⁅W,F⁆ ≤ Z Rg a :=
    (commutator_mono inf_le_left inf_le_right).trans
      (plane_radius_core_commutator h e hz hk u hR p.start_color)
  have hcrit : ⁅Z Rg a',Z Rg a⁆ ≤ Z Rg a :=
    le_normalizer_iff_commutator_le_right.mp
      ((critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
        (by rw [(sourceGeometry h).distance_constant a p.start_color]
            exact sourceDistance_pos h) p.critical).trans (Z_normalized Rg a))
  have hmove : ⁅Z Rg a',Z Rg c⁆ ≤ Z Rg a :=
    (commutator_mono le_rfl hCW).trans (hcmp.trans (sup_le hH hcrit))
  exact hnot (by rwa [commutator_comm])



include h e hz hk in
/-- All trapped radius movement equals the selected nonzero line. This is
an equality for the literal intersection with the last edge kernel. -/
private theorem plane_trapped_radius_kernel_eq_selected
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a a' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (hsmall : (Q Rg a').relIndex (Z Rg a) < 4)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hnot : ¬ ⁅Z Rg c,Z Rg a'⁆ ≤ Z Rg a) :
    let H := ⁅Z Rg c,Z Rg a' ⊓ Q Rg a⁆
    Nat.card H = 2 ∧
      ⁅V Rg a ⊓ Q Rg (p.walk.getVert (p.walk.length-1)),
        Z Rg a' ⊓ Q Rg a⁆ = H := by
  have hb := distance_gt_two h e hz hk
  let F := Z Rg a' ⊓ Q Rg a
  let H := ⁅Z Rg c,F⁆
  let W := V Rg a ⊓ Q Rg (p.walk.getVert (p.walk.length-1))
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hdist : (cosetGraph Rg).dist c a ≤ 2 := by
    have h1 : (cosetGraph Rg).dist c t=1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hct)
    have h2 : (cosetGraph Rg).dist t a=1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat))
    simpa only [h1,h2] using (cosetGraph_connected Rg).dist_triangle (u := c) (v := t) (w := a)
  have hCV : Z Rg c ≤ V Rg a :=
    (Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg hdist)
  have hVG := (sourceGeometry h).V_local a p.start_color
    (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact hb)
  have hv : color Rg (p.walk.getVert (p.walk.length-1)) = true := by
    have hh := adjacent_color_ne Rg
      ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)))
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length,p.end_color] at hh
    cases he : color Rg (p.walk.getVert (p.walk.length-1)) <;> simp_all
  have hpre : Q Rg (p.walk.getVert (p.walk.length-2)) ≤
      Q Rg (p.walk.getVert (p.walk.length-1)) := by
    apply Q_le_adjacent_h Rg hv
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hCW : Z Rg c ≤ W := le_inf hCV (hbad.trans hpre)
  have hHle : H ≤ ⁅W,F⁆ := commutator_mono hCW le_rfl
  have hwhole : ⁅W,F⁆ ≤ Z Rg a :=
    (commutator_mono inf_le_left inf_le_right).trans
      (plane_radius_core_commutator h e hz hk u hR p.start_color)
  have hne : H ≠ ⊥ := by
    intro hzero
    have hmove := small_critical_predecessor_commutator h e hz hk hb p hsmall
      (Z Rg c) hbad (commutator_eq_bot_iff_le_centralizer.mp hzero)
    exact hnot hmove
  let := finite_Z Rg a
  let : Finite (⁅W,F⁆ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion hwhole) (inclusion_injective _)
  let : Finite H := Finite.of_injective (inclusion hHle) (inclusion_injective _)
  have hpos : 1 < Nat.card H := (one_lt_card_iff_ne_bot _).mpr hne
  have hbound := plane_trapped_radius_kernel_card_le_two h e hz hk u hR p hsmall hat hct hbad hnot
  have hcard : Nat.card H = 2 := by
    have hh := card_le_of_le hHle
    change Nat.card (⁅W,F⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2 at hbound
    omega
  refine ⟨hcard,(eq_of_le_of_card_ge hHle ?_).symm⟩
  rw [hcard]
  exact hbound

include h e hz hk in
/-- For the same conjugator relating the two entire paths, the other
trapped kernel commutator transports into the selected obstruction line. -/
private theorem plane_paired_kernel_conjugate_le_selected
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a a' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (hsmall : (Q Rg a').relIndex (Z Rg a) < 4)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (x : FreeAmalgam Rg) (hx : x ∈ stabilizer Rg a)
    (q : CriticalPath Rg (sourceGeometry h) a (act Rg x a'))
    (hq : ∀ i, q.walk.getVert i = act Rg x (p.walk.getVert i))
    (hpbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hqbad : Z Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2)))
    (hnot : ¬ ⁅Z Rg c,Z Rg a'⁆ ≤ Z Rg a) :
    (⁅Z Rg c,Z Rg (act Rg x a') ⊓ Q Rg a⁆).map
      (MulAut.conj x).toMonoidHom ≤ ⁅Z Rg c,Z Rg a' ⊓ Q Rg a⁆ := by
  have hb := distance_gt_two h e hz hk
  have hQ : (Q Rg a).map (MulAut.conj x).toMonoidHom = Q Rg a :=
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized Rg a hx)
  have hZ : (Z Rg (act Rg x a')).map (MulAut.conj x).toMonoidHom = Z Rg a' := by
    have he := Z_act Rg x⁻¹ (act Rg x a')
    simpa only [inv_inv,←act_mul,mul_inv_cancel,act_one] using he.symm
  rw [map_commutator,Subgroup.map_inf _ _ _ (MulAut.conj x).injective,hQ,hZ]
  have heq := (plane_trapped_radius_kernel_eq_selected h e hz hk u hR p hsmall hat hct hpbad hnot).2
  rw [←heq]
  apply commutator_mono _ le_rfl
  apply le_inf
  · have hdist : (cosetGraph Rg).dist c a ≤ 2 := by
      have h1 : (cosetGraph Rg).dist c t=1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hct)
      have h2 : (cosetGraph Rg).dist t a=1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat))
      simpa only [h1,h2] using (cosetGraph_connected Rg).dist_triangle (u := c) (v := t) (w := a)
    have hV := map_mono (f := (MulAut.conj x).toMonoidHom)
      ((Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg hdist))
    have heV : (V Rg a).map (MulAut.conj x).toMonoidHom = V Rg a :=
      mem_normalizer_iff_map_conj_eq.mp (DistanceEight.V_normalized Rg a hx)
    rwa [heV] at hV
  · have hlen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
    have hh := map_mono (f := (MulAut.conj x).toMonoidHom) hqbad
    rw [hlen,hq] at hh
    have he := Q_act Rg x⁻¹ (act Rg x (p.walk.getVert (p.walk.length-2)))
    simp only [inv_inv,←act_mul,mul_inv_cancel,act_one] at he
    rw [←he] at hh
    apply hh.trans
    have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
    have hv : color Rg (p.walk.getVert (p.walk.length-1)) = true := by
      have ha := adjacent_color_ne Rg
        ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)))
      rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length,p.end_color] at ha
      cases he : color Rg (p.walk.getVert (p.walk.length-1)) <;> simp_all
    apply Q_le_adjacent_h Rg hv
    have ha := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at ha
    exact (cosetGraph_adj Rg _ _).mp ha



include h e hz hk in
private theorem plane_paired_commutator_escape
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z z' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) z')
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (hgen : (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg (alpha Rg))
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c)) :
    ¬ ⁅Z Rg c,Z Rg z⁆ ≤ Z Rg (alpha Rg) ∨
      ¬ ⁅Z Rg c,Z Rg z'⁆ ≤ Z Rg (alpha Rg) := by
  by_contra! hboth
  obtain ⟨hcomm,hcomm'⟩ := hboth
  have hb := distance_gt_two h e hz hk
  have hd : (cosetGraph Rg).dist c (alpha Rg) ≤ 2 := by
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hct)
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat))
    have hh := (cosetGraph_connected Rg).dist_triangle (u := c) (v := t) (w := alpha Rg)
    omega
  have hZV : Z Rg c ≤ V Rg (alpha Rg) :=
    (Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg hd)
  let Y := Z Rg c ⊔ Z Rg (alpha Rg)
  have hmove {w : Vertex Rg}
      (r : CriticalPath Rg (sourceGeometry h) (alpha Rg) w)
      (hm : ⁅Z Rg c,Z Rg w⁆ ≤ Z Rg (alpha Rg)) :
      ⁅Y,Z Rg w⁆ ≤ Z Rg (alpha Rg) := by
    apply commutator_sup_le_of_relative_normal (stabilizer Rg (alpha Rg))
      (Z Rg c) (Z Rg (alpha Rg)) (Z Rg w) (Z Rg (alpha Rg))
      (Z_normalized Rg _) (hZV.trans ((sourceGeometry h).V_local _ rfl hb))
      (Z_le_stabilizer Rg _) hm
    exact le_normalizer_iff_commutator_le_left.mp
      ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
        (sourceDistance_pos h) r.critical).trans (Z_normalized Rg _))
  have hpY := hmove p hcomm
  have hqY := hmove q hcomm'
  have hYN : stabilizer Rg (alpha Rg) ≤ normalizer (Y : Set (FreeAmalgam Rg)) := by
    rw [←hgen,plane_edgeOffenderJoin_eq h e hz hk u hR rfl hat]
    refine sup_le (sup_le ?_ (le_normalizer_iff_commutator_le_left.mpr
      (hpY.trans le_sup_right))) (le_normalizer_iff_commutator_le_left.mpr
        (hqY.trans le_sup_right))
    exact (le_inf ((show Q Rg t ≤ stabilizer Rg c from
      fun _ hx => hx.2 _ (adjacent_symm Rg hct)).trans (Z_normalized Rg c))
      ((show Q Rg t ≤ stabilizer Rg (alpha Rg) from
        fun _ hx => hx.2 _ (adjacent_symm Rg hat)).trans (Z_normalized Rg _))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hUB : U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    (DistanceEight.U_le_Z Rg c).trans (le_sup_left.trans
      (normalized_radius_le_slice_of_critical_commutator h e hz hb p Y
        (sup_le hZV (Z_le_VBall Rg _ 2)) hYN hpY))
  have hi := relIndex_eq_one.mpr hUB
  omega

include h e hz hk in
private theorem plane_trapped_conjugate_contradiction
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z z' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) z')
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (x : FreeAmalgam Rg) (hx : x ∈ stabilizer Rg (alpha Rg))
    (hqverts : ∀ i, q.walk.getVert i = act Rg x (p.walk.getVert i))
    (hpair : Q Rg t ⊔ Q Rg (act Rg x t) = stabilizer Rg (alpha Rg))
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hbad' : Z Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2)))
    (hnot : ¬ ⁅Z Rg c,Z Rg z⁆ ≤ Z Rg (alpha Rg))
    (hX : ∀ a : Vertex Rg, color Rg a = false → X Rg a = Z Rg a)
    (hbig : 2 < Nat.card (⁅Z Rg c,Z Rg z ⊓ Q Rg (alpha Rg)⁆ ⊔
      ⁅Z Rg c,Z Rg z' ⊓ Q Rg (alpha Rg)⁆ : Subgroup (FreeAmalgam Rg))) : False := by
  have hz' : z' = act Rg x z := by
    have hh := hqverts p.walk.length
    have hlen : p.walk.length = q.walk.length := p.length_eq_b.trans q.length_eq_b.symm
    rw [p.walk.getVert_length,hlen,q.walk.getVert_length] at hh
    exact hh
  subst z'
  let H := ⁅Z Rg c,Z Rg z ⊓ Q Rg (alpha Rg)⁆
  let H' := ⁅Z Rg c,Z Rg (act Rg x z) ⊓ Q Rg (alpha Rg)⁆
  have hcard := (plane_trapped_radius_kernel_eq_selected h e hz hk u hR p hp hat hct hbad hnot).1
  change Nat.card H = 2 at hcard
  have hcmp := plane_paired_kernel_conjugate_le_selected h e hz hk u hR
    p hp hat hct x hx q hqverts hbad hbad' hnot
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hc : color Rg c = false := by
    have hh := adjacent_color_ne Rg hct
    rw [ht] at hh
    cases he : color Rg c <;> simp_all
  have hedge (w : Vertex Rg) (hw : color Rg w = false) :
      ⁅Z Rg c,Z Rg w ⊓ Q Rg (alpha Rg)⁆ ≤ Z Rg t ∧
      ⁅⁅Z Rg c,Z Rg w ⊓ Q Rg (alpha Rg)⁆,Q Rg t⁆ = ⊥ := by
    have he := plane_reverse_kernel_edge_control h e hz hk u hR rfl hc hat hct (z := w)
    rw [hX w hw,commutator_comm (Z Rg w ⊓ Q Rg (alpha Rg)) (Z Rg c)] at he
    exact ⟨he.1,he.2.2⟩
  have he := hedge z p.end_color
  have he' := hedge (act Rg x z) q.end_color
  let := finite_Z Rg t
  let : Finite H := Finite.of_injective (inclusion he.1) (inclusion_injective _)
  let : Finite H' := Finite.of_injective (inclusion he'.1) (inclusion_injective _)
  have hne : H' ≠ ⊥ := by
    intro hz
    change 2 < Nat.card (H ⊔ H' : Subgroup (FreeAmalgam Rg)) at hbig
    rw [hz,sup_bot_eq] at hbig
    omega
  have hpos : 1 < Nat.card H' := (one_lt_card_iff_ne_bot _).mpr hne
  have hcard' : Nat.card H' = 2 := by
    have hh := card_le_of_le hcmp
    rw [card_map_of_injective (MulAut.conj x).injective,hcard] at hh
    change Nat.card H' ≤ 2 at hh
    omega
  have heq : H'.map (MulAut.conj x).toMonoidHom = H := eq_of_le_of_card_ge hcmp (by
    rw [card_map_of_injective (MulAut.conj x).injective,hcard,hcard'])
  have hback : (Q Rg (act Rg x t)).map (MulAut.conj x).toMonoidHom = Q Rg t := by
    have hh := Q_act Rg x⁻¹ (act Rg x t)
    simpa only [inv_inv,←act_mul,mul_inv_cancel,act_one] using hh.symm
  have hG : (stabilizer Rg (alpha Rg)).map (MulAut.conj x).toMonoidHom =
      stabilizer Rg (alpha Rg) :=
    mem_normalizer_iff_map_conj_eq.mp ((stabilizer Rg (alpha Rg)).le_normalizer hx)
  have hgen := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hpair
  rw [Subgroup.map_sup,hback,hG] at hgen
  have hfix : ⁅H,(Q Rg t).map (MulAut.conj x).toMonoidHom⁆ = ⊥ := by
    rw [←heq,←map_commutator,show ⁅H',Q Rg t⁆ = ⊥ from he'.2,Subgroup.map_bot]
  have hcentral : H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mpr
    rw [←hgen]
    exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hfix))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he.2))
  have hxn : x ∈ normalizer (H : Set (FreeAmalgam Rg)) :=
    ((le_centralizer_iff.mp hcentral).trans (Subgroup.centralizer_le_normalizer _)) hx
  have hsame : H' = H := (Subgroup.map_injective (MulAut.conj x).injective)
    (heq.trans (mem_normalizer_iff_map_conj_eq.mp hxn).symm)
  change 2 < Nat.card (H ⊔ H' : Subgroup (FreeAmalgam Rg)) at hbig
  rw [hsame,sup_idem] at hbig
  omega

include h e hz hk in
/-- The two trapped candidates cannot occur for the same selected switch.
The full reverse-kernel lines transport with both their arguments; generation
by the two selected edges then makes the line central at the starting vertex,
contradicting the strict-slice joint movement. -/
theorem plane_paired_trapped_impossible
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z z' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) z')
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hq : (Q Rg z').relIndex (Z Rg (alpha Rg)) < 4)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (x : FreeAmalgam Rg) (hx : x ∈ stabilizer Rg (alpha Rg))
    (hqverts : ∀ i, q.walk.getVert i = act Rg x (p.walk.getVert i))
    (hgen : (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg (alpha Rg))
    (hpair : edgeOffenderJoin (alpha Rg) t ⊔ edgeOffenderJoin (alpha Rg) (act Rg x t) =
      stabilizer Rg (alpha Rg))
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hbad' : Z Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2)))
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c)) : False := by
  have hxa : act Rg x (alpha Rg) = alpha Rg := hx
  have hat' : Adjacent Rg (alpha Rg) (act Rg x t) := by
    rw [←hxa]
    exact (adjacent_act_iff Rg x _ _).mpr hat
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl hat,
    plane_edgeOffenderJoin_eq h e hz hk u hR rfl hat'] at hpair
  have hX := plane_paired_trapped_omega_generation h e hz hk u hR
    p q hp hq hat hct hgen hbad hbad' hs
  have hbig := (plane_paired_trapped_commutator_comparison h e hz hk u hR
    p q hp hq hat hct hgen hbad hbad' hs).2.2.2.1
  rw [(hX z p.end_color).2,(hX z' q.end_color).2,
    commutator_comm (Z Rg z ⊓ Q Rg (alpha Rg)) (Z Rg c),
    commutator_comm (Z Rg z' ⊓ Q Rg (alpha Rg)) (Z Rg c)] at hbig
  rcases plane_paired_commutator_escape h e hz hk u hR p q hat hct hgen hs with hnot | hnot
  · exact plane_trapped_conjugate_contradiction h e hz hk u hR p q hp hat hct x hx hqverts
      hpair hbad hbad' hnot (fun a ha => (hX a ha).2) hbig
  · have hqback (i : ℕ) : p.walk.getVert i = act Rg x⁻¹ (q.walk.getVert i) := by
      rw [hqverts,←act_mul,mul_inv_cancel,act_one]
    have hback : (Q Rg (act Rg x t)).map (MulAut.conj x).toMonoidHom = Q Rg t := by
      have hh := Q_act Rg x⁻¹ (act Rg x t)
      simpa only [inv_inv,←act_mul,mul_inv_cancel,act_one] using hh.symm
    have hG : (stabilizer Rg (alpha Rg)).map (MulAut.conj x).toMonoidHom =
        stabilizer Rg (alpha Rg) :=
      mem_normalizer_iff_map_conj_eq.mp ((stabilizer Rg (alpha Rg)).le_normalizer hx)
    have hpair' := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hpair
    have htback : Q Rg (act Rg x⁻¹ t) = (Q Rg t).map (MulAut.conj x).toMonoidHom := by
      simpa only [inv_inv] using Q_act Rg x⁻¹ t
    rw [Subgroup.map_sup,hback,hG,←htback,
      sup_comm (Q Rg (act Rg x⁻¹ t)) (Q Rg t)] at hpair'
    apply plane_trapped_conjugate_contradiction h e hz hk u hR q p hq hat hct x⁻¹
      ((stabilizer Rg (alpha Rg)).inv_mem hx) hqback hpair' hbad' hbad hnot
      (fun a ha => (hX a ha).2)
    simpa only [sup_comm (⁅Z Rg c,Z Rg z ⊓ Q Rg (alpha Rg)⁆)
      (⁅Z Rg c,Z Rg z' ⊓ Q Rg (alpha Rg)⁆)] using hbig

include h e hz hk in
/-- A strict slice in the original cubic plane branch gives a backward critical
path for one of the same selected endpoints. The switch, transporter, both
generation identities and all walk overlaps are retained. -/
theorem plane_small_critical_backward_shift
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z delta : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hd : Adjacent Rg delta (p.walk.getVert 1))
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg delta)) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf M,
      let x := (embedM Rg r)⁻¹
      ∃ q : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
        (∀ i, q.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
        (Q Rg (act Rg x z)).relIndex (Z Rg (alpha Rg)) < 4 ∧
        (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
        edgeOffenderJoin (alpha Rg) t ⊔ edgeOffenderJoin (alpha Rg) (act Rg x t) = stabilizer Rg (alpha Rg) ∧
        x ∈ normalizer (edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ∧
        Z Rg z ⊔ Z Rg (act Rg x z) ≤ edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) ∧
        ∃ g ∈ stabilizer Rg (alpha Rg), act Rg g (p.walk.getVert 1) = t ∧
          let c := act Rg g delta
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ∧
          ((∃ b : CriticalPath Rg (sourceGeometry h) c (p.walk.getVert (p.walk.length-2)),
              b.walk.getVert 1 = t ∧
              ∀ i ≤ p.walk.length-2, b.walk.getVert (i+2) = p.walk.getVert i) ∨
           (∃ b : CriticalPath Rg (sourceGeometry h) c (q.walk.getVert (q.walk.length-2)),
              b.walk.getVert 1 = t ∧
              ∀ i ≤ q.walk.length-2, b.walk.getVert (i+2) = q.walk.getVert i)) := by
  obtain ⟨t,hat,r,hr,q,hqverts,hqs,hgen,hpair,hnorm,hinside,g,hg,hgt,hstrict,halt⟩ :=
    plane_small_critical_backward_separation h e hz hk u hR p hp hd hs
  refine ⟨t,hat,r,hr,q,hqverts,hqs,hgen,hpair,hnorm,hinside,g,hg,hgt,hstrict,?_⟩
  rcases halt with hback | hback | ⟨hbad,hbad',_⟩
  · exact Or.inl hback
  · exact Or.inr hback
  · have hxG : (embedM Rg r)⁻¹ ∈ stabilizer Rg (alpha Rg) := by
      change (embedM Rg r)⁻¹ ∈ stabilizer Rg (mVertex Rg 1)
      rw [stabilizer_m_base]
      exact ⟨r⁻¹,by rw [map_inv]⟩
    have hct : Adjacent Rg (act Rg g delta) t := by
      rw [←hgt]
      exact (adjacent_act_iff Rg g _ _).mpr hd
    exact (plane_paired_trapped_impossible h e hz hk u hR p q hp hqs hat hct
      ((embedM Rg r)⁻¹) hxG hqverts hgen hpair hbad hbad' hstrict).elim

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
