module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusLine
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneBackward
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneEscape
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicAttachmentMovement

/-!
# The full radius kernel line modulo the endpoint center

On the original cubic plane graph, let a--z be a small critical path and
let Y lie in the full radius V_a and the last edge kernel, with Z_a <= Y.
If [Y,Z_z] escapes Z_a, the previously proved full-radius calculation gives
a nonzero line H = [Y,Z_z intersect Q_a].

The two-cover representation calculation gives either
H <= [Z_a,Z_z] Z(G_z), or [Y,Z_z] <= H[Z_a,Z_z]. The second alternative
contradicts escape from Z_a. The first is transported through the actual
cubic projection and edge embedding, including the entire fixed attachment.
If H were central in G_z, the faithful natural quotient would make Y fix
the critical fixed hyperplane on the whole cover, contradicting H != 1.
Thus H misses Z(G_z); exchanging the two noncentral lines gives
H Z(G_z) = [Z_a,Z_z] Z(G_z). This is an equality modulo the endpoint center,
not an identification of the two lines before quotienting.

At distance four with uniformly small critical images, the actual selected
full radius kernel contains Z_a. The application preserves its equality
with the whole last-edge kernel commutator, its strict containment in the
endpoint commutator, and all previously proved seed and radius containments.
The whole-core and literal C.1.32 consumers retain both covers of orders
sixteen and thirty-two, the original radical, and the projection kernel E
with nontrivial odd E/Q. Further geometric control of this noncentral line,
the other image/distance cases and both core exhaustions remain required.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii) and the line comparison in (5.12)(1), printed pp.866--867,
924--925; Aschbacher--Smith C.1.31--32, printed pp.135--136.
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
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

local notation "W₀" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local instance : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.of_le (commutator_le_left _ _)

include h e hz hk in
/-- The exact alignment/control alternatives on the original marked cover,
with its whole central kernel retained. -/
private theorem plane_cover_alignment_or_control (u : S)
    (hR : (Rg).map π ≤ D.map (MulAut.conj u).toMonoidHom)
    (A P : Subgroup M) (hA : A ≤ Rg) (hP : P ≤ Rg)
    (hne : ¬ A ≤ pCore 2 M)
    (hindex : (centralizer (A : Set M)).relIndex (W₀) ≤ 2) :
    ⁅W₀ ⊓ centralizer (A : Set M),P⁆ ≤
      ⁅W₀,A⁆ ⊔ (W₀ ⊓ center M) ∨
    ⁅W₀,P⁆ ≤
      ⁅W₀ ⊓ centralizer (A : Set M),P⁆ ⊔ ⁅W₀,A⁆ := by
  let := h.relative_normal
  let U := W₀
  let F := U ⊓ centralizer (A : Set M)
  let K := ⁅F,P⁆
  have hKU : K ≤ U := (commutator_mono inf_le_left le_rfl).trans (commutator_le_left U P)
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
  have hC : subgroupSpace U (U ⊓ center M) = fixedSpace (coverAction h e hz hk) ⊤ := by
    ext v
    have hh := mem_fixedSpace_image U π (CubicEven.projection_surjective h e hz hk) hker (⊤ : Subgroup M) v
    rw [map_top_of_surjective π (CubicEven.projection_surjective h e hz hk),coe_top,centralizer_univ] at hh
    change ((v.toMul : M) ∈ U ∧ (v.toMul : M) ∈ center M) ↔ _
    simp only [v.toMul.property,true_and]
    exact hh.symm
  have hwhole (B : Subgroup M) : subgroupSpace U ⁅U,B⁆ =
      subspaceCommutator (coverAction h e hz hk) ⊤ (B.map π) := by
    rw [subgroupSpace_commutator U π (CubicEven.projection_surjective h e hz hk) hker U B le_rfl,hU]
  have hh := Natural.Exhaustion.LargeDistance.SectionFive.CubeAlignmentModel.model_dichotomy (coverAction h e hz hk) (moved_subgroup_cover_model h e hz hk)
    u t (P.map π) (by simpa only [CFSG.Quasithin.ChapterB.Offenders.SixCorePlane.cube_eq] using ((map_mono hP).trans hR)) (by simpa only [CFSG.Quasithin.ChapterB.Offenders.SixCorePlane.cube_eq] using (((map_mono hA).trans hR) ht)) hs
  rw [←he,←hK,←hwhole P,←hwhole A,←hC] at hh
  rcases hh with hh | hh
  · left
    rw [←subgroupSpace_sup U (commutator_le_left U A) inf_le_left] at hh
    intro v hv
    exact hh (show Additive.ofMul (⟨v,hKU hv⟩ : U) ∈ subgroupSpace U K from hv)
  · right
    rw [←subgroupSpace_sup U hKU (commutator_le_left U A)] at hh
    intro v hv
    exact hh (show Additive.ofMul (⟨v,(commutator_le_left U P) hv⟩ : U) ∈ subgroupSpace U ⁅U,P⁆ from hv)

private theorem map_center_eq_range_inf_centralizer {F N : Type*} [Group F] [Group N]
    (i : F →* N) (hi : Function.Injective i) :
    (center F).map i = i.range ⊓ centralizer (i.range : Set N) := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    refine ⟨⟨x,rfl⟩,?_⟩
    rintro y ⟨z,rfl⟩
    simpa only [←map_mul] using congrArg i ((mem_center_iff.mp hx) z)
  · rintro x ⟨⟨y,rfl⟩,hc⟩
    refine ⟨y,mem_center_iff.mpr ?_,rfl⟩
    intro z
    apply hi
    simpa only [map_mul] using hc (i z) ⟨z,rfl⟩

include h e hz hk in
/-- Alignment/control on a full endpoint seed. The central edge attachment
is retained and shown to centralize both actual actors. -/
theorem plane_edge_alignment_or_control (u : S)
    (hR : (Rg).map π ≤ D.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex Rg} (hcol : color Rg c = false)
    (hct : Adjacent Rg c t)
    (A P : Subgroup (FreeAmalgam Rg))
    (hA : A ≤ Q Rg t) (hP : P ≤ Q Rg t)
    (hne : ¬ A ≤ Q Rg c)
    (hindex : (centralizer (A : Set (FreeAmalgam Rg))).relIndex (U Rg c) ≤ 2) :
    ⁅Z Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)),P⁆ ≤
      ⁅Z Rg c,A⁆ ⊔
        (stabilizer Rg c ⊓ centralizer (stabilizer Rg c : Set (FreeAmalgam Rg))) ∨
    ⁅Z Rg c,P⁆ ≤
      ⁅Z Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)),P⁆ ⊔ ⁅Z Rg c,A⁆ := by
  obtain ⟨i,hi,hir,hiR,hiQ,hiU⟩ := remaining_edge_coordinates h e hz hcol hct
  have hmA : (A.comap i).map i = A :=
    map_comap_eq_self (hA.trans (hiR ▸ map_le_range i _))
  have hmP : (P.comap i).map i = P :=
    map_comap_eq_self (hP.trans (hiR ▸ map_le_range i _))
  have hAr : A.comap i ≤ Rg := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hmA,hiR]
  have hPr : P.comap i ≤ Rg := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hmP,hiR]
  have hAn : ¬ A.comap i ≤ pCore 2 M := by
    intro hh
    apply hne
    have hm := map_mono (f := i) hh
    rwa [hmA,hiQ] at hm
  have hidx : (centralizer (A.comap i : Set M)).relIndex (W₀) ≤ 2 := by
    rw [←hiU,←hmA,←inf_relIndex_right,inf_comm,
      map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,
      inf_relIndex_left] at hindex
    exact hindex
  have hh := plane_cover_alignment_or_control h e hz hk u hR (A.comap i) (P.comap i) hAr hPr hAn hidx
  have hmF : (W₀ ⊓ centralizer (A.comap i : Set M)).map i =
      U Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)) := by
    rw [←map_inf_centralizer_of_injective i hi,hiU,hmA]
  have hmC : (W₀ ⊓ center M).map i ≤
      stabilizer Rg c ⊓ centralizer (stabilizer Rg c : Set (FreeAmalgam Rg)) := by
    have hh := map_mono (f := i) (show W₀ ⊓ center M ≤ center M from inf_le_right)
    rwa [map_center_eq_range_inf_centralizer i hi,hir] at hh
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
  have hF : ⁅Z Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)),P⁆ = ⁅F,P⁆ := by
    rw [heq]
    exact commutator_sup_of_central_attachment F (Z Rg t) P
      ((le_inf hseedN (hseedA.trans (centralizer (A : Set (FreeAmalgam Rg))).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf) hseedP
  have hZA : ⁅Z Rg c,A⁆ = ⁅U Rg c,A⁆ := by
    rw [vertex_seed_eq_moving_sup_edge h e hz hcol hct]
    exact commutator_sup_of_central_attachment _ _ _ hseedN hseedA
  have hZP : ⁅Z Rg c,P⁆ = ⁅U Rg c,P⁆ := by
    rw [vertex_seed_eq_moving_sup_edge h e hz hcol hct]
    exact commutator_sup_of_central_attachment _ _ _ hseedN hseedP
  rcases hh with hh | hh
  · left
    have hm := map_mono (f := i) hh
    rw [Subgroup.map_sup,map_commutator,map_commutator,hmF,hiU,hmA,hmP] at hm
    rw [hF,hZA]
    exact hm.trans (sup_le_sup_left hmC _)
  · right
    have hm := map_mono (f := i) hh
    rw [Subgroup.map_sup,map_commutator,hiU,hmP,map_commutator,hmF,hmP,
      map_commutator,hiU,hmA] at hm
    rwa [hZP,hF,hZA]

include h e hz hk in
private theorem full_seed_fixed_commutator_noncentral
    {c t : Vertex Rg} (hc : color Rg c = false) (hct : Adjacent Rg c t)
    (A P : Subgroup (FreeAmalgam Rg)) (hA : A ≤ Q Rg t) (hP : P ≤ Q Rg t)
    (hAP : A ≤ P) (hne : ¬ A ≤ Q Rg c)
    (hindex : (centralizer (A : Set (FreeAmalgam Rg))).relIndex (U Rg c) ≤ 2)
    (hK : ⁅Z Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)),P⁆ ≠ ⊥) :
    ¬ ⁅Z Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)),P⁆ ≤
      centralizer (stabilizer Rg c : Set (FreeAmalgam Rg)) := by
  intro hcentral
  obtain ⟨i,hi,hir,hiR,hiQ,hiU⟩ := remaining_edge_coordinates h e hz hc hct
  have hmA : (A.comap i).map i = A :=
    map_comap_eq_self (hA.trans (hiR ▸ map_le_range i _))
  have hmP : (P.comap i).map i = P :=
    map_comap_eq_self (hP.trans (hiR ▸ map_le_range i _))
  have hAr : A.comap i ≤ Rg := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hmA,hiR]
  have hnA : ¬ A.comap i ≤ pCore 2 M := by
    intro hh
    exact hne (hmA ▸ (map_mono hh).trans_eq hiQ)
  have hidx : (centralizer (A.comap i : Set M)).relIndex W₀ ≤ 2 := by
    rw [←hiU,←hmA,←inf_relIndex_right,inf_comm,
      map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,
      inf_relIndex_left] at hindex
    exact hindex
  have hmF : (W₀ ⊓ centralizer (A.comap i : Set M)).map i =
      U Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)) := by
    rw [←map_inf_centralizer_of_injective i hi,hiU,hmA]
  have hC : ⁅W₀ ⊓ centralizer (A.comap i : Set M),P.comap i⁆ ≤ center M := by
    intro x hx
    apply mem_center_iff.mpr
    intro m
    apply hi
    simp only [map_mul]
    apply hcentral
    · have hh := mem_map_of_mem i hx
      rw [map_commutator,hmF,hmP] at hh
      exact commutator_mono (inf_le_inf_right _ (DistanceEight.U_le_Z Rg c)) le_rfl hh
    · rw [←hir]
      exact ⟨m,rfl⟩
  have hzero := congrArg (Subgroup.map i)
    (cover_fixed_central_commutator_eq_bot h e hz hk (A.comap i) (P.comap i)
      (comap_mono hAP) (h.relative_radical.isPGroup.to_le hAr) hnA hidx hC)
  rw [map_commutator,hmF,hmP,Subgroup.map_bot] at hzero
  have he := full_fixed_seed_edge_commutator (h := h) (e := e) (hz := hz)
    hc hct A hA P hP
  exact hK (he.trans hzero)

include h e hz hk in
/-- An escaping full-radius subactor has a noncentral kernel line whose
image modulo the actual endpoint center is precisely the critical line.
The full central attachment is retained in the equality of joins. -/
theorem plane_radius_kernel_alignment
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (Y : Subgroup (FreeAmalgam Rg)) (hYV : Y ≤ V Rg a)
    (hYt : Y ≤ Q Rg (p.walk.getVert (p.walk.length-1)))
    (hAY : Z Rg a ≤ Y) (hnot : ¬ ⁅Y,Z Rg z⁆ ≤ Z Rg a) :
    let H := ⁅Y,Z Rg z ⊓ Q Rg a⁆
    let C := stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
    Nat.card H = 2 ∧
      ⁅V Rg a ⊓ Q Rg (p.walk.getVert (p.walk.length-1)),Z Rg z ⊓ Q Rg a⁆ = H ∧
      H ≤ Z Rg a ∧ H < ⁅Y,Z Rg z⁆ ∧
      H ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) = ⊥ ∧
      H ⊔ C = ⁅Z Rg a,Z Rg z⁆ ⊔ C := by
  have hd := plane_radius_subactor_kernel_line h e hz hk u hR p hp Y hYV hYt hnot
  let H := ⁅Y,Z Rg z ⊓ Q Rg a⁆
  let C := stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
  let T := ⁅Z Rg a,Z Rg z⁆
  have hl : 0 < p.walk.length := p.length_eq_b ▸ sourceDistance_pos h
  have hzt : Adjacent Rg z (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have hfixed : Z Rg z ⊓ Q Rg a =
      Z Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
    (critical_seed_centralizer_intersection h e
      (CriticalPath.ofPair p.end_color (reverse_pair h e p))).symm
  let := finite_Z Rg z
  let : Finite (U Rg z) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg z)) (inclusion_injective _)
  have hQC := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
    (Z_centralizes_Q Rg a p.start_color))
  have hi : (centralizer (Z Rg a : Set (FreeAmalgam Rg))).relIndex (U Rg z) ≤ 2 :=
    ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg z) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices h e hz hk p hp).2
  have hA := hAY.trans hYt
  have hne : H ≠ ⊥ := by
    intro he
    have hh := hd.1
    change Nat.card H = 2 at hh
    rw [he,Subgroup.card_bot] at hh
    omega
  have hnon : ¬ H ≤ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) := by
    have hh := full_seed_fixed_commutator_noncentral h e hz hk p.end_color hzt
      (Z Rg a) Y hA hYt hAY p.critical.2 hi
    rw [←hfixed,commutator_comm (Z Rg z ⊓ Q Rg a) Y] at hh
    exact hh hne
  have halign : H ≤ T ⊔ C := by
    rcases plane_edge_alignment_or_control h e hz hk u hR.le p.end_color hzt
      (Z Rg a) Y hA hYt p.critical.2 hi with ha | hc
    · simpa only [←hfixed,commutator_comm (Z Rg z ⊓ Q Rg a) Y,
        commutator_comm (Z Rg z) (Z Rg a)] using ha
    · rw [←hfixed,commutator_comm (Z Rg z) Y,
        commutator_comm (Z Rg z ⊓ Q Rg a) Y] at hc
      exact (hnot (hc.trans (sup_le hd.2.2.1 (by
        rw [commutator_comm]
        exact critical_seed_commutator_le h p)))).elim
  let := finite_Z Rg a
  let : Finite H := Finite.of_injective (inclusion hd.2.2.1) (inclusion_injective _)
  let : Finite (H ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) :
      Subgroup (FreeAmalgam Rg)) := Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hdis : H ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) = ⊥ := by
    by_contra hn
    have hlo := (one_lt_card_iff_ne_bot _).mpr hn
    have hc := hd.1
    change Nat.card H = 2 at hc
    have he := eq_of_le_of_card_ge (show H ⊓ centralizer
      (stabilizer Rg z : Set (FreeAmalgam Rg)) ≤ H from inf_le_left) (by omega)
    exact hnon (he ▸ inf_le_right)
  have hTZ : T ≤ Z Rg z := by
    dsimp only [T]
    rw [commutator_comm]
    exact critical_seed_commutator_le h (CriticalPath.ofPair p.end_color (reverse_pair h e p))
  let : Finite T := Finite.of_injective (inclusion hTZ) (inclusion_injective _)
  have hCnorm : C ≤ normalizer (T : Set (FreeAmalgam Rg)) :=
    (inf_le_right.trans (centralizer_le (hTZ.trans (Z_le_stabilizer Rg z)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hback : T ≤ H ⊔ C := two_line_exchange H T C
    (small_critical_commutator_card h e hz hk p hp) halign hCnorm
    (fun hh => hnon (hh.trans inf_le_right))
  exact ⟨hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1,hdis,
    le_antisymm (sup_le halign le_sup_right) (sup_le hback le_sup_right)⟩

include h e hz hk in
/-- The selected full radius kernel gives a noncentral line with exactly
the critical line's image modulo the endpoint center. All radius and
commutator containments refer to this same original critical path. -/
theorem plane_small_four_radius_alignment
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4) :
    ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
      let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
      let H := ⁅Y,X Rg z ⊓ Q Rg a⁆
      Nat.card H = 2 ∧
      ⁅V Rg a ⊓ Q Rg (p.walk.getVert 3),X Rg z ⊓ Q Rg a⁆ = H ∧
      H ≤ Z Rg a ⊓ Z Rg (p.walk.getVert 2) ∧
      H ≤ centralizer ((V Rg a ⊔ V Rg (p.walk.getVert 2) :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      H < ⁅Y,X Rg z⁆ ∧
      ⁅Y,X Rg z⁆ ≤ Z Rg (p.walk.getVert 3) ⊓ Q Rg a ∧
      ⁅⁅Y,X Rg z⁆,Q Rg (p.walk.getVert 3)⁆ = ⊥ ∧
      ¬ ⁅Y,X Rg z⁆ ≤ Z Rg a ∧
      H ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) = ⊥ ∧
      H ⊔ (stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) =
        ⁅Z Rg a,Z Rg z⁆ ⊔
          (stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) := by
  obtain ⟨a,z,p,hd⟩ := plane_small_four_radius_line h e hz hk u hR hb4 hsmall
  have hXZ := (plane_small_four_omega_generated h e hz hk u hR hb4 hsmall z p.end_color).2
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hc : color Rg (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hct : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have ht : color Rg (p.walk.getVert 3) = true := by
    have hh := adjacent_color_ne Rg hct
    rw [hc] at hh
    cases he : color Rg (p.walk.getVert 3) <;> simp_all
  let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
  have hAY : Z Rg a ≤ Y := by
    refine le_inf (Z_le_VBall Rg _ 2) ?_
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.start_color)
    rw [(sourceGeometry h).distance_constant _ p.start_color,p.dist_start (by omega)]
    exact distance_gt_two h e hz hk
  have hYt : Y ≤ Q Rg (p.walk.getVert (p.walk.length-1)) := by
    simp only [hl,Nat.reduceSub]
    exact inf_le_right.trans (Q_le_adjacent_h Rg ht hct)
  have hnot : ¬ ⁅Y,Z Rg z⁆ ≤ Z Rg a := by
    rw [←hXZ]
    exact hd.2.2.2.2.2.2.2
  have he := plane_radius_kernel_alignment h e hz hk u hR p (hsmall _ _ p) Y
    inf_le_left hYt hAY hnot
  exact ⟨a,z,p,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1,hd.2.2.2.2.1,
    hd.2.2.2.2.2.1,hd.2.2.2.2.2.2.1,hd.2.2.2.2.2.2.2,(by simpa only [hXZ] using he.2.2.2.2.1),
    (by simpa only [hXZ] using he.2.2.2.2.2)⟩


omit hk in
include h e hz in
/-- Whole-core application of the aligned, noncentral full-omega radius line.
Both full moving covers, the original cubic kernel and the Borel alternative
are retained. The nonzero line still requires the terminal contradiction. -/
theorem coreExhaustion_or_cubic_plane_radius_alignment :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
          ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
      let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
      let H := ⁅Y,X Rg z ⊓ Q Rg a⁆
      Nat.card H = 2 ∧
      ⁅V Rg a ⊓ Q Rg (p.walk.getVert 3),X Rg z ⊓ Q Rg a⁆ = H ∧
      H ≤ Z Rg a ⊓ Z Rg (p.walk.getVert 2) ∧
      H ≤ centralizer ((V Rg a ⊔ V Rg (p.walk.getVert 2) :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      H < ⁅Y,X Rg z⁆ ∧
      ⁅Y,X Rg z⁆ ≤ Z Rg (p.walk.getVert 3) ⊓ Q Rg a ∧
      ⁅⁅Y,X Rg z⁆,Q Rg (p.walk.getVert 3)⁆ = ⊥ ∧
      ¬ ⁅Y,X Rg z⁆ ≤ Z Rg a ∧
      H ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) = ⊥ ∧
      H ⊔ (stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) =
        ⁅Z Rg a,Z Rg z⁆ ⊔
          (stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))))) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 hsmall => plane_small_four_radius_alignment h e hz hk u hplane hb4 hsmall⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application on the original cubic graph. Distance four
and uniformly small critical images remain premises of the line assertion;
neither core exhaustion nor the full reconstruction is asserted. -/
theorem rankTwo_or_cubic_plane_radius_alignment :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
          ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
      let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
      let H := ⁅Y,X Rg z ⊓ Q Rg a⁆
      Nat.card H = 2 ∧
      ⁅V Rg a ⊓ Q Rg (p.walk.getVert 3),X Rg z ⊓ Q Rg a⁆ = H ∧
      H ≤ Z Rg a ⊓ Z Rg (p.walk.getVert 2) ∧
      H ≤ centralizer ((V Rg a ⊔ V Rg (p.walk.getVert 2) :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      H < ⁅Y,X Rg z⁆ ∧
      ⁅Y,X Rg z⁆ ≤ Z Rg (p.walk.getVert 3) ⊓ Q Rg a ∧
      ⁅⁅Y,X Rg z⁆,Q Rg (p.walk.getVert 3)⁆ = ⊥ ∧
      ¬ ⁅Y,X Rg z⁆ ≤ Z Rg a ∧
      H ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) = ⊥ ∧
      H ⊔ (stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) =
        ⁅Z Rg a,Z Rg z⁆ ⊔
          (stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))))) :=
  (coreExhaustion_or_cubic_plane_radius_alignment h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
