module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalNormalization
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicKernelTransport
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalKernels
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.ElementaryKernelModel
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneComparison
import all CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardKernel
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusNormalizer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicAttachmentMovement

/-!
# Terminal kernel alignment on the original Borel graph

Failure of endpoint normalization gives an elementary actor containing the
critical transposition. The six-letter cover calculation puts its restricted
commutator in the critical line plus the entire moving central attachment.
Central movement of the fixed hyperplane would vanish, so this nonzero
commutator is noncentral at the endpoint. The two lines therefore generate
the same subgroup modulo that full attachment.

For three compatible backward shifts, the common edge intersection lies in
the last moving cover and is central under consecutive whole stabilizers.
The actual shift transporters carry it to the first forward component vertex.
At distance six this is exactly the reverse endpoint, so the intersection
lies in that endpoint's moving central attachment. OriginalSylowExceptional
constructs the shifts and applies these facts to the literal c.L,d.S source.

These are alignment and transport steps of MS93 (5.10). Attachment saturation
and the selected-seed avoidance argument are still needed for its distance-six
normalization conclusion. Both full moving covers and the original cubic
kernel E, including its odd quotient E/Q, are retained.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii), (5.10), printed pp.866--867,922. The model proof is reused
from Natural.Exhaustion.LargeDistance.SectionFive.ElementaryKernelModel; only
its representation theorem is used. The exceptional projection transport
adapts ElementaryKernelControl and uses the original graph throughout.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Representation.NormalElementaryQuotient
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W₀" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk
local instance : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.of_le (commutator_le_left _ _)

include h e hz hk in
private theorem terminal_cover_kernel_small_aligned
    (A P : Subgroup M) (hAP : A ≤ P) (hel : IsElementaryAbelian 2 P)
    (hne : ¬ A ≤ extensionKernel h)
    (hindex : (centralizer (A : Set M)).relIndex (W₀) ≤ 2)
    (hfail : ¬ ⁅W₀,P⁆ ≤
      ⁅W₀ ⊓ centralizer (A : Set M),P⁆ ⊔ ⁅W₀,A⁆) :
    Nat.card (⁅W₀ ⊓ centralizer (A : Set M),P⁆ : Subgroup M) ≤ 2 ∧
    ⁅W₀ ⊓ centralizer (A : Set M),P⁆ ≤
      ⁅W₀,A⁆ ⊔ (W₀ ⊓ center M) := by
  let := h.relative_normal
  let := hel
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
    exact hne ((CubicAction.projection_kernel h e hz hk) ▸ (map_eq_bot_iff A).mp he)
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
  have hfail' : ¬ subspaceCommutator (coverAction h e hz hk) ⊤ (P.map π) ≤
      subspaceCommutator (coverAction h e hz hk) (fixedSpace (coverAction h e hz hk) (zpowers t)) (P.map π) ⊔
        subspaceCommutator (coverAction h e hz hk) ⊤ (zpowers t) := by
    intro hh
    rw [←he,←hK,←hwhole P,←hwhole A,←subgroupSpace_sup U hKU (commutator_le_left U A)] at hh
    apply hfail
    intro v hv
    exact hh (show Additive.ofMul (⟨v,(commutator_le_left U P) hv⟩ : U) ∈ subgroupSpace U ⁅U,P⁆ from hv)
  have hh := Natural.Exhaustion.LargeDistance.SectionFive.ElementaryKernelModel.small_aligned_of_failure (coverAction h e hz hk) (moved_subgroup_cover_model h e hz hk) t
    (P.map π) (IsElementaryAbelian.map π) ((map_mono hAP) ht) hs hfail'
  rw [←he,←hK] at hh
  have hcard : Nat.card K = 2 ^ Module.finrank (ZMod 2) (subgroupSpace U K) := by
    calc Nat.card K = Nat.card (Additive K) := rfl
         _ = Nat.card (subgroupSpace U K) := Nat.card_congr (subgroupSpaceEquiv U K hKU).toEquiv
         _ = _ := by rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  refine ⟨?_,?_⟩
  · change Nat.card K ≤ 2
    rw [hcard]
    calc 2 ^ Module.finrank (ZMod 2) (subgroupSpace U K) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hh.1
         _ = 2 := rfl
  · have ha := hh.2
    rw [←hwhole A,←hC,←subgroupSpace_sup U (commutator_le_left U A) inf_le_left] at ha
    intro v hv
    exact ha (show Additive.ofMul (⟨v,hKU hv⟩ : U) ∈ subgroupSpace U K from hv)


include h e hz hk in
/-- The full restricted commutator in the nonnormalizing alternative lies
in the reverse critical line plus the entire endpoint central attachment. -/
theorem borel_restricted_kernel_alignment
    (hb : 4 < sourceDistance h)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (Y : Subgroup (FreeAmalgam Rg)) [IsElementaryAbelian 2 Y]
    (hYV : Y ≤ V Rg a)
    (htrap : Y ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hYN : Z Rg z ⊓ Q Rg a ≤ normalizer (Y : Set (FreeAmalgam Rg)))
    (hnorm : ¬ Z Rg z ≤ normalizer
      ((Y ⊔ Z Rg a : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg))) :
    ⁅Y,Z Rg z ⊓ Q Rg a⁆ ≤ ⁅Z Rg a,Z Rg z⁆ ⊔
      (U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) := by
  have hb2 : 2 < sourceDistance h := by omega
  let F := Z Rg z ⊓ Q Rg a
  let P := Y ⊔ Z Rg a
  let H := ⁅Y,F⁆
  have hYQ : Y ≤ Q Rg a := hYV.trans ((sourceGeometry h).V_le_Q hb2 a p.start_color)
  have hAC : Z Rg a ≤ centralizer (Y : Set (FreeAmalgam Rg)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a p.start_color)).trans
      (centralizer_le hYQ)
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a p.start_color
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.sup_of_le_centralizer hAC
  have hYG : Y ≤ stabilizer Rg z := htrap.trans (terminal_last_edge_inputs h p hb2).2.2
  let pr : CriticalPath Rg (sourceGeometry h) z a :=
    CriticalPath.ofPair p.end_color (reverse_pair h e p)
  have hAG : Z Rg a ≤ stabilizer Rg z :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) z p.end_color
      (by rw [(sourceGeometry h).distance_constant _ p.end_color]; exact sourceDistance_pos h)
      pr.critical
  have hPG : P ≤ stabilizer Rg z := sup_le hYG hAG
  have hAF : Z Rg a ≤ centralizer (F : Set (FreeAmalgam Rg)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a p.start_color)).trans
      (centralizer_le inf_le_right)
  have hPF : ⁅P,F⁆ = H := commutator_sup_fixed Y (Z Rg a) F
    (hAC.trans (Subgroup.centralizer_le_normalizer _)) hAF
  have hfixed : ⁅U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)),P⁆ = H := by
    have hAF' : Z Rg a ≤ centralizer
        (U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)) : Set _) :=
      le_centralizer_iff.mpr inf_le_right
    rw [commutator_comm,commutator_sup_fixed Y (Z Rg a) _
      (hAC.trans (Subgroup.centralizer_le_normalizer _)) hAF',commutator_comm]
    rw [←critical_moving_kernel_eq_fixed h e p]
    rw [←(critical_kernel_predecessor_moving h e hz hb2 p).2.2 Y htrap,commutator_comm]
  have hs : (Q Rg a).relIndex (Z Rg z) < 4 := by
    rw [(small_critical_indices h e hz hk p hp).2]
    decide
  have hD : ⁅U Rg z,Z Rg a⁆ = ⁅Z Rg a,Z Rg z⁆ := by
    rw [small_critical_moving_commutator_eq h e hz hk pr hs,commutator_comm]
  have hHY : H ≤ Y := le_normalizer_iff_commutator_le_left.mp hYN
  have hcrit := critical_seed_commutator_le h p
  have hfail : ¬ ⁅U Rg z,P⁆ ≤ H ⊔ ⁅Z Rg a,Z Rg z⁆ := by
    intro hh
    apply hnorm
    have hYmove : ⁅Y,Z Rg z⁆ ≤ H ⊔ ⁅Z Rg a,Z Rg z⁆ := by
      rw [commutator_comm,critical_predecessor_seed_movement h e hz hb2 p Y htrap]
      exact (commutator_mono le_rfl le_sup_left).trans hh
    have hZnorm : Z Rg z ≤ normalizer (Z Rg a : Set (FreeAmalgam Rg)) :=
      le_normalizer_iff_commutator_le_left.mpr hcrit
    apply le_normalizer_iff.mpr
    intro x hx v hv
    have hm : (Y ⊔ Z Rg a).map (MulAut.conj x).toMonoidHom ≤ Y ⊔ Z Rg a := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ((mem_normalizer_iff_map_conj_eq.mp (hZnorm hx)).le.trans le_sup_right)
      rintro _ ⟨y,hy,rfl⟩
      have hh := (Y ⊔ Z Rg a).mul_mem
        ((hYmove.trans (sup_le (hHY.trans le_sup_left) (hcrit.trans le_sup_right)))
          (by rw [commutator_comm]; exact commutator_mem_commutator hx hy))
        (mem_sup_left hy)
      simpa [MulAut.conj_apply,commutatorElement_def,mul_assoc] using hh
    exact hm (mem_map_of_mem (MulAut.conj x).toMonoidHom hv)
  let := h.relative_normal
  obtain ⟨i,hi,hir,hiQ,hiE,hiU,_⟩ := graph_cover h e hz hk z p.end_color
  let A := (Z Rg a).comap i
  let P₀ := P.comap i
  let : IsElementaryAbelian 2 P₀ := IsElementaryAbelian.comap_of_injective i hi P
  have hmA : A.map i = Z Rg a := map_comap_eq_self (hAG.trans_eq hir.symm)
  have hmP : P₀.map i = P := map_comap_eq_self (hPG.trans_eq hir.symm)
  have hnA : ¬ A ≤ extensionKernel h :=
    critical_comap_not_le_extension h e hz pr i hi (hAG.trans_eq hir.symm) hiQ
  have hidx : (centralizer (A : Set M)).relIndex W₀ ≤ 2 := by
    rw [←inf_relIndex_right,inf_comm,←relIndex_map_map_of_injective _ _ hi,
      ←map_inf_centralizer_of_injective i hi,hiU,hmA,inf_relIndex_left]
    let := finite_Z Rg z
    let : Finite (U Rg z) := Finite.of_injective
      (inclusion (DistanceEight.U_le_Z Rg z)) (inclusion_injective _)
    have hQC : Q Rg a ≤ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a p.start_color))
    exact ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg z) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices h e hz hk p hp).2
  have hmH : (⁅W₀ ⊓ centralizer (A : Set M),P₀⁆).map i = H := by
    rw [map_commutator,←map_inf_centralizer_of_injective i hi,hiU,hmA,hmP,hfixed]
  have hmD : (⁅W₀,A⁆).map i = ⁅Z Rg a,Z Rg z⁆ := by
    rw [map_commutator,hiU,hmA,hD]
  have hmC : (W₀ ⊓ center M).map i =
      U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) := by
    have hh := map_inf_centralizer_of_injective i hi W₀ ⊤
    simpa only [←MonoidHom.range_eq_map,hir,hiU,coe_top,centralizer_univ] using hh.symm
  have hh := terminal_cover_kernel_small_aligned h e hz hk A P₀
    (comap_mono (show Z Rg a ≤ P from le_sup_right)) inferInstance hnA hidx (by
      intro hh
      apply hfail
      have hm := map_mono (f := i) hh
      rwa [Subgroup.map_sup,hmH,hmD,map_commutator,hiU,hmP] at hm)
  have hm := map_mono (f := i) hh.2
  rwa [hmH,Subgroup.map_sup,hmD,hmC] at hm


include h e hz hk in
/-- A nonzero restricted critical-kernel displacement cannot be central
at the endpoint. This uses the full cubic cover, including its attachment. -/
theorem borel_restricted_kernel_noncentral
    (hb : 4 < sourceDistance h)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (Y : Subgroup (FreeAmalgam Rg)) [IsElementaryAbelian 2 Y]
    (hYV : Y ≤ V Rg a)
    (htrap : Y ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hne : ⁅Y,Z Rg z ⊓ Q Rg a⁆ ≠ ⊥) :
    ¬ ⁅Y,Z Rg z ⊓ Q Rg a⁆ ≤
      centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) := by
  intro hcentral
  have hb2 : 2 < sourceDistance h := by omega
  let F := Z Rg z ⊓ Q Rg a
  let P := Y ⊔ Z Rg a
  let H := ⁅Y,F⁆
  have hYQ : Y ≤ Q Rg a := hYV.trans ((sourceGeometry h).V_le_Q hb2 a p.start_color)
  have hAC : Z Rg a ≤ centralizer (Y : Set (FreeAmalgam Rg)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a p.start_color)).trans
      (centralizer_le hYQ)
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a p.start_color
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.sup_of_le_centralizer hAC
  have hYG : Y ≤ stabilizer Rg z := htrap.trans (terminal_last_edge_inputs h p hb2).2.2
  let pr : CriticalPath Rg (sourceGeometry h) z a :=
    CriticalPath.ofPair p.end_color (reverse_pair h e p)
  have hAG : Z Rg a ≤ stabilizer Rg z :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) z p.end_color
      (by rw [(sourceGeometry h).distance_constant _ p.end_color]; exact sourceDistance_pos h)
      pr.critical
  have hPG : P ≤ stabilizer Rg z := sup_le hYG hAG
  have hAF : Z Rg a ≤ centralizer (F : Set (FreeAmalgam Rg)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a p.start_color)).trans
      (centralizer_le inf_le_right)
  have hPF : ⁅P,F⁆ = H := commutator_sup_fixed Y (Z Rg a) F
    (hAC.trans (Subgroup.centralizer_le_normalizer _)) hAF
  have hfixed : ⁅U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)),P⁆ = H := by
    have hAF' : Z Rg a ≤ centralizer
        (U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)) : Set _) :=
      le_centralizer_iff.mpr inf_le_right
    rw [commutator_comm,commutator_sup_fixed Y (Z Rg a) _
      (hAC.trans (Subgroup.centralizer_le_normalizer _)) hAF',commutator_comm]
    rw [←critical_moving_kernel_eq_fixed h e p]
    rw [←(critical_kernel_predecessor_moving h e hz hb2 p).2.2 Y htrap,commutator_comm]
  let := h.relative_normal
  obtain ⟨i,hi,hir,hiQ,hiE,hiU,_⟩ := graph_cover h e hz hk z p.end_color
  let A := (Z Rg a).comap i
  let P₀ := P.comap i
  let : IsElementaryAbelian 2 P₀ := IsElementaryAbelian.comap_of_injective i hi P
  have hmA : A.map i = Z Rg a := map_comap_eq_self (hAG.trans_eq hir.symm)
  have hmP : P₀.map i = P := map_comap_eq_self (hPG.trans_eq hir.symm)
  have hnA : ¬ A ≤ pCore 2 M := by
    intro hh
    have he := map_mono (f := i) hh
    rw [hmA,hiQ] at he
    exact p.critical.2 he
  have hidx : (centralizer (A : Set M)).relIndex W₀ ≤ 2 := by
    rw [←inf_relIndex_right,inf_comm,←relIndex_map_map_of_injective _ _ hi,
      ←map_inf_centralizer_of_injective i hi,hiU,hmA,inf_relIndex_left]
    let := finite_Z Rg z
    let : Finite (U Rg z) := Finite.of_injective
      (inclusion (DistanceEight.U_le_Z Rg z)) (inclusion_injective _)
    have hQC : Q Rg a ≤ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a p.start_color))
    exact ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg z) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices h e hz hk p hp).2
  have hmH : (⁅W₀ ⊓ centralizer (A : Set M),P₀⁆).map i = H := by
    rw [map_commutator,←map_inf_centralizer_of_injective i hi,hiU,hmA,hmP,hfixed]
  have hcF : ⁅W₀ ⊓ centralizer (A : Set M),P₀⁆ ≤ center M := by
    intro x hx
    apply mem_center_iff.mpr
    intro m
    apply hi
    simp only [map_mul]
    apply hcentral
    · have hh := mem_map_of_mem i hx
      rwa [hmH] at hh
    · rw [←hir]
      exact ⟨m,rfl⟩
  have hzero := congrArg (Subgroup.map i)
    (cover_fixed_central_commutator_eq_bot h e hz hk A P₀
      (comap_mono (show Z Rg a ≤ P from le_sup_right))
      (((sourceGeometry h).Z_elementary (sourceDistance_pos h) a p.start_color).isPGroup.comap_of_injective i hi)
      hnA hidx hcF)
  rw [hmH,Subgroup.map_bot] at hzero
  exact hne hzero


private theorem shift_central_transport
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : BorelBackwardShift (h := h) p)
    (I : Subgroup (FreeAmalgam Rg))
    (hIa : I ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))) :
    (I ≤ centralizer (stabilizer Rg q.start : Set (FreeAmalgam Rg)) →
      I ≤ centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg))) ∧
    (I ≤ U Rg q.start → I ≤ U Rg (p.walk.getVert 2)) := by
  have he : act Rg q.transporter⁻¹ q.start = p.walk.getVert 2 := by
    rw [←q.start_eq,←act_mul,mul_inv_cancel,act_one]
  have hf := terminal_fixed_map I (stabilizer Rg a) hIa q.transporter_mem
  constructor
  · intro hIq
    rw [←he,stabilizer_act,inv_inv]
    have hh := (map_mono (f := (MulAut.conj q.transporter).toMonoidHom) hIq).trans
      (map_centralizer_le_centralizer_image _ _)
    rwa [hf] at hh
  · intro hIU
    rw [←he,U_act,inv_inv,←hf]
    exact map_mono hIU

include h e hz hk in
/-- The common central intersection travels through the actual backward
transporters to the first forward component vertex. No distance-six
identification or vanishing of the central attachment is assumed. -/
theorem borel_three_shift_attachment_transport
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    let H := ⁅Z Rg t.start ⊓ Q Rg v,Z Rg z ⊓ Q Rg r.start⁆
    let D := ⁅Z Rg t.start,Z Rg v⁆
    let I := (H ⊔ D) ⊓ Z Rg t.edge
    I ≤ U Rg t.start ∧
      I ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) ∧
      I ≤ U Rg (p.walk.getVert 2) ⊓
        centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) := by
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let H := ⁅Z Rg t.start ⊓ Q Rg v,Z Rg z ⊓ Q Rg r.start⁆
  let D := ⁅Z Rg t.start,Z Rg v⁆
  let I := (H ⊔ D) ⊓ Z Rg t.edge
  have hcol : color Rg t.edge = true := by
    have hh := adjacent_color_ne Rg t.adjacent_start
    rw [r.path.start_color] at hh
    cases he : color Rg t.edge <;> simp_all
  have hFT : Z Rg z ⊓ Q Rg r.start ≤ Q Rg t.edge :=
    inf_le_right.trans (Q_le_adjacent_h Rg hcol t.adjacent_start)
  have hHU : H ≤ U Rg t.start :=
    (commutator_mono inf_le_left hFT).trans
      (full_seed_edge_commutator_le_moving h e hz t.path.start_color t.adjacent_shift)
  have ht := two_borel_backward_shifts_small_moving h e hz hk hb q.path r t
  have hs : (Q Rg v).relIndex (Z Rg t.start) < 4 := by rw [ht.2.1]; decide
  have hDU : D ≤ U Rg t.start := by
    dsimp only [D]
    rw [←small_critical_moving_commutator_eq h e hz hk t.path hs]
    exact le_normalizer_iff_commutator_le_left.mp
      ((critical_Z_le_stabilizer Rg (sourceGeometry h) t.start t.path.start_color
        (by rw [(sourceGeometry h).distance_constant _ t.path.start_color]; exact sourceDistance_pos h)
        t.path.critical).trans (U_normalized t.start))
  have hIU : I ≤ U Rg t.start := inf_le_left.trans (sup_le hHU hDU)
  have hcent := borel_three_shift_kernel_intersection_central h e hz hk hb u hR p q r t
  have hIr : I ≤ centralizer (stabilizer Rg r.start : Set (FreeAmalgam Rg)) := hcent.2.2.1
  have hIq : I ≤ centralizer (stabilizer Rg q.start : Set (FreeAmalgam Rg)) := hcent.2.2.2.1
  have hq2 : q.path.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
  have hr2 : r.path.walk.getVert 2 = q.start := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using r.overlap 0 (Nat.zero_le _)
  have hIa : I ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
    have hh := (shift_central_transport h q.path r I hIq).1 hIr
    rwa [hq2] at hh
  have hIUq : I ≤ U Rg q.start := by
    have hh := (shift_central_transport h r.path t I hIr).2 hIU
    rwa [hr2] at hh
  have hf := shift_central_transport h p q I hIa
  exact ⟨hIU,hIa,le_inf (hf.2 hIUq) (hf.1 hIq)⟩

include h e hz hk in
/-- At distance six, the transported central intersection lies in the
actual reverse endpoint's whole moving attachment. -/
theorem borel_six_kernel_attachment
    (hb : sourceDistance h = 6)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    let H := ⁅Z Rg t.start ⊓ Q Rg v,Z Rg z ⊓ Q Rg r.start⁆
    let D := ⁅Z Rg t.start,Z Rg v⁆
    (H ⊔ D) ⊓ Z Rg t.edge ≤
      U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) := by
  have hlp : p.walk.length = 6 := p.length_eq_b.trans hb
  have hlq : q.path.walk.length = 6 := q.path.length_eq_b.trans hb
  have he : q.path.walk.getVert (q.path.walk.length-2) = p.walk.getVert 2 := by
    rw [hlq]
    exact q.overlap 2 (by omega)
  have hh := (borel_three_shift_attachment_transport h e hz hk (by omega) u hR p q r t).2.2
  simpa only [←he] using hh


include h e hz hk in
/-- The actual nonnormalizing terminal branch has an order-two displacement
aligned with the preceding critical line modulo the whole central attachment.
This applies to the full restricted seed, retaining the original quotient. -/
theorem borel_three_shift_nonnormalized_alignment
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path)
    (hnorm : ¬ Z Rg (q.path.walk.getVert (q.path.walk.length-2)) ≤ normalizer
      (((Z Rg t.start ⊓ Q Rg (r.path.walk.getVert (r.path.walk.length-2))) ⊔
        Z Rg r.start : Subgroup (FreeAmalgam Rg)) : Set _)) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    let H := ⁅Z Rg t.start ⊓ Q Rg v,Z Rg z ⊓ Q Rg r.start⁆
    Nat.card H = 2 ∧
      (¬ H ≤ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) ∧
      H ≤ ⁅Z Rg r.start,Z Rg z⁆ ⊔
        (U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) ∧
      H ⊔ (U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) =
        ⁅Z Rg r.start,Z Rg z⁆ ⊔
          (U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) := by
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let K := Z Rg t.start ⊓ Q Rg v
  have hdata := borel_three_shift_restricted_kernel h e hz hk hb u hR p q r t
  have hr := two_borel_backward_shifts_small_moving h e hz hk hb p q r
  have hs : (Q Rg z).relIndex (Z Rg r.start) < 4 := by rw [hr.2.1]; decide
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) t.start t.path.start_color
  let : IsElementaryAbelian 2 K := IsElementaryAbelian.of_le inf_le_left
  have hZX : Z Rg z ≤ X Rg z := (sourceGeometry h).omega_bound z r.path.end_color (by
    rw [(sourceGeometry h).distance_constant _ r.path.end_color]; exact sourceDistance_pos h)
  have hcard := (hdata.2.2.2.2 hnorm).1
  have hne : ⁅K,Z Rg z ⊓ Q Rg r.start⁆ ≠ ⊥ := by
    intro he
    have hh : Nat.card (⁅K,Z Rg z ⊓ Q Rg r.start⁆ : Subgroup (FreeAmalgam Rg)) = 2 := hcard
    rw [he,Subgroup.card_bot] at hh
    omega
  have hnon := borel_restricted_kernel_noncentral h e hz hk hb r.path hs K
    (inf_le_left.trans (terminal_neighbor_seed_radius t.adjacent_start t.adjacent_shift))
    inf_le_right hne
  have halign := borel_restricted_kernel_alignment h e hz hk hb r.path hs K
    (inf_le_left.trans (terminal_neighbor_seed_radius t.adjacent_start t.adjacent_shift))
    inf_le_right ((inf_le_inf_right _ hZX).trans hdata.2.2.2.1) hnorm
  let H := ⁅K,Z Rg z ⊓ Q Rg r.start⁆
  let D := ⁅Z Rg r.start,Z Rg z⁆
  let C := U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
  let := finite_Z Rg r.start
  let : Finite D := Finite.of_injective (inclusion (critical_seed_commutator_le h r.path))
    (inclusion_injective _)
  have hDz : D ≤ Z Rg z := by
    dsimp only [D]
    rw [commutator_comm]
    exact critical_seed_commutator_le h (CriticalPath.ofPair r.path.end_color (reverse_pair h e r.path))
  have hCN : C ≤ normalizer (D : Set (FreeAmalgam Rg)) :=
    (inf_le_right.trans (centralizer_le (hDz.trans (Z_le_stabilizer Rg z)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hDC : D ≤ H ⊔ C := two_line_exchange H D C
    (small_critical_commutator_card h e hz hk r.path hs) halign hCN
    (fun hh => hnon (hh.trans inf_le_right))
  exact ⟨hcard,hnon,halign,le_antisymm (sup_le halign le_sup_right) (sup_le hDC le_sup_right)⟩

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
