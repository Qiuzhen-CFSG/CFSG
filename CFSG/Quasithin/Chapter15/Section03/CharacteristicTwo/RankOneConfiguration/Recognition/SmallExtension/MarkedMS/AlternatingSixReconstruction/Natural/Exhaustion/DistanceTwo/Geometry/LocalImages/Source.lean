module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages.Orders
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Structure.Noncontainment
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.CentralLayer.Edges
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Recognition.Projection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Structure.Inputs
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.QuadraticPointCore.MovingFixer

/-!
# The literal critical image has order two or four

Use the opposite endpoint's incident edge to embed the unchanged replacement
carrier. The initial Z-layer pulls back to an elementary subgroup A, while
the initial two-core pulls back to a two-subgroup Y containing A centrally.
Failure of the Frattini containment forces the image of Y to be strictly
larger than the nontrivial image of A. The S₆ central-subgroup bound then
leaves orders two and four. The larger image also fixes the entire moved
space of A on the actual natural central quotient.

All maps come from the original replacement and the whole moved cover;
no natural complement or point-radical marking is an assumption. The
order-four alternative still needs the additional source exclusion. A separate
conditional application discharges LocalImageData from containment of the
actual radical image in a conjugate point core; no full-image equality is
needed. Establishing that containment, or excluding order four by the source
route, remains with this distance-two owner. Source: MS93 (3.3)(ii) and (3.6), printed pp.866--871.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages
open LargeDistance
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
  (d : Replacement L R)

include h e hz in
private theorem edge_coordinates {c b : Vertex d.radical}
    (hc : color d.radical c = false) (hcb : Adjacent d.radical c b) :
    ∃ i : d.overgroup →* FreeAmalgam d.radical, Function.Injective i ∧
      i.range = stabilizer d.radical c ∧ d.radical.map i = Q d.radical b ∧
      (pCore 2 d.overgroup).map i = Q d.radical c ∧
      (replacementMoved d).map i = U d.radical c ∧
      (pResidual 2 d.overgroup).map i = Ltilde d.radical c := by
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common d.radical c b).mp hcb
  · rcases hg with ⟨rfl,rfl⟩
    let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM d.radical)
    refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective d.radical),?_,?_,?_,?_,?_⟩
    · have he := stabilizer_act d.radical g (alpha d.radical)
      dsimp only [i]
      rw [MonoidHom.range_comp]
      change (Mbar d.radical).map (MulAut.conj g⁻¹).toMonoidHom = _
      simpa only [alpha,act_mVertex,one_mul,stabilizer_m_base] using he.symm
    · have he := Q_act d.radical g (beta d.radical)
      rw [Q_beta] at he
      simpa only [beta,act_hVertex,one_mul,Q_beta,map_map] using he.symm
    · have he := Q_act d.radical g (alpha d.radical)
      rw [Q_alpha d.radical (replacement_radical_isPGroup h d)
        (replacement_core_le_radical h d)] at he
      simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
    · have he := U_act d.radical g (alpha d.radical)
      rw [(CentralLayer.replacement_centralLayer d e hz h).U_eq_moved] at he
      simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
    · have he := Ltilde_act d.radical g (alpha d.radical)
      rw [Ltilde_alpha] at he
      simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
  · rw [hg.1] at hc
    cases hc

include hn in
/-- Equivariance of the genuine central-cover projection transports literal
commutator centralization to the natural moved space. -/
theorem image_fixes_moved_of_centralizes (A Y : Subgroup d.overgroup)
    (hY : Y ≤ centralizer ((⁅replacementMoved d,A⁆ : Subgroup d.overgroup) : Set d.overgroup)) :
    Y.map (Recognition.sourceProjection h e hz hn d) ≤
      subspaceKernel (naturalRepresentation (Fin 6))
        (subspaceCommutator (naturalRepresentation (Fin 6)) ⊤
          (A.map (Recognition.sourceProjection h e hz hn d))) ⊤ := by
  let := replacementMoved_normal h d
  let W := replacementMoved d
  let p := coverProjection h e hz hn d
  let q := Recognition.sourceProjection h e hz hn d
  have heq (g : d.overgroup) (w : W) :
      (p (MulAut.conjNormal g w)).toAdd =
        naturalRepresentation (Fin 6) (q g) (p w).toAdd := by
    rw [Recognition.sourceProjection_action]
    exact coverProjection_conjugate h e hz hn d g w (MulAut.conjNormal g w) rfl
  rintro _ ⟨y,hy,rfl⟩
  refine ⟨mem_top _,?_⟩
  have hspace : subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (A.map q) ≤
      LinearMap.ker (naturalRepresentation (Fin 6) (q y) - LinearMap.id) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨a,ha,rfl⟩,v,_,rfl⟩
    obtain ⟨w,hw⟩ := coverProjection_surjective h e hz hn d (Multiplicative.ofAdd v)
    let z : W := MulAut.conjNormal a w * w⁻¹
    have hzmem : (z : d.overgroup) ∈ ⁅W,A⁆ := by
      rw [commutator_comm]
      exact commutator_mem_commutator ha w.property
    have hfix : MulAut.conjNormal y z = z := by
      apply Subtype.ext
      change y * (z : d.overgroup) * y⁻¹ = z
      rw [←hY hy z hzmem,mul_inv_cancel_right]
    have hcoords : (p z).toAdd = naturalRepresentation (Fin 6) (q a) v - v := by
      dsimp only [z]
      rw [map_mul,map_inv]
      change (p (MulAut.conjNormal a w)).toAdd + -(p w).toAdd = _
      rw [heq,hw]
      exact (sub_eq_add_neg _ _).symm
    have hfixed := heq y z
    rw [hfix] at hfixed
    change naturalRepresentation (Fin 6) (q y)
      (naturalRepresentation (Fin 6) (q a) v-v) -
      (naturalRepresentation (Fin 6) (q a) v-v) = 0
    rw [←hcoords,←hfixed,sub_self]
  intro v hv
  simpa only [LinearMap.mem_ker,LinearMap.sub_apply,LinearMap.id_apply,sub_eq_zero] using hspace hv

include hn in
/-- The original critical pair supplies a nontrivial elementary central image
with a strictly larger two-group image fixing its natural displacement.
The equality records the literal relative-index convention. -/
theorem critical_image_data_coordinates_with_edge
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    {c : Vertex d.radical}
    (hc : CriticalPair d.radical (alpha d.radical) c
      ((replacementGeometry h d).exists_critical _ rfl)) :
    ∃ A Y : Subgroup d.overgroup,
      A ≤ Y ∧ Y ≤ d.radical ∧
      IsElementaryAbelian 2 A ∧
      Y ≤ centralizer (A : Set d.overgroup) ∧
      ¬ A ≤ pCore 2 d.overgroup ∧ ¬ Y ≤ A ⊔ pCore 2 d.overgroup ∧
      Y ≤ centralizer ((⁅replacementMoved d,A⁆ : Subgroup d.overgroup) : Set d.overgroup) ∧
      Y.map (Recognition.sourceProjection h e hz hn d) ≤
        subspaceKernel (naturalRepresentation (Fin 6))
          (subspaceCommutator (naturalRepresentation (Fin 6)) ⊤
            (A.map (Recognition.sourceProjection h e hz hn d))) ⊤ ∧
      (Q d.radical c).relIndex (Z d.radical (alpha d.radical)) =
        Nat.card (A.map (Recognition.sourceProjection h e hz hn d)) ∧
      ∃ (b : Vertex d.radical) (i : d.overgroup →* FreeAmalgam d.radical),
        Function.Injective i ∧ A.map i = Z d.radical (alpha d.radical) ∧ Adjacent d.radical (alpha d.radical) b ∧
        Adjacent d.radical c b ∧ Y.map i = Q d.radical (alpha d.radical) ∧
        (replacementMoved d).map i = U d.radical c ∧
        (omegaCenter d.radical).map i = Z d.radical b ∧
        (pResidual 2 d.overgroup).map i = Ltilde d.radical c ∧
        d.radical.map i = Q d.radical b ∧
        (pCore 2 d.overgroup).map i = Q d.radical c := by
  obtain ⟨b,hab,hcb⟩ := exists_common_neighbor_of_dist_two d.radical (alpha d.radical) c
    (hc.1.trans hb)
  have hc0 := critical_endpoint_color d.radical (alpha d.radical) rfl _ hc
  have hbpos : 0 < criticalDistance d.radical (alpha d.radical)
      ((replacementGeometry h d).exists_critical _ rfl) := by
    change 0 < replacementDistance h d
    omega
  have hcpos : 0 < criticalDistance d.radical c
      ((replacementGeometry h d).exists_critical c hc0) := by
    rw [(replacementGeometry h d).distance_constant c hc0]
    exact hbpos
  obtain ⟨i,hi,hir,hiR,hiQ,hiW,hiL⟩ := edge_coordinates h e hz d hc0 hcb
  let A := (Z d.radical (alpha d.radical)).comap i
  let Y := (Q d.radical (alpha d.radical)).comap i
  have hZX : Z d.radical (alpha d.radical) ≤ X d.radical (alpha d.radical) :=
    (replacementGeometry h d).omega_bound _ rfl hbpos
  have hZQ := hZX.trans (omegaCenter_le _)
  have hQG : Q d.radical (alpha d.radical) ≤ stabilizer d.radical c :=
    DistanceTwo.NaturalCore.Q_le_endpoint_stabilizer hab hcb
  have hAm : A.map i = Z d.radical (alpha d.radical) := by
    rw [map_comap_eq,hir,inf_eq_right.mpr (hZQ.trans hQG)]
  have hYm : Y.map i = Q d.radical (alpha d.radical) := by
    rw [map_comap_eq,hir,inf_eq_right.mpr hQG]
  have hAY : A ≤ Y := comap_mono hZQ
  have hYR : Y ≤ d.radical := by
    apply (map_le_map_iff_of_injective hi).mp
    rw [hYm,hiR]
    exact Q_le_adjacent_h d.radical (DistanceTwo.NaturalCore.edge_color hab) hab
  have hAc : IsElementaryAbelian 2 A := by
    let := Z_elementary_of_positive d.radical (replacementGeometry h d)
      (alpha d.radical) rfl hbpos
    exact IsElementaryAbelian.comap_of_injective (p := 2) i hi _
  have hYA : Y ≤ centralizer (A : Set d.overgroup) := by
    intro y hy a ha
    apply hi
    rw [map_mul,map_mul]
    exact (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical (alpha d.radical) rfl) ha (i y) hy).symm
  have hZcG : Z d.radical c ≤ stabilizer d.radical (alpha d.radical) :=
    critical_Z_le_stabilizer d.radical (replacementGeometry h d)
      (alpha d.radical) rfl hbpos hc
  have hmove : ⁅U d.radical c,Z d.radical (alpha d.radical)⁆ ≤
      Z d.radical (alpha d.radical) :=
    le_normalizer_iff_commutator_le_right.mp
      (((U_le_Z c).trans hZcG).trans (Z_normalized d.radical (alpha d.radical)))
  have hcentral : Y ≤ centralizer
      ((⁅replacementMoved d,A⁆ : Subgroup d.overgroup) : Set d.overgroup) := by
    intro y hy z hzmem
    apply hi
    rw [map_mul,map_mul]
    have hzZ : i z ∈ Z d.radical (alpha d.radical) := by
      apply hmove
      rw [←hiW,←hAm,←map_commutator]
      exact mem_map_of_mem i hzmem
    exact le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical (alpha d.radical) rfl)) hy _ hzZ
  have hne : ¬ A ≤ pCore 2 d.overgroup := by
    intro hle
    apply hc.2
    rw [←hAm,←hiQ]
    exact map_mono hle
  have hproper : ¬ Y ≤ A ⊔ pCore 2 d.overgroup := by
    intro hle
    apply replacement_critical_commutator_not_le h e hz d hb hlarge hc
    apply le_trans _ le_sup_right
    apply commutator_le.mpr
    intro q hq z hzZ
    obtain ⟨y,hy,rfl⟩ := hYm.ge hq
    obtain ⟨a,ha,k,hk,rfl⟩ := mem_sup_of_normal_right.mp (hle hy)
    have hkQ : i k ∈ Q d.radical c := hiQ ▸ mem_map_of_mem i hk
    have hkc : Commute (i k) z :=
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical c hc0)) hkQ z hzZ).symm
    rw [map_mul,commutatorElement_mul_left_eq_conj_mul,hkc.commutator_eq]
    simp only [mul_one,mul_inv_cancel,one_mul]
    exact commutator_mem_commutator (hZX ha)
      ((replacementGeometry h d).omega_bound c hc0 hcpos hzZ)
  refine ⟨A,Y,hAY,hYR,hAc,hYA,hne,hproper,hcentral,
    image_fixes_moved_of_centralizes h e hz hn d A Y hcentral,?_,b,i,hi,hAm,hab,hcb,hYm,hiW,?_,hiL,hiR,hiQ⟩
  · rw [←hAm,←hiQ,relIndex_map_map_of_injective _ _ hi,
      ←Recognition.sourceProjection_kernel h e hz hn d,relIndex_ker]
  · rw [←omegaCenter_map d.radical i hi,hiR]
    simp only [Z,DistanceTwo.NaturalCore.edge_color hab,Bool.true_eq_false,if_false,edgeOmega]

include hn in
/-- Original coordinate interface, retained with its unchanged public type. -/
theorem critical_image_data_coordinates_full
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    {c : Vertex d.radical}
    (hc : CriticalPair d.radical (alpha d.radical) c
      ((replacementGeometry h d).exists_critical _ rfl)) :
    ∃ A Y : Subgroup d.overgroup,
      A ≤ Y ∧ Y ≤ d.radical ∧
      IsElementaryAbelian 2 A ∧
      Y ≤ centralizer (A : Set d.overgroup) ∧
      ¬ A ≤ pCore 2 d.overgroup ∧ ¬ Y ≤ A ⊔ pCore 2 d.overgroup ∧
      Y ≤ centralizer ((⁅replacementMoved d,A⁆ : Subgroup d.overgroup) : Set d.overgroup) ∧
      Y.map (Recognition.sourceProjection h e hz hn d) ≤
        subspaceKernel (naturalRepresentation (Fin 6))
          (subspaceCommutator (naturalRepresentation (Fin 6)) ⊤
            (A.map (Recognition.sourceProjection h e hz hn d))) ⊤ ∧
      (Q d.radical c).relIndex (Z d.radical (alpha d.radical)) =
        Nat.card (A.map (Recognition.sourceProjection h e hz hn d)) ∧
      ∃ (b : Vertex d.radical) (i : d.overgroup →* FreeAmalgam d.radical),
        Function.Injective i ∧ A.map i = Z d.radical (alpha d.radical) ∧ Adjacent d.radical (alpha d.radical) b ∧
        Adjacent d.radical c b ∧ Y.map i = Q d.radical (alpha d.radical) ∧
        (replacementMoved d).map i = U d.radical c ∧
        (omegaCenter d.radical).map i = Z d.radical b ∧
        (pResidual 2 d.overgroup).map i = Ltilde d.radical c := by
  obtain ⟨A,Y,hAY,hYR,hAc,hYA,hne,hproper,hcentral,hfix,hindex,
      b,i,hi,hAm,hab,hcb,hYm,hiW,hiS,hiL,_,_⟩ :=
    critical_image_data_coordinates_with_edge h e hz hn d hb hlarge hc
  exact ⟨A,Y,hAY,hYR,hAc,hYA,hne,hproper,hcentral,hfix,hindex,
    b,i,hi,hAm,hab,hcb,hYm,hiW,hiS,hiL⟩

include hn in
/-- The original critical pair supplies a nontrivial elementary central image
with a strictly larger two-group image fixing its natural displacement.
The equality records the literal relative-index convention. -/
theorem critical_image_data_coordinates
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    {c : Vertex d.radical}
    (hc : CriticalPair d.radical (alpha d.radical) c
      ((replacementGeometry h d).exists_critical _ rfl)) :
    ∃ A Y : Subgroup d.overgroup,
      A ≤ Y ∧ Y ≤ d.radical ∧
      IsElementaryAbelian 2 A ∧
      Y ≤ centralizer (A : Set d.overgroup) ∧
      ¬ A ≤ pCore 2 d.overgroup ∧ ¬ Y ≤ A ⊔ pCore 2 d.overgroup ∧
      Y ≤ centralizer ((⁅replacementMoved d,A⁆ : Subgroup d.overgroup) : Set d.overgroup) ∧
      Y.map (Recognition.sourceProjection h e hz hn d) ≤
        subspaceKernel (naturalRepresentation (Fin 6))
          (subspaceCommutator (naturalRepresentation (Fin 6)) ⊤
            (A.map (Recognition.sourceProjection h e hz hn d))) ⊤ ∧
      (Q d.radical c).relIndex (Z d.radical (alpha d.radical)) =
        Nat.card (A.map (Recognition.sourceProjection h e hz hn d)) ∧
      ∃ (b : Vertex d.radical) (i : d.overgroup →* FreeAmalgam d.radical),
        Function.Injective i ∧ Adjacent d.radical (alpha d.radical) b ∧
        Adjacent d.radical c b ∧ Y.map i = Q d.radical (alpha d.radical) ∧
        (replacementMoved d).map i = U d.radical c ∧
        (omegaCenter d.radical).map i = Z d.radical b := by
  obtain ⟨A,Y,hAY,hYR,hAc,hYA,hne,hproper,hcentral,hfix,hindex,
      b,i,hi,_,hab,hcb,hYm,hiW,hiS,_⟩ :=
    critical_image_data_coordinates_full h e hz hn d hb hlarge hc
  exact ⟨A,Y,hAY,hYR,hAc,hYA,hne,hproper,hcentral,hfix,hindex,
    b,i,hi,hab,hcb,hYm,hiW,hiS⟩

include hn in
/-- The original critical pair supplies a nontrivial elementary central image
with a strictly larger two-group image fixing its natural displacement.
The equality records the literal relative-index convention. -/
theorem critical_image_data
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    {c : Vertex d.radical}
    (hc : CriticalPair d.radical (alpha d.radical) c
      ((replacementGeometry h d).exists_critical _ rfl)) :
    ∃ A Y : Subgroup d.overgroup,
      A ≤ Y ∧ Y ≤ d.radical ∧
      IsElementaryAbelian 2 A ∧
      Y ≤ centralizer (A : Set d.overgroup) ∧
      ¬ A ≤ pCore 2 d.overgroup ∧ ¬ Y ≤ A ⊔ pCore 2 d.overgroup ∧
      Y ≤ centralizer ((⁅replacementMoved d,A⁆ : Subgroup d.overgroup) : Set d.overgroup) ∧
      Y.map (Recognition.sourceProjection h e hz hn d) ≤
        subspaceKernel (naturalRepresentation (Fin 6))
          (subspaceCommutator (naturalRepresentation (Fin 6)) ⊤
            (A.map (Recognition.sourceProjection h e hz hn d))) ⊤ ∧
      (Q d.radical c).relIndex (Z d.radical (alpha d.radical)) =
        Nat.card (A.map (Recognition.sourceProjection h e hz hn d)) := by
  obtain ⟨A,Y,hAY,hYR,hAc,hYA,hne,hproper,hcentral,hfix,hindex,_⟩ :=
    critical_image_data_coordinates h e hz hn d hb hlarge hc
  exact ⟨A,Y,hAY,hYR,hAc,hYA,hne,hproper,hcentral,hfix,hindex⟩

include hn in
/-- On the original characteristic replacement, the non-Frattini branch
leaves exactly the order-two and order-four critical-image alternatives. -/
theorem critical_image_two_or_four
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    {c : Vertex d.radical}
    (hc : CriticalPair d.radical (alpha d.radical) c
      ((replacementGeometry h d).exists_critical _ rfl)) :
    (Q d.radical c).relIndex (Z d.radical (alpha d.radical)) = 2 ∨
      (Q d.radical c).relIndex (Z d.radical (alpha d.radical)) = 4 := by
  obtain ⟨A,Y,hAY,hYR,_,hYA,hne,hproper,_,_,hindex⟩ :=
    critical_image_data h e hz hn d hb hlarge hc
  let q := Recognition.sourceProjection h e hz hn d
  have hkernel : q.ker = pCore 2 d.overgroup := Recognition.sourceProjection_kernel h e hz hn d
  have hp : IsPGroup 2 (Y.map q) :=
    ((replacement_radical_isPGroup h d).of_injective (inclusion hYR) (inclusion_injective _)).map q
  have hcent : Y.map q ≤ centralizer (A.map q : Set (Equiv.Perm (Fin 6))) := by
    rintro _ ⟨y,hy,rfl⟩ a ⟨a,ha,rfl⟩
    exact (map_mul q a y).symm.trans ((congrArg q (hYA hy a ha)).trans (map_mul q y a))
  rw [hindex]
  apply central_proper_image_order _ _ hp (map_mono hAY) ?_ ?_ hcent
  · intro hbot
    exact hne (hkernel ▸ (Subgroup.map_eq_bot_iff A).mp hbot)
  · intro hle
    exact hproper (by simpa only [hkernel] using map_le_map_iff.mp hle)

include hn in
/-- Containment of the actual radical image in a point core excludes the
order-four alternative. Only containment is required; the whole central
cover remains in the commutator calculation. The point-core premise is an
additional local obligation, not a consequence asserted here. -/
theorem critical_image_two_of_point_core
    (t : Equiv.Perm (Fin 6))
    (hpoint : d.radical.map (Recognition.sourceProjection h e hz hn d) ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
        (MulAut.conj t).toMonoidHom)
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    {c : Vertex d.radical}
    (hc : CriticalPair d.radical (alpha d.radical) c
      ((replacementGeometry h d).exists_critical _ rfl)) :
    (Q d.radical c).relIndex (Z d.radical (alpha d.radical)) = 2 := by
  obtain ⟨A,Y,hAY,hYR,_,_,hne,hproper,_,hfix,hindex⟩ :=
    critical_image_data h e hz hn d hb hlarge hc
  let q := Recognition.sourceProjection h e hz hn d
  have hkernel : q.ker = pCore 2 d.overgroup := Recognition.sourceProjection_kernel h e hz hn d
  rw [hindex]
  apply Theory.SpecificGroups.SymmetricSix.BinaryFlags.QuadraticPointCore.card_two_of_centralizes_moved
    (A.map q) (Y.map q) t (map_mono hAY) ((map_mono hYR).trans hpoint)
    hfix
  · intro hbot
    exact hne (hkernel ▸ (Subgroup.map_eq_bot_iff A).mp hbot)
  · intro hle
    exact hproper (by simpa only [hkernel] using map_le_map_iff.mp hle)

include hn in
/-- Application to both fields of the actual local-image interface. The
replacement need not be Sylow, and its image need not be the full point core.
Establishing the displayed point-core containment remains with this owner. -/
theorem localImageData_of_point_core
    (t : Equiv.Perm (Fin 6))
    (hpoint : d.radical.map (Recognition.sourceProjection h e hz hn d) ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
        (MulAut.conj t).toMonoidHom)
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) :
    LocalImageData h d := by
  refine ⟨?_,fun _ hc => critical_image_two_of_point_core h e hz hn d t hpoint hb hlarge hc⟩
  let q := Recognition.sourceProjection h e hz hn d
  let C := Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
    (MulAut.conj t).toMonoidHom
  let := Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore_elementary
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.map _
  have hzero : ⁅d.radical.map q,d.radical.map q⁆ = ⊥ :=
    bot_unique ((commutator_mono hpoint hpoint).trans_eq
      (commutator_self_eq_bot_iff.mpr (inferInstance : IsMulCommutative C)))
  rw [←Recognition.sourceProjection_kernel h e hz hn d]
  apply (Subgroup.map_eq_bot_iff _).mp
  rwa [map_commutator]

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

