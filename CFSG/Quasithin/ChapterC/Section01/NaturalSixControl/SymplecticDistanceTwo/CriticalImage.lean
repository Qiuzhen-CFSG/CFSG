module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.CriticalImage.Coordinates
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.MovingLayer
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.Critical

/-!
# The distance-two critical image has order two

Choose the representative of the far endpoint's common edge. Conjugating the
original embedding by that representative identifies the edge kernel with
exactly R, the endpoint kernel with O₂(M), and its moving layer with W.
The initial kernel centralizes [W,A], where A is the pulled-back initial
Z-layer. If their quotient images agreed, the initial kernel would lie in
A O₂(M), contradicting the literal critical commutator noncontainment.
The finite quadratic point-core calculation therefore gives image order two.

The actual characteristic replacement application retains its original
projection and relabeler and obtains its moving-layer identification from
the native source theorem. Source: MS93 (3.3)(ii), (3.6), pp.867,871.
-/

public section
open Subgroup Theory.GroupTheory BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

private theorem edge_coordinates (h : NativeCentralLayer s) {c b : Vertex R}
    (hc : color R c = false) (hcb : Adjacent R c b) :
    ∃i : M →* FreeAmalgam R, Function.Injective i ∧
      i.range = stabilizer R c ∧ R.map i = Q R b ∧
      (pCore 2 M).map i = Q R c ∧ W.map i = U R c := by
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common R c b).mp hcb
  · rcases hg with ⟨rfl,rfl⟩
    let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R)
    refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective R),?_,?_,?_,?_⟩
    · have h := stabilizer_act R g (alpha R)
      dsimp only [i]
      rw [MonoidHom.range_comp]
      change (Mbar R).map (MulAut.conj g⁻¹).toMonoidHom = _
      simpa only [alpha,act_mVertex,one_mul,stabilizer_m_base] using h.symm
    · have h := Q_act R g (beta R)
      rw [Q_beta] at h
      simpa only [beta,act_hVertex,one_mul,Q_beta,map_map] using h.symm
    · have h := Q_act R g (alpha R)
      rw [Q_alpha R s.two_group s.core_le] at h
      simpa only [alpha,act_mVertex,one_mul,Q_alpha R s.two_group s.core_le,map_map] using h.symm
    · have he := U_act R g (alpha R)
      rw [h.U_eq_module] at he
      simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
  · rw [hg.1] at hc
    cases hc

theorem critical_image_order_two (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2) {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (hnot : ¬ ⁅Q R (alpha R),Z R c⁆ ≤
      ⁅Q R (alpha R),X R c ⊓ Q R (alpha R)⁆ ⊔ ⁅X R (alpha R),X R c⁆) :
    (Q R c).relIndex (Z R (alpha R)) = 2 := by
  have hc0 := critical_endpoint_color R (alpha R) rfl _ hc
  have hbpos : 0 < criticalDistance R (alpha R) (s.geometry.exists_critical (alpha R) rfl) := by
    change 0 < s.geometry.b R
    omega
  have hcpos : 0 < criticalDistance R c (s.geometry.exists_critical c hc0) := by
    rw [s.geometry.distance_constant c hc0]
    change 0 < s.geometry.b R
    omega
  obtain ⟨i,hi,hir,hiR,hiQ,hiW⟩ := s.edge_coordinates h hc0 hcb
  let A := (Z R (alpha R)).comap i
  let Y := (Q R (alpha R)).comap i
  have hZQ : Z R (alpha R) ≤ Q R (alpha R) :=
    s.Z_le_X.trans (omegaCenter_le _)
  have hQG : Q R (alpha R) ≤ stabilizer R c :=
    DistanceTwo.NaturalCore.Q_le_endpoint_stabilizer hab hcb
  have hAm : A.map i = Z R (alpha R) := by
    rw [map_comap_eq,hir,inf_eq_right.mpr (hZQ.trans hQG)]
  have hYm : Y.map i = Q R (alpha R) := by
    rw [map_comap_eq,hir,inf_eq_right.mpr hQG]
  have hAY : A ≤ Y := comap_mono hZQ
  have hYR : Y ≤ R := by
    apply (map_le_map_iff_of_injective hi).mp
    rw [hYm,hiR]
    exact Q_le_adjacent_h R (DistanceTwo.NaturalCore.edge_color hab) hab
  have hZcG : Z R c ≤ stabilizer R (alpha R) :=
    critical_Z_le_stabilizer R s.geometry (alpha R) rfl hbpos hc
  have hmove : ⁅U R c,Z R (alpha R)⁆ ≤ Z R (alpha R) :=
    le_normalizer_iff_commutator_le_right.mp
      (((U_le_Z c).trans hZcG).trans (Z_normalized R (alpha R)))
  have hcentral : Y ≤ centralizer ((⁅W,A⁆ : Subgroup M) : Set M) := by
    intro y hy d hd
    apply hi
    rw [map_mul,map_mul]
    have hdZ : i d ∈ Z R (alpha R) := by
      apply hmove
      rw [←hiW,←hAm,←map_commutator]
      exact mem_map_of_mem i hd
    exact le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R (alpha R) rfl)) hy _ hdZ
  have hne : ¬ A ≤ pCore 2 M := by
    intro hle
    apply hc.2
    rw [←hAm,←hiQ]
    exact map_mono hle
  have hproper : ¬ Y ≤ A ⊔ pCore 2 M := by
    intro hle
    apply hnot
    apply le_trans _ le_sup_right
    apply commutator_le.mpr
    intro q hq z hz
    obtain ⟨y,hy,rfl⟩ := hYm.ge hq
    obtain ⟨a,ha,k,hk,rfl⟩ := mem_sup_of_normal_right.mp (hle hy)
    have hkQ : i k ∈ Q R c := hiQ ▸ mem_map_of_mem i hk
    have hkc : Commute (i k) z :=
      (le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R c hc0)) hkQ z hz).symm
    rw [map_mul,commutatorElement_mul_left_eq_conj_mul,hkc.commutator_eq]
    simp only [mul_one,mul_inv_cancel,one_mul]
    exact commutator_mem_commutator (s.Z_le_X ha)
      (s.geometry.omega_bound c hc0 hcpos hz)
  have hcard := s.image_card_two_of_centralizes_moved A Y t hAY
    ((map_mono hYR).trans_eq hfull) hcentral hne hproper
  rw [←hAm,←hiQ,relIndex_map_map_of_injective _ _ hi,←s.projection_kernel,relIndex_ker]
  exact hcard

/-- The source noncontainment at any distance-two critical endpoint has
order-two image in the endpoint quotient. -/
theorem critical_image_order_two_of_noncontainment
    (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2) {c : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hnot : ¬ ⁅Q R (alpha R),Z R c⁆ ≤
      ⁅Q R (alpha R),X R c ⊓ Q R (alpha R)⁆ ⊔ ⁅X R (alpha R),X R c⁆) :
    (Q R c).relIndex (Z R (alpha R)) = 2 := by
  obtain ⟨b,hab,hcb⟩ := exists_common_neighbor_of_dist_two R (alpha R) c (hc.1.trans hb)
  exact s.critical_image_order_two h t hfull hb hc hab hcb hnot

/-- Failure of the native Frattini bound supplies the precise source
noncontainment internally. -/
theorem critical_image_order_two_of_core_large
    (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl)) :
    (Q R c).relIndex (Z R (alpha R)) = 2 :=
  s.critical_image_order_two_of_noncontainment h t hfull hb hc
    (s.critical_commutator_not_le hb hlarge hc)

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K]
  {L V : Subgroup K} [L.Normal] [V.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L V T)

/-- The actual characteristic replacement supplies its natural moving layer;
the full-point branch retains its original quotient and relabeler. -/
theorem reducedSource_critical_image_order_two (h : IntrinsicMSPair d)
    (r : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B)))
    (hfull : r.radical.map ((originalSource d h).reduce r).projection =
      pointCore.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom)
    (hb : ((originalSource d h).reduce r).geometry.b r.radical = 2)
    {c : Vertex r.radical}
    (hc : CriticalPair r.radical (alpha r.radical) c
      (((originalSource d h).reduce r).geometry.exists_critical (alpha r.radical) rfl))
    (hnot : ¬ ⁅Q r.radical (alpha r.radical),Z r.radical c⁆ ≤
      ⁅Q r.radical (alpha r.radical),X r.radical c ⊓ Q r.radical (alpha r.radical)⁆ ⊔
      ⁅X r.radical (alpha r.radical),X r.radical c⁆) :
    (Q r.radical c).relIndex (Z r.radical (alpha r.radical)) = 2 :=
  Source.critical_image_order_two_of_noncontainment ((originalSource d h).reduce r)
    (reduced_nativeCentralLayer d h r) d.relabeler.val⁻¹ hfull hb hc hnot

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
