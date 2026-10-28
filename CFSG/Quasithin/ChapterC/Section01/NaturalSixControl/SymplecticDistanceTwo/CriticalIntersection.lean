module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.CriticalIntersection.Coordinates
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.Critical

/-!
# The critical central intersection is the common edge layer

Under the native central-layer identification, an element of Zc intersect Xα
outside Zβ gives an extra fixed vector in Uc, using Zc=Uc Zβ. The full point
core already fixes a line, so the initial kernel acts with fixed codimension
at most two. Its action is quadratic, which puts [Qα,Zc] in Xα. The genuine
large-core premise excludes this by residual detection of the Frattini section.

The last theorem applies to the actual characteristic replacement, retaining
its original projection and relabeler. Source: MS93 (3.6), printed p.871.
-/

public section
open Subgroup Theory.GroupTheory BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement


namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)
include s

private theorem central_edge_coordinates (h : NativeCentralLayer s) {c b : Vertex R}
    (hc : color R c = false) (hcb : Adjacent R c b) :
    ∃i : M →* FreeAmalgam R, Function.Injective i ∧
      i.range = stabilizer R c ∧ R.map i = Q R b ∧
      (omegaCenter R).map i = Z R b ∧
      (W ⊔ omegaCenter R).map i = Z R c := by
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common R c b).mp hcb
  · rcases hg with ⟨rfl,rfl⟩
    let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R)
    have hi : Function.Injective i := (MulAut.conj g⁻¹).injective.comp (embedM_injective R)
    have hiR : R.map i = Q R (hVertex R g) := by
      have he := Q_act R g (beta R)
      rw [Q_beta] at he
      simpa only [beta,act_hVertex,one_mul,Q_beta,map_map] using he.symm
    refine ⟨i,hi,?_,hiR,?_,?_⟩
    · have he := stabilizer_act R g (alpha R)
      dsimp only [i]
      rw [MonoidHom.range_comp]
      change (Mbar R).map (MulAut.conj g⁻¹).toMonoidHom = _
      simpa only [alpha,act_mVertex,one_mul,stabilizer_m_base] using he.symm
    · rw [←omegaCenter_map R i hi,hiR]
      simp only [Z,show color R (hVertex R g) = true from rfl,Bool.true_eq_false,if_false,edgeOmega]
    · have he := Z_act R g (alpha R)
      rw [SymplecticSeed.Z_eq_seedHull,s.seedHull_eq_module_sup_seed h] at he
      simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
  · rw [hg.1] at hc
    cases hc

/-- An extra central vector in the opposite endpoint would make its whole
commutator central in the initial kernel. -/
theorem critical_commutator_le_X_of_intersection_escape
    (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2) {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (hescape : ¬ Z R c ⊓ X R (alpha R) ≤ Z R b) :
    ⁅Q R (alpha R),Z R c⁆ ≤ X R (alpha R) := by
  have hc0 := critical_endpoint_color R (alpha R) rfl _ hc
  have hb0 := DistanceTwo.NaturalCore.edge_color hab
  obtain ⟨i,hi,hir,hiR,hiS,hiH⟩ := s.central_edge_coordinates h hc0 hcb
  let Y := (Q R (alpha R)).comap i
  have hQG : Q R (alpha R) ≤ stabilizer R c :=
    DistanceTwo.NaturalCore.Q_le_endpoint_stabilizer hab hcb
  have hYm : Y.map i = Q R (alpha R) := by
    rw [map_comap_eq,hir,inf_eq_right.mpr hQG]
  have hYR : Y ≤ R := by
    apply (map_le_map_iff_of_injective hi).mp
    rw [hYm,hiR]
    exact Q_le_adjacent_h R hb0 hab
  have hfixed : ¬ W ⊓ centralizer (Y : Set M) ≤ omegaCenter R := by
    intro hle
    apply hescape
    rintro z ⟨hz,hzX⟩
    obtain ⟨x,hx,rfl⟩ := hiH.ge hz
    obtain ⟨w,hw,u,hu,rfl⟩ := mem_sup_of_normal_left.mp hx
    have hwf : w ∈ centralizer (Y : Set M) := by
      intro y hy
      have huy := (mem_omegaCenter_iff.mp hu).2.2 y (hYR hy)
      have hxy : y*(w*u) = (w*u)*y := by
        apply hi
        simpa only [map_mul] using
          (mem_omegaCenter_iff.mp hzX).2.2 (i y) hy
      apply mul_right_cancel (b := u)
      calc y*w*u = y*(w*u) := mul_assoc _ _ _
           _ = (w*u)*y := hxy
           _ = w*y*u := by rw [mul_assoc,←huy,←mul_assoc]
    rw [←hiS]
    exact mem_map_of_mem i (mul_mem (hle ⟨hw,hwf⟩) hu)
  have hmove := s.module_commutator_le_centralizer_of_fixed_escape Y hYR t hfull hfixed
  have hwhole : ⁅W ⊔ omegaCenter R,Y⁆ ≤ centralizer (Y : Set M) := by
    apply commutator_le.mpr
    intro x hx y hy
    obtain ⟨w,hw,u,hu,rfl⟩ := mem_sup_of_normal_left.mp hx
    have huy : Commute u y := ((mem_omegaCenter_iff.mp hu).2.2 y (hYR hy)).symm
    rw [commutatorElement_mul_left_eq_conj_mul,huy.commutator_eq]
    simp only [mul_one,mul_inv_cancel,one_mul]
    exact hmove (commutator_mem_commutator hw hy)
  have hcentral : ⁅Q R (alpha R),Z R c⁆ ≤ centralizer (Q R (alpha R) : Set (FreeAmalgam R)) := by
    rw [commutator_comm,←hiH,←hYm,←map_commutator]
    rintro z ⟨x,hx,rfl⟩ q hq
    obtain ⟨y,hy,rfl⟩ := hq
    simpa only [map_mul] using congrArg i (hwhole hx y hy)
  intro x hx
  apply mem_omegaCenter_iff.mpr
  exact ⟨DistanceTwo.NaturalCore.local_commutator_le_Q s.geometry hb hc hx,
    DistanceTwo.NaturalCore.local_commutator_pow_two s.geometry hb hc hab hcb hx,hcentral hx⟩

/-- In the genuine large-core branch the opposite central layer meets X-alpha
in exactly the common edge layer. -/
theorem critical_Z_inf_X_eq_edge
    (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b) :
    Z R c ⊓ X R (alpha R) = Z R b := by
  apply le_antisymm
  · by_contra hne
    apply hlarge
    exact s.core_le_frattini_of_critical_commutator_le hb hc
      ((s.critical_commutator_le_X_of_intersection_escape h t hfull hb hc hab hcb hne).trans le_sup_right)
  · have hb0 := DistanceTwo.NaturalCore.edge_color hab
    have hc0 := critical_endpoint_color R (alpha R) rfl _ hc
    have hba : Z R b ≤ Z R (alpha R) := by
      simp only [Z,show color R (alpha R) = false from rfl,hb0,
        Bool.true_eq_false,if_true,if_false]
      exact le_iSup_of_le b (le_iSup_of_le hab le_rfl)
    have hbc : Z R b ≤ Z R c := by
      simp only [Z,hc0,hb0,Bool.true_eq_false,if_true,if_false]
      exact le_iSup_of_le b (le_iSup_of_le hcb le_rfl)
    exact le_inf hbc (hba.trans s.Z_le_X)
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K]
  {L V : Subgroup K} [L.Normal] [V.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L V T)

/-- The actual characteristic replacement uses its original projection and
relabeler, and supplies the native central layer internally. -/
theorem reducedSource_critical_Z_inf_X_eq_edge (h : IntrinsicMSPair d)
    (r : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B)))
    (hfull : r.radical.map ((originalSource d h).reduce r).projection =
      pointCore.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom)
    (hb : ((originalSource d h).reduce r).geometry.b r.radical = 2)
    (hlarge : ¬ core r.radical (alpha r.radical) ≤
      (frattini (Q r.radical (alpha r.radical))).map (Q r.radical (alpha r.radical)).subtype ⊔
        X r.radical (alpha r.radical))
    {c b : Vertex r.radical}
    (hc : CriticalPair r.radical (alpha r.radical) c
      (((originalSource d h).reduce r).geometry.exists_critical (alpha r.radical) rfl))
    (hab : Adjacent r.radical (alpha r.radical) b) (hcb : Adjacent r.radical c b) :
    Z r.radical c ⊓ X r.radical (alpha r.radical) = Z r.radical b :=
  Source.critical_Z_inf_X_eq_edge ((originalSource d h).reduce r)
    (reduced_nativeCentralLayer d h r) d.relabeler.val⁻¹ hfull hb hlarge hc hab hcb

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
