module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.Graph
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.EdgeCentrality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.SectionFive.NoncentralPair

/-!
# Radius structure on the original exceptional graph

The incident edge radius is abelian and normally generates the full radius.
The original component and radical generate the vertex group, so the
residual fixed-or-covering alternative forces [V,Q] to centralize V.
Conversely, noncentrality selects a critical pair with image order at least
four: image orders one and two would make the mixed triple commutator vanish.

All pullbacks use the original factor embedding. The radical is not assumed
Sylow, and neither the cubic kernel nor the full moving cover is replaced.
CubicCentrality combines this structure with the cubic chief-factor budget
and the actual reverse actor. This adapts the corresponding natural-branch
RadiusStructure and RadiusGeometry proofs to the original exceptional pair.
Source: MS93 (5.2)(ii), printed pp.914--915.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.NaturalSixControl
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R}
local notation "T" => edge L R
omit [Finite G] in
include h in
private theorem component_sup_radical_eq_top : (L.subgroupOf (L ⊔ R)) ⊔ T = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨k,hk,t,ht,rfl⟩ := h.relative_product g
  exact mul_mem (mem_sup_left hk) (mem_sup_right ht)

omit [Finite G] in
private theorem adjacent_seed_le_radius {a t : Vertex T}
    (hat : Adjacent T a t) : Z T a ≤ V T t := by
  apply le_iSup_of_le a
  exact le_iSup_of_le
    (show (cosetGraph T).dist a t ≤ 2 from
      (SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj T _ _).mpr hat)).le.trans (by decide)) le_rfl

omit [Finite G] in
private theorem comap_normal_of_base_normalized (N : Subgroup (FreeAmalgam T))
    (hN : stabilizer T (alpha T) ≤ normalizer (N : Set (FreeAmalgam T))) :
    (N.comap (embedM T)).Normal := by
  refine ⟨?_⟩
  intro x hx g
  change embedM T (g * x * g⁻¹) ∈ N
  rw [map_mul, map_mul, map_inv]
  have hg : embedM T g ∈ stabilizer T (alpha T) := by
    rw [show alpha T = mVertex T 1 from rfl, stabilizer_m_base]
    exact ⟨g, rfl⟩
  exact le_normalizer_iff.mp hN _ hg _ hx

omit [Finite G] in
private theorem map_comap_of_le_base (N : Subgroup (FreeAmalgam T))
    (hN : N ≤ stabilizer T (alpha T)) : (N.comap (embedM T)).map (embedM T) = N := by
  rw [map_comap_eq]
  apply inf_eq_right.mpr
  change N ≤ stabilizer T (mVertex T 1) at hN
  rwa [stabilizer_m_base] at hN

omit [Finite G] in
private theorem base_normalizes_image (N : Subgroup (L ⊔ R : Subgroup G)) [N.Normal] :
    stabilizer T (alpha T) ≤ normalizer (N.map (embedM T) : Set (FreeAmalgam T)) := by
  rw [show alpha T = mVertex T 1 from rfl, stabilizer_m_base]
  change (embedM T).range ≤ _
  rw [MonoidHom.range_eq_map]
  simpa only [normalizer_eq_top] using N.le_normalizer_map (embedM T)


omit [Finite G] in
/-- The original local group normalizes its radius preimage. -/
theorem radius_comap_normal : ((V T (alpha T)).comap (embedM T)).Normal :=
  comap_normal_of_base_normalized _ (V_normalized _)

theorem radius_comap_map (hb : 2 < (sourceGeometry h).b T) :
    ((V T (alpha T)).comap (embedM T)).map (embedM T) = V T (alpha T) :=
  map_comap_of_le_base _ ((sourceGeometry h).V_local _ rfl hb)

theorem edge_radius_comap_map (hb : 2 < (sourceGeometry h).b T) :
    ((V T (beta T)).comap (embedM T)).map (embedM T) = V T (beta T) :=
  map_comap_of_le_base _ ((edge_radius_le_radius rfl (base_adjacent T)).trans
    ((sourceGeometry h).V_local _ rfl hb))

/-- Normal generation in the literal original vertex group, through embedM. -/
theorem radius_comap_eq_normalClosure_edge (hb : 2 < (sourceGeometry h).b T) :
    (V T (alpha T)).comap (embedM T) =
      normalClosure ((V T (beta T)).comap (embedM T) : Set (L ⊔ R : Subgroup G)) := by
  let V₀ := (V T (alpha T)).comap (embedM T)
  let E := (V T (beta T)).comap (embedM T)
  let := radius_comap_normal (L := L) (R := R)
  apply le_antisymm
  · have hV : V T (alpha T) ≤ (normalClosure (E : Set (L ⊔ R : Subgroup G))).map (embedM T) := by
      apply CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.radius_le_of_normalized_edge rfl (base_adjacent T)
      · change V T (beta T) ≤ _
        rw [←edge_radius_comap_map (h := h)  hb]
        exact map_mono le_normalClosure
      · exact base_normalizes_image _
    have h := comap_mono (f := embedM T) hV
    rwa [comap_map_eq_self_of_injective (embedM_injective T)] at h
  · apply normalClosure_le_normal
    exact comap_mono (f := embedM T) (edge_radius_le_radius rfl (base_adjacent T))

/-- The original radical normalizes the edge radius in the original vertex group. -/
theorem radical_normalizes_edge_radius_comap :
    T ≤ normalizer ((V T (beta T)).comap (embedM T) : Set (L ⊔ R : Subgroup G)) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  change embedM T (g*x*g⁻¹) ∈ V T (beta T)
  rw [map_mul,map_mul,map_inv]
  have hr' : embedM T g ∈ stabilizer T (beta T) := by
    have hq : embedM T g ∈ Q T (beta T) := by
      rw [Q_beta]
      exact mem_map_of_mem _ hg
    exact hq.1
  exact le_normalizer_iff.mp (V_normalized (beta T)) _ hr' _ hx

/-- The actual component–radical product supplies the edge-plus-moving cover. -/
theorem radius_comap_le_edge_sup_commutator (hb : 2 < (sourceGeometry h).b T) :
    (V T (alpha T)).comap (embedM T) ≤
      (V T (beta T)).comap (embedM T) ⊔ ⁅(V T (alpha T)).comap (embedM T), ((L.subgroupOf (L ⊔ R)))⁆ := by
  let := h.relative_normal
  let V₀ := (V T (alpha T)).comap (embedM T)
  let E := (V T (beta T)).comap (embedM T)
  let := radius_comap_normal (L := L) (R := R)
  have hEV : E ≤ V₀ := comap_mono (f := embedM T)
    (edge_radius_le_radius rfl (base_adjacent T))
  let D := E ⊔ ⁅V₀,((L.subgroupOf (L ⊔ R)))⁆
  let : D.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [←(component_sup_radical_eq_top (h := h) )]
    apply sup_le
    · exact le_normalizer_sup_of_commutator_le V₀ ((L.subgroupOf (L ⊔ R))) E ⁅V₀,((L.subgroupOf (L ⊔ R)))⁆ hEV le_rfl
    · exact (le_inf (radical_normalizes_edge_radius_comap ) le_normalizer_of_normal).trans
        (normalizer_inf_normalizer_le_normalizer_sup E ⁅V₀,((L.subgroupOf (L ⊔ R)))⁆)
  calc
    V₀ = normalClosure (E : Set (L ⊔ R : Subgroup G)) := radius_comap_eq_normalClosure_edge (h := h)  hb
    _ ≤ D := normalClosure_le_normal (show E ≤ D from le_sup_left)


/-- The source residual dichotomy forces centrality of the actual radius
commutator. All normality and edge-generation hypotheses are proved from the original pair. -/
theorem radius_commutator_central_of_residual_dichotomy (hb : 2 < (sourceGeometry h).b T)
    (hd : ⁅⁅V T (alpha T), Q T (alpha T)⁆, Ltilde T (alpha T)⁆ ≤ Z T (alpha T) ∨
      ⁅V T (alpha T), Ltilde T (alpha T)⁆ ≤ ⁅V T (alpha T), Q T (alpha T)⁆ ⊔ Z T (alpha T)) :
    ⁅V T (alpha T), Q T (alpha T)⁆ ≤ centralizer (V T (alpha T) : Set (FreeAmalgam T)) := by
  let := h.relative_normal
  let f := embedM T
  let V₀ := (V T (alpha T)).comap f
  let E := (V T (beta T)).comap f
  let Z₀ := (Z T (alpha T)).comap f
  let P := pCore 2 (L ⊔ R : Subgroup G)
  let := radius_comap_normal (L := L) (R := R)
  let := SymplecticSeed.Z_comap_normal T
  have hVm : V₀.map f = V T (alpha T) := radius_comap_map (h := h)  hb
  have hEm : E.map f = V T (beta T) := edge_radius_comap_map (h := h)  hb
  have hZm : Z₀.map f = Z T (alpha T) := map_comap_of_le_base _
    ((Z_le_VBall T (alpha T) 2).trans ((sourceGeometry h).V_local _ rfl hb))
  have hPm : P.map f = Q T (alpha T) := (Q_alpha T (h.relative_radical.isPGroup) (h.relative_radical.twoCore_le)).symm
  have hLm : ((L.subgroupOf (L ⊔ R))).map f = Ltilde T (alpha T) := by rw [Ltilde_alpha,(h.relative_residual)]
  have hVP : V₀ ≤ P := by
    have hbound := comap_mono (f := f) ((sourceGeometry h).V_le_Q hb (alpha T) rfl)
    rwa [Q_alpha_comap T (h.relative_radical.isPGroup) (h.relative_radical.twoCore_le)] at hbound
  have hEV : E ≤ V₀ := comap_mono (f := f)
    (edge_radius_le_radius rfl (base_adjacent T))
  have hZE : Z₀ ≤ E := comap_mono (f := f) (adjacent_seed_le_radius (base_adjacent T))
  have hE : E ≤ centralizer (E : Set (L ⊔ R : Subgroup G)) := by
    have hc := le_centralizer_iff_isMulCommutative.mpr
      (edge_radius_commutative (sourceGeometry h) hb (alpha T) (beta T) rfl (base_adjacent T))
    intro x hx y hy
    apply embedM_injective T
    simpa only [map_mul] using hc hx (f y) hy
  have hcentral : ⁅V₀,P⁆ ≤ centralizer (V₀ : Set (L ⊔ R : Subgroup G)) := by
    rcases hd with hd | hd
    · have hfixed : ⁅⁅V₀,P⁆,((L.subgroupOf (L ⊔ R)))⁆ ≤ Z₀ := by
        apply (map_le_map_iff_of_injective (embedM_injective T)).mp
        rwa [map_commutator,map_commutator,hVm,hPm,hLm,hZm]
      exact edge_commutator_central_of_residual_fixed V₀ P E Z₀ ((L.subgroupOf (L ⊔ R))) T
        (radius_comap_eq_normalClosure_edge (h := h)  hb) hEV hZE
        (radical_normalizes_edge_radius_comap ) (h.relative_radical.twoCore_le) (component_sup_radical_eq_top (h := h) ) hE hfixed
    · have hcover : ⁅V₀,((L.subgroupOf (L ⊔ R)))⁆ ≤ E ⊔ ⁅V₀,P⁆ := by
        have hc : ⁅V₀,((L.subgroupOf (L ⊔ R)))⁆ ≤ ⁅V₀,P⁆ ⊔ Z₀ := by
          apply (map_le_map_iff_of_injective (embedM_injective T)).mp
          rwa [map_commutator,Subgroup.map_sup,map_commutator,hVm,hPm,hLm,hZm]
        exact hc.trans (sup_le le_sup_right (hZE.trans le_sup_left))
      exact edge_commutator_central_of_residual_cover V₀ P E ((L.subgroupOf (L ⊔ R))) hVP (hEV.trans hVP)
        (pCore_isPGroup (p := 2) (G := (L ⊔ R : Subgroup G))).isNilpotent
        ((h.relative_radical.twoCore_le).trans (radical_normalizes_edge_radius_comap )) hE
        (radius_comap_le_edge_sup_commutator (h := h)  hb) hcover
  rw [←hVm,←hPm,←map_commutator]
  exact (map_mono hcentral).trans (map_centralizer_le_centralizer_image (V₀ : Set (L ⊔ R : Subgroup G)) f)


end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.NaturalSixControl
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R}
local notation "T" => edge L R
theorem noncentral_generator_image_four_le (hb : 2 < (sourceGeometry h).b T)
    (a d e : Vertex T) (ha : color T a = false)
    (hd : color T d = false) (he : color T e = false)
    (hda : (cosetGraph T).dist d a ≤ 2) (hea : (cosetGraph T).dist e a ≤ 2)
    (hne : ⁅⁅Z T d,Q T a⁆,Z T e⁆ ≠ ⊥) :
    4 ≤ (Q T e).relIndex (Z T d) := by
  have hnZd : Q T a ≤ normalizer (Z T d : Set (FreeAmalgam T)) :=
    (Q_le_stabilizer_of_dist_le_two a d ha hd
      (by rwa [SimpleGraph.dist_comm])).trans (Z_normalized T d)
  have hnQe : Q T a ≤ normalizer (Q T e : Set (FreeAmalgam T)) :=
    (Q_le_stabilizer_of_dist_le_two a e ha he
      (by rwa [SimpleGraph.dist_comm])).trans (Q_normalized T e)
  have hout := CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionFive.noncentral_generator_not_le T (sourceGeometry h) a d e ha he hea hne
  have hone : (Q T e).relIndex (Z T d) ≠ 1 := fun hh => hout (relIndex_eq_one.mp hh)
  have htwo : (Q T e).relIndex (Z T d) ≠ 2 := by
    intro hh
    have hnint : Q T a ≤ normalizer ((Z T d ⊓ Q T e : Subgroup (FreeAmalgam T)) : Set (FreeAmalgam T)) := by
      intro q hq
      rw [mem_normalizer_iff_map_conj_eq,Subgroup.map_inf _ _ _ (MulAut.conj q).injective,
        mem_normalizer_iff_map_conj_eq.mp (hnZd hq),
        mem_normalizer_iff_map_conj_eq.mp (hnQe hq)]
    have hc := commutator_le_of_normalized_index_two (Z T d) (Z T d ⊓ Q T e)
      (Q T a) inf_le_left (by rwa [inf_relIndex_left]) hnZd hnint
    apply hne
    apply le_bot_iff.mp
    exact (commutator_mono (hc.trans inf_le_right) le_rfl).trans (by
      rw [commutator_comm,(sourceGeometry h).centralizes e he])
  have hZdV : Z T d ≤ V T a := le_iSup_of_le d (le_iSup_of_le hda le_rfl)
  have hp : IsPGroup 2 (Z T d) :=
    (Q_isPGroup T (h.relative_radical.isPGroup) (h.relative_radical.twoCore_le) a ha).to_le (hZdV.trans (V_le_Q T ha hb))
  let : Finite (stabilizer T a) := finite_stabilizer T a
  have hZa : Z T d ≤ stabilizer T a :=
    (hZdV.trans (V_le_Q T ha hb)).trans (fun _ hx => hx.1)
  let : Finite (Z T d) := Finite.of_injective (inclusion hZa) (inclusion_injective hZa)
  obtain ⟨n,hn⟩ := hp.index ((Q T e).subgroupOf (Z T d))
  change (Q T e).relIndex (Z T d) = 2^n at hn
  have hn2 : 2 ≤ n := by
    by_contra h
    have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl <;> simp_all
  rw [hn]
  exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn2

theorem exists_noncentral_critical_pair_large_image (hb : (sourceGeometry h).b T = 4)
    (a : Vertex T) (ha : color T a = false)
    (hn : ¬ ⁅V T a,Q T a⁆ ≤ centralizer (V T a : Set (FreeAmalgam T))) :
    ∃ d e, color T d = false ∧ color T e = false ∧
      (cosetGraph T).dist d a = 2 ∧ (cosetGraph T).dist e a = 2 ∧
      ⁅⁅Z T d,Q T a⁆,Z T e⁆ ≠ ⊥ ∧ 4 ≤ (Q T e).relIndex (Z T d) ∧
      ∃ hd : color T d = false,CriticalPair T d e ((sourceGeometry h).exists_critical d hd) := by
  obtain ⟨d,e,hd,he,hda,hea,ht,hcrit⟩ :=
    CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionFive.exists_noncentral_critical_pair T (sourceGeometry h) hb a ha hn
  exact ⟨d,e,hd,he,hda,hea,ht,
    noncentral_generator_image_four_le (h := h)  (by omega) a d e ha hd he hda.le hea.le ht,hcrit⟩


/-- Noncentrality supplies a large-image critical path based at the original
vertex, using the actual graph conjugation. -/
theorem exists_base_large_critical_path
    (hb : (sourceGeometry h).b T = 4)
    (hn : ¬ ⁅V T (alpha T),Q T (alpha T)⁆ ≤
      centralizer (V T (alpha T) : Set (FreeAmalgam T))) :
    ∃ e, ∃ _p : CriticalPath T (sourceGeometry h) (alpha T) e,
      4 ≤ (Q T e).relIndex (Z T (alpha T)) := by
  obtain ⟨d,e,hd,_,_,_,_,hlarge,hd',hpair⟩ :=
    exists_noncentral_critical_pair_large_image (h := h)  hb (alpha T) rfl hn
  obtain ⟨g,hdg⟩ := exists_mVertex_of_color T hd
  have hf : act T g⁻¹ d = alpha T := by
    rw [hdg,act_mVertex]
    simp only [mul_inv_cancel]
    rfl
  have hfcol : color T (act T g⁻¹ d) = false := by rw [hf]; rfl
  have hcrit : CriticalPair T (alpha T) (act T g⁻¹ e)
      ((sourceGeometry h).exists_critical (alpha T) rfl) := by
    simpa only [hf] using (criticalPair_act_iff T g⁻¹ d e
      ((sourceGeometry h).exists_critical d hd')
      ((sourceGeometry h).exists_critical (act T g⁻¹ d) hfcol)).mpr hpair
  refine ⟨act T g⁻¹ e,CriticalPath.ofPair rfl hcrit,?_⟩
  rw [←hf,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj (g⁻¹)⁻¹).injective]
  exact hlarge
end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
