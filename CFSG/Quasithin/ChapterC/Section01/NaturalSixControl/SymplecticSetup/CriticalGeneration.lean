module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.CriticalEvenActor
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreEvenGeneration
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.PointFull

/-!
# Generating neighbors for every actual symplectic critical path

A small forward critical image gives a fixed-space bound of codimension at
most one on the reverse natural action. The complete elementary S6 catalogue
then supplies a transposition. A large forward image supplies an even
involution by the existing critical-image bound. For either actor a conjugate
of the marked full point core generates S6. Lifting its even conjugator through
the actual component projection supplies a neighbor whose kernel, together
with the opposite Z-layer, generates the starting vertex stabilizer.

The original edge seed centralizes the opposite Z-layer. Its intersection
with the selected neighbor-kernel centralizer therefore centralizes the whole
starting stabilizer. The SourceData application either produces the original
alternating block or supplies both conclusions, retaining the literal
characteristic replacement and imposing no additional actor or image premise.

These are the generation and kernel-fixer steps used in MS93 (5.5)(a,b),
printed pp.915--917. The later selected backward critical continuation and
terminal exclusion in (5.7)--(5.12) remain separate source arguments.
-/

public section
open Subgroup BinaryPermutation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open CFSG.Quasithin.ChapterC.NaturalSixControl
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup

private theorem exists_swap_of_small_codim (A : Subgroup (Equiv.Perm (Fin 6)))
    (hA : IsElementaryTwo A) (hsmall : fixedCodim Model.rho A ≤ 1) :
    ∃ a ∈ A, a.IsSwap := by
  rcases elementaryTwo_conjugacy hA with h | h | h | h | h | h | h | h | h | h
  · obtain ⟨g,rfl⟩ := h
    refine ⟨(MulAut.conj g) (Equiv.swap 0 1),mem_map_of_mem _ ?_,?_⟩
    · exact (mem_disjointTranspositions_iff (1:Fin 4) _).mpr ⟨1,by decide⟩
    · change (g*Equiv.swap 0 1*g⁻¹).IsSwap
      rw [←Equiv.swap_apply_apply]
      exact ⟨_,_,g.injective.ne (by decide),rfl⟩
  all_goals obtain ⟨g,he⟩ := h; rw [he,fixedCodim_map_conj] at hsmall
  · rw [fixedCodim_A2.2.2.2] at hsmall; omega
  · rw [fixedCodim_D.2.2.2] at hsmall; omega
  · rw [fixedCodim_exceptional.2.2.2] at hsmall; omega
  · rw [fixedCodim_evenPart.2.2.2] at hsmall; omega
  · rw [fixedCodim_plus.2.2.2] at hsmall; omega
  · rw [fixedCodim_double.2.2.2] at hsmall; omega
  · rw [fixedCodim_triple.2.2.2] at hsmall; omega
  · rw [fixedCodim_klein.2.2.2] at hsmall; omega
  · rw [fixedCodim_twisted.2.2.2] at hsmall; omega

namespace Source
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)

theorem exists_swap_reverse_critical_image_of_small {e : Vertex R}
    (p : DistanceEight.PathCentrality.CriticalPath R s.geometry (alpha R) e)
    (hsmall : (Q R e).relIndex (Z R (alpha R)) < 4) :
    ∃ a ∈ ((Z R e).comap (embedM R)).map s.projection, a.IsSwap := by
  let A := (Z R e).comap (embedM R)
  have hAe : A.map (embedM R) = Z R e := map_comap_eq_self
    ((critical_Z_le_stabilizer R s.geometry (alpha R) rfl s.criticalDistance_pos p.critical).trans_eq
      (stabilizer_m_base R))
  have hreverse := critical_reverse R s.geometry s.edgeCentralizerCondition
    (alpha R) rfl s.criticalDistance_pos e p.end_color p.critical
  have hne : A.map s.projection ≠ ⊥ := by
    intro hz
    have hk := (map_eq_bot_iff A).mp hz
    rw [s.projection_kernel] at hk
    have hh := map_mono (f := embedM R) hk
    rw [hAe,←Q_alpha R s.two_group s.core_le] at hh
    exact hreverse.2 hh
  let := s.geometry.Z_elementary s.criticalDistance_pos e p.end_color
  let := IsElementaryAbelian.comap_of_injective (p := 2) (embedM R) (embedM_injective R) (Z R e)
  let := IsElementaryAbelian.map (p := 2) (A := A) s.projection
  have hC : (Q R e).comap (embedM R) ≤ centralizer (A : Set M) := by
    intro x hx a ha
    apply embedM_injective R
    simp only [map_mul]
    exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q R e p.end_color)) hx) (embedM R a) ha
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite (Z R (alpha R)) := Finite.of_injective
    (inclusion (Z_le_stabilizer R (alpha R))) (inclusion_injective _)
  have hindex : (centralizer (A : Set M)).relIndex W < 4 := by
    calc
      (centralizer (A : Set M)).relIndex W ≤
          ((Q R e).comap (embedM R)).relIndex W :=
        relIndex_le_of_le_left hC index_ne_zero_of_finite
      _ = (Q R e).relIndex (W.map (embedM R)) := relIndex_comap (Q R e) (embedM R) W
      _ ≤ (Q R e).relIndex (Z R (alpha R)) :=
        relIndex_le_of_le_right s.module_le_Z index_ne_zero_of_finite
      _ < 4 := hsmall
  have hcodim : fixedCodim Model.rho (A.map s.projection) ≤ 1 := by
    rw [s.fixed_index A] at hindex
    have hh : fixedCodim Model.rho (A.map s.projection) < 2 :=
      (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hindex
    omega
  exact exists_swap_of_small_codim (A.map s.projection) ⟨hne,inferInstance⟩ hcodim
end Source
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup

open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)

omit [Finite M] in
theorem exists_component_conjugate_radical_generates (u : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom)
    (A : Subgroup M) (a : S) (ha : a.IsSwap ∨ orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6))
    (haA : a ∈ A.map s.projection) :
    ∃ g ∈ L, R.map (MulAut.conj g).toMonoidHom ⊔ A = ⊤ := by
  have hfinite : ∃ k : alternatingGroup (Fin 6),
      (pointCore.map (MulAut.conj u).toMonoidHom).map
        (MulAut.conj k.val).toMonoidHom ⊔ zpowers a = ⊤ := by
    rcases ha with ha | ⟨ha,heven⟩
    · exact PointCoreEvenGeneration.exists_even_conjugate_pointCore_generates_swap u a ha
    · exact PointCoreEvenGeneration.exists_even_conjugate_pointCore_generates u ⟨a,heven⟩
        ((Subgroup.orderOf_coe ⟨a,heven⟩).symm.trans ha)
  obtain ⟨k,hk⟩ := hfinite
  have hkL : k.val ∈ L.map s.projection := by rw [s.component_image]; exact k.property
  obtain ⟨g,hg,hgk⟩ := hkL
  refine ⟨g,hg,?_⟩
  have hm : (R.map (MulAut.conj g).toMonoidHom).map s.projection =
      (R.map s.projection).map (MulAut.conj k.val).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change s.projection (g*x*g⁻¹) = k.val*s.projection x*k.val⁻¹
    rw [map_mul,map_mul,map_inv,hgk]
  have hQ : (pCore 2 M).map (MulAut.conj g).toMonoidHom = pCore 2 M :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  have hker : s.projection.ker ≤ R.map (MulAut.conj g).toMonoidHom := by
    rw [s.projection_kernel,←hQ]
    exact map_mono s.core_le
  apply map_injective_of_ker_le s.projection (hker.trans le_sup_left) le_top
  rw [Subgroup.map_sup,hm,hfull]
  have htop : (pointCore.map (MulAut.conj u).toMonoidHom).map
      (MulAut.conj k.val).toMonoidHom ⊔ A.map s.projection = ⊤ := by
    apply top_unique
    rw [←hk]
    exact sup_le_sup_left (zpowers_le.mpr haA) _
  rw [htop]
  exact (map_top_of_surjective s.projection (by
    intro x
    have hx : x ∈ s.projection.range := by
      have hr := map_le_range s.projection (R.map (MulAut.conj g).toMonoidHom ⊔ A)
      rw [Subgroup.map_sup,hm,hfull,htop] at hr
      exact hr (mem_top x)
    exact hx)).symm


/-- A graph neighbor generated with a subgroup having a transposition or even involution image. -/
theorem exists_generating_neighbor_of_actor (u : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom)
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ stabilizer R (alpha R))
    (a : S) (ha : a.IsSwap ∨ orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6))
    (haA : a ∈ (A.comap (embedM R)).map s.projection) :
    ∃ t : Vertex R, Adjacent R (alpha R) t ∧
      Q R t ⊔ A = stabilizer R (alpha R) := by
  obtain ⟨g,hg,hgen⟩ := s.exists_component_conjugate_radical_generates u hfull
    (A.comap (embedM R)) a ha haA
  let f := (embedM R g)⁻¹
  have hf : f ∈ stabilizer R (alpha R) := by
    change f ∈ stabilizer R (mVertex R 1)
    rw [stabilizer_m_base]
    exact ⟨g⁻¹,by simp only [map_inv,f]⟩
  have hfix : act R f (alpha R) = alpha R := hf
  refine ⟨act R f (beta R),?_,?_⟩
  · rw [←hfix]
    exact (adjacent_act_iff R f (alpha R) (beta R)).mpr (base_adjacent R)
  · have hmapA : (A.comap (embedM R)).map (embedM R) = A :=
      map_comap_eq_self (hA.trans_eq (stabilizer_m_base R))
    have hh := congrArg (Subgroup.map (embedM R)) hgen
    rw [Subgroup.map_sup,hmapA,←MonoidHom.range_eq_map] at hh
    rw [Q_act,Q_beta]
    change _ = stabilizer R (mVertex R 1)
    rw [stabilizer_m_base]
    have hmapR : (R.map (embedM R)).map (MulAut.conj f⁻¹).toMonoidHom =
        (R.map (MulAut.conj g).toMonoidHom).map (embedM R) := by
      rw [map_map,map_map]
      congr 1
      apply MonoidHom.ext
      intro x
      change f⁻¹*embedM R x*(f⁻¹)⁻¹=embedM R (g*x*g⁻¹)
      simp only [f,inv_inv,map_mul,map_inv]
    rw [hmapR]
    exact hh

/-- The actual opposite critical layer supplies the actor for the generating neighbor. -/
theorem exists_generating_neighbor_of_large_critical_image
    (h : NativeCentralLayer s) (u : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom)
    {e : Vertex R} (p : DistanceEight.PathCentrality.CriticalPath R s.geometry (alpha R) e)
    (hforward : 4 ≤ (Q R e).relIndex (Z R (alpha R))) :
    ∃ t : Vertex R, Adjacent R (alpha R) t ∧
      Q R t ⊔ Z R e = stabilizer R (alpha R) := by
  obtain ⟨a,haA,ha,heven⟩ := s.exists_even_involution_reverse_critical_image h
    s.criticalDistance_pos p hforward
  apply s.exists_generating_neighbor_of_actor u hfull (Z R e)
    (critical_Z_le_stabilizer R s.geometry (alpha R) rfl s.criticalDistance_pos p.critical)
    a (Or.inr ⟨ha,heven⟩) haA


/-- Every actual critical path admits the generating neighbor in source (5.5)(a).
The small-image branch is a transposition; the large branch supplies an even involution. -/
theorem exists_generating_neighbor (h : NativeCentralLayer s) (u : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom)
    {e : Vertex R} (p : DistanceEight.PathCentrality.CriticalPath R s.geometry (alpha R) e) :
    ∃ t : Vertex R, Adjacent R (alpha R) t ∧
      Q R t ⊔ Z R e = stabilizer R (alpha R) := by
  by_cases hlarge : 4 ≤ (Q R e).relIndex (Z R (alpha R))
  · exact s.exists_generating_neighbor_of_large_critical_image h u hfull p hlarge
  · obtain ⟨a,ha,hswap⟩ := s.exists_swap_reverse_critical_image_of_small p (Nat.lt_of_not_ge hlarge)
    exact s.exists_generating_neighbor_of_actor u hfull (Z R e)
      (critical_Z_le_stabilizer R s.geometry (alpha R) rfl s.criticalDistance_pos p.critical)
      a (Or.inl hswap) ha

/-- The original edge seed fixed by a generating neighbor centralizes the
whole starting vertex group, as in source (5.5)(b). -/
theorem critical_seed_fixer_central_of_generation {e t : Vertex R}
    (p : DistanceEight.PathCentrality.CriticalPath R s.geometry (alpha R) e)
    (hgen : Q R t ⊔ Z R e = stabilizer R (alpha R)) :
    Z R (p.walk.getVert 1) ⊓ centralizer (Q R t : Set (FreeAmalgam R)) ≤
      centralizer (stabilizer R (alpha R) : Set (FreeAmalgam R)) := by
  have hb : 0 < p.walk.length := p.length_eq_b ▸ s.criticalDistance_pos
  have ht : color R (p.walk.getVert 1) ≠ false := by
    intro ht
    have hh := (p.vertex_color (i := 1) (by omega)).mp ht
    norm_num at hh
  have hZe : Z R e ≤ Q R (p.walk.getVert 1) := by
    apply Z_le_Q_of_dist_lt R e (s.geometry.exists_critical e p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,s.geometry.distance_constant e p.end_color]
    change p.walk.length - 1 < s.geometry.b R
    rw [←p.length_eq_b]
    omega
  have hcentral : Z R (p.walk.getVert 1) ≤ centralizer (Z R e : Set (FreeAmalgam R)) := by
    intro x hx z hz
    rw [Z,if_neg ht] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2 z (hZe hz)
  apply le_centralizer_iff.mpr
  rw [←hgen]
  exact sup_le (le_centralizer_iff.mp inf_le_right)
    (le_centralizer_iff.mp (inf_le_left.trans hcentral))

/-- Source (5.5)(a,b) on the same chosen neighbor and original path seed. -/
theorem exists_generating_neighbor_and_seed_fixer (h : NativeCentralLayer s) (u : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom)
    {e : Vertex R} (p : DistanceEight.PathCentrality.CriticalPath R s.geometry (alpha R) e) :
    ∃ t : Vertex R, Adjacent R (alpha R) t ∧
      Q R t ⊔ Z R e = stabilizer R (alpha R) ∧
      Z R (p.walk.getVert 1) ⊓ centralizer (Q R t : Set (FreeAmalgam R)) ≤
        centralizer (stabilizer R (alpha R) : Set (FreeAmalgam R)) := by
  obtain ⟨t,ht,hgen⟩ := s.exists_generating_neighbor h u hfull p
  exact ⟨t,ht,hgen,s.critical_seed_fixer_central_of_generation p hgen⟩

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K]
  {L W : Subgroup K} [L.Normal] [W.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L W T) (h : IntrinsicMSPair d)
local notation "J" => (L ⊔ d.B : Subgroup K)
local notation "R" => d.B.subgroupOf J

/-- The literal characteristic replacement needs no added point-image or actor premise. -/
theorem reducedSource_block_or_generating_neighbor
    (r : CharacteristicReduction (L.subgroupOf J) R) {e : Vertex r.radical}
    (p : DistanceEight.PathCentrality.CriticalPath r.radical
      ((originalSource d h).reduce r).geometry (alpha r.radical) e) :
    IsAlternatingBlock L 6 ∨
    ∃ t : Vertex r.radical, Adjacent r.radical (alpha r.radical) t ∧
      Q r.radical t ⊔ Z r.radical e = stabilizer r.radical (alpha r.radical) ∧
      Z r.radical (p.walk.getVert 1) ⊓ centralizer (Q r.radical t : Set (FreeAmalgam r.radical)) ≤
        centralizer (stabilizer r.radical (alpha r.radical) : Set (FreeAmalgam r.radical)) := by
  rcases reducedSource_block_or_full_point_image d h r with hb | hf
  · exact Or.inl hb
  · exact Or.inr (((originalSource d h).reduce r).exists_generating_neighbor_and_seed_fixer
      (reduced_nativeCentralLayer d h r) d.relabeler.val⁻¹ hf p)
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
