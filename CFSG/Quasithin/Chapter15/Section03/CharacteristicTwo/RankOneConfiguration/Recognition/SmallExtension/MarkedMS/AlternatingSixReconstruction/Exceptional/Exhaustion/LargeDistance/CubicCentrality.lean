module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicChief
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicRadiusStructure
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicCriticalActor
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicRadius

/-!
# The remaining cubic radius centrality obstruction

Apply the chief-factor budget to the actual radius pulled back through the
original factor embedding. An even marked subactor of the reverse seed,
together with its commutator control, gives the residual dichotomy; abelian
edge generation forces radius centrality. The source index-eight premise
is discharged on the actual critical path.

If centrality fails, the distance is four and an actual critical path has
both seed images of order at least four. Every reverse subactor with an
even marked involution must then fail the required commutator control.
This preserves the source's option of a proper restricted seed. Otherwise
centrality, derived-layer containment and the critical triple-commutator
identity hold at every component vertex. These conclusions feed the entire
intrinsic-core and literal rank-two alternatives.

Constructing the source restricted actor and its commutator control, excluding
the terminal paths, and assembling the natural and exceptional whole-core
outcomes remain with qt-e-ms-small-a6-reconstruction. This is not yet the
unconditional reconstruction or an unconditional radius-centrality theorem.
Source: MS93 (5.2), printed pp.914--915; C.1.31--32, pp.135--136.
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
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "T" => edge L R
local notation "π" => CubicAction.projection h e hz hk
omit [Finite G] in
private theorem normalized_comap_normal (J : Subgroup (FreeAmalgam T))
    (hJ : stabilizer T (alpha T) ≤ normalizer (J : Set (FreeAmalgam T))) :
    (J.comap (embedM T)).Normal := by
  constructor
  intro n hn g
  change embedM T (g*n*g⁻¹) ∈ J
  rw [map_mul,map_mul,map_inv]
  exact (le_normalizer_iff.mp hJ (embedM T g)
    (by change embedM T g ∈ stabilizer T (mVertex T 1); rw [stabilizer_m_base]; exact ⟨g,rfl⟩)) _ hn

/-- The S6 chief-factor dichotomy on the literal radius, transported through
its source embedding. -/
theorem radius_residual_dichotomy_of_index
    (hb : 2 < sourceDistance h)
    (A K : Subgroup (FreeAmalgam T))
    (hA : A ≤ stabilizer T (alpha T))
    (a : Equiv.Perm (Fin 6)) (ha : orderOf a = 2)
    (heven : a ∈ alternatingGroup (Fin 6))
    (haA : a ∈ (A.comap (embedM T)).map π)
    (hc : ⁅V T (alpha T) ⊓ K,A⁆ ≤ Z T (alpha T))
    (hindex : K.relIndex (V T (alpha T)) ≤ 8) :
    ⁅⁅V T (alpha T),Q T (alpha T)⁆,Ltilde T (alpha T)⁆ ≤ Z T (alpha T) ∨
      ⁅V T (alpha T),Ltilde T (alpha T)⁆ ≤
        ⁅V T (alpha T),Q T (alpha T)⁆ ⊔ Z T (alpha T) := by
  let f := embedM T
  let V₀ := (V T (alpha T)).comap f
  let Z₀ := (Z T (alpha T)).comap f
  let A₀ := A.comap f
  let K₀ := K.comap f
  let : V₀.Normal := normalized_comap_normal _ (V_normalized (alpha T))
  let : Z₀.Normal := normalized_comap_normal _ (Z_normalized T (alpha T))
  have hVQ : V T (alpha T) ≤ Q T (alpha T) := V_le_Q T rfl hb
  have hVrange : V T (alpha T) ≤ f.range :=
    (hVQ.trans (fun _ hx => hx.1)).trans_eq (stabilizer_m_base T)
  have hZV : Z T (alpha T) ≤ V T (alpha T) := by
    apply le_iSup_of_le (alpha T)
    exact le_iSup_of_le (by simp) le_rfl
  have hVm : V₀.map f = V T (alpha T) := by
    rw [map_comap_eq,inf_eq_right.mpr hVrange]
  have hZm : Z₀.map f = Z T (alpha T) := by
    rw [map_comap_eq,inf_eq_right.mpr (hZV.trans hVrange)]
  have hAm : A₀.map f = A := by
    rw [map_comap_eq]
    exact inf_eq_right.mpr (hA.trans_eq (stabilizer_m_base T))
  have hVcore : V₀ ≤ pCore 2 (L ⊔ R : Subgroup G) := by
    apply (map_le_map_iff_of_injective (embedM_injective T)).mp
    rw [hVm,←Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    exact hVQ
  have hc₀ : ⁅V₀ ⊓ K₀,A₀⁆ ≤ Z₀ := by
    apply (map_le_map_iff_of_injective (embedM_injective T)).mp
    rw [map_commutator,Subgroup.map_inf _ _ _ (embedM_injective T),hVm,hAm,hZm]
    exact (commutator_mono (inf_le_inf_left _ (map_comap_le _ _)) le_rfl).trans hc
  have hi₀ : K₀.relIndex V₀ ≤ 8 := by
    rw [relIndex_comap,hVm]
    exact hindex
  have hh := core_commutator_residual_dichotomy_of_index h e hz hk
    V₀ Z₀ (comap_mono hZV) hVcore A₀ a ha heven haA K₀ hc₀ hi₀
  have hQm : (pCore 2 (L ⊔ R : Subgroup G)).map f = Q T (alpha T) := by
    rw [Q_alpha T (h.relative_radical.isPGroup) (h.relative_radical.twoCore_le)]
  have hLm : (pResidual 2 (L ⊔ R : Subgroup G)).map f = Ltilde T (alpha T) := (Ltilde_alpha T).symm
  rcases hh with hh | hh
  · left
    have hh := map_mono (f := f) hh
    rwa [map_commutator,map_commutator,hVm,hQm,hLm,hZm] at hh
  · right
    have hh := map_mono (f := f) hh
    rwa [map_commutator,Subgroup.map_sup,map_commutator,hVm,hLm,hQm,hZm] at hh

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "T" => edge L R
local notation "π" => CubicAction.projection h e hz hk

/-- The chief-factor and index bounds apply to the actual restricted reverse
seed as soon as it has an even involution and the source commutator control.
The actor may be a proper subgroup of the full reverse Z-layer. -/
theorem critical_radius_central_of_marked_subactor {c : Vertex T}
    (p : CriticalPath T (sourceGeometry h) (alpha T) c)
    (A : Subgroup (FreeAmalgam T)) (hA : A ≤ Z T c)
    (a : Equiv.Perm (Fin 6)) (ha : orderOf a = 2)
    (heven : a ∈ alternatingGroup (Fin 6))
    (haA : a ∈ (A.comap (embedM T)).map π)
    (hc : ⁅V T (alpha T) ⊓ Q T (p.walk.getVert (p.walk.length-2)),A⁆ ≤
      Z T (alpha T)) :
    ⁅V T (alpha T),Q T (alpha T)⁆ ≤
      centralizer (V T (alpha T) : Set (FreeAmalgam T)) := by
  apply radius_commutator_central_of_residual_dichotomy (h := h) (distance_gt_two h e hz hk)
  apply radius_residual_dichotomy_of_index h e hz hk (distance_gt_two h e hz hk)
    A (Q T (p.walk.getVert (p.walk.length-2)))
    (hA.trans (critical_Z_le_stabilizer T (sourceGeometry h) (alpha T) rfl
      (sourceDistance_pos h) p.critical)) a ha heven haA hc
  exact critical_radius_image_index_le_eight h e hz hk p

include h e hz hk in
/-- The actual index-eight bound and the full reverse seed's even involution
give a sufficient full-seed specialization of the restricted-actor theorem.
The source may use a proper restricted seed instead. -/
theorem critical_radius_central_of_commutator {c : Vertex T}
    (p : CriticalPath T (sourceGeometry h) (alpha T) c)
    (hforward : 4 ≤ (Q T c).relIndex (Z T (alpha T)))
    (hc : ⁅V T (alpha T) ⊓ Q T (p.walk.getVert (p.walk.length-2)),Z T c⁆ ≤
      Z T (alpha T)) :
    ⁅V T (alpha T),Q T (alpha T)⁆ ≤
      centralizer (V T (alpha T) : Set (FreeAmalgam T)) := by
  obtain ⟨a,haA,ha,heven⟩ := exists_even_involution_reverse_critical_image h e hz hk
    (sourceDistance_pos h) p hforward
  exact critical_radius_central_of_marked_subactor h e hz hk p (Z T c) le_rfl
    a ha heven haA hc

include h e hz hk in
/-- Any failure of radius centrality is at distance four and selects an actual
large critical path on which every even marked subactor fails the required
commutator bound. This includes the source's restricted reverse seed. -/
theorem noncentral_radius_critical_obstruction
    (hn : ¬ ⁅V T (alpha T),Q T (alpha T)⁆ ≤
      centralizer (V T (alpha T) : Set (FreeAmalgam T))) :
    sourceDistance h = 4 ∧ ∃ c, ∃ p : CriticalPath T (sourceGeometry h) (alpha T) c,
      4 ≤ (Q T c).relIndex (Z T (alpha T)) ∧
      4 ≤ (Q T (alpha T)).relIndex (Z T c) ∧
      (Q T (p.walk.getVert (p.walk.length-2))).relIndex (V T (alpha T)) ≤ 8 ∧
      (∃ a ∈ ((Z T c).comap (embedM T)).map π,
        orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6)) ∧
      ∀ A : Subgroup (FreeAmalgam T), A ≤ Z T c → ∀ a : Equiv.Perm (Fin 6),
        orderOf a = 2 → a ∈ alternatingGroup (Fin 6) →
        a ∈ (A.comap (embedM T)).map π →
        ¬ ⁅V T (alpha T) ⊓ Q T (p.walk.getVert (p.walk.length-2)),A⁆ ≤
          Z T (alpha T) := by
  have hfour : sourceDistance h = 4 := by
    have hb := distance_gt_two h e hz hk
    have heven := sourceDistance_even h
    rw [Nat.even_iff] at heven
    by_contra hh
    exact hn (CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionFive.radius_commutator_central_of_four_lt
      T (sourceGeometry h) (by change 4 < sourceDistance h; omega) rfl)
  obtain ⟨c,p,hforward⟩ := exists_base_large_critical_path (h := h) hfour hn
  exact ⟨hfour,c,p,hforward,
    reverse_critical_image_four_le h e hz hk (sourceDistance_pos h) p hforward,
    critical_radius_image_index_le_eight h e hz hk p,
    exists_even_involution_reverse_critical_image h e hz hk (sourceDistance_pos h) p hforward,
    fun A hA a ha heven haA hc => hn
      (critical_radius_central_of_marked_subactor h e hz hk p A hA a ha heven haA hc)⟩

omit e hz hk in
/-- Base centrality carries all three radius conclusions to every component
vertex through the original graph conjugation. -/
theorem radius_bounds_at_of_base
    (hb : 2 < sourceDistance h)
    (hc : ⁅V T (alpha T),Q T (alpha T)⁆ ≤
      centralizer (V T (alpha T) : Set (FreeAmalgam T)))
    (a : Vertex T) (ha : color T a = false) (a' c : Vertex T) :
    ⁅V T a,Q T a⁆ ≤ centralizer (V T a : Set (FreeAmalgam T)) ∧
    ⁅V T a,V T a⁆ ≤ X T a ∧
    ⁅⁅X T a' ⊓ Q T a,V T a ⊓ Q T c⁆,V T a ⊓ Q T c⁆ = ⊥ := by
  have hcAt : ⁅V T a,Q T a⁆ ≤ centralizer (V T a : Set (FreeAmalgam T)) := by
    obtain ⟨g,rfl⟩ := exists_mVertex_of_color T ha
    have hV : V T (mVertex T g) = (V T (alpha T)).map (MulAut.conj g⁻¹).toMonoidHom := by
      simpa only [alpha,act_mVertex,one_mul] using V_act T g (alpha T)
    have hQ : Q T (mVertex T g) = (Q T (alpha T)).map (MulAut.conj g⁻¹).toMonoidHom := by
      simpa only [alpha,act_mVertex,one_mul] using Q_act T g (alpha T)
    rw [hV,hQ,←map_commutator]
    exact (map_mono hc).trans (map_centralizer_le_centralizer_image _ _)
  exact ⟨hcAt,
    CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionFive.radius_derived_le_X T (sourceGeometry h) hb ha hcAt,
    CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionFive.critical_radius_triple_commutator T hcAt⟩

omit hk in
include h e hz in
/-- The original whole core is exhausted, or the cubic branch has central
radius everywhere, or its distance-four path violates the specified source
commutator bound. The two-core and cubic action kernel remain distinct. -/
theorem coreExhaustion_or_cubic_radius_central_or_critical_obstruction :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      ((∀ a : Vertex T, color T a = false → ∀ a' c : Vertex T,
        ⁅V T a,Q T a⁆ ≤ centralizer (V T a : Set (FreeAmalgam T)) ∧
        ⁅V T a,V T a⁆ ≤ X T a ∧
        ⁅⁅X T a' ⊓ Q T a,V T a ⊓ Q T c⁆,V T a ⊓ Q T c⁆ = ⊥) ∨
      (sourceDistance h = 4 ∧ ∃ c, ∃ p : CriticalPath T (sourceGeometry h) (alpha T) c,
        4 ≤ (Q T c).relIndex (Z T (alpha T)) ∧
        4 ≤ (Q T (alpha T)).relIndex (Z T c) ∧
        (Q T (p.walk.getVert (p.walk.length-2))).relIndex (V T (alpha T)) ≤ 8 ∧
        (∃ a ∈ ((Z T c).comap (embedM T)).map (CubicAction.projection h e hz hk),
          orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6)) ∧
        ∀ A : Subgroup (FreeAmalgam T), A ≤ Z T c → ∀ a : Equiv.Perm (Fin 6),
          orderOf a = 2 → a ∈ alternatingGroup (Fin 6) →
          a ∈ (A.comap (embedM T)).map (CubicAction.projection h e hz hk) →
          ¬ ⁅V T (alpha T) ⊓ Q T (p.walk.getVert (p.walk.length-2)),A⁆ ≤ Z T (alpha T))) := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · refine Or.inr ⟨hk,hs,hb,?_⟩
    by_cases hc : ⁅V T (alpha T),Q T (alpha T)⁆ ≤
        centralizer (V T (alpha T) : Set (FreeAmalgam T))
    · exact Or.inl (radius_bounds_at_of_base h hb hc)
    · exact Or.inr (noncentral_radius_critical_obstruction h e hz hk hc)

omit hk in
include h e hz in
/-- Literal C.1.32 application of the refined radius alternative. Final
exhaustion of both remaining geometric cases stays in this reconstruction task. -/
theorem rankTwo_or_cubic_radius_central_or_critical_obstruction :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      ((∀ a : Vertex T, color T a = false → ∀ a' c : Vertex T,
        ⁅V T a,Q T a⁆ ≤ centralizer (V T a : Set (FreeAmalgam T)) ∧
        ⁅V T a,V T a⁆ ≤ X T a ∧
        ⁅⁅X T a' ⊓ Q T a,V T a ⊓ Q T c⁆,V T a ⊓ Q T c⁆ = ⊥) ∨
      (sourceDistance h = 4 ∧ ∃ c, ∃ p : CriticalPath T (sourceGeometry h) (alpha T) c,
        4 ≤ (Q T c).relIndex (Z T (alpha T)) ∧
        4 ≤ (Q T (alpha T)).relIndex (Z T c) ∧
        (Q T (p.walk.getVert (p.walk.length-2))).relIndex (V T (alpha T)) ≤ 8 ∧
        (∃ a ∈ ((Z T c).comap (embedM T)).map (CubicAction.projection h e hz hk),
          orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6)) ∧
        ∀ A : Subgroup (FreeAmalgam T), A ≤ Z T c → ∀ a : Equiv.Perm (Fin 6),
          orderOf a = 2 → a ∈ alternatingGroup (Fin 6) →
          a ∈ (A.comap (embedM T)).map (CubicAction.projection h e hz hk) →
          ¬ ⁅V T (alpha T) ⊓ Q T (p.walk.getVert (p.walk.length-2)),A⁆ ≤ Z T (alpha T))) :=
  (coreExhaustion_or_cubic_radius_central_or_critical_obstruction h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
