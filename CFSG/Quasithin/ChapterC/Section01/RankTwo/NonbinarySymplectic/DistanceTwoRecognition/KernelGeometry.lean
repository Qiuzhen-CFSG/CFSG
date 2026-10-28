module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.FullKernel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.FixedAttachment
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.CoreReconstruction.SecondaryFlag
public import Theory.SpecificGroups.SymplecticFour.MaximalElementary.Point
public import Theory.Representation.SymplecticFourOrthogonalCover.QuadraticLifting

/-!
# The original marked kernel action is a point radical

The full opposite kernel has the same elementary image of order q cubed as
its secondary orbit. Its action cannot be quadratic: quadraticity lifts
through the entire central cover and would force the critical displacement
into X. The plane-radical alternative is therefore excluded. The remaining
point radical and its critical root share the original natural coordinates,
projection kernel, and ambient conjugation action.

Source: MS93 (3.6), printed p.871, the seed displacement calculation.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NormalizerTransfer
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.CoreReconstruction
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The whole critical displacement cannot be central in the original
kernel when the intrinsic core escapes its Frattini and omega layers. -/
theorem replacement_nonfrattini_displacement_not_le_X
    {g : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    ¬ ⁅Z d.radical z,Q d.radical a⁆ ≤ X d.radical a := by
  obtain ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hQ,hC,hK,hfaith,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.start_color
  let C := replacementComponent d
  let : (((Ltilde d.radical a).subgroupOf (stabilizer d.radical a)).map κ).Normal := by
    rw [hK]
    exact replacementComponent_normal h d
  let : IsSimpleGroup (((Ltilde d.radical a).subgroupOf
      (stabilizer d.radical a)).map κ) := by
    rw [hK]
    exact (replacement_component_image_structure h d).2.2.1
  let : IsSimpleGroup C := (replacement_component_image_structure h d).2.2.1
  let : IsQuasisimple C := (replacement_component_image_structure h d).2.2.2.1
  have hna : ¬ IsMulCommutative (((Ltilde d.radical a).subgroupOf
      (stabilizer d.radical a)).map κ) := by
    rw [hK]
    exact Group.IsPerfect.not_isMulCommutative C
  have hcent : centralizer (((Ltilde d.radical a).subgroupOf
      (stabilizer d.radical a)).map κ : Set (d.overgroup ⧸ pCore 2 d.overgroup)) = ⊥ := by
    rw [hK]
    exact (replacement_component_image_structure h d).2.2.2.2
  intro hc
  apply hlarge
  apply core_le_frattini_of_critical_commutator_le path (by omega)
    (MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d))
    (Q_isPGroup d.radical (replacement_isPGroup h d) (replacement_core_le h d) a path.start_color)
    κ hκ hQ hna hcent
  rw [commutator_comm]
  exact hc.trans le_sup_right

/-- The entire opposite Z displacement is supplied by U. The common edge
center retains and centralizes all of its fixed attachments. -/
theorem replacement_kernel_displacement_eq_moving
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    ⁅Z d.radical z,Q d.radical a⁆ = ⁅U d.radical z,Q d.radical a⁆ := by
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g
        (MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
          (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d))
        a path.start_color (by
          rw [g.distance_constant a path.start_color]
          change 0 < g.b d.radical
          omega) z path.end_color path.critical }
  have hl : ¬ core d.radical z ≤
      (frattini (Q d.radical z)).map (Q d.radical z).subtype ⊔ X d.radical z := by
    obtain ⟨v,hv⟩ := exists_mVertex_of_color d.radical path.start_color
    have he : act d.radical v (alpha d.radical) = a := by
      rw [hv]
      simp only [alpha,act_mVertex,one_mul]
    exact nonfrattini_at_vertex d.radical
      ((nonfrattini_act_iff d.radical v (alpha d.radical)).mp (he.symm ▸ hlarge)) path.end_color
  have hzS : Z d.radical z ≤ stabilizer d.radical a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  have hZU : Z d.radical z ≤ U d.radical z ⊔
      centralizer (Q d.radical a : Set (FreeAmalgam d.radical)) := by
    rw [replacement_nonfrattini_Z_eq_moving_sup_edge h d rev hb hzt hl]
    exact sup_le_sup_left ((Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat).trans
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a path.start_color))) _
  apply le_antisymm
  · rw [commutator_comm (Z d.radical z),commutator_comm (U d.radical z)]
    exact commutator_le_moving_of_inner_mod_centralizer (Q d.radical a) (U d.radical z)
      (Z d.radical z) (((U_le_Z z).trans hzS).trans (Q_normalized d.radical a)) hZU
  · exact commutator_mono (U_le_Z z) le_rfl

/-- Quadraticity on the original natural quotient lifts through its whole
central cover and contradicts the non-Frattini core hypothesis. -/
theorem replacement_original_cover_not_quadratic
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a)
    {E W : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (L (K := E)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := E))) (hp : IsCover p)
    (j : Multiplicative W →* FreeAmalgam d.radical) (hjU : j.range = U d.radical z)
    (β : Q d.radical a →* L (K := E))
    (hact : ∀ u : Q d.radical a, ∀ w : W, j (Multiplicative.ofAdd (σ (β u) w)) =
      u.val*j (Multiplicative.ofAdd w)*u.val⁻¹) :
    ¬ ∀ u v : Q d.radical a, ∀ w,
      binaryNatural (β u) (binaryNatural (β v) w-w) = binaryNatural (β v) w-w := by
  intro hq
  have hquad := embedded_quadratic_of_natural_quadratic (U d.radical z) (Q d.radical a)
    j hjU β σ hact p hp hq
  rw [←replacement_kernel_displacement_eq_moving h d path hb hat hzt hlarge] at hquad
  exact replacement_nonfrattini_displacement_not_le_X h d path hb hlarge
    (critical_commutator_le_X_of_quadratic path hb hquad)

section Covers
variable {M J W : Type*} [Group M] [Group J] [AddCommGroup W] [Module (ZMod 2) W]
variable {ρ : Representation (ZMod 2) J W} {C : Subgroup J}

/-- The whole opposite-kernel action on a marked vertex cover, with the
literal kernel intersection and the critical root image. -/
structure KernelRootCover (T : Subgroup M) (s : MovedSection ρ C) (n : ℕ)
    (a z : Vertex T) extends AmbientVertexCover T s n z where
  actor : Q T a →* L (K := field.Carrier)
  actor_conjugation : ∀ u : Q T a, ∀ w : s.space.toSubmodule,
    embedding (Multiplicative.ofAdd (MovedSection.coverAction s equiv (actor u) w)) =
      u.val*embedding (Multiplicative.ofAdd w)*u.val⁻¹
  actor_kernel : ((commutator (Sp field.Carrier)).subtype.comp actor).ker.map
    (Q T a).subtype = Q T a ⊓ Q T z
  root_actor : ∀ u : Q T a, u.val ∈ Z T a →
    Module.finrank field.Carrier (InvolutionTypes.movedSpace (actor u).val) ≤ 1

/-- The point-radical identification on that same original marked cover. -/
structure KernelPointCover (T : Subgroup M) (s : MovedSection ρ C) (n : ℕ)
    (a z : Vertex T) extends KernelRootCover T s n a z where
  point_image : ∃ c : Sp field.Carrier,
    ((commutator (Sp field.Carrier)).subtype.comp actor).range.map
      (MulAut.conj c).toMonoidHom = pointRadicalAmbient
end Covers

omit h in
private theorem root_bound_of_cover_marking
    {M J W : Type*} [Group M] [Finite M] [Group J]
    [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) J W} {B : Subgroup J} [B.Normal]
    {T : Subgroup M} {g : Geometry T} {a z : Vertex T} {n : ℕ}
    (path : CriticalPath T g a z) (hb : 0 < g.b T)
    (hCa : C T a = Q T a) (hn : 1 < n)
    (he : (Q T z).relIndex (Z T a) = 2^n)
    (ha : (Q T a).relIndex (Z T z) = 2^n)
    (s : MovedSection ρ B) (hcent : centralizer (B : Set J) = ⊥)
    (cv : AmbientVertexCover T s n z)
    (hQS : Q T a ≤ stabilizer T z)
    (β : Q T a →* L (K := cv.field.Carrier))
    (hmark : ∀ u : Q T a, (cv.equiv.groupEquiv.symm (β u) : _) =
      cv.quotient (inclusion hQS u)) :
    ∀ u : Q T a, u.val ∈ Z T a →
      Module.finrank cv.field.Carrier (InvolutionTypes.movedSpace (β u).val) ≤ 1 := by
  rcases cv with ⟨E,hE,e,hecov,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩
  have hFc : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  have hAZ : Z T a ≤ stabilizer T z :=
    Z_le_stabilizer_of_dist_le a (g.exists_critical a path.start_color) path.critical.1.le
  let δZ := κ.comp (inclusion hAZ)
  have hδcard : Nat.card δZ.range = Nat.card E.Carrier :=
    (quotient_image_card _ _ _ hAZ κ hκQ).trans (he.trans hFc.symm)
  obtain ⟨βZ,hβZcard,hβZmark,hβZ,hd,hquad⟩ := inner_root_actor_of_field_index path hb
    hCa hn hFc s e hecov hcent
    j hj hjr δZ (fun x w => hconj (inclusion hAZ x) w) hδcard (ha.trans hFc.symm)
  intro u hu
  let v : Z T a := ⟨u,hu⟩
  have hs : β u = βZ v := by
    apply e.groupEquiv.symm.injective
    apply Subtype.ext
    rw [hmark,hβZmark]
    rfl
  have hm : InvolutionTypes.movedSpace (β u).val ≤
      displacementSpace (βZ.range.map (commutator (Sp E.Carrier)).subtype) := by
    rintro w ⟨w₀,rfl⟩
    change (β u).val • w₀-w₀ ∈ _
    rw [hs]
    exact Coinvariants.sub_mem_ker
      (ρ := (symplecticNatural 2).comp (βZ.range.map (commutator (Sp E.Carrier)).subtype).subtype)
      ⟨(βZ v).val,⟨βZ v,⟨v,rfl⟩,rfl⟩⟩ w₀
  exact (Submodule.finrank_mono hm).trans_eq hd


set_option maxHeartbeats 400000 in
/-- The kernel and critical-root actions share the original ambient cover,
including its complete natural projection kernel and component marking. -/
theorem replacement_kernel_root_cover
    {g : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    Nonempty (KernelRootCover d.radical (replacementMovedSection h d) n a z) := by
  let := replacementComponent_normal h d
  let s := replacementMovedSection h d
  obtain ⟨⟨E,hE,e,hecov,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.end_color
  let S := stabilizer d.radical z
  have hQS : Q d.radical a ≤ S := Q_le_stabilizer_of_dist_two d.radical a z path.start_color
    (path.critical.1.trans ((g.distance_constant a path.start_color).trans hb))
  have hk : κ.ker = (Q d.radical z).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [hκQ,map_subgroupOf_eq_of_le (show Q d.radical z ≤ S from fun _ hx => hx.1)]
  have hpre : (replacementComponent d).comap κ =
      (Ltilde d.radical z ⊔ Q d.radical z).subgroupOf S := by
    rw [←hκL,comap_map_eq,hk,subgroupOf_sup (Ltilde_le_stabilizer z)
      (show Q d.radical z ≤ S from fun _ hx => hx.1)]
  let δ := κ.comp (inclusion hQS)
  have hinner (u : Q d.radical a) : δ u ∈ replacementComponent d := by
    change inclusion hQS u ∈ (replacementComponent d).comap κ
    rw [hpre]
    exact replacement_nonfrattini_kernel_le_component h d path hb hlarge u.property
  let β := e.groupEquiv.toMonoidHom.comp (δ.codRestrict _ hinner)
  let α := (commutator (Sp E.Carrier)).subtype.comp β
  have hmark (u : Q d.radical a) : (e.groupEquiv.symm (β u) : _) = δ u := by
    change (e.groupEquiv.symm (e.groupEquiv ⟨δ u,hinner u⟩) : _) = δ u
    rw [e.groupEquiv.symm_apply_apply]
  have hact (u : Q d.radical a) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (β u) w)) =
        u.val*j (Multiplicative.ofAdd w)*u.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation (e.groupEquiv.symm (β u)) w)) = _
    rw [hmark]
    exact hconj (inclusion hQS u) w
  have hfk (x : Q d.radical a) : α x = 1 ↔ x.val ∈ Q d.radical z := by
    have he : α x = 1 ↔ δ x = 1 := by
      constructor
      · intro hx
        have hh : β x = 1 := Subtype.ext hx
        exact congrArg Subtype.val (e.groupEquiv.map_eq_one_iff.mp hh)
      · intro hx
        have hh : (⟨δ x,hinner x⟩ : replacementComponent d) = 1 := Subtype.ext hx
        change ((e.groupEquiv ⟨δ x,hinner x⟩ : L (K := E.Carrier)) : Sp E.Carrier) = 1
        rw [hh,map_one]
        rfl
    rw [he]
    change inclusion hQS x ∈ κ.ker ↔ x.val ∈ Q d.radical z
    rw [hk]
    rfl
  have hkα : α.ker.map (Q d.radical a).subtype = Q d.radical a ⊓ Q d.radical z := by
    ext x
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨u.property,(hfk u).mp hu⟩
    · rintro ⟨ha,hz⟩
      exact ⟨⟨x,ha⟩,(hfk ⟨x,ha⟩).mpr hz,rfl⟩
  obtain ⟨he,ha⟩ := replacement_critical_indices_eq_field_of_small h d path (by omega)
    (replacement_critical_index_lt_field_sq_of_nonfrattini h d path hb hlarge)
  have hroot := root_bound_of_cover_marking path (by omega)
    (MSCentralOrbit.C_eq_Q d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d) a path.start_color)
    h.nonbinary he ha s (replacement_component_image_structure h d).2.2.2.2
    ⟨E,hE,e,hecov,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ hQS β hmark
  exact ⟨⟨⟨E,hE,e,hecov,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩,
    β,hact,hkα,hroot⟩⟩

/-- The actual full kernel image is a point radical in the original natural
coordinates. The quadratic plane alternative is excluded through the full cover. -/
theorem replacement_kernel_point_cover
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    Nonempty (KernelPointCover d.radical (replacementMovedSection h d) n a z) := by
  obtain ⟨cv⟩ := replacement_kernel_root_cover h d path hb hlarge
  let E := cv.field
  let α := (commutator (Sp E.Carrier)).subtype.comp cv.actor
  have hfk (u : Q d.radical a) : α u = 1 ↔ u.val ∈ Q d.radical z := by
    constructor
    · intro hu
      exact (cv.actor_kernel ▸ mem_map_of_mem (Q d.radical a).subtype
        (show u ∈ α.ker from hu)).2
    · intro hu
      obtain ⟨v,hv,he⟩ := (cv.actor_kernel.symm ▸ ⟨u.property,hu⟩ :
        u.val ∈ α.ker.map (Q d.radical a).subtype)
      exact (Subtype.ext he : v=u) ▸ hv
  let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
  have hAQ := (replacement_secondary_orbit_bounds h d path hb hat hzt hlarge).1
  let fA := α.comp (inclusion hAQ)
  have hAr : fA.range = α.range := by
    rw [MonoidHom.range_comp,inclusion_range]
    exact (replacement_kernel_image_eq_secondary h d path hb hat hzt hlarge E cv.degree α cv.actor_kernel).symm
  obtain ⟨E',hE',γ,hγk,hγe,hγc,_⟩ := replacement_secondary_image h d path hb hat hzt hlarge
  have hkerA : fA.ker = γ.ker := by
    apply map_injective A.subtype_injective
    rw [hγk]
    ext x
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨u.property,(hfk (inclusion hAQ u)).mp hu⟩
    · rintro ⟨ha,hz⟩
      exact ⟨⟨x,ha⟩,(hfk (inclusion hAQ ⟨x,ha⟩)).mpr hz,rfl⟩
  let er := (QuotientGroup.quotientKerEquivRange fA).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hkerA).trans (QuotientGroup.quotientKerEquivRange γ))
  let := hγe
  have hAe : IsElementaryAbelian 2 fA.range :=
    IsElementaryAbelian.of_surjective er.symm.toMonoidHom er.symm.surjective
  let : IsElementaryAbelian 2 α.range := hAr ▸ hAe
  have hc : Nat.card α.range = Nat.card E.Carrier^3 := by
    rw [←hAr,Nat.card_congr er.toEquiv,hγc,
      (replacement_paired_secondary_orders h d path hb hat hzt hlarge).1,E.card_eq,cv.degree]
  refine ⟨⟨cv,?_⟩⟩
  apply MaximalElementary.conjugate_point_of_not_quadratic
    (E.card_eq.trans (congrArg (2^·) cv.degree)) (by have := h.nonbinary; omega) α.range hc
  intro hquad
  apply replacement_original_cover_not_quadratic h d path hb hat hzt hlarge
    (MovedSection.coverAction (replacementMovedSection h d) cv.equiv)
    (MovedSection.coverProjection (replacementMovedSection h d) cv.equiv)
    cv.cover cv.embedding cv.range_eq cv.actor cv.actor_conjugation
  intro u v w
  exact hquad (α u) ⟨u,rfl⟩ (α v) ⟨v,rfl⟩ w

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
