module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.SecondaryClosure
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.XDecomposition

/-!
# The full kernel in the secondary plane calculation

The opposite two-kernel lies in the actual component times the local
kernel. It therefore centralizes the entire component-fixed X-layer,
and the fixed part of the opposite Z-layer lies in the maximal secondary
seed Y. For the canonical normal closure N, the whole displacement
[Z_z,N] is exactly [U_z,N]; the fixed supplement is retained and centralized.

The constructed original-degree natural projection on U_z has kernel
C_{U_z}(Ltilde_z), entirely contained in Y, and is equivariant for the
literal Q_a action. Thus a self-orthogonal plane lifted into Y intersect U_z
would prove nontrivial component action on the secondary quotient. The
final application identifies the precise plane-lifting obstruction if that
quotient were fixed; it does not assume that such a plane has been built.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.6), printed p.871. The plane construction, paired-orbit
contradiction, whole-core bound and (3.7) field restriction remain open.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NormalizerTransfer
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.CoreReconstruction
open Theory.SpecificGroups.SymplecticFour
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The full component-fixed X-layer at the opposite endpoint is fixed by
Q_a. This includes all retained central attachments. -/
theorem replacement_nonfrattini_kernel_centralizes_fixed
    {g : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    Q d.radical a ≤ centralizer
      ((X d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) :
        Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  apply (replacement_nonfrattini_kernel_le_component h d path hb hlarge).trans
  exact sup_le (le_centralizer_iff.mp inf_le_right)
    ((Q_le_centralizer_X d.radical z).trans (centralizer_le inf_le_left))

/-- The whole fixed part of the opposite Z-layer lies in the maximal
secondary seed because it has trivial displacement, with no complement chosen. -/
theorem replacement_secondary_seed_contains_fixed
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    Z d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) ≤
      Sp4Four.secondarySeed d.radical a t z := by
  apply (Sp4Four.secondarySeed_greatest d.radical g path.end_color hzt (by omega)).2.2 _ inf_le_left
  apply le_trans _ bot_le
  apply le_of_eq
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mp
  exact (replacement_nonfrattini_kernel_centralizes_fixed h d path hb hlarge).trans
    (centralizer_le (inf_le_inf_right _ (g.omega_bound z path.end_color (by
      rw [g.distance_constant z path.end_color]
      change 0 < g.b d.radical
      omega))))

/-- The displacement of the whole opposite Z-layer by N is exactly that
of U. The fixed supplement is retained and centralized, not factored away. -/
theorem replacement_secondaryClosure_displacement_eq_moving
    {g : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    ⁅Z d.radical z,secondaryClosure a z⁆ = ⁅U d.radical z,secondaryClosure a z⁆ := by
  have hpos : 0 < g.b d.radical := by omega
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; exact hpos)
        z path.end_color path.critical }
  have hlarge' : ¬ core d.radical z ≤
      (frattini (Q d.radical z)).map (Q d.radical z).subtype ⊔ X d.radical z := by
    obtain ⟨v,hv⟩ := exists_mVertex_of_color d.radical path.start_color
    have he : act d.radical v (alpha d.radical) = a := by
      rw [hv]
      simp only [alpha,act_mVertex,one_mul]
    exact nonfrattini_at_vertex d.radical
      ((nonfrattini_act_iff d.radical v (alpha d.radical)).mp (he.symm ▸ hlarge))
      path.end_color
  have hNQ : secondaryClosure a z ≤ Q d.radical a :=
    Sp4Four.conjugatesIn_le_of_normalized _ _ _ inf_le_right (Q_normalized d.radical a)
  have hfixed := le_centralizer_iff.mp
    (hNQ.trans (replacement_nonfrattini_kernel_centralizes_fixed h d path hb hlarge))
  have hZU : Z d.radical z ≤ U d.radical z ⊔
      centralizer (secondaryClosure a z : Set (FreeAmalgam d.radical)) := by
    have hzX := g.omega_bound z path.end_color (by
      rw [g.distance_constant z path.end_color]
      exact hpos)
    rw [replacement_nonfrattini_X_decomposition h d rev hb hlarge'] at hzX
    exact hzX.trans (sup_le_sup_left hfixed _)
  have hzS : Z d.radical z ≤ stabilizer d.radical a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  have hUN : U d.radical z ≤ normalizer (secondaryClosure a z) :=
    ((U_le_Z z).trans hzS).trans (conjugatesIn_normalized _ _)
  apply le_antisymm
  · rw [commutator_comm (Z d.radical z),commutator_comm (U d.radical z)]
    exact commutator_le_moving_of_inner_mod_centralizer
      (secondaryClosure a z) (U d.radical z) (Z d.radical z) hUN hZU
  · exact commutator_mono (U_le_Z z) le_rfl


omit h d in
private theorem projection_kernel_of_embedding
    {G W V : Type*} [Group G] [Group W] [Group V]
    {U C : Subgroup G} (j : W →* G) (hjr : j.range = U) (π : U →* V)
    (hk : ∀ w, π ⟨j w, by rw [←hjr]; exact ⟨w,rfl⟩⟩ = 1 ↔ j w ∈ C) :
    π.ker.map U.subtype = U ⊓ C := by
  have hv (u : U) : π u = 1 ↔ u.val ∈ C := by
    obtain ⟨w,hw⟩ := (show u.val ∈ j.range from hjr.symm ▸ u.property)
    have hu : u = ⟨j w,by rw [←hjr]; exact ⟨w,rfl⟩⟩ := Subtype.ext hw.symm
    rw [hu]
    exact hk w
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨u.property,(hv u).mp hu⟩
  · rintro ⟨hxu,hxc⟩
    exact ⟨⟨x,hxu⟩,(hv ⟨x,hxu⟩).mpr hxc,rfl⟩

/-- The actual moving cover has an equivariant opposite-kernel action and
its full projection kernel is contained in the maximal secondary seed. -/
theorem replacement_secondary_moving_projection
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    ∃ E : BinaryField, E.degree = n ∧
      ∃ (π : U d.radical z →* Multiplicative (Theory.SpecificGroups.SymplecticFour.Vector E.Carrier))
        (α : Q d.radical a →* Sp E.Carrier),
        Function.Surjective π ∧
        π.ker.map (U d.radical z).subtype =
          U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) ∧
        π.ker.map (U d.radical z).subtype ≤ Sp4Four.secondarySeed d.radical a t z ∧
        (∀ (u : Q d.radical a) (v : U d.radical z)
          (hv : u.val*v.val*u.val⁻¹ ∈ U d.radical z),
          π ⟨u.val*v.val*u.val⁻¹,hv⟩ = Multiplicative.ofAdd (α u • (π v).toAdd)) := by
  let := replacementComponent_normal h d
  let s := replacementMovedSection h d
  obtain ⟨⟨E,hE,e,hecov,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.end_color
  let S := stabilizer d.radical z
  have hQS : Q d.radical a ≤ S :=
    Q_le_stabilizer_of_dist_two d.radical a z path.start_color
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
  have hβ (u : Q d.radical a) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (β u) w)) =
        u.val*j (Multiplicative.ofAdd w)*u.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation (e.groupEquiv.symm (β u)) w)) = _
    rw [hmark]
    exact hconj (inclusion hQS u) w
  have hn : Q d.radical a ≤ normalizer (U d.radical z) := hQS.trans (U_normalized z)
  obtain ⟨π,hπ,hπj,hact⟩ := exists_equivariant_embedded_projection
    (U d.radical z) (Q d.radical a) hn (MovedSection.coverAction s e)
    (binaryNatural (K := E.Carrier)) j hj hjr (MovedSection.coverProjection s e).toLinearMap
    hecov.1 (fun b w => LinearMap.congr_fun ((MovedSection.coverProjection s e).isIntertwining' b) w)
    β hβ
  have hπker : π.ker.map (U d.radical z).subtype =
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) := by
    apply projection_kernel_of_embedding j hjr π
    intro w
    exact (Iff.of_eq (congrArg (fun v => v = 1) (hπj w.toAdd))).trans (hker w.toAdd)
  refine ⟨E,hE,π,α,hπ,hπker,?_,?_⟩
  · rw [hπker]
    exact (inf_le_inf_right _ (U_le_Z z)).trans
      (replacement_secondary_seed_contains_fixed h d path hb hzt hlarge)
  · intro u v hv
    exact hact u v

/-- With the full kernel now proved to lie in the actual seed, only the
marked plane-lifting premise remains in the secondary-action calculation. -/
theorem replacement_secondary_moves_of_moving_plane
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a)
    {E : Type*} [Field E]
    (π : U d.radical z →* Multiplicative (Theory.SpecificGroups.SymplecticFour.Vector E))
    (α : Q d.radical a →* Sp E)
    (hact : ∀ (u : Q d.radical a) (v : U d.radical z)
      (hv : u.val*v.val*u.val⁻¹ ∈ U d.radical z),
      π ⟨u.val*v.val*u.val⁻¹,hv⟩ = Multiplicative.ofAdd (α u • (π v).toAdd))
    (hkernel : π.ker.map (U d.radical z).subtype =
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)))
    (P : Submodule E (Theory.SpecificGroups.SymplecticFour.Vector E))
    (hP : (Theory.SpecificGroups.SymplecticFour.form E).orthogonal P = P)
    (hcover : ∀ v ∈ P, ∃ y : (Sp4Four.secondarySeed d.radical a t z ⊓ U d.radical z :
        Subgroup (FreeAmalgam d.radical)), (π ⟨y.val,y.property.2⟩).toAdd = v) :
    ¬ ⁅Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z),
      Ltilde d.radical a⁆ ≤ Z d.radical a := by
  let Y := Sp4Four.secondarySeed d.radical a t z
  let A := Sp4Four.secondaryOrbit d.radical a Y
  let N := secondaryClosure a z
  have hYA : Y ≤ A := by
    change Y ≤ conjugatesIn Y (stabilizer d.radical a)
    rw [Sp4Four.conjugatesIn_eq_conjugateSpan]
    exact le_conjugateSpanBy _ _
  have hNQ : N ≤ Q d.radical a := Sp4Four.conjugatesIn_le_of_normalized _ _ _
    inf_le_right (Q_normalized d.radical a)
  have hNU : N ≤ normalizer (U d.radical z) :=
    (hNQ.trans (Q_le_stabilizer_of_dist_two d.radical a z path.start_color
      (path.critical.1.trans ((g.distance_constant a path.start_color).trans hb)))).trans
      (U_normalized z)
  intro hfixed
  apply replacement_secondary_moves_of_closure_displacement h d path hb hat hzt hlarge ?_ hfixed
  have hNY : N ≤ centralizer ((Y ⊓ U d.radical z : Subgroup (FreeAmalgam d.radical)) :
      Set (FreeAmalgam d.radical)) :=
    (replacement_secondaryClosure_centralizes_of_fixed h d path hb hat hzt hfixed).trans
      (centralizer_le (inf_le_left.trans hYA))
  have hbound := commutator_le_plane_sup_kernel (U d.radical z) N (Y ⊓ U d.radical z)
    inf_le_right hNU π (α.comp (inclusion hNQ))
    (fun u v => hact (inclusion hNQ u) v _) P hP hcover hNY
  have hk : π.ker.map (U d.radical z).subtype ≤ Y := by
    rw [hkernel]
    exact (inf_le_inf_right _ (U_le_Z z)).trans
      (replacement_secondary_seed_contains_fixed h d path hb hzt hlarge)
  rw [commutator_comm N, replacement_secondaryClosure_displacement_eq_moving h d path hb hlarge]
  exact hbound.trans (sup_le (inf_le_left.trans hYA) (hk.trans hYA))

/-- In the putative fixed secondary branch, the constructed original-degree
projection retains its entire kernel in Y, and the image of Y intersect U
contains no self-orthogonal plane. Thus the remaining obstruction concerns
plane lifting, not an omitted fixed layer or a missing compatible action. -/
theorem replacement_fixed_secondary_plane_obstruction
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a)
    (hfixed : ⁅Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z),
      Ltilde d.radical a⁆ ≤ Z d.radical a) :
    ∃ E : BinaryField, E.degree = n ∧
      ∃ (π : U d.radical z →* Multiplicative (Theory.SpecificGroups.SymplecticFour.Vector E.Carrier))
        (α : Q d.radical a →* Sp E.Carrier),
        Function.Surjective π ∧
        π.ker.map (U d.radical z).subtype =
          U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) ∧
        π.ker.map (U d.radical z).subtype ≤ Sp4Four.secondarySeed d.radical a t z ∧
        (∀ (u : Q d.radical a) (v : U d.radical z)
          (hv : u.val*v.val*u.val⁻¹ ∈ U d.radical z),
          π ⟨u.val*v.val*u.val⁻¹,hv⟩ = Multiplicative.ofAdd (α u • (π v).toAdd)) ∧
        ∀ P : Submodule E.Carrier (Theory.SpecificGroups.SymplecticFour.Vector E.Carrier),
          (Theory.SpecificGroups.SymplecticFour.form E.Carrier).orthogonal P = P →
          ¬ (∀ v ∈ P, ∃ y : (Sp4Four.secondarySeed d.radical a t z ⊓ U d.radical z :
            Subgroup (FreeAmalgam d.radical)), (π ⟨y.val,y.property.2⟩).toAdd = v) := by
  obtain ⟨E,hE,π,α,hπ,hk,hkY,hact⟩ :=
    replacement_secondary_moving_projection h d path hb hzt hlarge
  refine ⟨E,hE,π,α,hπ,hk,hkY,hact,?_⟩
  intro P hP hcover
  exact replacement_secondary_moves_of_moving_plane h d path hb hat hzt hlarge
    π α hact hk P hP hcover hfixed

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
