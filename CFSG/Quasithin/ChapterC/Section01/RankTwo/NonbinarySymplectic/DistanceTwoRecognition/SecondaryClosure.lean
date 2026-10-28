module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.SecondarySection
public import Theory.GroupTheory.NormalSectionResidualMonolith
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import Theory.SpecificGroups.SymplecticFour.FixedPlaneDisplacement

/-!
# The normal closure in the secondary-action argument

Let Y be the maximal secondary seed, A its local conjugate span, and N
the local normal closure of the opposite Z-kernel intersection. The actual
commutator core lies in N. If the component fixes A/Z, then A = YZ, N
centralizes all of A, and A is elementary. A bound [N,Z_opposite] ≤ A
would therefore contradict failure of the whole-core Frattini bound.

The literal secondary quotient from SecondarySection consequently has
nontrivial component action once this displacement is bounded. A marked
self-orthogonal plane covered by Y provides one sufficient criterion,
provided the whole coordinate kernel is retained in Y. The construction
of that plane and the displacement bound are not asserted here.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.6), printed p.871. The paired-orbit contradiction, whole-core
bound, replacement-radical comparison and field restriction remain open.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NormalizerTransfer
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.CoreReconstruction
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition

variable {M : Type*} [Group M] {T : Subgroup M}

/-- The normal closure used in the secondary-action argument of MS93 (3.6). -/
abbrev secondaryClosure (a z : Vertex T) : Subgroup (FreeAmalgam T) :=
  conjugatesIn (Z T z ⊓ Q T a) (stabilizer T a)

private theorem seed_le_orbit {G : Type*} [Group G] (Y S : Subgroup G) :
    Y ≤ conjugatesIn Y S := by
  rw [Sp4Four.conjugatesIn_eq_conjugateSpan]
  exact le_conjugateSpanBy _ _

variable [Finite M]

private theorem local_commutator_idempotent (a : Vertex T)
    (hp : IsPGroup 2 (Q T a)) : ⁅core T a,Ltilde T a⁆ = core T a := by
  let S := stabilizer T a
  let : Finite S := finite_stabilizer T a
  have hQ : Q T a ≤ S := fun _ hx => hx.1
  have hL : Ltilde T a ≤ S := Ltilde_le_stabilizer a
  have hLm : (pResidual 2 S).map S.subtype = Ltilde T a := rfl
  have hQm : ((Q T a).subgroupOf S).map S.subtype = Q T a :=
    map_subgroupOf_eq_of_le hQ
  let : ((Q T a).subgroupOf S).Normal := Q_normal T a
  have he := congrArg (Subgroup.map S.subtype)
    (commutator_isPPerfect_idempotent (pResidual 2 S) ((Q T a).subgroupOf S)
      (isPPerfect_pResidual 2) hp.comap_subtype le_normalizer_of_normal)
  simpa only [core,map_commutator,hLm,hQm] using he

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem replacement_normal_section_detection
    {g : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (V W : Subgroup (FreeAmalgam d.radical))
    (hVS : V ≤ stabilizer d.radical a)
    (hVN : stabilizer d.radical a ≤ normalizer V)
    (hWN : stabilizer d.radical a ≤ normalizer W)
    (hcomm : ⁅V,Z d.radical z⁆ ≤ W) : ⁅V,Ltilde d.radical a⁆ ≤ W := by
  let S := stabilizer d.radical a
  let : Finite S := finite_stabilizer d.radical a
  let V₀ := V.subgroupOf S
  let W₀ := W.subgroupOf S
  let E₀ := (Z d.radical z).subgroupOf S
  let : V₀.Normal := normal_subgroupOf_of_le_normalizer hVN
  let : W₀.Normal := normal_subgroupOf_of_le_normalizer hWN
  have hzS : Z d.radical z ≤ S := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  have hzQ : ¬ Z d.radical z ≤ Q d.radical a :=
    (critical_reverse d.radical g
      (MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
        (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d))
      a path.start_color (by
        rw [g.distance_constant a path.start_color]
        change 0 < g.b d.radical
        omega)
      z path.end_color path.critical).2
  obtain ⟨⟨E,hE,e,hcover,j,hj,hjU,κ,hκ,hk,hkC,him,hfaith,hsemi,hact,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.start_color
  have hLm : (pResidual 2 S).map S.subtype = Ltilde d.radical a := rfl
  have hLi : (pResidual 2 S).map κ = replacementComponent d := by
    have he : (Ltilde d.radical a).subgroupOf S = pResidual 2 S := by
      change ((pResidual 2 S).map S.subtype).comap S.subtype = _
      exact comap_map_eq_self_of_injective S.subtype_injective _
    rwa [he] at him
  let : IsSimpleGroup ((pResidual 2 S).map κ) := by
    rw [hLi]
    exact (replacement_component_image_structure h d).2.2.1
  have hc : centralizer ((pResidual 2 S).map κ : Set (d.overgroup ⧸ pCore 2 d.overgroup)) = ⊥ := by
    rw [hLi]
    exact (replacement_component_image_structure h d).2.2.2.2
  have hkernel : IsPGroup 2 κ.ker := by
    have he : κ.ker = (Q d.radical a).subgroupOf S := by
      apply map_injective S.subtype_injective
      rw [hk,map_subgroupOf_eq_of_le (show Q d.radical a ≤ S from fun _ hx => hx.1)]
    rw [he]
    exact (Q_isPGroup d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) a path.start_color).comap_subtype
  have hescape : ¬ E₀ ≤ κ.ker := by
    intro hh
    apply hzQ
    intro x hx
    exact hk ▸ mem_map_of_mem S.subtype (hh (show (⟨x,hzS hx⟩ : S) ∈ E₀ from hx))
  have hVm : V₀.map S.subtype = V := map_subgroupOf_eq_of_le hVS
  have hEm : E₀.map S.subtype = Z d.radical z := map_subgroupOf_eq_of_le hzS
  have hm : ⁅V₀,E₀⁆ ≤ W₀ := by
    apply map_le_iff_le_comap.mp
    simpa only [map_commutator,hVm,hEm] using hcomm
  have hh := map_mono (f := S.subtype)
    (commutator_pResidual_le_of_monolithic_kernel_escape 2 κ hκ hkernel hc V₀ W₀ E₀ hescape hm)
  rw [map_commutator,hLm,map_subgroupOf_eq_of_le hVS] at hh
  exact hh.trans (map_comap_le _ _)

/-- The actual critical commutator core lies in the normal closure of the
opposite Z-kernel intersection. No secondary-action premise is used. -/
theorem replacement_core_le_secondaryClosure
    {g : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2) :
    core d.radical a ≤ secondaryClosure a z := by
  have hd : (cosetGraph d.radical).dist a z = 2 :=
    path.critical.1.trans ((g.distance_constant a path.start_color).trans hb)
  have hzS : Z d.radical z ≤ stabilizer d.radical a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  apply replacement_normal_section_detection h d path hb (Q d.radical a) (secondaryClosure a z)
    (fun _ hx => hx.1) (Q_normalized d.radical a) (conjugatesIn_normalized _ _)
  apply le_trans _ (seed_le_orbit _ _)
  exact le_inf
    (le_normalizer_iff_commutator_le_right.mp
      ((Q_le_stabilizer_of_dist_two d.radical a z path.start_color hd).trans (Z_normalized d.radical z)))
    (le_normalizer_iff_commutator_le_left.mp (hzS.trans (Q_normalized d.radical a)))

/-- The local displacement bound in MS93 (3.6) is enough for nontrivial
component action on the literal secondary quotient. -/
theorem replacement_secondary_moves_of_closure_displacement
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (_hat : Adjacent d.radical a t) (_hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a)
    (hdisplacement : ⁅secondaryClosure a z,Z d.radical z⁆ ≤
      Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)) :
    ¬ ⁅Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z),
      Ltilde d.radical a⁆ ≤ Z d.radical a := by
  let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
  let N := secondaryClosure a z
  have hNQ : N ≤ Q d.radical a := Sp4Four.conjugatesIn_le_of_normalized _ _ _
    inf_le_right (Q_normalized d.radical a)
  have hNA : ⁅N,Ltilde d.radical a⁆ ≤ A :=
    replacement_normal_section_detection h d path hb N A
      (hNQ.trans (fun _ hx => hx.1)) (conjugatesIn_normalized _ _)
      (conjugatesIn_normalized _ _) hdisplacement
  have hid := local_commutator_idempotent a
    (Q_isPGroup d.radical (replacement_isPGroup h d) (replacement_core_le h d) a path.start_color)
  have hcoreA : core d.radical a ≤ A := by
    rw [←hid]
    exact (commutator_mono (replacement_core_le_secondaryClosure h d path hb) le_rfl).trans hNA
  intro hcentral
  have hcoreZ : core d.radical a ≤ Z d.radical a := by
    rw [←hid]
    exact (commutator_mono hcoreA le_rfl).trans hcentral
  apply hlarge
  exact hcoreZ.trans ((g.omega_bound a path.start_color (by
    rw [g.distance_constant a path.start_color]
    change 0 < g.b d.radical
    omega)).trans le_sup_right)


omit [Finite F] [CharP F 2] in
/-- If the component fixes A/Z, the full secondary orbit is YZ. The
whole endpoint Z subgroup is retained. -/
theorem replacement_secondary_eq_seed_sup_Z_of_fixed
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hfixed : ⁅Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z),
      Ltilde d.radical a⁆ ≤ Z d.radical a) :
    Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z) =
      Sp4Four.secondarySeed d.radical a t z ⊔ Z d.radical a := by
  let Y := Sp4Four.secondarySeed d.radical a t z
  let A := Sp4Four.secondaryOrbit d.radical a Y
  have hYA : Y ≤ A := seed_le_orbit _ _
  have hZA : Z d.radical a ≤ A :=
    secondary_orbit_contains_Z g (by omega) path.start_color path.end_color hat hzt
  have ht : color d.radical t = true := by
    have hn := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all [path.start_color]
  have htS : Q d.radical t ≤ stabilizer d.radical a := by
    rw [Q_h_eq_edge d.radical ht hat]
    exact inf_le_left
  have htS' : Q d.radical t ≤ stabilizer d.radical z := by
    rw [Q_h_eq_edge d.radical ht hzt]
    exact inf_le_left
  let := g.Z_elementary (by omega : 0 < g.b d.radical) z path.end_color
  have htZ : Q d.radical t ≤ normalizer (Z d.radical t) :=
    (show Q d.radical t ≤ stabilizer d.radical t from fun _ hx => hx.1).trans
      (Z_normalized d.radical t)
  have htY : Q d.radical t ≤ normalizer Y := by
    apply le_normalizer_iff.mpr
    intro u hu x hx
    have hbound (u : FreeAmalgam d.radical) (hu : u ∈ Q d.radical t) :
        Y.map (MulAut.conj u).toMonoidHom ≤ Y := by
      apply (Sp4Four.secondarySeed_greatest d.radical g path.end_color hzt (by omega)).2.2
      · exact (map_mono (Sp4Four.secondarySeed_le d.radical a t z)).trans_eq
          (mem_normalizer_iff_map_conj_eq.mp ((htS'.trans (Z_normalized d.radical z)) hu))
      · have hh := map_mono (f := (MulAut.conj u).toMonoidHom)
          (Sp4Four.secondarySeed_greatest d.radical g (a := a) path.end_color hzt (by omega)).2.1
        have hQe : (Q d.radical a).map (MulAut.conj u).toMonoidHom = Q d.radical a :=
          mem_normalizer_iff_map_conj_eq.mp ((htS.trans (Q_normalized d.radical a)) hu)
        have hZe : (Z d.radical t).map (MulAut.conj u).toMonoidHom = Z d.radical t :=
          mem_normalizer_iff_map_conj_eq.mp (htZ hu)
        rw [map_commutator,hQe,hZe] at hh
        exact hh
    exact hbound u hu (mem_map_of_mem (MulAut.conj u).toMonoidHom hx)
  have hLN : Ltilde d.radical a ≤ normalizer (Y ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :=
    le_normalizer_iff_commutator_le_left.mpr
      (((commutator_mono (sup_le hYA hZA) le_rfl).trans hfixed).trans le_sup_right)
  have hSN : stabilizer d.radical a ≤ normalizer (Y ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) := by
    rw [←replacement_edge_generation h d path.start_color hat]
    exact sup_le hLN ((le_inf htY (htS.trans (Z_normalized d.radical a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _))
  exact le_antisymm (Sp4Four.conjugatesIn_le_of_normalized _ _ _ le_sup_left hSN)
    (sup_le hYA hZA)

omit [Finite F] [CharP F 2] in
/-- In the putative fixed-section branch, the literal normal closure N
centralizes all of A, not just the original seed Y. -/
theorem replacement_secondaryClosure_centralizes_of_fixed
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hfixed : ⁅Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z),
      Ltilde d.radical a⁆ ≤ Z d.radical a) :
    secondaryClosure a z ≤ centralizer
      (Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z) :
        Set (FreeAmalgam d.radical)) := by
  let Y := Sp4Four.secondarySeed d.radical a t z
  let A := Sp4Four.secondaryOrbit d.radical a Y
  let := g.Z_elementary (by omega : 0 < g.b d.radical) z path.end_color
  have he := replacement_secondary_eq_seed_sup_Z_of_fixed h d path hb hat hzt hfixed
  change A = Y ⊔ Z d.radical a at he
  have hB : Z d.radical z ⊓ Q d.radical a ≤ centralizer (A : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mp
    rw [he]
    apply sup_le
    · exact (Sp4Four.secondarySeed_le d.radical a t z).trans
        ((Z d.radical z).le_centralizer.trans (centralizer_le inf_le_left))
    · exact (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a path.start_color)).trans (centralizer_le inf_le_right)
  exact Sp4Four.conjugatesIn_le_of_normalized _ _ _ hB
    ((conjugatesIn_normalized _ _).trans (normalizer_le_normalizer_centralizer A))

/-- The fixed-section branch already makes the full secondary orbit
 elementary, using its actual elementary seed and the centralizing normal
 closure. This does not make it central in Q. -/
theorem replacement_secondary_elementary_of_fixed
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a)
    (hfixed : ⁅Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z),
      Ltilde d.radical a⁆ ≤ Z d.radical a) :
    IsElementaryAbelian 2
      (Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)) := by
  let Y := Sp4Four.secondarySeed d.radical a t z
  let A := Sp4Four.secondaryOrbit d.radical a Y
  have hYN : Y ≤ secondaryClosure a z :=
    (le_inf (Sp4Four.secondarySeed_le d.radical a t z)
      (replacement_secondary_seed_le_kernel h d path hb hat hzt hlarge)).trans (seed_le_orbit _ _)
  have hAN : A ≤ secondaryClosure a z :=
    Sp4Four.conjugatesIn_le_of_normalized _ _ _ hYN (conjugatesIn_normalized _ _)
  have hc : IsMulCommutative A := le_centralizer_iff_isMulCommutative.mp
    (hAN.trans (replacement_secondaryClosure_centralizes_of_fixed h d path hb hat hzt hfixed))
  let : IsElementaryAbelian 2 Y :=
    Sp4Four.secondarySeed_elementary d.radical g path.end_color (by omega)
  change IsElementaryAbelian 2 (conjugatesIn Y (stabilizer d.radical a))
  change IsMulCommutative (conjugatesIn Y (stabilizer d.radical a)) at hc
  rw [Sp4Four.conjugatesIn_eq_conjugateSpan] at hc ⊢
  let := hc
  exact conjugateSpanBy_elementary_of_commutative _ _


/-- A marked natural quotient of the opposite Z-layer supplies the remaining
source displacement when the maximal seed covers a self-orthogonal plane.
The full kernel is required to lie in that seed and is retained in the proof. -/
theorem replacement_secondary_moves_of_seed_plane
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a)
    {E : Type*} [Field E]
    (π : Z d.radical z →* Multiplicative (Theory.SpecificGroups.SymplecticFour.Vector E))
    (α : Q d.radical a →* Theory.SpecificGroups.SymplecticFour.Sp E)
    (hact : ∀ (u : Q d.radical a) (v : Z d.radical z)
      (hv : u.val*v.val*u.val⁻¹ ∈ Z d.radical z),
      π ⟨u.val*v.val*u.val⁻¹,hv⟩ = Multiplicative.ofAdd (α u • (π v).toAdd))
    (P : Submodule E (Theory.SpecificGroups.SymplecticFour.Vector E))
    (hP : (Theory.SpecificGroups.SymplecticFour.form E).orthogonal P = P)
    (hcover : ∀ v ∈ P, ∃ y : Sp4Four.secondarySeed d.radical a t z,
      (π ⟨y.val,Sp4Four.secondarySeed_le d.radical a t z y.property⟩).toAdd = v)
    (hkernel : π.ker.map (Z d.radical z).subtype ≤ Sp4Four.secondarySeed d.radical a t z) :
    ¬ ⁅Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z),
      Ltilde d.radical a⁆ ≤ Z d.radical a := by
  let Y := Sp4Four.secondarySeed d.radical a t z
  let A := Sp4Four.secondaryOrbit d.radical a Y
  let N := secondaryClosure a z
  have hNQ : N ≤ Q d.radical a := Sp4Four.conjugatesIn_le_of_normalized _ _ _
    inf_le_right (Q_normalized d.radical a)
  have hNZ : N ≤ normalizer (Z d.radical z) :=
    (hNQ.trans (Q_le_stabilizer_of_dist_two d.radical a z path.start_color
      (path.critical.1.trans ((g.distance_constant a path.start_color).trans hb)))).trans
      (Z_normalized d.radical z)
  intro hfixed
  apply replacement_secondary_moves_of_closure_displacement h d path hb hat hzt hlarge ?_ hfixed
  have hNY : N ≤ centralizer (Y : Set (FreeAmalgam d.radical)) :=
    (replacement_secondaryClosure_centralizes_of_fixed h d path hb hat hzt hfixed).trans
      (centralizer_le (seed_le_orbit Y (stabilizer d.radical a)))
  have hbound := Theory.SpecificGroups.SymplecticFour.commutator_le_plane_sup_kernel
    (Z d.radical z) N Y (Sp4Four.secondarySeed_le d.radical a t z) hNZ π
    (α.comp (inclusion hNQ)) (fun u v => hact (inclusion hNQ u) v _) P hP hcover hNY
  rw [commutator_comm] at hbound
  exact hbound.trans (sup_le (seed_le_orbit _ _) (hkernel.trans (seed_le_orbit _ _)))

omit h [Finite H] in
/-- Nontrivial group displacement is detected by every literal coordinate
section with the original component marking. -/
theorem secondary_component_action_nontrivial
    {a z t : Vertex d.radical}
    {J V : Type*} [Group J] [AddCommGroup V] [Module (ZMod 2) V]
    (κ : stabilizer d.radical a →* J) (B : Subgroup J)
    (hmark : ((Ltilde d.radical a).subgroupOf (stabilizer d.radical a)).map κ = B)
    (σ : Representation (ZMod 2) J V)
    (c : BinaryConjugationSection (stabilizer d.radical a)
      (Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z))
      (Z d.radical a) (σ.comp κ))
    (hmove : ¬ ⁅Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z),
      Ltilde d.radical a⁆ ≤ Z d.radical a) :
    ∃ b : B, ∃ v : V, σ b.val v ≠ v := by
  by_contra hn
  push Not at hn
  apply hmove
  rw [commutator_comm]
  apply c.commutator_le_of_imageSpace_fixed (Ltilde d.radical a) _
    (Ltilde_le_stabilizer a) le_rfl
  intro v _ u
  change σ (κ u.val) v = v
  have hu : κ u.val ∈ B := hmark ▸ mem_map_of_mem κ u.property
  exact hn ⟨κ u.val,hu⟩ v


/-- A fixed secondary section would leave a precise nonzero displacement:
the canonical normal closure centralizes A but displaces Z_z outside A.
This is the remaining local geometric obstruction with all source inputs. -/
theorem replacement_fixed_secondary_obstruction
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a)
    (hfixed : ⁅Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z),
      Ltilde d.radical a⁆ ≤ Z d.radical a) :
    let Y := Sp4Four.secondarySeed d.radical a t z
    let A := Sp4Four.secondaryOrbit d.radical a Y
    let N := secondaryClosure a z
    A = Y ⊔ Z d.radical a ∧ IsElementaryAbelian 2 A ∧
      N ≤ centralizer (A : Set (FreeAmalgam d.radical)) ∧
      ¬ ⁅N,Z d.radical z⁆ ≤ A := by
  exact ⟨replacement_secondary_eq_seed_sup_Z_of_fixed h d path hb hat hzt hfixed,
    replacement_secondary_elementary_of_fixed h d path hb hat hzt hlarge hfixed,
    replacement_secondaryClosure_centralizes_of_fixed h d path hb hat hzt hfixed,
    fun hbound => replacement_secondary_moves_of_closure_displacement h d path hb hat hzt
      hlarge hbound hfixed⟩

/-- The constructed secondary quotient, original quotient marking and
quadratic opposite action now also have nontrivial component action when
the explicit normal-closure displacement has been supplied. -/
theorem replacement_secondary_section_of_closure_displacement
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a)
    (hdisplacement : ⁅secondaryClosure a z,Z d.radical z⁆ ≤
      Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)) :
    let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
    let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
    let := replacement_secondary_quotient_normal h d path hb hat hzt hlarge
    let := replacement_secondary_quotient_elementary h d path hb hat hzt hlarge
    ∃ (κ : stabilizer d.radical a →* (d.overgroup ⧸ pCore 2 d.overgroup)),
      Function.Surjective κ ∧
      κ.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
      ((Ltilde d.radical a).subgroupOf (stabilizer d.radical a)).map κ =
        replacementComponent d ∧
      ∃ (σ : Representation (ZMod 2) (d.overgroup ⧸ pCore 2 d.overgroup)
          (Additive (A ⧸ (Z d.radical a).subgroupOf A)))
        (c : BinaryConjugationSection (stabilizer d.radical a) A (Z d.radical a) (σ.comp κ)),
        (∀ u : A, (c.coordinates u).toAdd =
          Additive.ofMul (QuotientGroup.mk' ((Z d.radical a).subgroupOf A) u)) ∧
        Representation.BinaryOffender.IsQuadratic σ
          ((A'.subgroupOf (stabilizer d.radical a)).map κ) ∧
        Representation.BinaryOffender.fixedCodim σ
          ((A'.subgroupOf (stabilizer d.radical a)).map κ) ≤ 2*n ∧
        ∃ b : replacementComponent d, ∃ v, σ b.val v ≠ v := by
  let := replacement_secondary_quotient_normal h d path hb hat hzt hlarge
  let := replacement_secondary_quotient_elementary h d path hb hat hzt hlarge
  obtain ⟨κ,hκ,hk,hL,σ,c,hc,hquad,hcodim⟩ :=
    replacement_secondary_section h d path hb hat hzt hlarge
  refine ⟨κ,hκ,hk,hL,σ,c,hc,hquad,hcodim,?_⟩
  exact secondary_component_action_nontrivial d κ (replacementComponent d) hL σ c
    (replacement_secondary_moves_of_closure_displacement h d path hb hat hzt hlarge hdisplacement)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
