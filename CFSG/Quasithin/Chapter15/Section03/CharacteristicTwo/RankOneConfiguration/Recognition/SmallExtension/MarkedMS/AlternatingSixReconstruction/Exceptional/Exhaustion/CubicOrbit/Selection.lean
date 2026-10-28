module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.CubicOrbit.Noncentral
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Noncentral.Selection
public import Theory.Representation.BinaryConjugationSection.QuadraticCommutator
public import Theory.Representation.BinaryOffender.QuadraticDualOffender

/-!
# The actual favorable cubic orbit pair and its action bounds

Choose the source favorable pair at the original base edge using the proved
noncentrality, critical index two and edge commutator estimate. The actual
quotient by the base Z-layer is elementary, as are the paired intersection
and commutator. Its conjugation kernel is Q or the retained cubic extension
E, and on two-subgroups both kernels give exactly the Q intersection.

The opposite orbit acts quadratically on this literal quotient. Faithfulness
in its automorphism group makes its image elementary; the original six-letter
projection retains its order. Thus both favorable orbit indices are at most
eight and the fixed preimage index is at most four. CubicOrbit.Source applies
the constructed pair to the entire blockU and original rank-two conclusion.
Full movement, fixed-quotient recognition and the intersection bound still
belong to the reconstruction owner, as do larger critical distances.
Source: Meierfrankenfeld--Stellmacher (1993), (3.6), printed p.871.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation BinaryPermutation
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.CubicAction
open Natural.Exhaustion.DistanceTwo.Geometry
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "T" => edge L R
local notation "W" => (⁅centralOmega L R,K⁆ : Subgroup M)
local notation "π" => projection h e hz hk

include h e hz hk in
/-- The critical index two also holds in the orientation used for orbit selection. -/
theorem opposite_Z_core_index_two (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical _ rfl)) :
    (Q T c).relIndex (Z T (alpha T)) = 2 := by
  have hcCol := critical_endpoint_color T (alpha T) rfl _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    (alpha T) rfl (sourceDistance_pos h) c hcCol hc
  obtain ⟨g,hgc⟩ := exists_mVertex_of_color T hcCol
  have hg : act T g⁻¹ c = alpha T := by
    rw [hgc,act_mVertex,mul_inv_cancel]
    rfl
  have hc' : color T (act T g⁻¹ c) = false := by rw [hg];rfl
  have hd0 := (criticalPair_act_iff T g⁻¹ c (alpha T)
    ((sourceGeometry h).exists_critical c hcCol)
    ((sourceGeometry h).exists_critical (act T g⁻¹ c) hc')).mpr hr
  have hd : CriticalPair T (alpha T) (act T g⁻¹ (alpha T))
      ((sourceGeometry h).exists_critical _ rfl) := by simpa only [hg] using hd0
  have hh := critical_Z_core_index_two h e hz hk hb _ hd
  have hi : (Q T (act T g⁻¹ c)).relIndex (Z T (act T g⁻¹ (alpha T))) = 2 := by
    simpa only [hg] using hh
  rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj (g⁻¹)⁻¹).injective] at hi
  exact hi

include h e hz hk in
/-- The original cubic-kernel pair supplies every geometric premise for
favorable-pair selection; no plane equality or full orbit movement is assumed. -/
theorem preliminary_localData (hb : sourceDistance h = 2) :
    BeforePlane.LocalData (sourceGeometry h) where
  edge_centralizer := sourceEdgeCentralizer h e
  orbit_core := fun _ _ hc hab hcb => critical_orbit_le_core h e hz hk hb hc hab hcb
  commutator_edge := fun _ _ hc hab hcb => orbit_commutator_le_edge h e hz hk hb hc hab hcb
  image_two := fun _ hc => opposite_Z_core_index_two h e hz hk hb _ hc
  plane_not_fixed := fun _ _ hc hab hcb => critical_plane_not_fixed h e hz hk hb hc hab hcb

include h e hz hk in
/-- A favorable pair at the actual base edge, including the literal reversed
orbit and the strict displacement comparison used in source (3.6). -/
theorem exists_preliminary_pair (hb : sourceDistance h = 2) :
    ∃ o : BeforePlane.PreliminaryPair T (sourceGeometry h), o.b = beta T :=
  BeforePlane.exists_preliminaryPair_base (sourceGeometry h)
    h.relative_radical.isPGroup h.relative_radical.twoCore_le
    (preliminary_localData h e hz hk hb) hb

include h e hz hk in
/-- Selection and exponent two together on one actual critical pair. The
orbit quotient and paired commutator are elementary; the whole orbit is
still to be recognized and its movement and intersection bounds discharged. -/
theorem exists_elementary_preliminary_pair (hb : sourceDistance h = 2) :
    ∃ o : BeforePlane.PreliminaryPair T (sourceGeometry h), o.b = beta T ∧
      IsElementaryAbelian 2 (OrbitQuotient T o.c o.b) ∧
      IsElementaryAbelian 2 (criticalOrbit T o.c o.b ⊓ o.opposite : Subgroup (FreeAmalgam T)) ∧
      IsElementaryAbelian 2 (⁅criticalOrbit T o.c o.b,o.opposite⁆ : Subgroup (FreeAmalgam T)) := by
  obtain ⟨o,ho⟩ := exists_preliminary_pair h e hz hk hb
  exact ⟨o,ho,o.quotient_elementary,
    paired_intersection_elementary h e hz hk hb o.critical o.adjacent_left o.adjacent_right o.rebased,
    paired_commutator_elementary h e hz hk hb o.critical o.adjacent_left o.adjacent_right o.rebased⟩

/-- Conjugation on the literal orbit quotient, with actor the original relative group. -/
@[expose] def orbitQuotientAction (o : BeforePlane.PreliminaryPair T (sourceGeometry h)) :
    M →* MulAut (OrbitQuotient T o.c o.b) :=
  (orbitConjugation T o.c o.b).comp Subgroup.topEquiv.symm.toMonoidHom

include h in
/-- The orbit action kernel is measured on the actual subgroup quotient. -/
theorem orbitQuotientAction_mem_kernel (o : BeforePlane.PreliminaryPair T (sourceGeometry h))
    (g : M) : g ∈ (orbitQuotientAction h o).ker ↔
      ∀ a ∈ criticalOrbitNative T o.c o.b, ⁅g,a⁆ ∈ orbitLayer T := by
  let := o.quotient_elementary
  have he : g ∈ (orbitQuotientAction h o).ker ↔
      (⟨g,mem_top g⟩ : (⊤ : Subgroup M)) ∈ (orbitRepresentation T o.c o.b).ker := by
    constructor
    · intro hg
      apply LinearMap.ext
      intro x
      exact congrArg (fun f : MulAut (OrbitQuotient T o.c o.b) => Additive.ofMul (f x.toMul)) hg
    · intro hg
      apply MulEquiv.ext
      intro x
      exact congrArg (fun f : Module.End (ZMod 2) (Additive (OrbitQuotient T o.c o.b)) =>
        (f (Additive.ofMul x)).toMul) hg
  exact he.trans ((orbitSection T o.c o.b o.layer_le).action_mem_ker_iff ⟨g,mem_top g⟩)

include h e hz hk in
/-- The kernel on the later orbit quotient also lies between Q and E.
Noncentrality excludes killing the component; the odd central factor remains. -/
theorem orbitQuotientAction_kernel_bounds
    (o : BeforePlane.PreliminaryPair T (sourceGeometry h)) :
    pCore 2 M ≤ (orbitQuotientAction h o).ker ∧
      (orbitQuotientAction h o).ker ≤ extensionKernel h := by
  let C := (orbitQuotientAction h o).ker
  have hQC : pCore 2 M ≤ C := by
    intro g hg
    apply (orbitQuotientAction_mem_kernel h o g).mpr
    intro a ha
    exact o.commutator_le_layer (commutator_mem_commutator hg ha)
  refine ⟨hQC,?_⟩
  rcases normal_over_core_dichotomy h e C hQC with hCE | hKC
  · exact hCE
  exfalso
  apply critical_orbit_noncentral h e hz hk o.distance_two o.critical
    o.adjacent_left o.adjacent_right
  have hcomm : ⁅K,criticalOrbitNative T o.c o.b⁆ ≤ orbitLayer T := by
    apply commutator_le.mpr
    intro k hkK a ha
    exact (orbitQuotientAction_mem_kernel h o k).mp (hKC hkK) a ha
  rw [commutator_comm] at hcomm
  have hh := map_mono (f := embedM T) hcomm
  rw [map_commutator,←graph_component h] at hh
  exact hh.trans (map_comap_le _ _)

include h e hz hk in
/-- The literal orbit action kernel is Q or the retained cubic extension E. -/
theorem orbitQuotientAction_kernel_cases
    (o : BeforePlane.PreliminaryPair T (sourceGeometry h)) :
    (orbitQuotientAction h o).ker = pCore 2 M ∨
      (orbitQuotientAction h o).ker = extensionKernel h := by
  let C := (orbitQuotientAction h o).ker
  obtain ⟨hQC,hCE⟩ := orbitQuotientAction_kernel_bounds h e hz hk o
  have hi : (pCore 2 M).relIndex (extensionKernel h) = 3 := by
    change ((pCore 2 M).comap (extensionKernel h).subtype).index = 3
    rw [←pCore_subnormal_eq_comap 2 (inferInstance : (extensionKernel h).Normal).isSubnormal]
    exact extensionKernel_core_index h hz
  have hm := relIndex_mul_relIndex (pCore 2 M) C (extensionKernel h) hQC hCE
  rw [hi] at hm
  have hd : (pCore 2 M).relIndex C ∣ 3 := ⟨C.relIndex (extensionKernel h),hm.symm⟩
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with hone | hthree
  · exact Or.inl (le_antisymm (relIndex_eq_one.mp hone) hQC)
  · rw [hthree] at hm
    have hone : C.relIndex (extensionKernel h) = 1 := by omega
    exact Or.inr (le_antisymm hCE (relIndex_eq_one.mp hone))

include h e hz hk in
/-- On any two-subgroup the orbit action loses exactly its original Q intersection,
even when its full kernel contains the odd cubic quotient. -/
theorem orbitQuotientAction_two_intersection
    (o : BeforePlane.PreliminaryPair T (sourceGeometry h))
    (A : Subgroup M) (hA : IsPGroup 2 A) :
    A ⊓ (orbitQuotientAction h o).ker = A ⊓ pCore 2 M := by
  obtain ⟨hQC,hCE⟩ := orbitQuotientAction_kernel_bounds h e hz hk o
  apply le_antisymm
  · exact le_inf inf_le_left (two_subgroup_le_core_of_le_extensionKernel h hz
      (A ⊓ (orbitQuotientAction h o).ker)
      (hA.of_injective (inclusion inf_le_left) (inclusion_injective _))
      (inf_le_right.trans hCE))
  · exact inf_le_inf_left A hQC

include h e hz hk in
/-- Exact order of the opposite actor on the literal orbit quotient.
This is the source index required by the subsequent strict-offender calculation. -/
theorem orbitQuotientAction_opposite_card
    (o : BeforePlane.PreliminaryPair T (sourceGeometry h)) :
    Nat.card ((o.opposite.comap (embedM T)).map (orbitQuotientAction h o)) =
      (Q T (alpha T)).relIndex o.opposite := by
  let A := o.opposite.comap (embedM T)
  have hA : IsPGroup 2 A :=
    ((Q_isPGroup T h.relative_radical.isPGroup h.relative_radical.twoCore_le o.c
      (critical_endpoint_color T (alpha T) rfl _ o.critical)).of_injective
        (inclusion o.opposite_le) (inclusion_injective _)).comap_of_injective
      (embedM T) (embedM_injective T)
  rw [←relIndex_ker,←inf_relIndex_left A,orbitQuotientAction_two_intersection h e hz hk o A hA,
    inf_relIndex_left]
  have hh := relIndex_map_map_of_injective (pCore 2 M) A (embedM_injective T)
  rw [o.opposite_map,←Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le] at hh
  exact hh.symm

/-- The faithful binary action of all automorphisms of the actual elementary orbit quotient. -/
@[expose] def orbitAutomorphismRepresentation
    (o : BeforePlane.PreliminaryPair T (sourceGeometry h)) :
    letI := o.quotient_elementary
    Representation (ZMod 2) (MulAut (OrbitQuotient T o.c o.b))
      (Additive (OrbitQuotient T o.c o.b)) := by
  letI := o.quotient_elementary
  exact {
    toFun g := g.toMonoidHom.toAdditive.toZModLinearMap 2
    map_one' := by ext v; rfl
    map_mul' := by intros; ext v; rfl }

include h in
theorem orbitAutomorphismRepresentation_injective
    (o : BeforePlane.PreliminaryPair T (sourceGeometry h)) :
    Function.Injective (orbitAutomorphismRepresentation h o) := by
  let := o.quotient_elementary
  intro a b he
  apply MulEquiv.ext
  intro x
  exact congrArg (fun f : Module.End (ZMod 2) (Additive (OrbitQuotient T o.c o.b)) =>
    (f (Additive.ofMul x)).toMul) he

include h in
/-- The reversed orbit acts quadratically on the literal elementary quotient. -/
theorem orbit_actor_quadratic
    (o : BeforePlane.PreliminaryPair T (sourceGeometry h)) :
    letI := o.quotient_elementary
    Representation.BinaryOffender.IsQuadratic (orbitAutomorphismRepresentation h o)
      ((o.opposite.comap (embedM T)).map (orbitQuotientAction h o)) := by
  let := o.quotient_elementary
  let A := criticalOrbitNative T o.c o.b
  let B := o.opposite.comap (embedM T)
  let q := (orbitQuotientAction h o).comp (⊤ : Subgroup M).subtype
  let σ := orbitAutomorphismRepresentation h o
  have hcomp : σ.comp q = orbitRepresentation T o.c o.b := by
    ext g v
    rfl
  have hmap : (B.subgroupOf ⊤).map q = B.map (orbitQuotientAction h o) := by
    rw [show q = (orbitQuotientAction h o).comp (⊤ : Subgroup M).subtype from rfl,
      ←map_map,map_subgroupOf_eq_of_le (show B ≤ ⊤ from le_top)]
  have hd : (cosetGraph T).dist (alpha T) o.c = 2 :=
    o.critical.1.trans (((sourceGeometry h).distance_constant _ rfl).trans o.distance_two)
  have hAG : criticalOrbit T o.c o.b ≤ stabilizer T o.c := by
    have hAQ : criticalOrbit T o.c o.b ≤ Q T (alpha T) := by
      rw [Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
      exact map_mono o.orbit_le_core
    exact hAQ.trans (Q_le_stabilizer_of_dist_two T (alpha T) o.c rfl hd)
  have hAB : ⁅criticalOrbit T o.c o.b,o.opposite⁆ ≤ o.opposite :=
    le_normalizer_iff_commutator_le_right.mp (hAG.trans o.opposite_normalized)
  have htrip : ⁅o.opposite,⁅o.opposite,criticalOrbit T o.c o.b⁆⁆ ≤ Z T (alpha T) := by
    rw [commutator_comm o.opposite (criticalOrbit T o.c o.b)]
    apply ((commutator_mono o.opposite_le hAB).trans o.opposite_commutator).trans
    have hbcol := CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore.edge_color o.adjacent_left
    simp only [Z,show color T (alpha T) = false from rfl,hbcol,
      Bool.true_eq_false,if_true,if_false]
    exact le_iSup_of_le o.b (le_iSup_of_le o.adjacent_left le_rfl)
  have ht : ⁅B,⁅B,A⁆⁆ ≤ orbitLayer T := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator,map_commutator,o.opposite_map]
    exact htrip
  have s : BinaryConjugationSection ⊤ A (orbitLayer T) (σ.comp q) := by
    rw [hcomp]
    exact orbitSection T o.c o.b o.layer_le
  have hh := s.isQuadratic_of_triple_commutator_le ⊤ A (orbitLayer T) B σ q ht
  rwa [hmap] at hh

include h in
/-- The actual opposite-orbit image is elementary, proved from quadraticity and faithfulness. -/
theorem orbit_actor_elementary
    (o : BeforePlane.PreliminaryPair T (sourceGeometry h)) :
    IsElementaryAbelian 2 ((o.opposite.comap (embedM T)).map (orbitQuotientAction h o)) := by
  let := o.quotient_elementary
  exact Representation.BinaryOffender.elementary_of_faithful_quadratic
    (orbitAutomorphismRepresentation h o) (orbitAutomorphismRepresentation_injective h o)
    _ (orbit_actor_quadratic h o)

include h e hz hk in
/-- Elementary orbit automorphisms give an elementary six-letter image;
the larger odd kernel is killed explicitly by its original projection. -/
theorem opposite_permutation_image_elementary
    (o : BeforePlane.PreliminaryPair T (sourceGeometry h)) :
    IsElementaryAbelian 2 ((o.opposite.comap (embedM T)).map π) := by
  let A := o.opposite.comap (embedM T)
  let D := A.map π
  let := orbit_actor_elementary h o
  have hs (x : D) : x ^ 2 = 1 := by
    obtain ⟨a,ha,he⟩ := x.property
    have hc : a ^ 2 ∈ (orbitQuotientAction h o).ker := by
      change orbitQuotientAction h o (a ^ 2) = 1
      rw [map_pow]
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2) _
        (mem_map_of_mem (orbitQuotientAction h o) ha)
    have hE := (orbitQuotientAction_kernel_bounds h e hz hk o).2 hc
    have hp : π (a ^ 2) = 1 := by
      change a ^ 2 ∈ (π).ker
      rw [projection_kernel]
      exact hE
    apply Subtype.ext
    change (x : Equiv.Perm (Fin 6)) ^ 2 = 1
    rw [←he,←map_pow]
    exact hp
  exact {
    toIsMulCommutative := ⟨⟨fun a b =>
      Commute.of_orderOf_dvd_two (fun x => orderOf_dvd_of_pow_eq_one (hs x)) a b⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }

include h e hz hk in
/-- The source opposite-orbit index is exactly its six-letter image order,
although neither initial nor later action kernel has been replaced by Q. -/
theorem opposite_permutation_image_card
    (o : BeforePlane.PreliminaryPair T (sourceGeometry h)) :
    Nat.card ((o.opposite.comap (embedM T)).map π) =
      (Q T (alpha T)).relIndex o.opposite := by
  let A := o.opposite.comap (embedM T)
  have hA : IsPGroup 2 A :=
    ((Q_isPGroup T h.relative_radical.isPGroup h.relative_radical.twoCore_le o.c
      (critical_endpoint_color T (alpha T) rfl _ o.critical)).of_injective
        (inclusion o.opposite_le) (inclusion_injective _)).comap_of_injective
      (embedM T) (embedM_injective T)
  have hi : A ⊓ extensionKernel h = A ⊓ pCore 2 M := by
    apply le_antisymm
    · exact le_inf inf_le_left (two_subgroup_le_core_of_le_extensionKernel h hz
        (A ⊓ extensionKernel h)
        (hA.of_injective (inclusion inf_le_left) (inclusion_injective _)) inf_le_right)
    · exact inf_le_inf_left A le_sup_right
  rw [←relIndex_ker,projection_kernel,←inf_relIndex_left A,hi,inf_relIndex_left]
  have hh := relIndex_map_map_of_injective (pCore 2 M) A (embedM_injective T)
  rw [o.opposite_map,←Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le] at hh
  exact hh.symm

include h e hz hk in
/-- Both literal favorable orbit indices are at most eight, and the fixed
preimage index is at most four. These bounds precede full orbit recognition. -/
theorem preliminary_orbit_index_bounds
    (o : BeforePlane.PreliminaryPair T (sourceGeometry h)) :
    (Q T (alpha T)).relIndex o.opposite ≤ 8 ∧
    (Q T o.c).relIndex (criticalOrbit T o.c o.b) ≤ 8 ∧
    (commutatorPreimage (criticalOrbit T o.c o.b) o.opposite (Z T (alpha T))).relIndex
      (criticalOrbit T o.c o.b) ≤ 4 := by
  let A := (o.opposite.comap (embedM T)).map π
  let := opposite_permutation_image_elementary h e hz hk o
  have hcard : Nat.card A ≤ 8 := by
    by_cases ha : A = ⊥
    · simp [ha]
    have hel : Representation.BinaryOffender.IsElementaryTwo A := ⟨ha,inferInstance⟩
    have hr := CFSG.Quasithin.ChapterB.Offenders.Six.rank_le_three hel
    rw [hel.card_eq_two_pow_rank]
    exact Nat.pow_le_pow_right (by decide) hr
  rw [opposite_permutation_image_card h e hz hk o] at hcard
  have hsecond := o.ordered_index.trans hcard
  exact ⟨hcard,hsecond,by have hh := o.strict_index; omega⟩

/-- The favorable pair selected from the original cubic distance-two hypotheses. -/
@[expose] def selectedOrbitPair (hb : sourceDistance h = 2) :
    BeforePlane.PreliminaryPair T (sourceGeometry h) :=
  (exists_preliminary_pair h e hz hk hb).choose

include h e hz hk in
/-- The selected pair uses the original base edge. -/
theorem selectedOrbitPair_base (hb : sourceDistance h = 2) :
    (selectedOrbitPair h e hz hk hb).b = beta T :=
  (exists_preliminary_pair h e hz hk hb).choose_spec

include h e hz hk in
/-- All bounds on one selected source pair, with its actual action kernel retained. -/
theorem selectedOrbitPair_estimates (hb : sourceDistance h = 2) :
    let o := selectedOrbitPair h e hz hk hb
    ((orbitQuotientAction h o).ker = pCore 2 M ∨
      (orbitQuotientAction h o).ker = extensionKernel h) ∧
    (Q T (alpha T)).relIndex o.opposite ≤ 8 ∧
    (Q T o.c).relIndex (criticalOrbit T o.c o.b) ≤ 8 ∧
    (commutatorPreimage (criticalOrbit T o.c o.b) o.opposite (Z T (alpha T))).relIndex
      (criticalOrbit T o.c o.b) ≤ 4 :=
  ⟨orbitQuotientAction_kernel_cases h e hz hk _,preliminary_orbit_index_bounds h e hz hk _⟩

end AlternatingSixReconstruction.Exceptional.Exhaustion.CubicAction
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
