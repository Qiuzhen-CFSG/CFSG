module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicEndpointGrowth
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalMovedSpace
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreTranspositionFixed.SmallImage
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.Representation.GeneratedSubgroupInvariants
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import Theory.Representation.BinaryOffender.IrreducibleTransport

/-!
# Critical kernel transport with the cubic action kernel retained

A fixed hyperplane in either full central cover determines the small marked
actor image. Its pointwise fixer is the actual initial-action kernel E joined
to that actor; E/Q retains order three. The natural invariant pairing then
recovers the small actor image from its commutator line.

At a critical vertex this identifies the pointwise fixer of Z_a intersect Q_c
with E_a joined to Z_c. Equal lines give equal full critical kernels, and
conversely. The line centralizer and kernel normalizer coincide inside the
starting stabilizer, so a single conjugator displaces the kernel and line and
transports the entire critical path. The edge centralizer identity recovers
literal intersections with Q without replacing E by Q.

CubicCoordinatedPaths applies this family to source path choices and the
whole-core and literal C.1.32 consumers. The source-prescribed shifted
endpoints, the exclusions of (5.11)--(5.12), and both final reconstruction
outcomes remain with qt-e-ms-small-a6-reconstruction.

Source: MS93 (3.3)(ii), pp.866--867, and (5.11), printed p.923.
Adapts Natural.Exhaustion.LargeDistance.SectionFive.SmallKernel and
KernelTransport to the original cubic kernel, preserving both cover orders.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W" => (⁅centralOmega L R,L.subgroupOf (L ⊔ R)⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk
local notation "T" => edge L R
local instance : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left _ _)
private abbrev coverAction : Representation (ZMod 2) (Equiv.Perm (Fin 6)) (Additive W) := by
  let := h.relative_normal
  exact NormalElementaryQuotient.representation W π
    (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk)
private def coverMap : Additive W →ₗ[ZMod 2] natural (Fin 6) :=
  Classical.choose (CubicAction.moved_natural_projection h e hz hk)
private theorem coverMap_surjective : Function.Surjective (coverMap h e hz hk) :=
  (Classical.choose_spec (CubicAction.moved_natural_projection h e hz hk)).1
private theorem coverMap_equivariant (g : Equiv.Perm (Fin 6)) (v : Additive W) :
    coverMap h e hz hk (coverAction h e hz hk g v) =
      naturalRepresentation (Fin 6) g (coverMap h e hz hk v) := by
  let := h.relative_normal
  obtain ⟨a,rfl⟩ := CubicEven.projection_surjective h e hz hk g
  have he : coverAction h e hz hk (π a) v = Additive.ofMul (MulAut.conjNormal a v.toMul) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact NormalElementaryQuotient.representation_apply W π
      (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk) a v
  rw [he]
  exact (Classical.choose_spec (CubicAction.moved_natural_projection h e hz hk)).2.2 a v

include h e hz hk in
/-- The pointwise fixer of the full cover's fixed hyperplane has no larger
marked image than the original nontrivial actor. Its full preimage retains E. -/
theorem cover_small_fixed_centralizer (A : Subgroup M)
    (hne : ¬ A ≤ extensionKernel h)
    (hindex : (centralizer (A : Set M)).relIndex (W) ≤ 2) :
    centralizer (W ⊓ centralizer (A : Set M) : Set M) ≤
      extensionKernel h ⊔ A := by
  let := h.relative_normal
  let F := W ⊓ centralizer (A : Set M)
  let B := centralizer (F : Set M)
  have hAB : A ≤ B := le_centralizer_iff.mpr inf_le_right
  have hFB : F ≤ centralizer (B : Set M) := le_centralizer_iff.mpr le_rfl
  have hfix : fixedSpace (coverAction h e hz hk) (A.map π) ≤
      fixedSpace (coverAction h e hz hk) (B.map π) := by
    intro v hv
    apply (NormalElementaryQuotient.mem_fixedSpace_image (W)
      π (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk) B v).mpr
    exact hFB ⟨v.toMul.property,
      (NormalElementaryQuotient.mem_fixedSpace_image (W)
        π (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk) A v).mp hv⟩
  have hsmallA : fixedCodim (coverAction h e hz hk) (A.map π) ≤ 1 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
      (W) π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk)] at hindex
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hindex
  have hsmallB : fixedCodim (coverAction h e hz hk) (B.map π) ≤ 1 := by
    have ha := fixedCodim_add_finrank (coverAction h e hz hk) (A.map π)
    have hb := fixedCodim_add_finrank (coverAction h e hz hk) (B.map π)
    have hh := Submodule.finrank_mono hfix
    omega
  have hnB : B.map π ≠ ⊥ := by
    intro he
    apply hne
    have hker := (map_eq_bot_iff B).mp he
    rw [(CubicAction.projection_kernel h e hz hk)] at hker
    exact hAB.trans hker
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (B.map π) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction h e hz hk) (naturalRepresentation (Fin 6))
      (coverMap h e hz hk)
      (coverMap_surjective h e hz hk)
      (coverMap_equivariant h e hz hk) (B.map π)).trans hsmallB
  obtain ⟨t,ht,hswap,hB⟩ :=
    Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreTranspositionFixed.small_image_eq_zpowers
      (B.map π) hnB hnat
  have hnA : A.map π ≠ ⊥ := by
    intro he
    exact hne ((CubicAction.projection_kernel h e hz hk) ▸ (map_eq_bot_iff A).mp he)
  have hcardA := (one_lt_card_iff_ne_bot (A.map π)).mpr hnA
  have hcardB : Nat.card (B.map π) = 2 := by
    rw [hB,Nat.card_zpowers,hswap.orderOf]
  have hBA : B.map π = A.map π :=
    (eq_of_le_of_card_ge (map_mono hAB) (by omega)).symm
  have hle : B ≤ (A.map π).comap π := by
    rw [←hBA]
    exact le_comap_map π B
  rw [Subgroup.comap_map_eq,(CubicAction.projection_kernel h e hz hk)] at hle
  exact hle.trans_eq (sup_comm _ _)

private theorem small_images_eq_of_moved_eq
    (A B : Subgroup (Equiv.Perm (Fin 6))) (hA : A ≠ ⊥) (hB : B ≠ ⊥)
    (hsmall : fixedCodim (naturalRepresentation (Fin 6)) A ≤ 1)
    (hmoved : subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ A =
      subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ B) : A = B := by
  open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing in
  have hfixed : fixedSpace (naturalRepresentation (Fin 6)) A =
      fixedSpace (naturalRepresentation (Fin 6)) B := by
    rw [moved_eq_fixed_orthogonal,moved_eq_fixed_orthogonal] at hmoved
    have he := congrArg (fun I => form.orthogonal I) hmoved
    simpa only [LinearMap.BilinForm.orthogonal_orthogonal form_nondegenerate form_alt.isRefl] using he
  have hsup : fixedSpace (naturalRepresentation (Fin 6)) (A ⊔ B) =
      fixedSpace (naturalRepresentation (Fin 6)) A := by
    have hh : fixedSpace (naturalRepresentation (Fin 6)) (A ⊔ B) =
        fixedSpace (naturalRepresentation (Fin 6)) A ⊓ fixedSpace (naturalRepresentation (Fin 6)) B :=
      (naturalRepresentation (Fin 6)).invariants_comp_sup A B
    rw [hh,hfixed,inf_idem]
  have hsupsmall : fixedCodim (naturalRepresentation (Fin 6)) (A ⊔ B) ≤ 1 := by
    change Module.finrank (ZMod 2) ((natural (Fin 6)) ⧸
      fixedSpace (naturalRepresentation (Fin 6)) (A ⊔ B)) ≤ 1
    rw [hsup]
    exact hsmall
  have hsupne : A ⊔ B ≠ ⊥ := fun he => hA (le_bot_iff.mp (he ▸ le_sup_left))
  obtain ⟨t,_,ht,he⟩ :=
    Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreTranspositionFixed.small_image_eq_zpowers
      (A ⊔ B) hsupne hsupsmall
  have hc : Nat.card (A ⊔ B : Subgroup (Equiv.Perm (Fin 6))) = 2 := by rw [he,Nat.card_zpowers,ht.orderOf]
  have hAc := (one_lt_card_iff_ne_bot A).mpr hA
  have hBc := (one_lt_card_iff_ne_bot B).mpr hB
  exact (eq_of_le_of_card_ge (show A ≤ A ⊔ B from le_sup_left) (by omega)).trans
    (eq_of_le_of_card_ge (show B ≤ A ⊔ B from le_sup_right) (by omega)).symm

include h e hz hk in
/-- Equal commutators on the full cover determine equal small actor images.
The argument uses its surjective natural quotient, preserving the central kernel. -/
theorem cover_small_images_eq_of_commutator_eq (A B : Subgroup M)
    (hA : ¬ A ≤ extensionKernel h) (hB : ¬ B ≤ extensionKernel h)
    (hsmall : (centralizer (A : Set M)).relIndex (W) ≤ 2)
    (hcomm : ⁅W,A⁆ = ⁅W,B⁆) :
    A.map π = B.map π := by
  let := h.relative_normal
  have hne (X : Subgroup M) (hX : ¬ X ≤ extensionKernel h) :
      X.map π ≠ ⊥ := by
    intro he
    exact hX ((CubicAction.projection_kernel h e hz hk) ▸ (map_eq_bot_iff X).mp he)
  have hsmall' : fixedCodim (coverAction h e hz hk) (A.map π) ≤ 1 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
      (W) π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk)] at hsmall
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hsmall
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map π) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction h e hz hk) (naturalRepresentation (Fin 6))
      (coverMap h e hz hk)
      (coverMap_surjective h e hz hk)
      (coverMap_equivariant h e hz hk) (A.map π)).trans hsmall'
  have he : subspaceCommutator (coverAction h e hz hk) ⊤ (A.map π) =
      subspaceCommutator (coverAction h e hz hk) ⊤ (B.map π) := by
    have hm (X : Subgroup M) :
        NormalElementaryQuotient.commutatorSpace (W) X =
          subspaceCommutator (coverAction h e hz hk) ⊤ (X.map π) :=
      NormalElementaryQuotient.commutatorSpace_eq (W) π (CubicEven.projection_surjective h e hz hk)
        (CubicAction.moved_projection_kernel h e hz hk) X
    rw [←hm A,←hm B]
    unfold NormalElementaryQuotient.commutatorSpace
    rw [hcomm]
  have hm (X : Subgroup M) :
      subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (X.map π) =
        (subspaceCommutator (coverAction h e hz hk) ⊤ (X.map π)).map
          (coverMap h e hz hk) := by
    have hh := subspaceCommutator_map_embedding (naturalRepresentation (Fin 6))
      (coverAction h e hz hk) (MonoidHom.id _) (coverMap h e hz hk)
      (fun g v => (coverMap_equivariant h e hz hk g v).symm) (X.map π) ⊤
    simpa only [Submodule.map_top,LinearMap.range_eq_top.mpr
      (coverMap_surjective h e hz hk),map_id] using hh
  exact small_images_eq_of_moved_eq _ _ (hne A hA) (hne B hB) hnat (by rw [hm A,hm B,he])


include h e in
private theorem reverse_critical {a c : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a c) :
    CriticalPair T c a ((sourceGeometry h).exists_critical c p.end_color) :=
  critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    a p.start_color (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h)
    c p.end_color p.critical

include h e hz in
private theorem critical_comap_not_le_extension {a c : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a c)
    (i : M →* FreeAmalgam T) (hi : Function.Injective i)
    (hA : Z T c ≤ i.range) (hiQ : (pCore 2 M).map i = Q T a) :
    ¬ (Z T c).comap i ≤ extensionKernel h := by
  intro he
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) c p.end_color
  have ht : IsPGroup 2 ((Z T c).comap i) :=
    (IsElementaryAbelian.isPGroup 2 (Z T c)).comap_of_injective i hi
  have hh := map_mono (f := i)
    (two_subgroup_le_core_of_le_extensionKernel h hz _ ht he)
  rw [map_comap_eq_self hA,hiQ] at hh
  exact (reverse_critical h e p).2 hh

include h e hz hk in
/-- In the cubic branch, the relative fixer retains the entire initial kernel
E. The critical two-subgroup is still measured modulo the actual Q. -/
theorem small_critical_kernel_centralizer
    {a c : Vertex T} (p : CriticalPath T (sourceGeometry h) a c)
    (hp : (Q T c).relIndex (Z T a) < 4) :
    stabilizer T a ⊓ centralizer (Z T a ⊓ Q T c : Set (FreeAmalgam T)) ≤
      (stabilizer T a ⊓ centralizer (X T a : Set (FreeAmalgam T))) ⊔ Z T c := by
  obtain ⟨i,hi,hir,hiQ,hiE,hiU,_⟩ := graph_cover h e hz hk a p.start_color
  have hA : Z T c ≤ i.range := by
    rw [hir]
    exact critical_Z_le_stabilizer T (sourceGeometry h) a p.start_color
      (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h)
      p.critical
  have hfixed : U T a ⊓ centralizer (Z T c : Set (FreeAmalgam T)) ≤ Z T a ⊓ Q T c := by
    rw [←critical_seed_centralizer_intersection h e p]
    exact inf_le_inf_right _ (DistanceEight.U_le_Z T a)
  let A := (Z T c).comap i
  have hmA : A.map i = Z T c := map_comap_eq_self hA
  have hnA : ¬ A ≤ extensionKernel h := critical_comap_not_le_extension h e hz p i hi hA hiQ
  let := finite_Z T a
  let : Finite (U T a) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z T a)) (inclusion_injective _)
  have hC : Q T c ≤ centralizer (Z T c : Set (FreeAmalgam T)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q T c p.end_color))
  have hidx : (centralizer (Z T c : Set (FreeAmalgam T))).relIndex (U T a) ≤ 2 :=
    ((relIndex_le_of_le_left hC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z T a) index_ne_zero_of_finite)).trans_eq
      (small_critical_indices h e hz hk p hp).1
  have hidx' : (centralizer (A : Set M)).relIndex W ≤ 2 := by
    rw [←hiU,←hmA,←inf_relIndex_right,inf_comm,
      map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,
      inf_relIndex_left] at hidx
    exact hidx
  have hf := cover_small_fixed_centralizer h e hz hk A hnA hidx'
  rintro x ⟨hx,hfix⟩
  obtain ⟨m,rfl⟩ := hir.symm ▸ hx
  have hmfix : m ∈ centralizer (W ⊓ centralizer (A : Set M) : Set M) := by
    intro w hw
    apply hi
    simp only [map_mul]
    apply hfix
    apply hfixed
    rw [←hiU,←hmA,map_inf_centralizer_of_injective i hi]
    exact mem_map_of_mem i hw
  have hh := mem_map_of_mem i (hf hmfix)
  rwa [Subgroup.map_sup,hiE,hmA] at hh

include h e hz hk in
/-- The full pointwise fixer of a small critical kernel, with E/Q retained. -/
theorem small_critical_kernel_centralizer_eq
    {a c : Vertex T} (p : CriticalPath T (sourceGeometry h) a c)
    (hp : (Q T c).relIndex (Z T a) < 4) :
    stabilizer T a ⊓ centralizer (Z T a ⊓ Q T c : Set (FreeAmalgam T)) =
      (stabilizer T a ⊓ centralizer (X T a : Set (FreeAmalgam T))) ⊔ Z T c := by
  apply le_antisymm (small_critical_kernel_centralizer h e hz hk p hp)
  apply sup_le
  · exact inf_le_inf_left _ (centralizer_le
      (inf_le_left.trans ((sourceGeometry h).omega_bound a p.start_color (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h))))
  · apply le_inf
    · exact critical_Z_le_stabilizer T (sourceGeometry h) a p.start_color
        (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h)
        p.critical
    · exact (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q T c p.end_color)).trans (centralizer_le inf_le_right)

include h e hz hk in
/-- Equal kernels determine the same full initial-actor coset and critical line. -/
theorem small_critical_equal_kernels
    {a c f : Vertex T} (p : CriticalPath T (sourceGeometry h) a c)
    (q : CriticalPath T (sourceGeometry h) a f)
    (hp : (Q T c).relIndex (Z T a) < 4) (hq : (Q T f).relIndex (Z T a) < 4)
    (hkernel : Z T a ⊓ Q T c = Z T a ⊓ Q T f) :
    (stabilizer T a ⊓ centralizer (X T a : Set (FreeAmalgam T))) ⊔ Z T c =
      (stabilizer T a ⊓ centralizer (X T a : Set (FreeAmalgam T))) ⊔ Z T f ∧
      ⁅Z T a,Z T c⁆ = ⁅Z T a,Z T f⁆ := by
  have hj : (stabilizer T a ⊓ centralizer (X T a : Set (FreeAmalgam T))) ⊔ Z T c =
      (stabilizer T a ⊓ centralizer (X T a : Set (FreeAmalgam T))) ⊔ Z T f := by
    rw [←small_critical_kernel_centralizer_eq h e hz hk p hp,
      ←small_critical_kernel_centralizer_eq h e hz hk q hq]
    exact congrArg (fun D : Subgroup (FreeAmalgam T) =>
      stabilizer T a ⊓ centralizer (D : Set (FreeAmalgam T))) hkernel
  refine ⟨hj,?_⟩
  have hE : stabilizer T a ⊓ centralizer (X T a : Set (FreeAmalgam T)) ≤
      centralizer (Z T a : Set (FreeAmalgam T)) :=
    inf_le_right.trans (centralizer_le
      ((sourceGeometry h).omega_bound a p.start_color (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h)))
  have hA := critical_Z_le_stabilizer T (sourceGeometry h) a p.start_color
    (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h) p.critical
  have hB := critical_Z_le_stabilizer T (sourceGeometry h) a q.start_color
    (by rw [(sourceGeometry h).distance_constant a q.start_color]; exact sourceDistance_pos h) q.critical
  exact (commutator_eq_of_centralizing_sup rfl hE (hA.trans (Z_normalized T a))).trans
    ((congrArg (fun E => ⁅Z T a,E⁆) hj).trans
      (commutator_eq_of_centralizing_sup rfl hE (hB.trans (Z_normalized T a))).symm)
include h e hz hk in
/-- At a common critical starting vertex, equality of the actual small lines
forces equality of the opposite seed images modulo the retained cubic kernel. -/
theorem small_critical_equal_lines_image
    {a a' b' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a a')
    (q : CriticalPath T (sourceGeometry h) a b')
    (hp : (Q T a').relIndex (Z T a) < 4)
    (hq : (Q T b').relIndex (Z T a) < 4)
    (hline : ⁅Z T a,Z T a'⁆ = ⁅Z T a,Z T b'⁆) :
    (stabilizer T a ⊓ centralizer (X T a : Set (FreeAmalgam T))) ⊔ Z T a' = (stabilizer T a ⊓ centralizer (X T a : Set (FreeAmalgam T))) ⊔ Z T b' := by
  obtain ⟨i,hi,hir,hiQ,hiE,hiU,_⟩ := graph_cover h e hz hk a p.start_color
  have hA : Z T a' ≤ i.range := by
    rw [hir]
    exact critical_Z_le_stabilizer T (sourceGeometry h) a p.start_color
      (by rw [(sourceGeometry h).distance_constant a p.start_color]
          exact sourceDistance_pos h) p.critical
  have hB : Z T b' ≤ i.range := by
    rw [hir]
    exact critical_Z_le_stabilizer T (sourceGeometry h) a q.start_color
      (by rw [(sourceGeometry h).distance_constant a q.start_color]
          exact sourceDistance_pos h) q.critical
  let A := (Z T a').comap i
  let B := (Z T b').comap i
  have hmA : A.map i = Z T a' := map_comap_eq_self hA
  have hmB : B.map i = Z T b' := map_comap_eq_self hB
  have hneA : ¬ A ≤ extensionKernel h := critical_comap_not_le_extension h e hz p i hi hA hiQ
  have hneB : ¬ B ≤ extensionKernel h := critical_comap_not_le_extension h e hz q i hi hB hiQ
  have hcomm : ⁅W,A⁆ = ⁅W,B⁆ := by
    apply map_injective hi
    rw [map_commutator,hiU,hmA,map_commutator,hiU,hmB,
      small_critical_moving_commutator_eq h e hz hk p hp,
      small_critical_moving_commutator_eq h e hz hk q hq]
    exact hline
  have hC : Q T a' ≤ centralizer (Z T a' : Set (FreeAmalgam T)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q T a' p.end_color))
  let := finite_Z T a
  let : Finite (U T a) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z T a)) (inclusion_injective _)
  have hidx : (centralizer (Z T a' : Set (FreeAmalgam T))).relIndex
      (U T a) ≤ 2 :=
    ((relIndex_le_of_le_left hC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z T a)
        index_ne_zero_of_finite)).trans_eq (small_critical_indices h e hz hk p hp).1
  have hidx' : (centralizer (A : Set M)).relIndex (W) ≤ 2 := by
    rw [←hiU,←hmA,←inf_relIndex_right,inf_comm,
      map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,
      inf_relIndex_left] at hidx
    exact hidx
  have him := cover_small_images_eq_of_commutator_eq h e hz hk A B hneA hneB hidx' hcomm
  have hj := congrArg (Subgroup.comap π) him
  rw [comap_map_eq,comap_map_eq,CubicAction.projection_kernel h e hz hk] at hj
  have hj' := congrArg (Subgroup.map i) hj
  rw [Subgroup.map_sup,Subgroup.map_sup,hmA,hmB,hiE] at hj'
  exact (sup_comm _ _).trans (hj'.trans (sup_comm _ _))

include h e hz hk in
/-- The full endpoint kernel is recovered from the small critical line.
This is the reverse implication needed in the first paragraph of (5.11). -/
theorem small_critical_equal_lines_kernels
    {a a' b' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a a')
    (q : CriticalPath T (sourceGeometry h) a b')
    (hp : (Q T a').relIndex (Z T a) < 4)
    (hq : (Q T b').relIndex (Z T a) < 4)
    (hline : ⁅Z T a,Z T a'⁆ = ⁅Z T a,Z T b'⁆) :
    Z T a ⊓ Q T a' = Z T a ⊓ Q T b' := by
  have hj := small_critical_equal_lines_image h e hz hk p q hp hq hline
  have hQ : stabilizer T a ⊓ centralizer (X T a : Set (FreeAmalgam T)) ≤
      centralizer (Z T a : Set (FreeAmalgam T)) :=
    inf_le_right.trans (centralizer_le
      ((sourceGeometry h).omega_bound a p.start_color (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h)))
  have step {c f : Vertex T}
      (pc : CriticalPath T (sourceGeometry h) a c)
      (pf : CriticalPath T (sourceGeometry h) a f)
      (he : (stabilizer T a ⊓ centralizer (X T a : Set (FreeAmalgam T))) ⊔ Z T c = (stabilizer T a ⊓ centralizer (X T a : Set (FreeAmalgam T))) ⊔ Z T f) :
      Z T a ⊓ Q T c ≤ Z T a ⊓ Q T f := by
    intro x hx
    rw [←critical_seed_centralizer_intersection h e pf]
    refine ⟨hx.1,?_⟩
    have hfix : (stabilizer T a ⊓ centralizer (X T a : Set (FreeAmalgam T))) ⊔ Z T c ≤
        centralizer ({x} : Set (FreeAmalgam T)) := by
      apply sup_le
      · intro y hy z hz
        rw [Set.mem_singleton_iff.mp hz]
        exact hQ hy x hx.1
      · intro y hy z hz
        rw [Set.mem_singleton_iff.mp hz]
        exact (commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q T c pc.end_color) hy) x hx.2
    intro z hz
    have hz' := hfix (he.symm ▸ (show z ∈ (stabilizer T a ⊓ centralizer (X T a : Set (FreeAmalgam T))) ⊔ Z T f from mem_sup_right hz))
    exact (hz' x (Set.mem_singleton _)).symm
  exact le_antisymm (step p q hj) (step q p hj.symm)

include h e hz hk in
/-- Kernel and line equality are equivalent for two small critical paths
with the same starting vertex and the literal original endpoint groups. -/
theorem small_critical_kernel_eq_iff_line_eq
    {a a' b' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a a')
    (q : CriticalPath T (sourceGeometry h) a b')
    (hp : (Q T a').relIndex (Z T a) < 4)
    (hq : (Q T b').relIndex (Z T a) < 4) :
    Z T a ⊓ Q T a' = Z T a ⊓ Q T b' ↔
      ⁅Z T a,Z T a'⁆ = ⁅Z T a,Z T b'⁆ :=
  ⟨fun he => (small_critical_equal_kernels h e hz hk p q hp hq he).2,
    small_critical_equal_lines_kernels h e hz hk p q hp hq⟩


include h e hz hk in
/-- The source conjugator preserves the full endpoint kernel exactly when
it preserves the critical line. The starting vertex and conjugator are shared. -/
theorem small_critical_conjugate_kernel_iff
    {a a' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a a')
    (hp : (Q T a').relIndex (Z T a) < 4)
    (g : FreeAmalgam T) (hg : g ∈ stabilizer T a) :
    Z T a ⊓ Q T (act T g a') = Z T a ⊓ Q T a' ↔
      (⁅Z T a,Z T a'⁆ : Subgroup (FreeAmalgam T)).map
        (MulAut.conj g⁻¹).toMonoidHom = ⁅Z T a,Z T a'⁆ := by
  have hga : act T g a = a := hg
  have q : CriticalPath T (sourceGeometry h) a (act T g a') := by
    simpa only [hga] using p.act g
  have hq : (Q T (act T g a')).relIndex (Z T a) < 4 := by
    rw [←hga,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hp
  have hmap : (⁅Z T a,Z T a'⁆ : Subgroup (FreeAmalgam T)).map
      (MulAut.conj g⁻¹).toMonoidHom = ⁅Z T a,Z T (act T g a')⁆ := by
    rw [map_commutator,←Z_act,←Z_act,hga]
  rw [hmap]
  exact small_critical_kernel_eq_iff_line_eq h e hz hk q p hq hp

include h e hz hk in
/-- Inside the starting stabilizer, the full kernel and critical line have
the same setwise stabilizer, including on the order-thirty-two cover. -/
theorem small_critical_kernel_normalizer_eq_line_normalizer
    {a a' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a a')
    (hp : (Q T a').relIndex (Z T a) < 4) :
    stabilizer T a ⊓ normalizer
      ((Z T a ⊓ Q T a' : Subgroup (FreeAmalgam T)) : Set (FreeAmalgam T)) =
    stabilizer T a ⊓ normalizer
      ((⁅Z T a,Z T a'⁆ : Subgroup (FreeAmalgam T)) : Set (FreeAmalgam T)) := by
  ext g
  constructor <;> rintro ⟨hg,hn⟩ <;> refine ⟨hg,?_⟩
  · apply mem_normalizer_iff_map_conj_eq.mpr
    have he := (small_critical_conjugate_kernel_iff h e hz hk p hp g⁻¹
      ((stabilizer T a).inv_mem hg)).mp
    simp only [inv_inv] at he
    apply he
    have hmap := mem_normalizer_iff_map_conj_eq.mp hn
    change (Z T a ⊓ Q T a').map (MulAut.conj g).toMonoidHom =
      Z T a ⊓ Q T a' at hmap
    have hga : act T g⁻¹ a = a := (stabilizer T a).inv_mem hg
    have hmZ := Z_act T g⁻¹ a
    have hmQ := Q_act T g⁻¹ a'
    simp only [inv_inv,hga] at hmZ hmQ
    rwa [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,←hmZ,←hmQ] at hmap
  · apply mem_normalizer_iff_map_conj_eq.mpr
    have he := (small_critical_conjugate_kernel_iff h e hz hk p hp g⁻¹
      ((stabilizer T a).inv_mem hg)).mpr
    simp only [inv_inv] at he
    have he' := he (mem_normalizer_iff_map_conj_eq.mp hn)
    change (Z T a ⊓ Q T a').map (MulAut.conj g).toMonoidHom =
      Z T a ⊓ Q T a'
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
    have hga : act T g⁻¹ a = a := (stabilizer T a).inv_mem hg
    have hmZ := Z_act T g⁻¹ a
    have hmQ := Q_act T g⁻¹ a'
    simp only [inv_inv,hga] at hmZ hmQ
    rwa [←hmZ,←hmQ]

include h e hz hk in
/-- The actual critical kernel is displaced by the starting stabilizer. -/
theorem small_critical_kernel_not_normalized
    {a c : Vertex T} (p : CriticalPath T (sourceGeometry h) a c)
    (hp : (Q T c).relIndex (Z T a) < 4) :
    ¬ stabilizer T a ≤ normalizer (Z T a ⊓ Q T c : Set (FreeAmalgam T)) := by
  intro hn
  have hle : stabilizer T a ≤ stabilizer T a ⊓ normalizer
      ((⁅Z T a,Z T c⁆ : Subgroup (FreeAmalgam T)) : Set (FreeAmalgam T)) := by
    rw [←small_critical_kernel_normalizer_eq_line_normalizer h e hz hk p hp]
    exact le_inf le_rfl hn
  have hf := (hle.trans inf_le_right).trans
    (normalizer_le_centralizer_of_card_two _ (small_critical_commutator_card h e hz hk p hp))
  exact critical_commutator_not_central h e hz hk p (le_centralizer_iff.mp hf)

include h e hz hk in
/-- A single actual conjugator moves both the small critical kernel and its
line, and carries the full critical path with it. This is a synchronized
choice; it does not assert the additional shifted-path conditions of (5.11). -/
theorem exists_small_critical_kernel_line_displacement
    {a a' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a a')
    (hp : (Q T a').relIndex (Z T a) < 4) :
    ∃ g ∈ stabilizer T a,
      ∃ q : CriticalPath T (sourceGeometry h) a (act T g a'),
      (∀ i, q.walk.getVert i = act T g (p.walk.getVert i)) ∧
      (Q T (act T g a')).relIndex (Z T a) = 2 ∧
      Z T a ⊓ Q T (act T g a') ≠ Z T a ⊓ Q T a' ∧
      ⁅Z T a,Z T (act T g a')⁆ ≠ ⁅Z T a,Z T a'⁆ := by
  classical
  have hn := small_critical_kernel_not_normalized h e hz hk p hp
  obtain ⟨g,hg,hgn⟩ := SetLike.not_le_iff_exists.mp hn
  let k := g⁻¹
  have hkG : k ∈ stabilizer T a := (stabilizer T a).inv_mem hg
  have hka : act T k a = a := hkG
  have hpath : ∃ q : CriticalPath T (sourceGeometry h)
      (act T k a) (act T k a'),
      ∀ i, q.walk.getVert i = act T k (p.walk.getVert i) :=
    ⟨p.act k,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hka] at hpath
  obtain ⟨q,hwalk⟩ := hpath
  have hq : (Q T (act T k a')).relIndex (Z T a) < 4 := by
    rw [←hka,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj k⁻¹).injective]
    exact hp
  have hkernel : Z T a ⊓ Q T (act T k a') ≠
      Z T a ⊓ Q T a' := by
    intro he
    apply hgn
    change g ∈ normalizer ((Z T a ⊓ Q T a' :
      Subgroup (FreeAmalgam T)) : Set (FreeAmalgam T))
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (Z T a ⊓ Q T a').map (MulAut.conj g).toMonoidHom =
      Z T a ⊓ Q T a'
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
    have hZ : (Z T a).map (MulAut.conj g).toMonoidHom = Z T a := by
      simpa only [k,inv_inv,hka] using (Z_act T k a).symm
    rw [hZ]
    simpa only [Q_act,k,inv_inv] using he
  refine ⟨k,hkG,q,hwalk,(small_critical_indices h e hz hk q hq).1,hkernel,?_⟩
  exact fun he => hkernel (small_critical_equal_lines_kernels h e hz hk q p hq hp he)


include h e hz hk in
/-- The kernel's setwise stabilizer is exactly the pointwise fixer of its
order-two critical line, relative to the same vertex stabilizer. -/
theorem small_critical_kernel_normalizer_eq_line_centralizer
    {a a' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a a')
    (hp : (Q T a').relIndex (Z T a) < 4) :
    stabilizer T a ⊓ normalizer
      ((Z T a ⊓ Q T a' : Subgroup (FreeAmalgam T)) : Set (FreeAmalgam T)) =
    stabilizer T a ⊓ centralizer
      ((⁅Z T a,Z T a'⁆ : Subgroup (FreeAmalgam T)) : Set (FreeAmalgam T)) := by
  rw [small_critical_kernel_normalizer_eq_line_normalizer h e hz hk p hp]
  apply le_antisymm
  · exact inf_le_inf_left _ (normalizer_le_centralizer_of_card_two _
      (small_critical_commutator_card h e hz hk p hp))
  · exact inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)


end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
