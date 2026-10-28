module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Recognition.FromModel
public import Theory.Representation.BinaryOffender.QuadraticDualOffender
public import Theory.Representation.BinaryConjugationSection.QuadraticCommutator
/-!
# The faithful orbit image is the full symmetric group

The literal conjugation action descends to the image of a marking with kernel
O₂. Nontrivial component action makes this image action faithful. The paired
commutator bounds make the opposite orbit quadratic on the orbit quotient,
so its image is elementary. Translating the strict relative-index inequality
then excludes an A₆-only image: every nonidentity actor costs at least two
fixed codimensions, forcing an impossible elementary subgroup of order eight.
Thus the marking is onto S₆ and supplies the model used by FromModel.

No natural subgroup complement or full point-radical image is assumed.
Source: MS93 (3.6), printed p.871.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Recognition
variable {M : Type*} [Group M] [Finite M] {K R : Subgroup M} {geo : Geometry R}
  (o : PairedOrbit K R geo)
/-- A marking before surjectivity or actor recognition is known. -/
structure ImageModel (o : PairedOrbit K R geo) where
  projection : M →* Equiv.Perm (Fin 6)
  kernel : projection.ker = pCore 2 M
  component_image : K.map projection = alternatingGroup (Fin 6)
namespace ImageModel
variable {o} (s : ImageModel o)
abbrev actor : Subgroup s.projection.range :=
  (o.opposite.comap (embedM R)).map s.projection.rangeRestrict
abbrev topProjection : (⊤ : Subgroup M) →* s.projection.range :=
  s.projection.rangeRestrict.comp (⊤ : Subgroup M).subtype

omit [Finite M] in
theorem topProjection_onto : Function.Surjective s.topProjection := by
  intro g
  obtain ⟨m,hm⟩ := s.projection.rangeRestrict_surjective g
  exact ⟨⟨m,mem_top _⟩,hm⟩

variable [IsElementaryAbelian 2 (OrbitQuotient R o.c o.b)]

omit [Finite M] in
theorem kernel_le : s.topProjection.ker ≤ (orbitRepresentation R o.c o.b).ker := by
  intro m hm
  have hmQ : (m : M) ∈ pCore 2 M := s.kernel ▸ (show s.projection m = 1 from congrArg Subtype.val hm)
  apply ((orbitSection R o.c o.b o.layer_le).action_mem_ker_iff m).mpr
  intro a ha
  exact o.commutator_le_layer (commutator_mem_commutator hmQ ha)

omit [Finite M] in
theorem conjugation_kernel_le : s.topProjection.ker ≤ (orbitConjugation R o.c o.b).ker := by
  intro m hm
  have he : orbitRepresentation R o.c o.b m = 1 := s.kernel_le hm
  apply MulEquiv.ext
  intro x
  exact congrArg (fun f => (f (Additive.ofMul x)).toMul) he

/-- Literal orbit conjugation descended along the specified two-core quotient. -/
def conjugation : s.projection.range →* MulAut (OrbitQuotient R o.c o.b) :=
  s.topProjection.liftOfSurjective s.topProjection_onto
    ⟨orbitConjugation R o.c o.b,s.conjugation_kernel_le⟩

omit [Finite M] in
theorem conjugation_projection (m : (⊤ : Subgroup M)) :
    s.conjugation (s.projection.rangeRestrict m) = orbitConjugation R o.c o.b m :=
  MonoidHom.liftOfRightInverse_comp_apply s.topProjection
    (Function.surjInv s.topProjection_onto) (Function.rightInverse_surjInv s.topProjection_onto)
    ⟨orbitConjugation R o.c o.b,s.conjugation_kernel_le⟩ m

/-- The binary linear action of the descended conjugation automorphisms. -/
def action : Representation (ZMod 2) (s.projection.range)
    (Additive (OrbitQuotient R o.c o.b)) where
  toFun g := { (s.conjugation g).toAdditive.toAddMonoidHom with
    map_smul' := ZMod.map_smul (s.conjugation g).toAdditive.toAddMonoidHom }
  map_one' := by
    ext x
    change s.conjugation 1 x.toMul = x.toMul
    rw [map_one]
    rfl
  map_mul' g h := by
    ext x
    change s.conjugation (g*h) x.toMul = s.conjugation g (s.conjugation h x.toMul)
    rw [map_mul]
    rfl

omit [Finite M] in
theorem action_projection (m : (⊤ : Subgroup M)) :
    s.action (s.projection.rangeRestrict m) = orbitRepresentation R o.c o.b m := by
  ext x
  change s.conjugation (s.projection.rangeRestrict m) x.toMul = orbitConjugation R o.c o.b m x.toMul
  rw [s.conjugation_projection]

omit [Finite M] in
theorem action_comp : s.action.comp s.topProjection = orbitRepresentation R o.c o.b :=
  MonoidHom.ext s.action_projection


omit [Finite M] [IsElementaryAbelian 2 (OrbitQuotient R o.c o.b)] in
theorem alternating_le_range : alternatingGroup (Fin 6) ≤ s.projection.range := by
  rw [← s.component_image]
  exact map_le_range _ _

omit [Finite M] [IsElementaryAbelian 2 (OrbitQuotient R o.c o.b)] in
theorem component_map : K.map s.projection.rangeRestrict =
    (alternatingGroup (Fin 6)).subgroupOf s.projection.range := by
  apply map_injective s.projection.range.subtype_injective
  rw [map_map, map_subgroupOf_eq_of_le s.alternating_le_range]
  exact s.component_image

omit [Finite M] in
theorem action_component_nontrivial :
    ∃ k : K, s.action (s.projection.rangeRestrict k) ≠ 1 := by
  by_contra! hn
  apply o.plane_not_fixed
  intro y hy
  apply (mem_orbitFixedKernel_iff K R o.c o.b ⟨y,le_normalClosure hy⟩).mpr
  intro k
  change orbitRepresentation R o.c o.b ⟨k,mem_top _⟩ _ = _
  rw [← s.action_projection, hn k]
  rfl

omit [Finite M] in
theorem action_injective : Function.Injective s.action := by
  let H := s.projection.range
  let C := (alternatingGroup (Fin 6)).subgroupOf H
  let e : C ≃* alternatingGroup (Fin 6) := subgroupOfEquivOfLe s.alternating_le_range
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup C := e.isSimpleGroup
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hC : centralizer (C : Set H) = ⊥ := by
    apply bot_unique
    intro x hx
    have hm : (x : Equiv.Perm (Fin 6)) ∈ centralizer
        (alternatingGroup (Fin 6) : Set (Equiv.Perm (Fin 6))) := by
      intro y hy
      exact congrArg Subtype.val (hx ⟨y,s.alternating_le_range hy⟩ hy)
    rw [GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 6 (by decide)] at hm
    exact mem_bot.mpr (Subtype.ext (mem_bot.mp hm))
  apply s.action.ker_eq_bot_iff.mp
  by_contra hn
  have hle := simple_normal_le_of_normal_ne_bot_of_centralizer_eq_bot C
    (Group.IsPerfect.not_isMulCommutative C) hC s.action.ker hn
  obtain ⟨k,hk⟩ := s.action_component_nontrivial
  apply hk
  apply hle
  change s.projection.rangeRestrict k ∈ (alternatingGroup (Fin 6)).subgroupOf s.projection.range
  rw [← s.component_map]
  exact mem_map_of_mem _ k.property

def sectionData : BinaryConjugationSection ⊤ (criticalOrbitNative R o.c o.b)
    (orbitLayer R) (s.action.comp s.topProjection) := by
  rw [s.action_comp]
  exact orbitSection R o.c o.b o.layer_le

omit [Finite M] [IsElementaryAbelian 2 (OrbitQuotient R o.c o.b)] in
theorem actor_map : ((o.opposite.comap (embedM R)).subgroupOf ⊤).map
    s.topProjection = s.actor := by
  rw [show s.topProjection = s.projection.rangeRestrict.comp (⊤ : Subgroup M).subtype from rfl,
    ← map_map,map_subgroupOf_eq_of_le (show o.opposite.comap (embedM R) ≤ ⊤ from le_top)]

/-- The original opposite orbit acts quadratically, by its literal triple commutator. -/
theorem actor_quadratic (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R) :
    IsQuadratic s.action s.actor := by
  let A := criticalOrbitNative R o.c o.b
  let B := o.opposite.comap (embedM R)
  have hd : (cosetGraph R).dist (alpha R) o.c = 2 :=
    o.critical.1.trans ((geo.distance_constant _ rfl).trans o.distance_two)
  have hAG : criticalOrbit R o.c o.b ≤ stabilizer R o.c := by
    have hAQ : criticalOrbit R o.c o.b ≤ Q R (alpha R) := by
      rw [Q_alpha R hp hQR]
      exact map_mono o.orbit_le_core
    exact hAQ.trans (Q_le_stabilizer_of_dist_two R (alpha R) o.c rfl hd)
  have hAB : ⁅criticalOrbit R o.c o.b,o.opposite⁆ ≤ o.opposite :=
    le_normalizer_iff_commutator_le_right.mp (hAG.trans o.opposite_normalized)
  have htrip : ⁅o.opposite,⁅o.opposite,criticalOrbit R o.c o.b⁆⁆ ≤ Z R (alpha R) := by
    rw [commutator_comm o.opposite (criticalOrbit R o.c o.b)]
    apply ((commutator_mono o.opposite_le hAB).trans o.opposite_commutator).trans
    have hbcol := DistanceTwo.NaturalCore.edge_color o.adjacent_left
    simp only [Z, show color R (alpha R) = false from rfl, hbcol,
      Bool.true_eq_false, if_true, if_false]
    exact le_iSup_of_le o.b (le_iSup_of_le o.adjacent_left le_rfl)
  have ht : ⁅B,⁅B,A⁆⁆ ≤ orbitLayer R := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator, map_commutator,
      PermutationModel.opposite_map (o := o)]
    exact htrip
  have hh := s.sectionData.isQuadratic_of_triple_commutator_le
    ⊤ A (orbitLayer R) B s.action s.topProjection ht
  rwa [s.actor_map] at hh

theorem actor_elementary (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R) :
    IsElementaryAbelian 2 s.actor :=
  elementary_of_faithful_quadratic s.action s.action_injective s.actor
    (s.actor_quadratic hp hQR)

omit [IsElementaryAbelian 2 (OrbitQuotient R o.c o.b)] in
theorem actor_card (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R) :
    Nat.card s.actor = (Q R (alpha R)).relIndex o.opposite := by
  rw [actor, ←relIndex_ker]
  have hk : s.projection.rangeRestrict.ker = pCore 2 M := by
    rw [MonoidHom.ker_rangeRestrict, s.kernel]
  rw [hk]
  have he := relIndex_map_map_of_injective (pCore 2 M) (o.opposite.comap (embedM R))
    (embedM_injective R)
  rw [PermutationModel.opposite_map (o := o),←Q_alpha R hp hQR] at he
  exact he.symm

theorem fixed_index :
    (commutatorPreimage (criticalOrbit R o.c o.b) o.opposite (Z R (alpha R))).relIndex
      (criticalOrbit R o.c o.b) = 2 ^ fixedCodim s.action s.actor := by
  have hZm : (orbitLayer R).map (embedM R) = Z R (alpha R) := map_comap_eq_self
    ((Z_le_stabilizer R (alpha R)).trans_eq (stabilizer_m_base R))
  have hCm := PermutationModel.commutatorPreimage_map_injective (embedM R) (embedM_injective R)
    (criticalOrbitNative R o.c o.b) (o.opposite.comap (embedM R)) (orbitLayer R)
    le_normalizer_of_normal
  rw [PermutationModel.opposite_map (o := o),hZm] at hCm
  simp only [criticalOrbit]
  rw [←hCm,relIndex_map_map_of_injective _ _ (embedM_injective R)]
  have hi := BinaryConjugationSection.fixed_index_image _ _ s.sectionData
    (o.opposite.comap (embedM R)) le_top
  rwa [s.actor_map] at hi

/-- The strict index inequality rules out the alternating-only image. -/
theorem onto (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R) :
    Function.Surjective s.projection := by
  let := s.actor_elementary hp hQR
  let A := s.actor.map s.projection.range.subtype
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hcard : Nat.card A = Nat.card s.actor := card_map_of_injective Subtype.coe_injective
  have hsmall : Nat.card s.actor ≤ 8 := by
    rw [← hcard]
    exact PermutationModel.elementary_actor_card_le_eight A
  have hstrict : 2 * 2 ^ fixedCodim s.action s.actor ≤ Nat.card s.actor := by
    rw [s.actor_card hp hQR, ← s.fixed_index]
    exact o.strict_index.trans o.ordered_index
  by_contra hn
  have hr : s.projection.range = alternatingGroup (Fin 6) := by
    have hd := index_dvd_of_le s.alternating_le_range
    rw [alternatingGroup.index_eq_two] at hd
    rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd with h1 | h2
    · exact (hn (MonoidHom.range_eq_top.mp (index_eq_one.mp h1))).elim
    · exact Equiv.Perm.eq_alternatingGroup_of_index_eq_two h2
  let e : s.projection.range ≃* alternatingGroup (Fin 6) := MulEquiv.subgroupCongr hr
  let σ := s.action.comp e.symm.toMonoidHom
  let B := s.actor.map e.toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hB : Nat.card B = Nat.card s.actor := card_map_of_injective e.injective
  have hf : Function.Injective σ := s.action_injective.comp e.symm.injective
  have hcod : fixedCodim σ B = fixedCodim s.action s.actor := by
    unfold fixedCodim
    rw [fixedSpace_comp_map, map_map]
    have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      exact e.symm_apply_apply x
    rw [he, map_id]
  have hBne : B ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hB
    have : 0 < 2 ^ fixedCodim s.action s.actor := by positivity
    omega
  obtain ⟨a, ha, hane⟩ := B.bot_or_exists_ne_one.resolve_left hBne
  have hao : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian a ha) hane
  have hlo := AlternatingSixInvolutionDisplacement.fixedCodim_lower_of_involution_mem
    σ (⟨a, fun hh => hane (hf (hh.trans (map_one σ).symm))⟩) a hao ha
  rw [hcod] at hlo
  have hpow : 4 ≤ 2 ^ fixedCodim s.action s.actor :=
    show 2^2 ≤ _ from Nat.pow_le_pow_right (by decide) hlo
  have h8 : Nat.card A = 8 := by omega
  exact PermutationModel.elementary_eight_odd A h8
    ((map_le_range s.projection.range.subtype s.actor).trans_eq
      ((range_subtype s.projection.range).trans hr))

/-- Supply both missing model fields from the actual paired orbit. -/
def permutationModel (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R) : PermutationModel o where
  projection := s.projection
  onto := s.onto hp hQR
  kernel := s.kernel
  component_image := s.component_image
  actor_elementary := by
    let := s.actor_elementary hp hQR
    have hh : IsElementaryAbelian 2 (s.actor.map s.projection.range.subtype) :=
      IsElementaryAbelian.map _
    have he : s.actor.map s.projection.range.subtype =
        (o.opposite.comap (embedM R)).map s.projection := by
      change ((o.opposite.comap (embedM R)).map s.projection.rangeRestrict).map
        s.projection.range.subtype = _
      rw [map_map, MonoidHom.subtype_comp_rangeRestrict]
    exact he ▸ hh

end ImageModel
end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Recognition
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
