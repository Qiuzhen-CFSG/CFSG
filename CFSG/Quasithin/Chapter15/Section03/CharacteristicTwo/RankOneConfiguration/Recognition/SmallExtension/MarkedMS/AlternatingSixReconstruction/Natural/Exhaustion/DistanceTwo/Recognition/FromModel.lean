module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Recognition.Action
public import Theory.Representation.BinaryConjugationSection.FixedIndex
public import Theory.Representation.BinaryConjugationSection.FixedDisplacement
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.SymmetricSixCover
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport
public import Theory.SpecificGroups.Alternating.SixSubgroupObstructions

/-!
# Recognition of the paired-orbit fixed quotient from its action model

The two literal relative indices become the order and fixed-space index of
the opposite-orbit image. Their strict inequality forces order eight and
fixed codimension two. The proved symmetric-six module theorem supplies a
natural quotient and moves the whole component-fixed kernel, including its
possible central line. Transport through the original quotient and embedding
proves both clauses of `PairedOrbit.Recognized` and its terminal contradiction.

The assembly in this module is conditional on `PermutationModelInput`.
Recognition.Source constructs that model from the original hypotheses.
Source: MS93 (3.6), printed p.871, using B.5.1 and the augmentation-cover theorem.
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
namespace PermutationModel
variable {o} (s : PermutationModel o)
variable [IsElementaryAbelian 2 (OrbitQuotient R o.c o.b)]

omit [IsElementaryAbelian 2 (OrbitQuotient R o.c o.b)] in
include o in
theorem opposite_stabilizer : o.opposite ≤ stabilizer R (alpha R) :=
  (o.opposite_le.trans
    (Q_le_adjacent_h R (DistanceTwo.NaturalCore.edge_color o.adjacent_left)
      o.adjacent_right)).trans (fun _ hx => hx.2 _ (adjacent_symm R o.adjacent_left))

omit [IsElementaryAbelian 2 (OrbitQuotient R o.c o.b)] in
include o in
theorem opposite_map : (o.opposite.comap (embedM R)).map (embedM R) = o.opposite :=
  map_comap_eq_self ((opposite_stabilizer (o := o)).trans_eq (stabilizer_m_base R))

omit [Finite M] [IsElementaryAbelian 2 (OrbitQuotient R o.c o.b)] in
theorem actor_map : ((o.opposite.comap (embedM R)).subgroupOf ⊤).map
    s.topProjection = s.actor := by
  rw [show s.topProjection = s.projection.comp (⊤ : Subgroup M).subtype from rfl,
    ← map_map,map_subgroupOf_eq_of_le (show o.opposite.comap (embedM R) ≤ ⊤ from le_top)]

omit [IsElementaryAbelian 2 (OrbitQuotient R o.c o.b)] in
theorem actor_card (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R) :
    Nat.card s.actor = (Q R (alpha R)).relIndex o.opposite := by
  rw [actor,←relIndex_ker,s.kernel]
  have he := relIndex_map_map_of_injective (pCore 2 M) (o.opposite.comap (embedM R))
    (embedM_injective R)
  rw [opposite_map (o := o),←Q_alpha R hp hQR] at he
  exact he.symm

theorem commutatorPreimage_map_injective
    {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Injective f)
    (A E Z : Subgroup G) (hn : A ≤ normalizer (Z : Set G)) :
    (commutatorPreimage A E Z).map f =
      commutatorPreimage (A.map f) (E.map f) (Z.map f) := by
  have hnf : A.map f ≤ normalizer (Z.map f : Set H) :=
    (map_mono hn).trans (le_normalizer_map f)
  apply le_antisymm
  · apply le_commutatorPreimage (map_mono (commutatorPreimage_le A E Z))
    rw [←map_commutator]
    exact map_mono (commutator_commutatorPreimage_le A E Z hn)
  · let D := commutatorPreimage (A.map f) (E.map f) (Z.map f)
    have hDr : D ≤ f.range := (commutatorPreimage_le _ _ _).trans (map_le_range f A)
    have hDm : (D.comap f).map f = D := map_comap_eq_self hDr
    have hDA : D.comap f ≤ A := by
      have hh := comap_mono (f := f) (commutatorPreimage_le (A.map f) (E.map f) (Z.map f))
      simpa only [comap_map_eq_self_of_injective hf] using hh
    have hDc : ⁅D.comap f,E⁆ ≤ Z := by
      apply (map_le_map_iff_of_injective hf).mp
      rw [map_commutator,hDm]
      exact commutator_commutatorPreimage_le _ _ _ hnf
    change D ≤ _
    rw [←hDm]
    exact map_mono (le_commutatorPreimage hDA hDc)

theorem fixed_index :
    (commutatorPreimage (criticalOrbit R o.c o.b) o.opposite (Z R (alpha R))).relIndex
      (criticalOrbit R o.c o.b) = 2 ^ fixedCodim s.action s.actor := by
  have hZm : (orbitLayer R).map (embedM R) = Z R (alpha R) := map_comap_eq_self
    ((Z_le_stabilizer R (alpha R)).trans_eq (stabilizer_m_base R))
  have hCm := commutatorPreimage_map_injective (embedM R) (embedM_injective R)
    (criticalOrbitNative R o.c o.b) (o.opposite.comap (embedM R)) (orbitLayer R)
    le_normalizer_of_normal
  rw [opposite_map (o := o),hZm] at hCm
  simp only [criticalOrbit]
  rw [←hCm,relIndex_map_map_of_injective _ _ (embedM_injective R)]
  have hi := BinaryConjugationSection.fixed_index_image _ _ s.sectionData
    (o.opposite.comap (embedM R)) le_top
  rwa [s.actor_map] at hi

/-- The actor bound follows intrinsically in S6; it is not a source input. -/
theorem elementary_actor_card_le_eight (A : Subgroup (Equiv.Perm (Fin 6)))
    [IsElementaryAbelian 2 A] : Nat.card A ≤ 8 := by
  obtain ⟨P,hP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  have hPc : Nat.card (P : Subgroup (Equiv.Perm (Fin 6))) = 16 := by
    rw [P.card_eq_multiplicity,Nat.card_perm,Nat.card_fin]
    decide +kernel
  have hAc : Nat.card A ≤ 16 := (card_le_of_le hP).trans_eq hPc
  have hne : Nat.card A ≠ 16 := by
    intro hc
    let Q : Sylow 2 (Equiv.Perm (Fin 6)) := Sylow.ofCard A (by
      rw [hc,Nat.card_perm,Nat.card_fin]
      decide +kernel)
    exact alternatingGroup.SixSubgroupObstructions.not_injective_of_sylow_involutions_commute Q
      (by
        change ∀ a b : A, a ^ 2 = 1 → b ^ 2 = 1 → Commute a b
        intro a b _ _
        exact mul_comm a b)
      (alternatingGroup (Fin 6)).subtype Subtype.coe_injective
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hn4 : n < 4 := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    change 2 ^ n < 16
    omega
  rw [hn]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : n ≤ 3)

omit [Finite M] [IsElementaryAbelian 2 (OrbitQuotient R o.c o.b)] in
theorem actor_card_le_eight : Nat.card s.actor ≤ 8 := by
  let := s.actor_elementary
  exact elementary_actor_card_le_eight s.actor

theorem strict_actor (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R) :
    Nat.card s.actor = 8 ∧ fixedCodim s.action s.actor = 2 := by
  let := s.actor_elementary
  apply AlternatingSixInvolutionDisplacement.strict_small_elementary_card
    s.action s.action_injective s.actor s.actor_card_le_eight
  rw [s.actor_card hp hQR,←s.fixed_index]
  exact o.strict_index.trans o.ordered_index

theorem elementary_eight_odd (A : Subgroup (Equiv.Perm (Fin 6)))
    [IsElementaryAbelian 2 A] (hc : Nat.card A = 8) : ¬ A ≤ alternatingGroup (Fin 6) := by
  intro hle
  let E := A.subgroupOf (alternatingGroup (Fin 6))
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hle).toMonoidHom (subgroupOfEquivOfLe hle).injective
  have hE : Nat.card E = 8 := (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans hc
  let P : Sylow 2 (alternatingGroup (Fin 6)) := Sylow.ofCard E (by
    rw [hE,alternatingGroup.SixSubgroupObstructions.card_six]
    decide +kernel)
  exact alternatingGroup.SixSubgroupObstructions.not_injective_of_sylow_involutions_commute
    P (by
      change ∀ a b : E, a ^ 2 = 1 → b ^ 2 = 1 → Commute a b
      intro a b _ _
      exact mul_comm a b) (MonoidHom.id _) Function.injective_id

theorem natural_quotient (hsq : IsSQTK KnownSimple.IsKnownSimple M)
    (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R) :
    ∃ (e : Equiv.Perm (Fin 6) ≃* Equiv.Perm (Fin 6))
      (p : Additive (OrbitQuotient R o.c o.b) →ₗ[ZMod 2] BinaryPermutation.natural (Fin 6)),
      Function.Surjective p ∧ p.ker = fixedSpace s.action (alternatingGroup (Fin 6)) ∧
      (∀ g v, p (s.action g v) = BinaryPermutation.naturalRepresentation (Fin 6) (e g) (p v)) ∧
      fixedSpace s.action (alternatingGroup (Fin 6)) ≤ subspaceCommutator s.action ⊤ s.actor := by
  let := s.actor_elementary
  obtain ⟨hcard,hcod⟩ := s.strict_actor hp hQR
  exact ChapterB.QuasisimpleSource.SourceCompletion.symmetricSix_natural_quotient_fixed_le_moved
    s.action s.action_injective (s.alternating_sqtk hsq) s.actor hcard hcod
    (elementary_eight_odd s.actor hcard) s.action_full_movement

theorem displacement_of_linear_bound
    (hfix : fixedSpace s.action (alternatingGroup (Fin 6)) ≤
      subspaceCommutator s.action ⊤ s.actor) :
    (orbitFixedKernel K R o.c o.b).map (embedM R) ≤
      ⁅criticalOrbit R o.c o.b,o.opposite⁆ ⊔ Z R (alpha R) := by
  have hfix0 : fixedSpace (s.action.comp s.topProjection) (K.subgroupOf ⊤) ≤
      subspaceCommutator (s.action.comp s.topProjection) ⊤
        ((o.opposite.comap (embedM R)).subgroupOf ⊤) := by
    rw [fixedSpace_comp_map,subspaceCommutator_comp_map,s.component_map,s.actor_map]
    exact hfix
  have hh := s.sectionData.fixedPreimage_le_commutator_sup_of_fixed_le_moved
    K (o.opposite.comap (embedM R)) le_top le_top
    (by rw [normalizer_eq_top];exact le_top) hfix0
  have hZm : (orbitLayer R).map (embedM R) = Z R (alpha R) := map_comap_eq_self
    ((Z_le_stabilizer R (alpha R)).trans_eq (stabilizer_m_base R))
  have hm := map_mono (f := embedM R) hh
  rw [Subgroup.map_sup,map_commutator,opposite_map (o := o),hZm] at hm
  exact hm

omit [Finite M] in
theorem fixedSpace_eq : fixedSpace s.action (alternatingGroup (Fin 6)) =
    orbitFixedSpace K R o.c o.b := by
  rw [←s.component_map,←fixedSpace_comp_map,s.action_comp]
  ext v
  constructor
  · intro hv k
    exact hv ⟨⟨k,mem_top _⟩,k.property⟩
  · intro hv k
    exact hv ⟨k.val.val,k.property⟩

omit [Finite M] in
theorem quotient_transitive [K.Normal]
    (e : Equiv.Perm (Fin 6) ≃* Equiv.Perm (Fin 6))
    (p : Additive (OrbitQuotient R o.c o.b) →ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (hk : p.ker = fixedSpace s.action (alternatingGroup (Fin 6)))
    (he : ∀ g v, p (s.action g v) = BinaryPermutation.naturalRepresentation (Fin 6) (e g) (p v)) :
    ∀ u v, u ≠ 0 → v ≠ 0 → ∃ m : (⊤ : Subgroup M),
      orbitFixedQuotientRepresentation K R o.c o.b o.layer_le m u = v := by
  rw [s.fixedSpace_eq] at hk
  intro u v hu hv
  obtain ⟨x,rfl⟩ := (orbitFixedSpace K R o.c o.b).mkQ_surjective u
  obtain ⟨y,rfl⟩ := (orbitFixedSpace K R o.c o.b).mkQ_surjective v
  have hx : p x ≠ 0 := by
    intro hh
    apply hu
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hk ▸ hh)
  have hy : p y ≠ 0 := by
    intro hh
    apply hv
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hk ▸ hh)
  obtain ⟨g,hg⟩ := Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport.transitive_nonzero
    (p x) (p y) hx hy
  obtain ⟨m,hm⟩ := s.topProjection_onto (e.symm g.val)
  refine ⟨m,?_⟩
  change (orbitFixedSpace K R o.c o.b).mkQ (orbitRepresentation R o.c o.b m x) =
    (orbitFixedSpace K R o.c o.b).mkQ y
  apply (Submodule.Quotient.eq _).mpr
  rw [←hk]
  change p (orbitRepresentation R o.c o.b m x - y) = 0
  rw [map_sub,←s.action_projection,show s.projection m = e.symm g.val from hm,he,
    e.apply_symm_apply,hg,sub_self]

include s in
/-- Both clauses of recognition for the literal paired orbit, with its central
fixed line retained. -/
theorem recognized [K.Normal] (hsq : IsSQTK KnownSimple.IsKnownSimple M)
    (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R) : o.Recognized := by
  obtain ⟨e,p,_,hk,he,hfix⟩ := s.natural_quotient hsq hp hQR
  exact ⟨s.quotient_transitive e p hk he,s.displacement_of_linear_bound hfix⟩

include s in
/-- Actual terminal consumer of both representation conclusions. -/
theorem contradiction [K.Normal] (hsq : IsSQTK KnownSimple.IsKnownSimple M)
    (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R) : False :=
  o.false_of_recognized hp hQR (s.recognized hsq hp hQR)

end PermutationModel

universe u
/-- Conditional assembly, with the model constructed in Recognition.Source. -/
theorem orbitRecognition_of_permutationModel
    (hm : PermutationModelInput.{u} KnownSimple.IsKnownSimple) :
    OrbitRecognitionInput.{u} KnownSimple.IsKnownSimple := by
  intro G _ _ L R h e hz hn d hl hd hf o
  obtain ⟨s⟩ := hm G L R h e hz hn d hl hd hf o
  let := o.quotient_elementary
  exact s.recognized (h.sqtk.subgroup d.overgroup)
    (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Recognition
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
