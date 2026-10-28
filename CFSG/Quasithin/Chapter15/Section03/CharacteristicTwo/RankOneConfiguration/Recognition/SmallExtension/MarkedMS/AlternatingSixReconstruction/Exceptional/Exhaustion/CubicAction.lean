module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.InitialAction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedCover.Ambient
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient
public import Theory.Representation.NormalElementaryQuotient.FixedIndex
public import Theory.Representation.BinaryOffender.SectionLinear

/-!
# The literal natural quotient when the initial kernel is cubic

The canonical moved/fixed quotient of X has a faithful action of M/E.
The natural A₆ normalizer realizes the entire action by six-letter
permutations. Its kernel on M is exactly E, including E/Q of order three.
Fixed codimension on this quotient is bounded by displacement on X;
no splitting of the fixed attachment or exhaustion of [Q,K] is used.

Source: MS93 (3.2)(vi), pp.863--864, and (2.2)(vi), p.857.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.CubicAction
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hc : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "X₀" => centralOmega L R
local notation "q" => QuotientGroup.mk' (layerKernel L R)
local notation "V₄" => BinaryPermutation.natural (Fin 6)
local notation "ρ₆" => BinaryPermutation.naturalRepresentation (Fin 6)

/-- Coordinates on the actual moved/fixed quotient, including its quotient map. -/
@[expose] def coordinates :
    ActionEquiv ((layerSection h).action.comp (layerComponent L R).subtype)
      (alternatingNatural 6) :=
  Classical.choice (layer_moved_alternating h e hz hc).2

/-- The entire initial actor acts on the same central quotient. -/
@[expose] def action : Representation (ZMod 2) (LayerActor L R) V₄ :=
  (layerSection h).ambientAction (coordinates h e hz hc)

include h e hz hc in
/-- The retained initial actor has a centric simple component. -/
theorem component_centralizer :
    centralizer (layerComponent L R : Set (LayerActor L R)) = ⊥ := by
  let := layerComponent_normal h
  obtain ⟨a⟩ := layerComponent_equiv_alternating h e hc
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by norm_num)
  let : IsSimpleGroup (layerComponent L R) := a.isSimpleGroup
  let := layerComponent_quasisimple h e hz
  apply centralizer_eq_bot_of_simple_two_quotient (layerComponent L R) ?_
    (layerActor_component_quotient_two h) (layerActor_twoCore h e hz)
  intro ha
  let := ha
  exact Group.IsPerfect.not_isSolvable (layerComponent L R) inferInstance

/-- Faithfulness is on the quotient by E, not the quotient by Q. -/
theorem action_faithful : Function.Injective (action h e hz hc) := by
  let := layerComponent_normal h
  exact (layerSection h).ambientAction_faithful (coordinates h e hz hc)
    ((BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)).comp
      (alternatingGroup (Fin 6)).subtype_injective) (component_centralizer h e hz hc)

open BinaryAlternatingSixNaturalNormalizer in
private theorem exists_permutation_action :
    ∃ p : LayerActor L R →* Equiv.Perm (Fin 6), ∀ g v,
      action h e hz hc g v = ρ₆ (p g) v := by
  let := layerComponent_normal h
  let f : LayerActor L R →* (V₄ ≃ₗ[ZMod 2] V₄) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V₄).toMonoidHom.comp
      (action h e hz hc).asGroupHom
  let a := (coordinates h e hz hc).groupEquiv
  have he (k : layerComponent L R) : f k = naturalLinearAction (a k).val := by
    apply LinearEquiv.ext
    intro v
    exact (layerSection h).ambientAction_component (coordinates h e hz hc) k v
  have him : (layerComponent L R).map f = alternatingLinearImage := by
    ext t
    constructor
    · rintro ⟨k,hk,rfl⟩
      exact ⟨a ⟨k,hk⟩,(he ⟨k,hk⟩).symm⟩
    · rintro ⟨k,rfl⟩
      obtain ⟨l,rfl⟩ := a.surjective k
      exact ⟨l,l.property,he l⟩
  have hm (g : LayerActor L R) : f g ∈ naturalLinearAction.range := by
    rw [← BinaryAlternatingSixNaturalNormalizer.normalizer,←him]
    apply Subgroup.le_normalizer_map f
    exact ⟨g,by rw [Subgroup.normalizer_eq_top]; trivial,rfl⟩
  have hi : Function.Injective naturalLinearAction := by
    intro g k heq
    apply BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)
    exact LinearMap.ext (fun v => LinearEquiv.congr_fun heq v)
  let j := f.codRestrict naturalLinearAction.range hm
  let p := (MonoidHom.ofInjective hi).symm.toMonoidHom.comp j
  refine ⟨p,fun g v => ?_⟩
  have hp : naturalLinearAction (p g) = f g := MonoidHom.apply_ofInjective_symm hi (j g)
  exact (LinearEquiv.congr_fun hp v).symm

/-- The six-letter map uses the marking of the natural section. -/
def permutationAction : LayerActor L R →* Equiv.Perm (Fin 6) :=
  Classical.choose (exists_permutation_action h e hz hc)

theorem permutationAction_apply (g : LayerActor L R) (v : V₄) :
    action h e hz hc g v = ρ₆ (permutationAction h e hz hc g) v :=
  Classical.choose_spec (exists_permutation_action h e hz hc) g v

theorem permutationAction_injective : Function.Injective (permutationAction h e hz hc) := by
  intro g k hh
  apply action_faithful h e hz hc
  apply LinearMap.ext
  intro v
  rw [permutationAction_apply,permutationAction_apply,hh]

/-- The original group acts through its actual cubic kernel. -/
@[expose] def projection : M →* Equiv.Perm (Fin 6) :=
  (permutationAction h e hz hc).comp q

theorem projection_kernel : (projection h e hz hc).ker = extensionKernel h := by
  rw [projection,MonoidHom.ker_comp_of_injective _ _ (permutationAction_injective h e hz hc),
    QuotientGroup.ker_mk',hc]

theorem projection_component (k : K) : projection h e hz hc k =
    ((coordinates h e hz hc).groupEquiv ((q).subgroupMap K k)).val := by
  apply BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)
  apply LinearMap.ext
  intro v
  exact (permutationAction_apply h e hz hc (q k) v).symm.trans
    ((layerSection h).ambientAction_component (coordinates h e hz hc) ((q).subgroupMap K k) v)

theorem component_image : (K).map (projection h e hz hc) = alternatingGroup (Fin 6) := by
  ext g
  constructor
  · rintro ⟨k,hk,rfl⟩
    rw [projection_component h e hz hc ⟨k,hk⟩]
    exact ((coordinates h e hz hc).groupEquiv ((q).subgroupMap K ⟨k,hk⟩)).property
  · intro hg
    obtain ⟨k,hk⟩ := (coordinates h e hz hc).groupEquiv.surjective ⟨g,hg⟩
    obtain ⟨l,rfl⟩ := (q).subgroupMap_surjective K k
    exact ⟨l,l.property,(projection_component h e hz hc l).trans (congrArg Subtype.val hk)⟩

/-- The literal natural action has either derived or full symmetric image. -/
theorem range_alternatives :
    (projection h e hz hc).range = alternatingGroup (Fin 6) ∨
      Function.Surjective (projection h e hz hc) := by
  have hA : alternatingGroup (Fin 6) ≤ (projection h e hz hc).range := by
    rw [←component_image h e hz hc]
    exact map_le_range _ _
  have hd : (projection h e hz hc).range.index ∣ 2 := by
    simpa only [alternatingGroup.index_eq_two] using index_dvd_of_le hA
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hi | hi
  · exact Or.inr (MonoidHom.range_eq_top.mp (index_eq_one.mp hi))
  · exact Or.inl (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi)

/-- Passing to the natural quotient cannot increase displacement on X. -/
theorem natural_index_le (A : Subgroup M) :
    2 ^ fixedCodim ρ₆ (A.map (projection h e hz hc)) ≤
      (centralizer (A : Set M)).relIndex X₀ := by
  let s := layerSection h
  have he : ∀ g v, (coordinates h e hz hc).linearEquiv ((MovedSection.action (layerAction L R) s) g v) =
      ρ₆ (permutationAction h e hz hc g) ((coordinates h e hz hc).linearEquiv v) := by
    intro g v
    exact (congrArg (fun w => (coordinates h e hz hc).linearEquiv
      (MovedSection.action (layerAction L R) s g w))
      ((coordinates h e hz hc).linearEquiv.symm_apply_apply v)).symm.trans
        (permutationAction_apply h e hz hc g ((coordinates h e hz hc).linearEquiv v))
  have hm := fixedCodim_map_equivariant (MovedSection.action (layerAction L R) s) ρ₆ (permutationAction h e hz hc)
    (coordinates h e hz hc).linearEquiv he (A.map q)
  rw [map_map] at hm
  have hq := fixedCodim_quotient_add_subrepresentation_le s.space.toRepresentation s.central (A.map q)
  have hu := fixedCodim_subrepresentation_le (layerAction L R) s.space (A.map q)
  have hi := NormalElementaryQuotient.centralizer_index_eq_fixedCodim X₀ q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) A
  rw [hi]
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  change fixedCodim ρ₆ (A.map ((permutationAction h e hz hc).comp q)) ≤ _
  rw [←hm]
  exact (Nat.le_add_right _ _).trans (hq.trans hu)

end AlternatingSixReconstruction.Exceptional.Exhaustion.CubicAction
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
