module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive.Stabilizer
public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.Normalizer

/-!
# The faithful natural image of the original A₅ cover action

An actor trivial on the natural quotient has trivial induced conjugation on
SL₂(4). Uniqueness of lifts on the commutator-generated central cover then
makes it trivial on the whole moved subgroup. Thus passage to the natural
quotient loses none of the original LT-action. The semilinear normalizer
identifies this same image inside ΓL₂(4), retaining its marked SL₂ subgroup.

Source: Aschbacher--Smith, proof of 13.1.12, printed p.872; the lift
uniqueness argument is the universal-cover argument of I.1.5 and I.2.3.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive
open Chapter1 Chapter1.Section02 Chapter12.Section02
open Representation.SL2FourNatural
open Representation.OneCohomology.CentralCoverOriginalAction
namespace Marking
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  {T : Sylow 2 G} {L : Subgroup G} (d : Marking T L W)

/-- The original natural quotient action, as invertible binary linear maps. -/
@[expose] def naturalLinearHom :
    (L ⊔ (T : Subgroup G) : Subgroup G) →* SemilinearNormalizer.BinaryGL :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp
    d.naturalActor.asGroupHom

@[simp] theorem naturalLinearHom_apply
    (a : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V) :
    d.naturalLinearHom a v = d.naturalActor a v := rfl

/-- Restriction is the given natural SL₂ marking, on the same quotient map. -/
theorem naturalLinearHom_component (l : L) :
    d.naturalLinearHom (inclusion (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) l) =
      SL2FourNatural.action (d.component l) := by
  apply LinearEquiv.ext
  intro v
  obtain ⟨w,rfl⟩ := d.projection_onto v
  change d.naturalActor _ (d.projection w) = Natural (d.component l) (d.projection w)
  rw [← d.quotient_action, d.component_action, d.projection.isIntertwining]

/-- The image of the literal component is the actual natural SL₂ subgroup. -/
theorem naturalLinearHom_component_image :
    (L.subgroupOf (L ⊔ (T : Subgroup G))).map d.naturalLinearHom =
      SL2FourNatural.action.range := by
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨d.component ⟨a,ha⟩, (d.naturalLinearHom_component ⟨a,ha⟩).symm⟩
  · rintro ⟨l,rfl⟩
    obtain ⟨l,rfl⟩ := d.onto l
    exact ⟨inclusion le_sup_left l,l.property,d.naturalLinearHom_component l⟩

private theorem naturalActor_compatible
    (hmoved : ⁅normalizerMoved L,L⁆ = normalizerMoved L)
    (a : (L ⊔ (T : Subgroup G) : Subgroup G)) (l : SL) (v : V) :
    d.naturalActor a (Natural l v) = Natural (d.conjugation a l) (d.naturalActor a v) :=
  (d.naturalCover hmoved).natural_compatible a l v

/-- Normalizer membership follows from the original compatible actions. -/
theorem naturalLinearHom_mem_normalizer
    (hmoved : ⁅normalizerMoved L,L⁆ = normalizerMoved L)
    (a : (L ⊔ (T : Subgroup G) : Subgroup G)) :
    d.naturalLinearHom a ∈ SemilinearNormalizer.normalizer := by
  apply (Subgroup.mem_normalizer_iff).mpr
  intro x
  constructor
  · rintro ⟨l,rfl⟩
    refine ⟨d.conjugation a l, ?_⟩
    apply LinearEquiv.ext
    intro v
    change Natural (d.conjugation a l) v =
      d.naturalActor a (Natural l ((d.naturalLinearHom a)⁻¹ v))
    rw [naturalActor_compatible d hmoved]
    congr 1
    exact ((d.naturalLinearHom a).apply_symm_apply v).symm
  · rintro ⟨l,hl⟩
    refine ⟨(d.conjugation a).symm l, ?_⟩
    apply LinearEquiv.ext
    intro v
    have hh := LinearEquiv.congr_fun hl (d.naturalLinearHom a v)
    change Natural l (d.naturalActor a v) =
      d.naturalActor a (x ((d.naturalLinearHom a).symm (d.naturalLinearHom a v))) at hh
    rw [LinearEquiv.symm_apply_apply] at hh
    apply (d.naturalLinearHom a).injective
    change d.naturalActor a (Natural ((d.conjugation a).symm l) v) = d.naturalActor a (x v)
    rw [naturalActor_compatible d hmoved, MulEquiv.apply_symm_apply]
    exact hh

/-- A trivial quotient actor is already trivial on the generated cover. -/
theorem actor_eq_one_of_naturalLinearHom_eq_one
    (hmoved : ⁅normalizerMoved L,L⁆ = normalizerMoved L)
    (a : (L ⊔ (T : Subgroup G) : Subgroup G))
    (ha : d.naturalLinearHom a = 1) : d.actor a = 1 := by
  have hnat (v : V) : d.naturalActor a v = v := LinearEquiv.congr_fun ha v
  have hc (l : SL) : d.conjugation a l = l := by
    apply action_faithful
    apply LinearEquiv.ext
    intro v
    have hh := naturalActor_compatible d hmoved a l v
    rw [hnat, hnat] at hh
    exact hh.symm
  exact lift_unique d.representation d.representation (d.naturalCover hmoved).cover.2.2
    d.projection.toLinearMap d.kernel_fixed (d.actor a) 1
    (fun l w => by rw [d.compatible, hc]) (fun _ _ => rfl)
    (fun w => by
      change d.projection (d.actor a w) = d.projection w
      rw [d.quotient_action, hnat])

/-- The natural action kernel is literally C_LT(U), not a larger quotient kernel. -/
theorem naturalLinearHom_kernel
    (hmoved : ⁅normalizerMoved L,L⁆ = normalizerMoved L) :
    d.naturalLinearHom.ker =
      (centralizer (normalizerMoved L : Set G)).subgroupOf (L ⊔ (T : Subgroup G)) := by
  ext a
  rw [MonoidHom.mem_ker]
  constructor
  · intro ha u hu
    have he := d.equivariant a ⟨u,hu⟩
    rw [d.actor_eq_one_of_naturalLinearHom_eq_one hmoved a ha] at he
    have hf := congrArg Subtype.val (d.coordinates.injective he)
    change (a : G) * u * (a : G)⁻¹ = u at hf
    exact (mul_inv_eq_iff_eq_mul.mp hf).symm
  · intro ha
    apply LinearEquiv.ext
    intro v
    obtain ⟨w,rfl⟩ := d.projection_onto v
    obtain ⟨u,hu⟩ := d.coordinates.surjective (Multiplicative.ofAdd w)
    have hf : (normalizerMoved L).normalizerMonoidHom (inclusion d.invariant a) u = u := by
      apply Subtype.ext
      change (a : G) * (u : G) * (a : G)⁻¹ = (u : G)
      have hc : (u : G) * (a : G) = (a : G) * (u : G) := ha u u.property
      rw [← hc,mul_inv_cancel_right]
    have he := d.equivariant a u
    rw [hf, hu] at he
    change d.naturalActor a (d.projection w) = d.projection w
    change w = d.actor a w at he
    rw [← d.quotient_action, ← he]

/-- The original action inside the actual semilinear normalizer. -/
@[expose] def semilinearHom
    (hmoved : ⁅normalizerMoved L,L⁆ = normalizerMoved L) :
    (L ⊔ (T : Subgroup G) : Subgroup G) →* SemilinearNormalizer.Gamma :=
  SemilinearNormalizer.normalizerEquiv.symm.toMonoidHom.comp
    (d.naturalLinearHom.codRestrict SemilinearNormalizer.normalizer
      (d.naturalLinearHom_mem_normalizer hmoved))

theorem semilinearHom_natural
    (hmoved : ⁅normalizerMoved L,L⁆ = normalizerMoved L)
    (a : (L ⊔ (T : Subgroup G) : Subgroup G)) :
    SemilinearNormalizer.natural (d.semilinearHom hmoved a) = d.naturalLinearHom a := by
  exact congrArg Subtype.val (SemilinearNormalizer.normalizerEquiv.apply_symm_apply _)

theorem semilinearHom_component
    (hmoved : ⁅normalizerMoved L,L⁆ = normalizerMoved L) (l : L) :
    d.semilinearHom hmoved (inclusion le_sup_left l) =
      SemilinearNormalizer.special (d.component l) := by
  apply SemilinearNormalizer.natural_injective
  rw [d.semilinearHom_natural, SemilinearNormalizer.natural_special,
    d.naturalLinearHom_component]

theorem semilinearHom_kernel
    (hmoved : ⁅normalizerMoved L,L⁆ = normalizerMoved L) :
    (d.semilinearHom hmoved).ker =
      (centralizer (normalizerMoved L : Set G)).subgroupOf (L ⊔ (T : Subgroup G)) := by
  rw [← d.naturalLinearHom_kernel hmoved]
  ext a
  simp only [MonoidHom.mem_ker]
  rw [← SemilinearNormalizer.natural_injective.eq_iff,
    d.semilinearHom_natural, map_one]

theorem semilinearHom_component_image
    (hmoved : ⁅normalizerMoved L,L⁆ = normalizerMoved L) :
    (L.subgroupOf (L ⊔ (T : Subgroup G))).map (d.semilinearHom hmoved) =
      SemilinearNormalizer.special.range := by
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨d.component ⟨a,ha⟩, (d.semilinearHom_component hmoved ⟨a,ha⟩).symm⟩
  · rintro ⟨l,rfl⟩
    obtain ⟨l,rfl⟩ := d.onto l
    exact ⟨inclusion le_sup_left l,l.property,d.semilinearHom_component hmoved l⟩

/-- The exact semilinear image is SL₂ times the image of the original T. -/
theorem semilinearHom_range
    (hmoved : ⁅normalizerMoved L,L⁆ = normalizerMoved L) :
    (d.semilinearHom hmoved).range = SemilinearNormalizer.special.range ⊔
      ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))).map (d.semilinearHom hmoved) := by
  let M := L ⊔ (T : Subgroup G)
  have hgen : L.subgroupOf M ⊔ (T : Subgroup G).subgroupOf M = ⊤ := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show L ≤ M from le_sup_left),
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ M from le_sup_right),
      ← MonoidHom.range_eq_map, M.range_subtype]
  have hr := congrArg (Subgroup.map (d.semilinearHom hmoved)) hgen
  rw [Subgroup.map_sup, d.semilinearHom_component_image, ← MonoidHom.range_eq_map] at hr
  exact hr.symm

/-- Some element of the original T has a genuinely outer natural action. -/
@[expose] def HasOuterNaturalAction : Prop :=
  ¬ ∀ t : T, ∃ l : SL, ∀ v : V,
    d.naturalActor (inclusion (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right) t) v =
      Natural l v

theorem semilinearHom_two_image_not_le
    (hmoved : ⁅normalizerMoved L,L⁆ = normalizerMoved L)
    (ho : d.HasOuterNaturalAction) :
    ¬ ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))).map (d.semilinearHom hmoved) ≤
      SemilinearNormalizer.special.range := by
  intro hh
  apply ho
  intro t
  obtain ⟨l,hl⟩ := hh (show d.semilinearHom hmoved (inclusion le_sup_right t) ∈
      ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))).map (d.semilinearHom hmoved) from
    ⟨inclusion le_sup_right t,t.property,rfl⟩)
  refine ⟨l,fun v => ?_⟩
  have he := congrArg SemilinearNormalizer.natural hl
  rw [SemilinearNormalizer.natural_special,d.semilinearHom_natural] at he
  exact (LinearEquiv.congr_fun he v).symm

/-- Source 13.1.8 supplies the generation used by all these kernel comparisons. -/
theorem source_moved_commutator [Finite G]
    (h : Hypothesis1311 T) (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    ⁅normalizerMoved L,L⁆ = normalizerMoved L := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  exact (normalizerMoved_commutator_and_card hL.1.1
    (faithful_maximal_normalizer_moved h.simpleQTKE hL hTL).2.1).1

end Marking

/-- An identification of the original action image with S₅. The kernel and
component clauses refer to the literal subgroups of LT. This is output data
for the outer-image construction, not an assumed source theorem. -/
structure OuterMarking {G : Type*} [Group G] (T : Sylow 2 G) (L : Subgroup G) where
  quotient : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 5)
  onto : Function.Surjective quotient
  kernel : quotient.ker =
    (centralizer (normalizerMoved L : Set G)).subgroupOf (L ⊔ (T : Subgroup G))
  component : (L.subgroupOf (L ⊔ (T : Subgroup G))).map quotient = alternatingGroup (Fin 5)

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive
