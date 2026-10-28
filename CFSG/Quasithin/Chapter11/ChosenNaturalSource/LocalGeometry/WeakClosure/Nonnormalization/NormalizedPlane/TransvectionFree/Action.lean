module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.NormalizedPlane.Actor
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport
public import Theory.Representation.SymplecticNaturalNormalizer.FixedLineInner
public import Theory.Representation.CentralCoverOriginalAction

/-!
# Lifting the actual symplectic normalizer action

Conjugation by N_G(V) acts on the original chosen module and its marked
central quotient. The latter action normalizes the literal natural Sp4
image. Commutator generation makes a compatible lift unique: an actor
trivial on the quotient is trivial on the whole original module, and an
inner quotient actor has exactly the marked inner action on that module.
No splitting or field structure on the central kernel is used.

A square-one actor fixing a full field line has no field or scalar part,
so its quotient action lies in the actual symplectic image. The source consumer applies these results to the reciprocal normalized pair in 11.2.4.

Source: Aschbacher--Smith, 11.2.4, printed pp.769--770, and the central-cover
generation and uniqueness principle of I.1.5, printed p.408.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open scoped IsMulCommutative
open SymplecticConjugatePair.Ambient SymplecticConjugatePair.Ambient.Normalizer
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.NormalizedPlane.TransvectionFree
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

private def spaceLinear : letI := D.elementary
    D.space ≃ₗ[ZMod 2] Additive V := by
  letI := D.elementary
  let f : D.space ≃+ Additive V :=
    { toFun v := Additive.ofMul (D.spaceEquiv (Multiplicative.ofAdd v))
      invFun v := (D.spaceEquiv.symm v.toMul).toAdd
      left_inv v := congrArg Multiplicative.toAdd
        (D.spaceEquiv.symm_apply_apply (Multiplicative.ofAdd v))
      right_inv v := congrArg Additive.ofMul (D.spaceEquiv.apply_symm_apply v.toMul)
      map_add' v w := congrArg Additive.ofMul (D.spaceEquiv.map_mul
        (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)) }
  exact f.toLinearEquiv (ZMod.map_smul f)

/-- The full original normalizer action, before taking any central quotient. -/
def fullAction : Representation (ZMod 2) (normalizer (V : Set G)) D.space := by
  letI := D.elementary
  exact (spaceLinear D).symm.conjRingEquiv.toMonoidHom.comp
    (elementaryRepresentation (p := 2) V.normalizerMonoidHom)

set_option backward.isDefEq.respectTransparency false in
omit [Finite G] in
theorem fullAction_component (l : L) :
    fullAction D ⟨l, D.normalizes l.property⟩ = D.chosenAction l := by
  letI := D.elementary
  apply LinearMap.ext
  intro v
  apply (spaceLinear D).injective
  change (spaceLinear D) ((spaceLinear D).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  apply Additive.toMul.injective
  apply Subtype.ext
  simp only [LinearEquiv.symm_symm]
  change (l : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (l : G)⁻¹ =
    (D.spaceEquiv (Multiplicative.ofAdd (D.chosenAction l v)) : G)
  rw [D.spaceEquiv_apply, D.spaceEquiv_apply]
  rfl

omit [Finite G] in
theorem fullAction_conjugation (a : normalizer (V : Set G)) (v : D.space) :
    (D.spaceEquiv (Multiplicative.ofAdd (fullAction D a v)) : G) =
      (a : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (a : G)⁻¹ := by
  letI := D.elementary
  have h := (spaceLinear D).apply_symm_apply
    (elementaryRepresentation (p := 2) V.normalizerMonoidHom a ((spaceLinear D) v))
  exact congrArg (fun w : Additive V => (w.toMul : G)) h

variable (m : ActionEquiv D.centralQuotientAction
    (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

/-- The same action descended through the original marked central projection. -/
def quotientAction : Representation (ZMod 2) (normalizer (V : Set G))
    (Vector S.field.Carrier) :=
  (Coordinates.sp4 m).conjugationAction (seed_normalizer_le D S) le_rfl

/-- The quotient action on each original vector representative. -/
theorem quotientAction_projection (a : normalizer (V : Set G)) (v : V) :
    quotientAction D S m a ((Coordinates.sp4 m).projection v).toAdd =
      ((Coordinates.sp4 m).projection (V.normalizerMonoidHom a v)).toAdd := by
  exact (Coordinates.sp4 m).conjugationAction_projection (seed_normalizer_le D S) le_rfl a v

theorem quotientAction_component (l : L) (v : Vector S.field.Carrier) :
    quotientAction D S m ⟨l,D.normalizes l.property⟩ v =
      symplecticNatural 2 ((Coordinates.sp4 m).quotientMap l) v := by
  let c := Coordinates.sp4 m
  obtain ⟨w,hw⟩ := c.projection_surjective (Multiplicative.ofAdd v)
  have he : (c.projection w).toAdd = v := congrArg Multiplicative.toAdd hw
  rw [←he]
  change c.conjugationAction _ _ _ _ = _
  rw [c.conjugationAction_projection]
  exact c.projection_component_conjugation l w

theorem projection_fullAction (a : normalizer (V : Set G)) (v : D.space) :
    Preliminary.markedProjection D m (fullAction D a v) =
      quotientAction D S m a (Preliminary.markedProjection D m v) := by
  let c := Coordinates.sp4 m
  have he : D.spaceEquiv (Multiplicative.ofAdd (fullAction D a v)) =
      V.normalizerMonoidHom a (D.spaceEquiv (Multiplicative.ofAdd v)) :=
    Subtype.ext (fullAction_conjugation D a v)
  have h := c.conjugationAction_projection (seed_normalizer_le D S) le_rfl a
    (D.spaceEquiv (Multiplicative.ofAdd v))
  change quotientAction D S m a (c.projection (D.spaceEquiv (Multiplicative.ofAdd v))).toAdd =
    (c.projection (V.normalizerMonoidHom a (D.spaceEquiv (Multiplicative.ofAdd v)))).toAdd at h
  rw [←he] at h
  have hproj (w : D.space) : (c.projection (D.spaceEquiv (Multiplicative.ofAdd w))).toAdd =
      Preliminary.markedProjection D m w := by
    change m.linearEquiv (Submodule.Quotient.mk
      (D.spaceEquiv.symm (D.spaceEquiv (Multiplicative.ofAdd w))).toAdd) = _
    rw [D.spaceEquiv.symm_apply_apply]
    rfl
  simpa only [hproj] using h.symm

private theorem markedAction_quotient (l : L) :
    Preliminary.markedAction D m ((Coordinates.sp4 m).quotientMap l) = D.chosenAction l := by
  apply LinearMap.ext
  exact Preliminary.markedAction_mk D m l

/-- The original covering action is faithful to its quotient on the seed normalizer.
The proof uses commutator generation, so it keeps nonsplit central kernels. -/
theorem fullAction_eq_one_of_quotient (a : normalizer (V : Set G))
    (ha : linearAction (quotientAction D S m) a = 1) : fullAction D a = 1 := by
  let c := Coordinates.sp4 m
  let n : normalizer (L : Set G) := ⟨a,seed_normalizer_le D S a.property⟩
  have hconj (l : L) : c.quotientMap (L.normalizerMonoidHom n l) = c.quotientMap l := by
    apply SymplecticNaturalNormalizer.naturalHom_injective
    have hc (l : L) : linearAction (quotientAction D S m) ⟨l,D.normalizes l.property⟩ =
        SymplecticNaturalNormalizer.naturalHom (c.quotientMap l) := by
      apply LinearEquiv.ext
      exact quotientAction_component D S m l
    rw [←hc,←hc]
    have he : (⟨(L.normalizerMonoidHom n l : G),
        D.normalizes (L.normalizerMonoidHom n l).property⟩ : normalizer (V : Set G)) =
        a * ⟨l,D.normalizes l.property⟩ * a⁻¹ := rfl
    rw [he,map_mul,map_mul,map_inv,ha,one_mul,inv_one,mul_one]
  let σ := Preliminary.markedAction D m
  let p := Preliminary.markedProjection D m
  have hp := Preliminary.markedProjection_isCover D m
  apply OneCohomology.CentralCoverOriginalAction.lift_unique σ σ hp.2.2
    p.toLinearMap hp.2.1
  · intro g v
    obtain ⟨l,rfl⟩ := c.quotientMap_surjective g
    change fullAction D a (Preliminary.markedAction D m (c.quotientMap l) v) =
      Preliminary.markedAction D m (c.quotientMap l) (fullAction D a v)
    rw [markedAction_quotient]
    have he : D.chosenAction (L.normalizerMonoidHom n l) = D.chosenAction l := by
      exact (markedAction_quotient D S m _).symm.trans
        ((congrArg (Preliminary.markedAction D m) (hconj l)).trans
          (markedAction_quotient D S m l))
    conv_rhs => rw [←he]
    rw [←fullAction_component D l,←fullAction_component D (L.normalizerMonoidHom n l)]
    change fullAction D a (fullAction D ⟨l,D.normalizes l.property⟩ v) =
      fullAction D (a * ⟨l,D.normalizes l.property⟩ * a⁻¹) (fullAction D a v)
    simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one]
  · intro g v
    rfl
  · intro v
    change p (fullAction D a v) = p v
    rw [projection_fullAction]
    exact LinearEquiv.congr_fun ha _

/-- A marked inner quotient operator has that same action on the entire cover. -/
theorem fullAction_eq_marked (a : normalizer (V : Set G)) (g : Sp S.field.Carrier)
    (ha : linearAction (quotientAction D S m) a = SymplecticNaturalNormalizer.naturalHom g) :
    fullAction D a = Preliminary.markedAction D m g := by
  obtain ⟨l,hl⟩ := (Coordinates.sp4 m).quotientMap_surjective g
  let b : normalizer (V : Set G) := ⟨l,D.normalizes l.property⟩
  have hb : linearAction (quotientAction D S m) b = SymplecticNaturalNormalizer.naturalHom g := by
    apply LinearEquiv.ext
    intro v
    change quotientAction D S m ⟨l,D.normalizes l.property⟩ v = symplecticNatural 2 g v
    exact (quotientAction_component D S m l v).trans (congrArg (fun x => symplecticNatural 2 x v) hl)
  have hk := fullAction_eq_one_of_quotient D S m (a * b⁻¹) (by
    rw [map_mul,map_inv,ha,hb,mul_inv_cancel])
  have he : fullAction D a = fullAction D b := by
    have hh := congrArg (fun f : Module.End (ZMod 2) D.space => f * fullAction D b) hk
    simpa only [←map_mul,mul_assoc,inv_mul_cancel,mul_one,one_mul] using hh
  rw [he,fullAction_component]
  rw [←hl,markedAction_quotient]

private theorem field_large : 2 < Nat.card S.field.Carrier := by
  rw [S.field.card_eq]
  simpa only [pow_one] using pow_lt_pow_right₀ (by decide : 1 < (2 : ℕ)) S.nonbinary

/-- The quotient operators normalize the literal natural symplectic image. -/
theorem quotientAction_mem_normalizer (a : normalizer (V : Set G)) :
    linearAction (quotientAction D S m) a ∈
      SymplecticConjugatePair.Ambient.Normalizer.naturalNormalizer := by
  let H := normalizer (V : Set G)
  let J := L.subgroupOf H
  let ρ := quotientAction D S m
  let q := (Coordinates.sp4 m).quotientMap
  have himage : J.map (linearAction ρ) =
      SymplecticConjugatePair.Ambient.Normalizer.naturalDerivedImage := by
    apply le_antisymm
    · rintro _ ⟨l,hl,rfl⟩
      have he : linearAction ρ l = SymplecticNaturalNormalizer.naturalHom (q ⟨l,hl⟩) := by
        apply LinearEquiv.ext
        exact quotientAction_component D S m ⟨l,hl⟩
      rw [he]
      exact SymplecticNaturalNormalizer.naturalHom_mem (field_large D S) _
    · rintro _ ⟨x,rfl⟩
      obtain ⟨l,hl⟩ := (Coordinates.sp4 m).quotientMap_surjective x.val
      refine ⟨⟨l,D.normalizes l.property⟩,l.property,?_⟩
      apply LinearEquiv.ext
      intro v
      exact (quotientAction_component D S m l v).trans (congrArg (fun x => symplecticNatural 2 x v) hl)
  have hnorm : a ∈ normalizer (J : Set H) := by
    apply mem_normalizer_iff.mpr
    intro l
    exact mem_normalizer_iff.mp (seed_normalizer_le D S a.property) l.val
  change linearAction ρ a ∈ normalizer
    (SymplecticConjugatePair.Ambient.Normalizer.naturalDerivedImage (F := S.field.Carrier) : Set _)
  rw [←himage]
  exact J.le_normalizer_map (linearAction ρ) (mem_map_of_mem _ hnorm)

/-- A square-one actor fixing a whole field line has an inner quotient action. -/
theorem quotientAction_inner_of_line (a : normalizer (V : Set G)) (ha : a ^ 2 = 1)
    (v : Vector S.field.Carrier) (hv : v ≠ 0)
    (hfix : ∀ t : S.field.Carrier, quotientAction D S m a (t • v) = t • v) :
    linearAction (quotientAction D S m) a ∈
      SymplecticConjugatePair.Ambient.Normalizer.naturalDerivedImage := by
  let s : SymplecticConjugatePair.Ambient.Normalizer.naturalNormalizer :=
    ⟨linearAction (quotientAction D S m) a, quotientAction_mem_normalizer D S m a⟩
  have hs : s ^ 2 = 1 := by
    apply Subtype.ext
    change linearAction (quotientAction D S m) a ^ 2 = 1
    rw [←map_pow,ha,map_one]
  obtain ⟨g,hg⟩ := SymplecticNaturalNormalizer.conjugation_inner_of_fixes_field_line
    (field_large D S) s v hv hfix
  by_contra hout
  apply SymplecticNaturalNormalizer.conjugation_not_inner (field_large D S) s hs hout
  exact ⟨g,hg.symm⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.NormalizedPlane.TransvectionFree
