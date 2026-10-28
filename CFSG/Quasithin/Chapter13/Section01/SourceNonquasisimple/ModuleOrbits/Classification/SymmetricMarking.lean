module
public import Theory.Representation.BinaryPermutation.FiveNaturalNormalizer
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification.IrreducibleMarkings
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.CohomologyReduction

/-!
# The actual symmetric-five moved-module marking

The deleted A₅ action has scalar centralizer and its normalizer is the
permutation S₅ action. Thus the marked component determines the action of
the original normalizer. The offender marking makes this action surjective;
the image of LT contains A₅ and a Sylow two-subgroup, so it is S₅ as well.
All vector identifications pass through the original moved section and its
zero-kernel quotient. The source consumer now leaves only the two product
alternatives of B.5.6.

Source: Aschbacher--Smith 13.1.10(2), pp.871--872; B.4.2 and B.5.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open ChapterB.QuasisimpleSource

private def fiveAutEquiv : Equiv.Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
  MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 5)))
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide))

private theorem fiveNatural_commuting
    (f : BinaryPermutation.natural (Fin 5) →ₗ[ZMod 2] BinaryPermutation.natural (Fin 5))
    (hf : ∀ g : alternatingGroup (Fin 5), ∀ v,
      f (BinaryPermutation.naturalRepresentation (Fin 5) g.val v) =
        BinaryPermutation.naturalRepresentation (Fin 5) g.val (f v))
    (hi : Function.Injective f) : ∀ v, f v = v := by
  let e := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
  let F := e.symm.toLinearMap.comp (f.comp e.toLinearMap)
  have hF : ∀ v, F v = v := by
    apply BinaryPermutation.FiveCentralExtension.core_commuting_eq_id F
    · intro g hg v
      apply e.injective
      simp only [F, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      rw [BinaryPermutation.coreEquivNatural_equivariant, hf ⟨g,hg⟩,
        BinaryPermutation.coreEquivNatural_equivariant, LinearEquiv.apply_symm_apply]
    · exact e.symm.injective.comp (hi.comp e.injective)
  intro v
  have hh := congrArg e (hF (e.symm v))
  simpa only [F, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using hh

/-- The normalizer of the actual A5 deleted action is the original S5 action. -/
private theorem fiveNatural_normalizer
    (f : BinaryPermutation.natural (Fin 5) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5))
    (φ : MulAut (alternatingGroup (Fin 5)))
    (hf : ∀ g : alternatingGroup (Fin 5), ∀ v,
      f (BinaryPermutation.naturalRepresentation (Fin 5) g.val v) =
        BinaryPermutation.naturalRepresentation (Fin 5) (φ g).val (f v)) :
    ∀ v, f v = BinaryPermutation.naturalRepresentation (Fin 5) (fiveAutEquiv.symm φ) v := by
  let s := fiveAutEquiv.symm φ
  have he (g : alternatingGroup (Fin 5)) : (φ g : Equiv.Perm (Fin 5)) = s * g.val * s⁻¹ := by
    have hh := congrArg (fun a : MulAut (alternatingGroup (Fin 5)) => (a g).val)
      (fiveAutEquiv.apply_symm_apply φ)
    exact hh.symm
  let τ := BinaryPermutation.naturalRepresentation (Fin 5)
  let F := (τ s⁻¹).comp f.toLinearMap
  have hF : ∀ v, F v = v := by
    apply fiveNatural_commuting F
    · intro g v
      change τ s⁻¹ (f (τ g.val v)) = τ g.val (τ s⁻¹ (f v))
      rw [hf, he]
      change τ s⁻¹ (τ (s * g.val * s⁻¹) (f v)) = τ g.val (τ s⁻¹ (f v))
      simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel_left]
    · exact (τ.apply_bijective s⁻¹).1.comp f.injective
  intro v
  have hh := congrArg (τ s) (hF v)
  change τ s (τ s⁻¹ (f v)) = _ at hh
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
    map_one, Module.End.one_apply] using hh

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]

private theorem fiveMarked_intertwines {ρ : Representation (ZMod 2) D V}
    {H K : Subgroup D}
    (a : MarkedActionEquiv ρ H K (BinaryPermutation.naturalRepresentation (Fin 5))
      (alternatingGroup (Fin 5))) (g : K) (v : V) :
    a.action.linearEquiv (ρ g v) =
      BinaryPermutation.naturalRepresentation (Fin 5) (a.subgroupEquiv g).val
        (a.action.linearEquiv v) := by
  have he := a.action.intertwines ⟨g, a.contained g.property⟩ v
  rw [a.compatible] at he
  exact he

/-- The actual conjugation action on the component, marked as permutations. -/
def fiveActor {K : Subgroup D} [K.Normal] (e : K ≃* alternatingGroup (Fin 5)) :
    D →* Equiv.Perm (Fin 5) :=
  fiveAutEquiv.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal))

/-- The quotient homomorphism preserves the original component inclusion. -/
theorem fiveActor_component {K : Subgroup D} [K.Normal]
    (e : K ≃* alternatingGroup (Fin 5)) (g : K) : fiveActor e g = (e g).val := by
  apply fiveAutEquiv.injective
  change fiveAutEquiv (fiveAutEquiv.symm (MulAut.congr e (MulAut.conjNormal (g : D)))) = _
  rw [fiveAutEquiv.apply_symm_apply]
  apply MulEquiv.ext
  intro a
  change e (MulAut.conjNormal (g : D) (e.symm a)) =
    MulAut.conjNormal (e g).val a
  have he : MulAut.conjNormal (g : D) (e.symm a) = g * e.symm a * g⁻¹ := Subtype.ext rfl
  rw [he, map_mul, map_mul, map_inv, e.apply_symm_apply]
  apply Subtype.ext
  rfl

/-- A marked A5 component determines the action of every original normalizer element. -/
theorem fiveActor_equivariant (ρ : Representation (ZMod 2) D V)
    {K : Subgroup D} [K.Normal]
    (a : ActionEquiv (ρ.comp K.subtype) (alternatingNatural 5)) (g : D) (v : V) :
    a.linearEquiv (ρ g v) =
      BinaryPermutation.naturalRepresentation (Fin 5) (fiveActor a.groupEquiv g)
        (a.linearEquiv v) := by
  let f := a.linearEquiv.symm.trans
    ((LinearEquiv.ofBijective (ρ g) (ρ.apply_bijective g)).trans a.linearEquiv)
  have hh := fiveNatural_normalizer f (MulAut.congr a.groupEquiv (MulAut.conjNormal g))
    (by
      intro k w
      obtain ⟨x,rfl⟩ := a.linearEquiv.surjective w
      have he := a.intertwines (a.groupEquiv.symm k) x
      rw [a.groupEquiv.apply_symm_apply] at he
      change a.linearEquiv (ρ (a.groupEquiv.symm k) x) =
        BinaryPermutation.naturalRepresentation (Fin 5) k.val (a.linearEquiv x) at he
      change f (BinaryPermutation.naturalRepresentation (Fin 5) k.val (a.linearEquiv x)) = _
      rw [← he]
      simp only [f, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
        LinearEquiv.ofBijective_apply]
      have hc := a.intertwines (MulAut.conjNormal g (a.groupEquiv.symm k)) (ρ g x)
      change a.linearEquiv (ρ (MulAut.conjNormal g (a.groupEquiv.symm k) : K) (ρ g x)) =
        BinaryPermutation.naturalRepresentation (Fin 5)
          (a.groupEquiv (MulAut.conjNormal g (a.groupEquiv.symm k))).val
          (a.linearEquiv (ρ g x)) at hc
      calc
        _ = a.linearEquiv (ρ (MulAut.conjNormal g (a.groupEquiv.symm k) : K) (ρ g x)) := by
          congr 1
          simp only [← Module.End.mul_apply, ← map_mul]
          apply congrArg (fun z : D => ρ z x)
          change g * (a.groupEquiv.symm k : D) =
            (g * (a.groupEquiv.symm k : D) * g⁻¹) * g
          simp only [inv_mul_cancel_right]
        _ = _ := hc) (a.linearEquiv v)
  change a.linearEquiv (ρ g v) =
    BinaryPermutation.naturalRepresentation (Fin 5)
      (fiveAutEquiv.symm (MulAut.congr a.groupEquiv (MulAut.conjNormal g))) (a.linearEquiv v)
  simpa only [f, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.ofBijective_apply] using hh

private theorem fiveActor_surjective_of_action (ρ : Representation (ZMod 2) D V)
    {K : Subgroup D} [K.Normal]
    (b : ActionEquiv (ρ.comp K.subtype) (alternatingNatural 5))
    {E : Type*} [Group E] (e : E ≃* Equiv.Perm (Fin 5)) (f : E →* D)
    (hf : ∀ g v, b.linearEquiv (ρ (f g) v) =
      BinaryPermutation.naturalRepresentation (Fin 5) (e g) (b.linearEquiv v)) :
    Function.Surjective (fiveActor b.groupEquiv) := by
  intro p
  obtain ⟨g,rfl⟩ := e.surjective p
  refine ⟨f g, ?_⟩
  apply BinaryPermutation.naturalMulAction_injective_of_odd (Fin 5) (by decide)
  apply MulEquiv.ext
  intro v
  obtain ⟨w,hw⟩ := b.linearEquiv.surjective v.toAdd
  have he := (fiveActor_equivariant ρ b (f g) w).symm.trans (hf g w)
  apply Multiplicative.toAdd.injective
  change BinaryPermutation.naturalRepresentation (Fin 5) (fiveActor b.groupEquiv (f g)) v.toAdd =
    BinaryPermutation.naturalRepresentation (Fin 5) (e g) v.toAdd
  simpa only [hw] using he

/-- The original central quotient in the symmetric-five row has zero kernel. -/
theorem symmetricFive_central_eq_bot [Finite D] [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {K : Subgroup D}
    (s : MovedSection ρ K) (hi : IsIrrPlus ρ K s.space.toSubmodule)
    (a : MarkedActionEquiv s.action (offenderSubgroup s.action) K
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5))) :
    s.central.toSubmodule = ⊥ := by
  have hc := ExtensionConsequences.symmetricOdd_isCompl s hi (Or.inl rfl) a
  rw [s.central_eq]
  apply bot_unique
  intro v hv
  apply Subtype.ext
  exact hc.disjoint.le_bot ⟨v.property, fun k => congrArg Subtype.val (hv k)⟩


/-- A subgroup containing A5 and a full Sylow two-subgroup is S5. -/
theorem five_range_eq_top (R : Subgroup (Equiv.Perm (Fin 5)))
    (hA : alternatingGroup (Fin 5) ≤ R)
    (P : Sylow 2 (Equiv.Perm (Fin 5))) (hP : (P : Subgroup _) ≤ R) : R = ⊤ := by
  have hd : R.index ∣ 2 := by
    simpa only [alternatingGroup.index_eq_two] using index_dvd_of_le hA
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact index_eq_one.mp h
  · have hdP : 2 ∣ (P : Subgroup (Equiv.Perm (Fin 5))).index := by
      simpa only [h] using (index_dvd_of_le hP)
    exact (P.not_dvd_index hdP).elim

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterB.SourceInduction
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The full moved section and the offender section have identical vectors. -/
def fullSectionSpaceEquiv {L : Subgroup G}
    {H : Subgroup (NormalizerReducedAction.Star L)}
    (hCH : NormalizerReducedAction.componentImage L ≤ H)
    (s : MovedSection ((reducedRepresentation L).comp H.subtype)
      ((NormalizerReducedAction.componentImage L).subgroupOf H)) :
    (fullMovedSection L).space.toSubmodule ≃ₗ[ZMod 2] s.space.toSubmodule :=
  LinearEquiv.ofEq _ _ (by
    rw [(fullMovedSection L).space_eq, s.space_eq, moved_comp_map,
      map_subgroupOf_eq_of_le hCH])

omit [Finite G] in
theorem fullSectionSpaceEquiv_intertwines {L : Subgroup G}
    {H : Subgroup (NormalizerReducedAction.Star L)}
    (hCH : NormalizerReducedAction.componentImage L ≤ H)
    (s : MovedSection ((reducedRepresentation L).comp H.subtype)
      ((NormalizerReducedAction.componentImage L).subgroupOf H))
    (g : H) (v : (fullMovedSection L).space.toSubmodule) :
    fullSectionSpaceEquiv hCH s ((fullMovedSection L).space.toRepresentation g v) =
      s.space.toRepresentation g (fullSectionSpaceEquiv hCH s v) := by
  apply Subtype.ext
  rfl

/-- The deleted component marking lifts along the actual zero-kernel quotient. -/
def fullDeletedComponentEquiv {L : Subgroup G}
    (hj : NormalizerReducedAction.componentImage L ≤ offenderSubgroup (reducedRepresentation L))
    (s : MovedSection ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype)
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L))))
    (hz : s.central.toSubmodule = ⊥)
    (a : MarkedActionEquiv s.action (offenderSubgroup s.action)
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L)))
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5))) :
    ActionEquiv ((fullMovedSection L).space.toRepresentation.comp
      (NormalizerReducedAction.componentImage L).subtype) (alternatingNatural 5) := by
  let b := fullSectionSpaceEquiv hj s
  let q := sectionQuotientEquiv s hz
  let k := (subgroupOfEquivOfLe hj).symm
  refine ⟨k.trans a.subgroupEquiv, b.trans (q.linearEquiv.trans a.action.linearEquiv), ?_⟩
  intro g v
  have h1 := fullSectionSpaceEquiv_intertwines hj s (k g) v
  have h2 := sectionQuotientEquiv_intertwines s hz (k g) (b v)
  have h3 := fiveMarked_intertwines a (k g) (q.linearEquiv (b v))
  exact (congrArg a.action.linearEquiv ((congrArg q.linearEquiv h1).trans h2)).trans h3

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterB.SourceInduction
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
/-- The original full normalizer covers S5 because its offender section does. -/
theorem fullDeletedActor_surjective {L : Subgroup G}
    (hj : NormalizerReducedAction.componentImage L ≤ offenderSubgroup (reducedRepresentation L))
    (s : MovedSection ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype)
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L))))
    (hz : s.central.toSubmodule = ⊥)
    (a : MarkedActionEquiv s.action (offenderSubgroup s.action)
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L)))
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5))) :
    let := reducedComponent_normal L
    Function.Surjective (fiveActor (fullDeletedComponentEquiv hj s hz a).groupEquiv) := by
  let := reducedComponent_normal L
  let b := fullDeletedComponentEquiv hj s hz a
  let τ := (fullMovedSection L).space.toRepresentation
  let c := fullSectionSpaceEquiv hj s
  let q := sectionQuotientEquiv s hz
  change Function.Surjective (fiveActor b.groupEquiv)
  apply fiveActor_surjective_of_action τ b a.action.groupEquiv
    ((offenderSubgroup (reducedRepresentation L)).subtype.comp
      (offenderSubgroup s.action).subtype)
  intro g w
  have h1 := fullSectionSpaceEquiv_intertwines hj s g.val w
  have h2 := sectionQuotientEquiv_intertwines s hz g.val (c w)
  have h3 := a.action.intertwines g (q.linearEquiv (c w))
  exact (congrArg a.action.linearEquiv ((congrArg q.linearEquiv h1).trans h2)).trans h3

/-- The deleted marking belongs to LT, with its original component image. -/
def irreducibleSymmetricFiveMarking
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} [IsElementaryAbelian 2 (normalizerMoved L)]
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (s : MovedSection ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype)
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L))))
    (hi : IsIrrPlus ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype)
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L))) s.space.toSubmodule)
    (a : MarkedActionEquiv s.action (offenderSubgroup s.action)
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L)))
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5))) :
    SymmetricFiveRow T L := by
  let common := CommonMarking.of_source h hmany hL hn hmove
  have hj := componentImage_le_reducedOffender h hL hn hmove
  have hz := symmetricFive_central_eq_bot s hi a
  let := reducedComponent_normal L
  let b := fullDeletedComponentEquiv hj s hz a
  let φ := fiveActor b.groupEquiv
  let f := φ.comp (NormalizerReducedAction.quotient L)
  let q := f.comp (inclusion common.ambient_invariant)
  have hf : Function.Surjective f :=
    (fullDeletedActor_surjective hj s hz a).comp (QuotientGroup.mk'_surjective _)
  have hcomp (l : L) : q (inclusion le_sup_left l) =
      (b.groupEquiv (reducedComponentMap L l)).val := by
    change φ (NormalizerReducedAction.quotient L
      (inclusion common.ambient_invariant (inclusion le_sup_left l))) = _
    have he : NormalizerReducedAction.quotient L
        (inclusion common.ambient_invariant (inclusion le_sup_left l)) =
        (reducedComponentMap L l).val := by
      change NormalizerReducedAction.quotient L _ = NormalizerReducedAction.componentMap L l
      rw [NormalizerReducedAction.componentMap_eq]
      rfl
    rw [he]
    exact fiveActor_component b.groupEquiv _
  have hc : (L.subgroupOf (L ⊔ (T : Subgroup G))).map q = alternatingGroup (Fin 5) := by
    apply le_antisymm
    · rintro _ ⟨l,hl,rfl⟩
      have he := hcomp ⟨l,hl⟩
      change q l ∈ alternatingGroup (Fin 5)
      rw [show q l = (b.groupEquiv (reducedComponentMap L ⟨l,hl⟩)).val from he]
      exact (b.groupEquiv _).property
    · intro p hp
      obtain ⟨l,hl⟩ := (b.groupEquiv.surjective.comp (reducedComponentMap_surjective L)) ⟨p,hp⟩
      exact ⟨inclusion le_sup_left l, l.property, (hcomp l).trans (congrArg Subtype.val hl)⟩
  have hTL : (T : Subgroup G) ≤ NormalizerReducedAction.Ambient L :=
    le_sup_right.trans common.ambient_invariant
  let P := (T.subtype hTL).mapSurjective (f := f) hf
  have hP : (P : Subgroup (Equiv.Perm (Fin 5))) ≤ q.range := by
    rintro p ⟨t,ht,rfl⟩
    exact ⟨⟨t, (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right) ht⟩, rfl⟩
  have hq : Function.Surjective q := MonoidHom.range_eq_top.mp
    (five_range_eq_top q.range (hc ▸ map_le_range q _) P hP)
  let e := (MulEquiv.multiplicativeAdditive (normalizerMoved L)).symm.trans
    (fullSectionCoordinates.trans b.linearEquiv).toAddEquiv.toMultiplicative
  refine ⟨common, ⟨common.invariant, q, hq, e, ?_, hc⟩⟩
  intro m v
  have he := fiveActor_equivariant (fullMovedSection L).space.toRepresentation b
    (NormalizerReducedAction.quotient L (inclusion common.ambient_invariant m))
    (fullSectionCoordinates (Additive.ofMul v))
  rw [← fullSectionCoordinates_equivariant] at he
  exact congrArg Multiplicative.ofAdd he

/-- The genuine irreducible branches all give literal source markings.
Only the two product alternatives of B.5.6 remain for final assembly. -/
theorem reducedOffender_marked_or_products
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆) :
    Nonempty (FourWayMarking.{u,u} T L) ∨
      Nonempty (SourceTwoFactorCase ((reducedRepresentation L).comp
        (offenderSubgroup (reducedRepresentation L)).subtype)) ∨
      Nonempty (HyperplaneCase ((reducedRepresentation L).comp
        (offenderSubgroup (reducedRepresentation L)).subtype)) := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  let : IsElementaryAbelian 2 (normalizerMoved L) :=
    (faithful_maximal_normalizer_moved h.simpleQTKE hL hTL).1
  rcases reducedOffender_marked_or_symmetric_products h hmany hL hn hmove with hm | hi | hp
  · exact Or.inl hm
  · obtain ⟨d,hd,⟨a⟩⟩ := hi
    exact Or.inl ⟨.symmetricFive (irreducibleSymmetricFiveMarking h hmany hL hn hmove
      d.sectionData ((irreducibleSectionCase_iff _).mp hd).1 a)⟩
  · exact Or.inr hp

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
