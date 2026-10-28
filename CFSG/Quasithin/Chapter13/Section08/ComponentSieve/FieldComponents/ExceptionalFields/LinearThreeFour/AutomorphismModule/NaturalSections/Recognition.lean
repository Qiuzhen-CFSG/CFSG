module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.Constructions
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.Projective.Transfer
public import Theory.Representation.SL3FourNaturalDual.CentralSections
public import Theory.GroupTheory.PrimeRankCubeFree

/-!
# Natural recognition of an invariant SL₃(4) central section

For a normal SL₃(F₄) component K and a two-group quotient, an invariant
Irr⁺ member gives an irreducible action on the literal quotient I/C_I(K).
The faithful action image has quasisimple component image and trivial
two-core, hence that component image is its generalized Fitting subgroup.
The original elementary quadratic actor retains its rank: the section
kernel centralizes K, while the actor acts faithfully on K. Restriction
and quotient only decrease its fixed codimension.

The component kernel is either trivial or the center of order three.
In the latter case its image is actually PSL₃(F₄), whose odd-prime ranks
are at most two by its order. This proves SQTK for the whole image and
allows the projective quadratic bound to exclude loss of the center.
In the faithful case the entire action kernel is a two-group, so SQTK
passes from the given actor. The SL₃(F₄) B.4 inputs now supply natural
coordinates, transported through the actual component action map.

The universal earlier classification implications remain explicit:
`Projective.IrreducibleProjectiveBound`, `LinearSmallRatioInput`, and
`LinearFFInput`. Their faithful-action, SQTK, F*, and irreducibility
hypotheses are all discharged here. Naturality of the selected section
is a conclusion, with a possibly changed marking. Homogeneous selection,
graph remarking, exclusion of F.9.18(4i),(4ii), and saturation belong to
the parent assembly.

The image and codimension arguments adapt `Projective/Transfer.lean`.
The concrete matrix simplicity and cardinality results come from the
attributed ATLAS ports imported there; no additional ATLAS code is copied.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.20, printed p.955 (PDF p.972); B.4.2 and B.4.5, pp.86–87;
F.9.18(3),(4), pp.325–326.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.SL3FourNaturalDual
open Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NaturalRecognition
universe u

private theorem field_card : Nat.card F = 4 := by
  rw [Nat.card_eq_fintype_card]
  exact SL2FourNatural.card_field

private theorem sl_quasisimple : IsQuasisimple SL :=
  { toIsPerfect := Atlas.sl_perfect 3 (by decide)
    simple := Atlas.psl_simple_high_rank 3 (by decide) }

private theorem projective_card : Nat.card PSL(3, F) = 20160 := by
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  rw [field_card] at h
  norm_num [Fin.prod_univ_succ] at h
  rw [Nat.card_eq_fintype_card]
  omega

private theorem projective_rank (p : ℕ) (hp : p.Prime) (ho : Odd p) :
    primeRank p PSL(3, F) ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  apply primeRank_le_two_of_cube_not_dvd
  rw [projective_card]
  intro hd
  have hpd : p ∣ 2 ^ 6 * (3 ^ 2 * (5 * 7)) := by
    norm_num
    exact (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
  have hpv : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
    rcases hp.dvd_mul.mp hpd with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    rcases hp.dvd_mul.mp h with h | h
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)))
    rcases hp.dvd_mul.mp h with h | h
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)))
    · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)))
  rcases hpv with rfl | rfl | rfl | rfl
  · exact ho.not_two_dvd_nat (dvd_refl 2)
  all_goals norm_num at hd

private theorem quotient_center_equiv {K : Type*} [Group K] (e : K ≃* SL) :
    Nonempty (K ⧸ center K ≃* PSL(3, F)) := by
  refine ⟨QuotientGroup.congr _ _ e ?_⟩
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (centerCongr e ⟨x, hx⟩).property
  · intro x hx
    exact ⟨e.symm x, ((centerCongr e).symm ⟨x, hx⟩).property, e.apply_symm_apply x⟩

private theorem component_image_alternatives {K X : Type*} [Group K] [Finite K]
    [Group X] [Nontrivial X] (e : K ≃* SL) (f : K →* X) (hf : Function.Surjective f) :
    Function.Injective f ∨ Nonempty (X ≃* PSL(3, F)) := by
  let := sl_quasisimple
  let : IsQuasisimple K := IsQuasisimple.of_mulEquiv e.symm
  have hk : f.ker ≤ center K := by
    rcases IsQuasisimple.normal_le_center_or_eq_top f.ker with h | h
    · exact h
    · exfalso
      have hs : Subsingleton X := ⟨fun x y => by
        obtain ⟨x, rfl⟩ := hf x
        obtain ⟨y, rfl⟩ := hf y
        have hx : f x = 1 := (show x ∈ f.ker from h.symm ▸ mem_top x)
        have hy : f y = 1 := (show y ∈ f.ker from h.symm ▸ mem_top y)
        exact hx.trans hy.symm⟩
      exact not_subsingleton X hs
  have hc : Nat.card (center K) = 3 := by
    rw [Nat.card_congr (centerCongr e).toEquiv]
    change Nat.card (center SL(3, F)) = 3
    rw [Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin, field_card]
    decide
  have hd : Nat.card f.ker ∣ 3 := hc ▸ card_dvd_of_le hk
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · exact Or.inl ((MonoidHom.ker_eq_bot_iff f).mp (card_eq_one.mp h))
  · have he : f.ker = center K := eq_of_le_of_card_ge hk (by rw [hc, h])
    obtain ⟨q⟩ := quotient_center_equiv e
    exact Or.inr ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq he).trans q)⟩

variable {G V : Type u} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

private def factorFixed (ρ : Representation (ZMod 2) G V) (K : Subgroup G) [K.Normal]
    (I : Subrepresentation ρ) : Subrepresentation I.toRepresentation where
  toSubmodule := (fixedSpace ρ K).comap I.toSubmodule.subtype
  apply_mem_toSubmodule g v hv := (fixedSpace_stable_of_normal ρ K (mem_top g) v).2 hv

private def factor (ρ : Representation (ZMod 2) G V) (K : Subgroup G) [K.Normal]
    (I : Subrepresentation ρ) : Representation (ZMod 2) G (centralQuotient ρ K I.toSubmodule) :=
  (factorFixed ρ K I).quotientRepresentation

private theorem central_nontrivial (ρ : Representation (ZMod 2) G V)
    (K : Subgroup G) (I : Submodule (ZMod 2) V)
    (hs : K ≤ subspaceStabilizer ρ I) (hI : IsIrrPlus ρ K I) :
    ¬ (⊤ : Subgroup K) ≤ (actionHom (centralQuotientRepresentation ρ K I hs)).ker := by
  intro hk
  apply hI.not_le_fixedSpace ρ
  rw [← hI.choose_spec.1]
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hl, v, hv, rfl⟩
  have hfix := (actionHom_eq_one_iff _ ⟨l, hl⟩).mp (hk (mem_top _))
    (Submodule.Quotient.mk (⟨v, hv⟩ : I))
  exact (Submodule.Quotient.eq ((fixedSpace ρ K).comap I.subtype)).mp hfix

private theorem irreducible_of_component (ρ : Representation (ZMod 2) G V)
    (K : Subgroup G) [IsIrreducible (ρ.comp K.subtype)] : IsIrreducible ρ := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial (ρ.comp K.subtype)
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  let T : Subrepresentation (ρ.comp K.subtype) :=
    ⟨S.toSubmodule, fun l _ hv => S.apply_mem_toSubmodule l hv⟩
  rcases eq_bot_or_eq_top T with h | h
  · left
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun U : Subrepresentation (ρ.comp K.subtype) => U.toSubmodule) h)
  · right
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun U : Subrepresentation (ρ.comp K.subtype) => U.toSubmodule) h)

variable [Finite G] [FiniteDimensional (ZMod 2) V]

private instance imageComponent_normal (σ : Representation (ZMod 2) G V)
    (K : Subgroup G) [K.Normal] : (actionSubgroup σ K).Normal :=
  Subgroup.Normal.map inferInstance (actionHom σ) σ.asGroupHom.rangeRestrict_surjective

private theorem image_structure (σ : Representation (ZMod 2) G V)
    (K : Subgroup G) [K.Normal] [IsQuasisimple K]
    (hquot : IsPGroup 2 (G ⧸ K))
    (hsurvive : ¬ K ≤ (actionHom σ).ker)
    (hirr : IsIrreducible (σ.comp K.subtype)) :
    IsQuasisimple (actionSubgroup σ K) ∧
    IsIrreducible ((imageRepresentation σ).comp (actionSubgroup σ K).subtype) ∧
    generalizedFitting (actionImage σ) = actionSubgroup σ K ∧
    IsPGroup 2 (actionImage σ ⧸ actionSubgroup σ K) ∧
    (actionHom σ).ker ≤ centralizer (K : Set G) := by
  let f := actionHom σ
  let L := actionSubgroup σ K
  let : L.Normal := Subgroup.Normal.map inferInstance f σ.asGroupHom.rangeRestrict_surjective
  let : Nontrivial L := (nontrivial_iff_ne_bot _).2
    (fun h => hsurvive ((map_eq_bot_iff K).mp h))
  let : IsQuasisimple L := IsQuasisimple.of_surjective (f.subgroupMap K) (f.subgroupMap_surjective K)
  have hLI : IsIrreducible ((imageRepresentation σ).comp L.subtype) :=
    (irreducible_comp_surjective_iff (f.subgroupMap K) (f.subgroupMap_surjective K)
      ((imageRepresentation σ).comp L.subtype)).mp hirr
  let := hLI
  let : IsIrreducible (imageRepresentation σ) := irreducible_of_component _ L
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcore : pCore 2 (actionImage σ) = ⊥ := le_bot_iff.mp
    ((normal_p_subgroup_le_ker (imageRepresentation σ) (pCore 2 (actionImage σ)) pCore_isPGroup).trans
      ((MonoidHom.ker_eq_bot_iff _).mpr (imageRepresentation_injective σ)).le)
  have hquo : IsPGroup 2 (actionImage σ ⧸ L) := hquot.of_surjective
    (QuotientGroup.map K L f (Subgroup.le_comap_map _ _))
    (QuotientGroup.map_surjective_of_surjective K L f
      (QuotientGroup.mk_surjective.comp σ.asGroupHom.rangeRestrict_surjective) _)
  refine ⟨inferInstance, hLI, generalizedFitting_eq_of_quasisimple_two_quotient L hquo hcore, hquo, ?_⟩
  have hc : IsComponent G K := ⟨(inferInstance : K.Normal).isSubnormal, inferInstance⟩
  have hcomm := (hc.normal_dichotomy f.ker).resolve_left hsurvive
  exact commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans hcomm)

private theorem rank_two_extension {X : Type*} [Group X] [Finite X]
    (L : Subgroup X) [L.Normal] (hq : IsPGroup 2 (X ⧸ L))
    (hL : IsStronglyQuasithin L) : IsStronglyQuasithin X := by
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply (primeRank_le_iff p 2).mpr
  intro A hAp hAc
  let q := QuotientGroup.mk' L
  have hdis := IsPGroup.disjoint_of_ne p 2 (by intro h; subst p; norm_num at ho)
    (A.map q) (A.map q) (hAp.map q) (hq.to_subgroup _)
  have hz : A.map q = ⊥ := by simpa using hdis.eq_bot
  have hAL : A ≤ L := by simpa only [q, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] using hz
  let B := A.subgroupOf L
  have he : B ≃* A := subgroupOfEquivOfLe hAL
  have hB : IsPGroup p B := hAp.of_equiv he.symm
  let := hAc
  let : IsMulCommutative B := ⟨⟨fun x y => he.injective (by simp only [map_mul, mul_comm])⟩⟩
  rw [← Group.rank_congr he]
  exact (primeRank_le_iff p 2).mp (hL p hp ho) B hB inferInstance

omit [FiniteDimensional (ZMod 2) V] in
private theorem image_sqtk_faithful {κ : GroupClass.{u}}
    (σ : Representation (ZMod 2) G V) (K : Subgroup G) [K.Normal]
    (hG : IsSQTK κ G) (hq : IsPGroup 2 (G ⧸ K))
    (hf : Function.Injective ((actionHom σ).subgroupMap K)) : IsSQTK κ (actionImage σ) := by
  let f := actionHom σ
  have hkerTwo : IsPGroup 2 f.ker := by
    apply hq.of_injective ((QuotientGroup.mk' K).comp f.ker.subtype)
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply le_bot_iff.mp
    intro x hx
    apply Subtype.ext
    have hxK : (x : G) ∈ K := (QuotientGroup.eq_one_iff _).mp hx
    have he : f.subgroupMap K ⟨x, hxK⟩ = f.subgroupMap K 1 := by
      apply Subtype.ext
      change f x = f 1
      rw [map_one]
      exact x.property
    exact congrArg (fun k : K => (k : G)) (hf he)
  have hSQ : IsSQTK κ (G ⧸ f.ker) := by
    refine ⟨?_, hG.isKGroup.quotient f.ker⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho f.ker hkerTwo).trans
      (hG.stronglyQuasithin p hp ho)
  exact (IsSQTK.equiv (QuotientGroup.quotientKerEquivOfSurjective f
    σ.asGroupHom.rangeRestrict_surjective)).mp hSQ

private theorem factor_small_actor (ρ : Representation (ZMod 2) G V)
    (K : Subgroup G) [K.Normal] (I : Subrepresentation ρ)
    (A : Subgroup G) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A)
    (hfaith : ∀ a ∈ A, (∀ v, factor ρ K I a v = v) → a = 1) :
    quadraticRatio (imageRepresentation (factor ρ K I)) ≤ 2 := by
  let σ := factor ρ K I
  have hqσ : IsQuadratic σ A :=
    quadratic_of_equivariant_surjection I.toRepresentation σ
      (factorFixed ρ K I).toSubmodule.mkQ
      (factorFixed ρ K I).toSubmodule.mkQ_surjective (fun _ _ => rfl) A
      (quadratic_subrepresentation ρ I hq)
  apply (quadraticRatio_le_two_iff _).mpr
  refine ⟨actionSubgroup σ A, hA.actionSubgroup σ hfaith, ?_, ?_⟩
  · rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩ v
    exact hqσ x hx y hy v
  · rw [fixedCodim_actionSubgroup, actionSubgroup_rank σ A hfaith]
    exact (fixedCodim_le_of_equivariant_surjection I.toRepresentation σ
      (factorFixed ρ K I).toSubmodule.mkQ
      (factorFixed ρ K I).toSubmodule.mkQ_surjective (fun _ _ => rfl) A).trans
        ((fixedCodim_subrepresentation_le ρ I A).trans hc)

/-- The B.4.5 implication for an actual SL₃(F₄) component, together with its
B.4.2 alternative. For a non-FF module the quadratic ratio is greater than two:
otherwise q̂ ≤ q ≤ 2 permits B.4.5 and none of its non-FF rows has this component.
This universal earlier classification input is not asserted here. -/
def LinearSmallRatioInput (κ : GroupClass.{u}) : Prop :=
  ∀ (X U : Type u) [Group X] [Finite X] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] (τ : Representation (ZMod 2) X U) (L : Subgroup X),
    IsSQTK κ X → generalizedFitting X = L → IsQuasisimple L →
    Function.Injective τ → IsIrreducible (τ.comp L.subtype) → Nonempty (L ≃* SL) →
    IsFFModule τ ∨ 2 < quadraticRatio τ

/-- The SL₃(F₄) specialization of the universal B.4.2 implication. The actual
binary intertwiner with the concrete natural F₄ action is part of its conclusion;
the marking may change, accommodating the dual and field twists. -/
def LinearFFInput (κ : GroupClass.{u}) : Prop :=
  ∀ (X U : Type u) [Group X] [Finite X] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] (τ : Representation (ZMod 2) X U) (L : Subgroup X),
    IsSQTK κ X → generalizedFitting X = L → IsQuasisimple L →
    Function.Injective τ → IsIrreducible (τ.comp L.subtype) → Nonempty (L ≃* SL) →
    IsFFModule τ → ∃ e : L ≃* SL, ∃ c : U ≃ₗ[ZMod 2] W,
      ∀ (l : L) v, c (τ l v) = natural (e l) (c v)

/-- Recognize any invariant Irr⁺ section using the faithful quadratic actor
from F.9.18(3). All B.4 image hypotheses are established before classification.
In particular the projective image is excluded rather than assuming that the
order-three center survives. No homogeneous choice or saturation is assumed. -/
theorem invariant_natural_section {κ : GroupClass.{u}}
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G) [K.Normal]
    (eK : K ≃* SL) (hG : IsSQTK κ G) (hquot : IsPGroup 2 (G ⧸ K))
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
    (hstable : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ I)
    (A : Subgroup G) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A)
    (hAC : Disjoint A (centralizer (K : Set G)))
    (hprojective : Projective.IrreducibleProjectiveBound κ F)
    (hsmallClass : LinearSmallRatioInput κ) (hFFClass : LinearFFInput κ) :
    ∃ e : K ≃* SL, Nonempty (NaturalCentralSection ρ K e I) := by
  let := sl_quasisimple
  let : IsQuasisimple K := IsQuasisimple.of_mulEquiv eK.symm
  let S : Subrepresentation ρ := ⟨I, fun g _ hv => (hstable (mem_top g) _).2 hv⟩
  let σ := factor ρ K S
  have hsurvive : ¬ K ≤ (actionHom σ).ker := by
    intro h
    apply central_nontrivial ρ K I hI.choose hI
    intro k _
    apply (actionHom_eq_one_iff _ k).mpr
    exact (actionHom_eq_one_iff σ k).mp (h k.property)
  have hi : IsIrreducible (σ.comp K.subtype) := hI.choose_spec.2
  obtain ⟨hqs, hirr, hfit, hquo, hker⟩ := image_structure σ K hquot hsurvive hi
  let L := actionSubgroup σ K
  let τ := imageRepresentation σ
  let : IsQuasisimple L := hqs
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  have hfaithA : ∀ a ∈ A, (∀ v, σ a v = v) → a = 1 := by
    intro a ha hfix
    exact (disjoint_iff_inf_le.mp hAC) ⟨ha,
      hker ((actionHom_eq_one_iff σ a).mpr hfix)⟩
  have hsmall := factor_small_actor ρ K S A hA hq hc hfaithA
  let f := (actionHom σ).subgroupMap K
  have hf := (actionHom σ).subgroupMap_surjective K
  rcases component_image_alternatives (X := L) eK f hf with hfaith | hprojectiveModel
  · have hSQ := image_sqtk_faithful σ K hG hquot hfaith
    let e : K ≃* L := MulEquiv.ofBijective f ⟨hfaith, hf⟩
    have hmodel : Nonempty (L ≃* SL) := ⟨e.symm.trans eK⟩
    have hFF : IsFFModule τ :=
      (hsmallClass (actionImage σ) (centralQuotient ρ K I) τ L hSQ hfit hqs
        (imageRepresentation_injective σ) hirr hmodel).resolve_right (not_lt_of_ge hsmall)
    obtain ⟨eL, c, hact⟩ := hFFClass (actionImage σ) (centralQuotient ρ K I) τ L
      hSQ hfit hqs (imageRepresentation_injective σ) hirr hmodel hFF
    refine ⟨e.trans eL, ⟨⟨hI.choose, c, ?_⟩⟩⟩
    intro k v
    exact hact (e k) v
  · obtain ⟨eP⟩ := hprojectiveModel
    have hSQ : IsSQTK κ (actionImage σ) := by
      refine ⟨rank_two_extension L hquo ?_,
        hG.isKGroup.of_surjective (actionHom σ) σ.asGroupHom.rangeRestrict_surjective⟩
      intro p hp ho
      rw [primeRank_congr p eP]
      exact projective_rank p hp ho
    have hlarge := hprojective field_card (actionImage σ) (centralQuotient ρ K I) τ L
      hSQ hfit hqs (imageRepresentation_injective σ) hirr ⟨eP⟩
    exact ((not_lt_of_ge hsmall) hlarge).elim

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NaturalRecognition
