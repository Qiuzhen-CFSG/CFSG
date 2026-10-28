module
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.M11HigmanSimsSourceHSOuterElementary
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceTwenty.SymmetricOuter.Factors
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.ElementaryCentralizer
import all Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.FiveSubgroup
import all CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.ElementaryCentralizer.Data

/-!
# The elementary outer rank-five argument on the original HS action

Removing the actual component center gives coordinates compatible with the
specified central-quotient marking. The inner intersection of a rank-five
actor has at least sixteen elements in the elementary outer centralizer.
If its S5 quotient is nontrivial, its normal closure contains an order-five
element. Otherwise it fills the literal E16 kernel. A checked HS word then
shows that multiplying the outer involution by a kernel element gives the
symmetric outer class.

The order-five element is transported into the actual centralizer-conjugate
closure. Thus the elementary estimates follow from the symmetric rank-five
estimate, without a complement, ambient normality, or a representation-model
comparison. The symmetric estimates remain an explicit premise of the final
consumer in this module.

Source: GM02 Proposition 5.1, HS paragraph, author-preprint pp.16–17;
Aschbacher–Smith K.4, printed p.457/PDF p.468. The concrete word uses the
existing ATLAS HSG1-p100B0 carrier and its source attribution. Internal
imports expose the packed permutations solely for the finite word check.
-/

public section

open Subgroup Theory.GroupTheory Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims
open HigmanSims Twenty
open Sporadic.LeechRelated.HS (Carrier)
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue
namespace HSOuterCalculations
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- The source component identified through the literal central-quotient marking. -/
noncomputable def markedComponent (h : HigmanSims.SourceHypotheses ρ)
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* Carrier) :
    generalizedFitting G ≃* Carrier := by
  let := h.quasisimple
  have hz := h.center_eq_bot_of_two_group
    (Theory.SpecificGroups.J2HSMultipliers.HS.center_isPGroup_of_quotient_equiv e)
  have hq : Function.Injective (QuotientGroup.mk' (center (generalizedFitting G))) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [QuotientGroup.ker_mk', hz]
  exact MulEquiv.ofBijective
    (e.toMonoidHom.comp (QuotientGroup.mk' (center (generalizedFitting G))))
    ⟨e.injective.comp hq, e.surjective.comp (QuotientGroup.mk'_surjective _)⟩

/-- Component coordinates intertwine the original ambient conjugation action. -/
theorem markedComponent_action (h : HigmanSims.SourceHypotheses ρ)
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* Carrier)
    (g : G) (x : generalizedFitting G) :
    markedComponent h e (MulAut.conjNormal g x) =
      quotientAction e g (markedComponent h e x) :=
  (MulAut.centralQuotientAction_apply e (MulAut.conjNormal g) x).symm

/-- The original inner action retains its specified quotient marking. -/
theorem markedComponent_inner (h : HigmanSims.SourceHypotheses ρ)
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* Carrier)
    (x : generalizedFitting G) :
    quotientAction e (x : G) = MulAut.conj (markedComponent h e x) := by
  change MulAut.centralQuotientAction e (MulAut.conjNormal (x : G)) = _
  rw [MulAut.conjNormal_val, MulAut.centralQuotientAction_conj]
  rfl

omit [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] in
private theorem centralizer_iff_fixed {t : G}
    (f : generalizedFitting G ≃* Carrier) (r : MulAut Carrier)
    (ha : ∀ x, f (MulAut.conjNormal t x) = r (f x)) (x : generalizedFitting G) :
    (x : G) ∈ centralizer ({t} : Set G) ↔ f x ∈ r.fixedSubgroup := by
  rw [MulAut.mem_fixedSubgroup, ← ha, f.injective.eq_iff, Subtype.ext_iff,
    mem_centralizer_singleton_iff]
  change (x : G) * t = t * x ↔ t * x * t⁻¹ = x
  rw [mul_inv_eq_iff_eq_mul, eq_comm]

omit [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] in
/-- The relative inner centralizer is the fixed subgroup in compatible coordinates. -/
noncomputable def centralizerEquiv {t : G}
    (f : generalizedFitting G ≃* Carrier) (r : MulAut Carrier)
    (ha : ∀ x, f (MulAut.conjNormal t x) = r (f x)) :
    Symmetric.innerCentralizer t ≃* r.fixedSubgroup where
  toFun x := ⟨f ⟨x, x.property.2⟩,
    (centralizer_iff_fixed f r ha ⟨x, x.property.2⟩).mp x.property.1⟩
  invFun y := ⟨f.symm y, by
    refine ⟨?_, (f.symm y).property⟩
    apply (centralizer_iff_fixed f r ha (f.symm y)).mpr
    simpa only [f.apply_symm_apply] using y.property⟩
  left_inv x := Subtype.ext (congrArg (fun z : generalizedFitting G => (z : G))
    (f.symm_apply_apply ⟨x, x.property.2⟩))
  right_inv y := by apply Subtype.ext; exact f.apply_symm_apply _
  map_mul' x y := Subtype.ext (f.map_mul ⟨x, x.property.2⟩ ⟨y, y.property.2⟩)

omit [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] in
/-- The relative-centralizer equivalence uses the same component coordinates. -/
theorem centralizerEquiv_apply {t : G}
    (f : generalizedFitting G ≃* Carrier) (r : MulAut Carrier)
    (ha : ∀ x, f (MulAut.conjNormal t x) = r (f x))
    (x : Symmetric.innerCentralizer t) :
    (centralizerEquiv f r ha x).val = f ⟨x, x.property.2⟩ := by
  rfl

/-- Coordinates on the original component normalized to the specified outer class. -/
theorem normalizedComponent (h : HigmanSims.SourceHypotheses ρ)
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* Carrier)
    {t : G} {r : MulAut Carrier} (ht : IsConj r (quotientAction e t)) :
    ∃ (c : MulAut Carrier) (f : generalizedFitting G ≃* Carrier),
      quotientAction e t = c * r * c⁻¹ ∧
      (∀ x, f (MulAut.conjNormal t x) = r (f x)) ∧
      (∀ x : generalizedFitting G, quotientAction e (x : G) = MulAut.conj (c (f x))) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp ht
  let f := (markedComponent h e).trans c.symm
  refine ⟨c, f, hc.symm, ?_, ?_⟩
  · intro x
    change c.symm (markedComponent h e (MulAut.conjNormal t x)) =
      r (c.symm (markedComponent h e x))
    rw [markedComponent_action, ← hc]
    change c.symm (c (r (c.symm (markedComponent h e x)))) = _
    rw [c.symm_apply_apply]
  · intro x
    rw [markedComponent_inner h e]
    change MulAut.conj (markedComponent h e x) =
      MulAut.conj (c (c.symm (markedComponent h e x)))
    rw [c.apply_symm_apply]

open HSOuter.ElementaryCentralizer in
private theorem elementary_closure_or_kernel (B : Subgroup C) (hcard : 16 ≤ Nat.card B) :
    (∃ x ∈ normalClosure (B : Set C), orderOf x = 5) ∨ kernelGenerator 0 ∈ B := by
  by_cases hBQ : B ≤ Q
  · have he : B = Q := eq_of_le_of_card_ge hBQ (kernel_card ▸ hcard)
    exact Or.inr (he ▸ kernelGenerator_mem 0)
  · left
    let f : C →* S5 := quotientEquivS5.toMonoidHom.comp (QuotientGroup.mk' Q)
    have hf : Function.Surjective f :=
      quotientEquivS5.surjective.comp (QuotientGroup.mk'_surjective Q)
    let N := normalClosure (B : Set C)
    let M := N.map f
    let : M.Normal := Subgroup.Normal.map inferInstance f hf
    have hM : M ≠ ⊥ := by
      intro hM
      apply hBQ
      intro a ha
      have hfa : f a ∈ M := mem_map_of_mem f (subset_normalClosure ha)
      have hfa1 : f a = 1 := mem_bot.mp (hM ▸ hfa)
      apply (QuotientGroup.eq_one_iff _).mp
      exact quotientEquivS5.injective (hfa1.trans quotientEquivS5.map_one.symm)
    have hAlt : alternatingGroup (Fin 5) ≤ M :=
      Equiv.Perm.alternatingGroup_le_of_normal (by simp)
        ((nontrivial_iff_ne_bot _).mpr hM)
    have hAltCard : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      decide
    have hdiv : 5 ∣ Nat.card N :=
      dvd_trans (by decide : 5 ∣ 60)
        (dvd_trans (hAltCard ▸ card_dvd_of_le hAlt) (N.card_map_dvd f))
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) 5 hdiv
    exact ⟨x, x.property, (orderOf_injective N.subtype N.subtype_injective x).trans hx⟩

omit [Finite G] [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] in
private theorem normalClosure_map_le {C : Type*} [Group C] (φ : C →* G)
    {A : Subgroup G} {t : G} (hC : ∀ c, φ c ∈ centralizer ({t} : Set G))
    (B : Subgroup C) (hB : ∀ b ∈ B, φ b ∈ A) :
    (normalClosure (B : Set C)).map φ ≤ centralizerConjugateClosure A t := by
  rw [map_le_iff_le_comap]
  apply (closure_le _).mpr
  intro x hx
  obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨c, rfl⟩ := isConj_iff.mp hax
  change φ (c * a * c⁻¹) ∈ centralizerConjugateClosure A t
  rw [map_mul, map_mul, map_inv]
  apply (le_iSup (fun c : centralizer ({t} : Set G) =>
    A.map (MulAut.conj (c : G)).toMonoidHom) ⟨φ c, hC c⟩)
  exact mem_map_of_mem (MulAut.conj (φ c)).toMonoidHom (hB a ha)

open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.FiveSubgroup in
private def kernelConjugator : Carrier := b * a * b ^ 2 * a * b * a * b⁻¹ ^ 2 * a

open Sporadic.LeechRelated.HS.FiveSubgroup in
private theorem kernelConjugator_spec :
    (kernelConjugator : Equiv.Perm (Fin 100)) * HSOuter.symmetricPermutation *
      (kernelConjugator : Equiv.Perm (Fin 100))⁻¹ =
    HSOuter.elementaryPermutation * (HSOuter.ElementaryCentralizer.kernelGenerator 0).val.val := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem kernel_product_isSymmetric :
    IsConj (Sporadic.LeechRelated.HS.generated.normalizerMonoidHom HSOuter.symmetricNormalizer)
      (Sporadic.LeechRelated.HS.generated.normalizerMonoidHom HSOuter.elementaryNormalizer *
        MulAut.conj (HSOuter.ElementaryCentralizer.kernelGenerator 0).val) := by
  apply isConj_iff.mpr
  refine ⟨MulAut.conj kernelConjugator, ?_⟩
  let inc : Carrier →* HSOuter.PermutationNormalizer :=
    inclusion Sporadic.LeechRelated.HS.generated.le_normalizer
  have he : inc kernelConjugator * HSOuter.symmetricNormalizer * (inc kernelConjugator)⁻¹ =
      HSOuter.elementaryNormalizer * inc (HSOuter.ElementaryCentralizer.kernelGenerator 0).val :=
    Subtype.ext kernelConjugator_spec
  have hh := congrArg Sporadic.LeechRelated.HS.generated.normalizerMonoidHom he
  have hinc (x : Carrier) : Sporadic.LeechRelated.HS.generated.normalizerMonoidHom
      (inc x) = MulAut.conj x := rfl
  simpa only [map_mul, map_inv, hinc] using hh

private theorem aut_conj (c : MulAut Carrier) (x : Carrier) :
    c * MulAut.conj x * c⁻¹ = MulAut.conj (c x) := by
  apply MulEquiv.ext
  intro y
  change c (x * c.symm y * x⁻¹) = c x * y * (c x)⁻¹
  simp only [map_mul, map_inv, c.apply_symm_apply]

/-- A rank-five elementary actor either generates an actual component five-element
under centralizer conjugation, or contains the other outer involution class. -/
theorem elementary_rank_five_cases (h : HigmanSims.SourceHypotheses ρ)
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* Carrier)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hr : rank A = 5)
    {t : G} (htA : t ∈ A) (htE : IsElementaryOuter e t) :
    (∃ x ∈ centralizerConjugateClosure A t, x ∈ generalizedFitting G ∧ orderOf x = 5) ∨
      ∃ s ∈ A, IsSymmetricOuter e s := by
  let := hA.2
  let L := generalizedFitting G
  let K := Symmetric.innerCentralizer t
  let D := A ⊓ L
  have hAC : A ≤ centralizer ({t} : Set G) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hA.2.toIsMulCommutative.is_comm.comm
        (⟨a, ha⟩ : A) ⟨t, htA⟩))
  have hDK : D ≤ K := le_inf (inf_le_left.trans hAC) inf_le_right
  have hDr : 4 ≤ rank D := by
    have hb := rank_le_inner_rank_add_one h hA
    change rank A ≤ rank D + 1 at hb
    omega
  have hDne : D ≠ ⊥ := by
    intro he
    rw [he, Representation.BinaryOffender.rank_bot] at hDr
    omega
  have hD := hA.of_le (show D ≤ A from inf_le_left) hDne
  let r := Sporadic.LeechRelated.HS.generated.normalizerMonoidHom HSOuter.elementaryNormalizer
  obtain ⟨c, f, htc, hfact, hfinner⟩ := normalizedComponent h e htE
  let ec : K ≃* HSOuter.ElementaryCentralizer.C :=
    (centralizerEquiv f r hfact).trans
      (MulEquiv.subgroupCongr (HSOuter.fixedSubgroup_eq_permutationCentralizer
        HSOuter.elementaryNormalizer))
  let B := (D.subgroupOf K).map ec.toMonoidHom
  have hcard : 16 ≤ Nat.card B := by
    rw [Subgroup.card_map_of_injective ec.injective,
      Nat.card_congr (subgroupOfEquivOfLe hDK).toEquiv, hD.card_eq_two_pow_rank]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hDr
  let φ : HSOuter.ElementaryCentralizer.C →* G := K.subtype.comp ec.symm.toMonoidHom
  have hφC (x) : φ x ∈ centralizer ({t} : Set G) := (ec.symm x).property.1
  have hφB (x) (hx : x ∈ B) : φ x ∈ A := by
    obtain ⟨y, hy, rfl⟩ := hx
    change ((ec.symm (ec y) : K) : G) ∈ A
    rw [ec.symm_apply_apply]
    exact hy.1
  rcases elementary_closure_or_kernel B hcard with ⟨x, hx, ho⟩ | hq
  · left
    refine ⟨φ x, normalClosure_map_le φ hφC B hφB (mem_map_of_mem φ hx),
      (ec.symm x).property.2, ?_⟩
    exact (orderOf_injective φ (K.subtype_injective.comp ec.symm.injective) x).trans ho
  · obtain ⟨y, hy, he⟩ := hq
    have hfy : f ⟨y, y.property.2⟩ = (HSOuter.ElementaryCentralizer.kernelGenerator 0).val :=
      congrArg Subtype.val he
    refine Or.inr ⟨t * y, A.mul_mem htA hy.1, ?_⟩
    have heq : (show MulAut Carrier from quotientAction e (t * y)) =
        c * (r * MulAut.conj (HSOuter.ElementaryCentralizer.kernelGenerator 0).val) * c⁻¹ := by
      rw [map_mul, htc, hfinner ⟨y, y.property.2⟩, hfy,
        ← aut_conj c (HSOuter.ElementaryCentralizer.kernelGenerator 0).val]
      exact (map_mul (MulAut.conj c) r
        (MulAut.conj (HSOuter.ElementaryCentralizer.kernelGenerator 0).val)).symm
    have hc := kernel_product_isSymmetric.trans (isConj_iff.mpr ⟨c, rfl⟩)
    exact (congrArg (fun z : MulAut Carrier => IsConj
      (Sporadic.LeechRelated.HS.generated.normalizerMonoidHom HSOuter.symmetricNormalizer) z)
      heq).mpr hc


end HSOuterCalculations
universe u v

/-- The elementary outer estimates now require only the symmetric rank-five bound;
the actual centralizer closure and its kernel case are discharged. -/
theorem higmanSims_elementary_outer_estimates_of_symmetric
    {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V}
    (h : HigmanSims.SourceHypotheses ρ) (hd : Module.finrank (ZMod 2) V = 20)
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* Carrier)
    (hS : SymmetricOuterEstimates ρ e) : ElementaryOuterEstimates ρ e := by
  constructor
  · intro t _ htE
    exact higmanSims_elementary_outer_involution_bound h hd e htE
  · intro A hA hr t htA htE
    rcases HSOuterCalculations.elementary_rank_five_cases h e hA hr htA htE with
      ⟨x, hxC, hxL, hx5⟩ | ⟨s, hsA, hsS⟩
    · exact higmanSims_elementary_outer_bound_of_closure_five h hd e htA htE hxC hxL hx5
    · exact hS.rank_five A hA hr s hsA hsS

end CFSG.Quasithin.ChapterK.SporadicCatalogue
