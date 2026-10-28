module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherComponentsFaithful
public import Theory.GroupAction.AbelianConjugationDisplacement
public import Theory.GroupTheory.Commutator.CentralizingComplement
public import Theory.GroupTheory.PrimeIndexCentralizer

/-!
# Two identically marked natural sections before component normality

Put R=C_T(U), W=U∩V and Z=C_T(L). For v in V outside U the actual
commutator map r ↦ [r,v] is a surjective homomorphism R → W with kernel
WZ. The index-two hyperplane calculation makes its action commute with Y,
so the same surjective map Y → SL_(d−1)(2) marks both W and R/WZ.
This establishes the two identical natural factors used in the exceptional
A₇ exclusion, without assuming that Y is normal in N_G(R).

The original centralizer splitting also gives |R|≤2^(2(d−1)+1), and
hence rank(R)≤7 when d=4. The component sieve and its exceptional-module
recognition remain with qt-d-12213-local-rigidity.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
original 12.2.25, printed p.805.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

abbrev sectionRadical (T : Sylow 2 G) (U : Subgroup G) :=
  (T : Subgroup G) ⊓ centralizer (U : Set G)

omit [Finite G] in
theorem sylow_normalizes_sectionRadical (C : CyclicLocalAnalysis T L V d H P U) :
    (T : Subgroup G) ≤ normalizer (sectionRadical T U : Set G) :=
  (le_inf (T : Subgroup G).le_normalizer
    (C.sylow_normalizes_core.trans (normalizer_le_normalizer_centralizer U))).trans
    inf_normalizer_le_normalizer_inf

omit [Finite G] in
theorem radical_chosen_commutator
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    ⁅sectionRadical T U,V⁆ = U ⊓ V := by
  let := C.elementary
  have hUR : U ≤ sectionRadical T U := le_inf C.core_le_sylow (le_centralizer U)
  have hRW : sectionRadical T U ≤ centralizer ((U ⊓ V : Subgroup G) : Set G) :=
    inf_le_right.trans (centralizer_le inf_le_left)
  apply le_antisymm
  · rw [commutator_comm]
    exact commutator_le_of_normalized_index_two V (U ⊓ V) (sectionRadical T U)
      inf_le_right (RigidityResidual.hyperplane_index A C) (inf_le_left.trans hTV)
      (hRW.trans (Subgroup.centralizer_le_normalizer _))
  · rw [← C.transvections]
    exact commutator_mono hUR le_rfl

omit [Finite G] in
theorem radical_single_commutator
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (C : CyclicLocalAnalysis T L V d H P U)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (v : G) (hv : v ∈ V) (hvU : v ∉ U) :
    ⁅sectionRadical T U,zpowers v⁆ = U ⊓ V := by
  have hg : (U ⊓ V) ⊔ zpowers v = V := sup_zpowers_eq_of_relIndex_prime
    inf_le_right Nat.prime_two (RigidityResidual.hyperplane_index A C) hv (fun hw => hvU hw.1)
  exact (commutator_eq_of_centralizing_sup hg
    (le_centralizer_iff.mp (inf_le_right.trans (centralizer_le inf_le_left)))
    ((zpowers_le.mpr hv).trans (D.le_sylow.trans (sylow_normalizes_sectionRadical C)))).trans
      (radical_chosen_commutator A C hTV)

omit [Finite G] in
theorem chosen_residual_actions_commute
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (v : V) (y : rigidityHyperplaneResidual L U V) :
    Commute ((sectionRadical T U).normalizerMonoidHom
      ⟨v,sylow_normalizes_sectionRadical C (D.le_sylow v.property)⟩)
      ((sectionRadical T U).normalizerMonoidHom ⟨y,B.residual_normalizes y.property⟩) := by
  let R := sectionRadical T U
  let Y := rigidityHyperplaneResidual L U V
  let a : normalizer (R : Set G) := ⟨v,sylow_normalizes_sectionRadical C (D.le_sylow v.property)⟩
  let b : normalizer (R : Set G) := ⟨y,B.residual_normalizes y.property⟩
  have hVY : ⁅V,Y⁆ ≤ U ⊓ V := commutator_le_of_normalized_index_two V (U ⊓ V) Y
    inf_le_right (RigidityResidual.hyperplane_index A C)
    ((map_subtype_le _).trans (inf_le_left.trans D.normalizes)) ((map_subtype_le _).trans inf_le_right)
  have hk : ⁅a,b⁆ ∈ R.normalizerMonoidHom.ker := by
    rw [normalizerMonoidHom_ker]
    exact le_centralizer_iff.mp (inf_le_right.trans (centralizer_le inf_le_left))
      (hVY (commutator_mem_commutator v.property y.property))
  have he := MonoidHom.mem_ker.mp hk
  rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm] at he
  exact he

omit [Finite G] in
/-- A marked natural section before the residual normality argument. -/
theorem exists_radical_displacement
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    ∃ (v : V) (δ : sectionRadical T U →* (U ⊓ V : Subgroup G)),
      (v : G) ∉ U ∧ Function.Surjective δ ∧
      (∀ r, (δ r : G) = ⁅(r : G),(v : G)⁆) ∧
      δ.ker = (centralizer (V : Set G)).subgroupOf (sectionRadical T U) ∧
      ∀ (y : rigidityHyperplaneResidual L U V) r,
        δ ((sectionRadical T U).normalizerMonoidHom ⟨y,B.residual_normalizes y.property⟩ r) =
          residualHyperplaneAction L U V y (δ r) := by
  let := D.elementary
  let R := sectionRadical T U
  let : IsElementaryAbelian 2 R := B.elementary
  obtain ⟨v,hv,hvU,_⟩ := C.inverted
  let vR : normalizer (R : Set G) := ⟨v,sylow_normalizes_sectionRadical C (D.le_sylow hv)⟩
  let f := ConjugationDisplacement.hom R vR
  have hv2 : v ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv
  have hr : f.range.map R.subtype = U ⊓ V :=
    (ConjugationDisplacement.range R vR hv2).trans (radical_single_commutator D A C hTV v hv hvU)
  let δ : R →* (U ⊓ V : Subgroup G) :=
    (R.subtype.comp f).codRestrict _ (fun r => hr ▸ mem_map_of_mem _ (show f r ∈ f.range from ⟨r,rfl⟩))
  have hδ (r : R) : (δ r : G) = ⁅(r : G),v⁆ := ConjugationDisplacement.hom_apply R vR r
  refine ⟨⟨v,hv⟩,δ,hvU,?_,hδ,?_,?_⟩
  · intro w
    have hw : (w : G) ∈ f.range.map R.subtype := hr.symm ▸ w.property
    obtain ⟨r,⟨s,rfl⟩,he⟩ := hw
    exact ⟨s,Subtype.ext he⟩
  · have he := inf_centralizer_eq_of_prime_index_supplement R (U ⊓ V) V inf_le_right
      Nat.prime_two (RigidityResidual.hyperplane_index A C)
      (inf_le_right.trans (centralizer_le inf_le_left)) v hv (fun hw => hvU hw.1)
    ext r
    change δ r = 1 ↔ (r : G) ∈ centralizer (V : Set G)
    rw [← Subtype.val_inj,hδ]
    change ⁅(r : G),v⁆ = 1 ↔ _
    rw [commutatorElement_eq_one_iff_mul_comm]
    have hh := SetLike.ext_iff.mp he (r : G)
    have hrR : (r : G) ∈ R := r.property
    simpa only [mem_inf, hrR, true_and, mem_centralizer_singleton_iff] using hh
  · intro y r
    have he := ConjugationDisplacement.equivariant R vR
      ⟨y,B.residual_normalizes y.property⟩ (chosen_residual_actions_commute D A C B ⟨v,hv⟩ y) r
    exact Subtype.ext (congrArg (fun r : R => (r : G)) he)


omit [Finite G] in
/-- The intermediate fixed kernel is the hyperplane plus the central factor. -/
theorem radical_chosen_fixed_kernel (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) :
    sectionRadical T U ⊓ centralizer (V : Set G) =
      (U ⊓ V) ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  let Z := (T : Subgroup G) ⊓ centralizer (L : Set G)
  have hZR : Z ≤ sectionRadical T U := le_sup_right.trans B.centralizer_split.symm.le
  have hZV : Z ≤ centralizer (V : Set G) := by
    have hh : Z ≤ (T : Subgroup G) ⊓ centralizer (V : Set G) :=
      le_sup_right.trans B.kernel_split.symm.le
    exact hh.trans inf_le_right
  rw [show sectionRadical T U = U ⊔ Z from B.centralizer_split, sup_comm U Z,
    inf_centralizer_sup_of_centralizing Z U V
      ((hZR.trans inf_le_right).trans (Subgroup.centralizer_le_normalizer _)) hZV,
    C.action_kernel,sup_comm]

/-- The two natural factors use the same matrix marking. The second marking is
on the literal quotient of R by its hyperplane and central fixed factor. -/
theorem source_radical_natural_sections
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d) :
    let R := sectionRadical T U
    let Y := rigidityHyperplaneResidual L U V
    let B := RigidityKernel.source_centralizers h D structural A C hnone
    ∃ (q : Y →* Matrix.SpecialLinearGroup (Fin (d-1)) (ZMod 2))
      (f : (U ⊓ V : Subgroup G) ≃* Multiplicative (Fin (d-1) → ZMod 2))
      (δ : R →* (U ⊓ V : Subgroup G)),
      Function.Surjective q ∧ Function.Surjective δ ∧
      δ.ker = ((U ⊓ V) ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G))).subgroupOf R ∧
      (∀ y w, f (residualHyperplaneAction L U V y w) = Multiplicative.ofAdd
        (Representation.specialLinearNatural (d-1) (q y) (f w).toAdd)) ∧
      ∃ e : (R ⧸ δ.ker) ≃* Multiplicative (Fin (d-1) → ZMod 2),
        (∀ r, e (QuotientGroup.mk' δ.ker r) = f (δ r)) ∧
        ∀ (y : Y) (r : R),
          e (QuotientGroup.mk' δ.ker (R.normalizerMonoidHom
            ⟨y,B.residual_normalizes y.property⟩ r)) = Multiplicative.ofAdd
              (Representation.specialLinearNatural (d-1) (q y)
                (e (QuotientGroup.mk' δ.ker r)).toAdd) := by
  let R := sectionRadical T U
  let Y := rigidityHyperplaneResidual L U V
  let B := RigidityKernel.source_centralizers h D structural A C hnone
  obtain ⟨v,δ,hv,hs,hδ,hker,hact⟩ := exists_radical_displacement D A C B
    (((structural G T L h).2.2 V D).1)
  obtain ⟨a,f,hf⟩ := residual_natural_model D A C hd
  let q := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 Y))
  have hq : Function.Surjective q := a.surjective.comp (QuotientGroup.mk'_surjective _)
  have hmark (y : Y) (w : (U ⊓ V : Subgroup G)) :
      f (residualHyperplaneAction L U V y w) = Multiplicative.ofAdd
        (Representation.specialLinearNatural (d-1) (q y) (f w).toAdd) := by
    apply f.symm.injective
    rw [f.symm_apply_apply]
    exact Subtype.ext (hf y w).symm
  have hk : δ.ker = ((U ⊓ V) ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G))).subgroupOf R := by
    rw [hker]
    ext r
    have he := SetLike.ext_iff.mp (radical_chosen_fixed_kernel C B) (r : G)
    have hr : (r : G) ∈ sectionRadical T U := r.property
    simpa only [mem_subgroupOf, mem_inf, hr, true_and] using he
  let e : (R ⧸ δ.ker) ≃* Multiplicative (Fin (d-1) → ZMod 2) :=
    (QuotientGroup.quotientKerEquivOfSurjective δ hs).trans f
  have he (r : R) : e (QuotientGroup.mk' δ.ker r) = f (δ r) := rfl
  refine ⟨q,f,δ,hq,hs,hk,hmark,e,he,?_⟩
  intro y r
  rw [he,he,hact]
  exact hmark y (δ r)

/-- The rank bound before the exceptional A₇ exclusion. -/
theorem source_radical_card_bound
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) : Nat.card (sectionRadical T U) ≤ 2 ^ (2*(d-1)+1) := by
  let B := RigidityKernel.source_centralizers h D structural A C hnone
  let Z := (T : Subgroup G) ⊓ centralizer (L : Set G)
  have hZR : Z ≤ sectionRadical T U := le_sup_right.trans B.centralizer_split.symm.le
  have hn : Z ≤ normalizer (U : Set G) :=
    (hZR.trans inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
  rw [show sectionRadical T U = U ⊔ Z from B.centralizer_split,
    card_sup_eq_mul_of_normalizes_of_disjoint U Z hn B.centralizer_disjoint,C.dimension,
    pow_succ]
  exact Nat.mul_le_mul_left _ B.component_centralizer_card

/-- In the source exceptional dimension the original radical has rank at most seven. -/
theorem source_radical_rank_bound_four
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 4) (C : CyclicLocalAnalysis T L V 4 H P U)
    (hnone : NoEscape L V) :
    Nat.log 2 (Nat.card (sectionRadical T U)) ≤ 7 := by
  have hc := source_radical_card_bound h D structural A C hnone
  have hm := Nat.log_mono_right hc (b := 2)
  simpa only [Nat.log_pow (by decide : 1 < 2)] using hm

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
