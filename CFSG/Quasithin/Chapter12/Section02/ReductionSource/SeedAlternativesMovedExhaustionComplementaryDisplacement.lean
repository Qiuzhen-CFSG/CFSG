module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionSupportActorRank
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionComplementaryDisplacement

/-!
# Excluding normal natural support on the literal chosen normalizer orbit

The support's marked natural SL₃ action is faithful on the original full
isotypic half. The order-four obstruction forces three copies of the chosen
component's module there. Invariant sections retain the original inner lift,
and conjugation supplies the second half, giving the complementary bound
9m ≤ fixedCodim(A) ≤ 2 rank(A).

The preceding support estimate gives rank(A) ≤ 2(m+n) and 2n ≤ m in the
normal natural-support branch, contradicting this new bound since m > 0.
Thus every original starred actor exchanges a genuine marked Suzuki pair.
The simultaneous centralizer has already been retained by the preceding
alternative; it is never assumed trivial here.

The exchanged Suzuki exclusion, other FF branches, U = W and original
Source325 assembly remain with qt-baumann-fsu. The standing guard and all
chosen-seed hypotheses are preserved by the existing input applications.
Source: Aschbacher--Smith D.3.10, final argument, printed p.204, applied in
3.2.5, p.580; refs/quasithin.pdf.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped MonoidAlgebra IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource ChapterD
open Chapter3.Section02.ChosenSource325.ComplementaryDisplacement
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The normal natural support forces at least three original component copies
in the actual full isotypic half. -/
theorem normalizer_normal_support_original_multiplicity
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G)) :
    let := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let f := internalHom M U hn
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map f
    let C := centralizer (K : Set (internalActionImage M U hn))
    let I := (typePart (internalSubrepresentation hn D.normalizes)).toSubmodule
    let S := (internalSylow T M U hn D.sylow_normalizes_component : Subgroup (internalActionImage M U hn))
    ∀ A : Subgroup (internalActionImage M U hn), A ≤ S → A ∈ QhatStar ρ →
      ∀ X : Subgroup (internalActionImage M U hn),
        X.Normal → IsQuasisimple X → X ≤ C → ⁅X,A ⊓ C⁆ = X → primeRank 3 X = 1 →
        3 * Module.finrank (ZMod 2) (internalSection U V) ≤ Module.finrank (ZMod 2) I := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  intro hU M U hn f ρ K C I S A hAS hA X hXN hqs hXC hXB hr
  let := hXN
  let := hqs
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : K.Normal := Normal.map inferInstance f
    (UniqueFactor.actionHom M U hn).rangeRestrict_surjective
  obtain ⟨_,_,_,_,_,hR,_,_,_,_,_,_,_,_,F₁,ho₁,⟨a⟩⟩ :=
    D.normalizer_normal_support_natural_seed h hmany hc hm hne
      A hAS hA X hXN hqs hXC hXB hr
  have hz : center X = ⊥ := by
    have hSL : center (Matrix.SpecialLinearGroup (Fin 3) F₁.Carrier) = ⊥ := by
      apply (Matrix.SL3.center_eq_bot_iff_card_mod_three F₁.Carrier).mpr
      rw [F₁.card_eq,Nat.BinaryTorusParity.two_pow_mod_three,Nat.odd_iff.mp ho₁]
      decide
    apply bot_unique
    intro x hx
    exact a.groupEquiv.injective
      ((hSL.le ((centerCongr a.groupEquiv) ⟨x,hx⟩).property).trans a.groupEquiv.map_one.symm)
  have hX : IsComponent (internalActionImage M U hn) X := ⟨hXN.isSubnormal,hqs⟩
  have hXorbit : X = componentOrbit X A := le_antisymm (le_componentOrbit X A)
    (iSup_conjugates_le_of_le_normalizer X A X le_rfl (by rw [normalizer_eq_top]; exact le_top))
  have hXne : X ≠ ⊥ := by
    intro hz
    apply hR.isIrrPlus.not_le_fixedSpace ρ
    intro v _ x
    change ρ x.val v = v
    rw [show x.val = 1 from hz.le x.property,map_one,Module.End.one_apply]
  obtain ⟨_,_,_,_,_,_,hXI,_,_,_,_,_,hfaith⟩ :=
    D.normalizer_normal_support_on_isotypic_pair h hmany hc hm hne A hAS hA
      X X hXN hXC hXne hX hXorbit
  let R := internalImageSubrepresentation hn D.normalizes
  have hi : IsIrreducible R.toRepresentation := internalImageSubrepresentation_irreducible
    hn D.normalizes (internalSubrepresentation_irreducible hn L.le_normalizer
      (le_componentOrbit V M) D.normalizes D.ne_bot (D.seed_invariant_subgroup_eq hc))
  have htype := typePart_comp_surjective (ρ.comp K.subtype)
    (f.subgroupMap (L.subgroupOf M)) (f.subgroupMap_surjective (L.subgroupOf M)) R
  change I = (typePart R).toSubmodule at htype
  obtain ⟨_,_,_,_,hstrict,_,_,_⟩ :=
    D.normalizer_starred_isotypic_pair_of_moved_of_many h hmany hc hm hne
  have hp : R < typePart R := lt_of_le_of_ne (le_typePart R) (by
    intro he
    exact hstrict.ne ((congrArg Subrepresentation.toSubmodule he).trans htype.symm))
  have hτ : Function.Injective (invariantSubspace ρ X I hXI).toRepresentation := by
    intro x y he
    apply (hfaith hz).1
    apply subspaceImageRepresentation_injective ρ I
    exact he
  have hXI' : X ≤ subspaceStabilizer ρ (typePart R).toSubmodule := htype ▸ hXI
  have hτ' : Function.Injective
      (invariantSubspace ρ X (typePart R).toSubmodule hXI').toRepresentation := by
    have transport (P Q : Submodule (ZMod 2) (Additive U))
        (hP : X ≤ subspaceStabilizer ρ P) (hQ : X ≤ subspaceStabilizer ρ Q) (he : P = Q) :
        Function.Injective (invariantSubspace ρ X P hP).toRepresentation →
          Function.Injective (invariantSubspace ρ X Q hQ).toRepresentation := by
      subst Q
      exact id
    exact transport I _ hXI hXI' htype hτ
  have hd := typePart_triple_degree_of_commuting_linearThree ρ K X R hi hp hXI'
    hτ' hXC F₁ a.groupEquiv
  rw [←htype] at hd
  exact hd


/-- The complementary D.3.10 displacement bound on the original normalizer
orbit. The three-copy premise is discharged using the actual normal support. -/
theorem normalizer_normal_support_nine_degree_displacement
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G))
    (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3)) :
    let := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let f := internalHom M U hn
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map f
    let C := centralizer (K : Set (internalActionImage M U hn))
    let S := (internalSylow T M U hn D.sylow_normalizes_component : Subgroup (internalActionImage M U hn))
    ∀ A : Subgroup (internalActionImage M U hn), A ≤ S → A ∈ QhatStar ρ →
      ∀ X : Subgroup (internalActionImage M U hn),
        X.Normal → IsQuasisimple X → X ≤ C → ⁅X,A ⊓ C⁆ = X → primeRank 3 X = 1 →
        9 * F.degree ≤ fixedCodim ρ A ∧ 9 * F.degree ≤ 2 * rank A := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  intro hU M U hn f ρ K C S A hAS hA X hXN hqs hXC hXB hr
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : K.Normal := Normal.map inferInstance f
    (UniqueFactor.actionHom M U hn).rangeRestrict_surjective
  let R := internalImageSubrepresentation hn D.normalizes
  let I := (typePart (internalSubrepresentation hn D.normalizes)).toSubmodule
  let W := internalSection U (componentOrbit V (T : Subgroup G))
  have hi : IsIrreducible R.toRepresentation := internalImageSubrepresentation_irreducible
    hn D.normalizes (internalSubrepresentation_irreducible hn L.le_normalizer
      (le_componentOrbit V M) D.normalizes D.ne_bot (D.seed_invariant_subgroup_eq hc))
  have htype := typePart_comp_surjective (ρ.comp K.subtype)
    (f.subgroupMap (L.subgroupOf M)) (f.subgroupMap_surjective (L.subgroupOf M)) R
  change I = (typePart R).toSubmodule at htype
  obtain ⟨t,ht,hnt,hcompl,_,hdim,hperm,_⟩ :=
    D.normalizer_starred_isotypic_pair_of_moved_of_many h hmany hc hm hne
  change IsCompl I (I.map (ρ (f t))) at hcompl
  let Q := conjugateSubrepresentationOrderIso ρ K (f t) R
  have hj : IsIrreducible Q.toRepresentation :=
    (normalTypeAction ρ K).conjugate_irreducible R hi (f t)
  have hQtype : (typePart Q).toSubmodule = I.map (ρ (f t)) := by
    change (typePart ((normalTypeAction ρ K).conjugate (f t) R)).toSubmodule = _
    rw [←conjugate_typePart (normalTypeAction ρ K) R (f t)]
    change (conjugateSubrepresentationOrderIso ρ K (f t) (typePart R)).toSubmodule = _
    rw [conjugateSubrepresentationOrderIso_toSubmodule,←htype]
  have hcomp : IsCompl (typePart R).toSubmodule (typePart Q).toSubmodule := by
    rw [←htype,hQtype]
    exact hcompl
  have hAR : A ≤ subspaceStabilizer ρ (typePart R).toSubmodule := by
    rw [←htype]
    exact D.normalizer_starred_stabilizes_isotypic_of_moved_of_many h hmany hc hm hne A hAS hA
  have hneq : I ≠ I.map (ρ (f t)) := by
    intro he
    have hz : I = ⊥ := disjoint_self.mp (by simpa only [←he] using hcompl.disjoint)
    change 2 < Module.finrank (ZMod 2) I at hdim
    rw [hz,finrank_bot] at hdim
    omega
  have hAQ : A ≤ subspaceStabilizer ρ (typePart Q).toSubmodule := by
    rw [hQtype]
    intro a ha
    apply (subspace_map_eq_iff ρ (I.map (ρ (f t))) a).mp
    apply pair_second_stabilized ρ I (f t) a hneq hperm
    apply (subspace_map_eq_iff ρ I a).mpr
    rw [htype]
    exact hAR ha
  have hd := D.normalizer_normal_support_original_multiplicity h hmany hc hm hne
    A hAS hA X hXN hqs hXC hXB hr
  change 3 * Module.finrank (ZMod 2) R.toSubmodule ≤ Module.finrank (ZMod 2) I at hd
  let := hi
  let : Nontrivial R.toSubmodule := Subrepresentation.irreducible_module_nontrivial R.toRepresentation
  have hpos : 0 < Module.finrank (ZMod 2) R.toSubmodule := Module.finrank_pos
  have hdR : 2 * Module.finrank (ZMod 2) R.toSubmodule <
      Module.finrank (ZMod 2) (typePart R).toSubmodule := by rw [←htype]; omega
  have hdQ : 2 * Module.finrank (ZMod 2) Q.toSubmodule <
      Module.finrank (ZMod 2) (typePart Q).toSubmodule := by
    rw [hQtype,conjugateSubrepresentationOrderIso_toSubmodule,finrank_map_action,finrank_map_action]
    change 2 * Module.finrank (ZMod 2) R.toSubmodule < Module.finrank (ZMod 2) I
    omega
  obtain ⟨_,_,⟨φ,_,_,hφ,hφW⟩,_,_⟩ :=
    D.normalizer_starred_inner_and_rank_of_odd_linearThree h hmany hc hm hne F ho e A hAS hA
  have hbound := isotypic_pair_triple_cost ρ K A R Q hi hj hAR hAQ hcomp hA.1.2.1.2 φ hφ hdR hdQ
  have hVU : V ≤ U := le_componentOrbit V M
  have hpair := D.sylowOrbit_eq_sup_of_two_module_types t ht (fun s hs =>
    D.normalizer_two_types_of_moved_of_many h hmany hc hm t ht hnt s (D.sylow_normalizes_component hs))
  let Vt := V.map (MulAut.conj t.val).toMonoidHom
  have hVtW : Vt ≤ componentOrbit V (T : Subgroup G) := by rw [hpair]; exact le_sup_right
  have hWU : componentOrbit V (T : Subgroup G) ≤ U :=
    iSup_conjugates_le_of_le_normalizer V T U hVU (D.sylow_normalizes_component.trans hn)
  have hQ : Q.toSubmodule = internalSection U Vt := by
    rw [conjugateSubrepresentationOrderIso_toSubmodule]
    exact internalSection_map_action hn hVU t
  have hspan : R.toSubmodule ⊔ Q.toSubmodule = W := by
    rw [hQ]
    change internalSection U V ⊔ internalSection U Vt =
      internalSection U (componentOrbit V (T : Subgroup G))
    rw [hpair,internalSection_sup U V Vt hVU (hVtW.trans hWU)]
  have hdis : Disjoint R.toSubmodule Q.toSubmodule :=
    hcomp.disjoint.mono (le_typePart R) (le_typePart Q)
  have hAW : A ≤ subspaceStabilizer ρ W := hAS.trans
    (internalSylow_section_stable T M U (componentOrbit V (T : Subgroup G)) hn
      D.sylow_normalizes_component (le_normalizer_componentOrbit V T))
  rw [spanning_inner_pair_cost ρ K A R Q W hspan hdis hAW φ hφW] at hbound
  obtain ⟨_,_,hcost,_⟩ := D.normalizer_normal_support_movement_and_cost h hmany hc hm hne
    F ho e A hAS hA X hXN hqs hXC hXB hr
  change fixedCodim (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) = 3 * F.degree at hcost
  rw [hcost] at hbound
  have hupper := (actionRatio_le_nat_iff ρ hA.1.2.1 2).mp (hA.1.2.2.2.le.trans hA.1.1)
  constructor <;> omega

/-- The two complementary displacement bounds exclude the normal natural
support branch. Every original starred actor must exchange a genuine Suzuki pair. -/
theorem normalizer_starred_support_suzuki_pair_of_odd_linearThree
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G))
    (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3)) :
    let := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let f := internalHom M U hn
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map f
    let C := centralizer (K : Set (internalActionImage M U hn))
    let S := (internalSylow T M U hn D.sylow_normalizes_component : Subgroup (internalActionImage M U hn))
    ∀ A : Subgroup (internalActionImage M U hn), A ≤ S → A ∈ QhatStar ρ →
      ∃ J : Subgroup (internalActionImage M U hn),
        IsComponent (internalActionImage M U hn) J ∧ J ≤ C ∧
        ∃ r : ℕ, 0 < r ∧ Nonempty (J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) ∧
          ∃ a ∈ A, a ∉ normalizer (J : Set (internalActionImage M U hn)) ∧
            (normalizer (J : Set (internalActionImage M U hn))).index = 2 ∧
            componentOrbit J A = J ⊔ J.map (MulAut.conj a).toMonoidHom := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  intro hU M U hn f ρ K C S A hAS hA
  rcases D.normalizer_support_rank_degree_or_suzuki h hmany hc hm hne F ho e A hAS hA with
      hpair | ⟨X,hXN,hqs,hXC,hXB,hr,_,_,F₁,_,_,_,_,_,hrank,hdeg⟩
  · exact hpair
  · have h9 := (D.normalizer_normal_support_nine_degree_displacement
      h hmany hc hm hne F ho e A hAS hA X hXN hqs hXC hXB hr).2
    have hpos := F.degree_pos
    omega

/-- On the original enlargement, the remaining alternatives are a genuine
exchanged Suzuki pair or offending on the literal local section or its quotient.
The original natural marking is retained in the Suzuki branch. -/
theorem exists_normalizer_suzuki_pair_or_section_offender_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map (internalHom M U hn)
    let C := centralizer (K : Set (internalActionImage M U hn))
    let S := D.normalizerLocalSection h.toHypothesis1221
    ∃ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component ∧ A ∈ QhatStar ρ ∧
      ((∃ F : BinaryField, Odd F.degree ∧
          Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
            (linearNatural F 3)) ∧
          ∃ J : Subgroup (internalActionImage M U hn),
            IsComponent (internalActionImage M U hn) J ∧ J ≤ C ∧
            ∃ r : ℕ, 0 < r ∧ Nonempty (J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) ∧
              ∃ a ∈ A, a ∉ normalizer (J : Set (internalActionImage M U hn)) ∧
                (normalizer (J : Set (internalActionImage M U hn))).index = 2 ∧
                componentOrbit J A = J ⊔ J.map (MulAut.conj a).toMonoidHom) ∨
        (IsOffender (imageRepresentation S.toRepresentation)
          (actionSubgroup S.toRepresentation (A.subgroupOf D.normalizerLocalActor)) ∨
        IsOffender (imageRepresentation S.quotientRepresentation)
          (actionSubgroup S.quotientRepresentation (A.subgroupOf D.normalizerLocalActor)))) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  intro M U hn ρ K C S
  refine (D.exists_normalizer_odd_linearThree_or_section_offender_of_many
    h hmany hc hm hne).imp ?_
  rintro A ⟨hAS,hA,hcase⟩
  refine ⟨hAS,hA,?_⟩
  rcases hcase with ⟨F,ho,⟨e⟩⟩ | hff
  · exact Or.inl ⟨F,ho,⟨e⟩,
      D.normalizer_starred_support_suzuki_pair_of_odd_linearThree h hmany hc hm hne F ho e A hAS hA⟩
  · exact Or.inr hff

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
