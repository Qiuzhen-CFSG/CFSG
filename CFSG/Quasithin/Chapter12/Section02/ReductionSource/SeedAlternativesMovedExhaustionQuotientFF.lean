module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionLinearThreeFF
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionInnerSections

/-!
# Quotient FF exclusion for the actual odd-degree SL₃ seed

An escaping normalizer conjugate of the seed is disjoint from the whole
local orbit W. Its conjugate by the original moving Sylow element is
also disjoint from W, and has the other component-module type. These
two natural SL₃ copies therefore survive in the literal quotient U/W.

The original starred actor has a Sylow-preserving inner lift. If its
component centralizer is trivial, that lift is injective. The invariant
copy selection and binary Schur argument in MovedExhaustionInnerSections
then exclude its literal quotient offender. Together with the existing
W exclusion this proves D.3.13 in the odd-degree SL₃ branch. Applying
the already proved order-three and rank exclusions to the same actor
leaves actual Suzuki-or-normal-rank-one component support.

No extra source premise is introduced. The remaining component-support
exclusions, other constituent rows, U = W and Source325 assembly remain
with qt-baumann-fsu. Source: Aschbacher--Smith D.3.9(1), D.3.13--15 and
B.4.9(2), printed pp.92--94 and199--202.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource ChapterD
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The escaping seed and its Sylow conjugate give two distinct natural
component types, both disjoint from the whole original Sylow orbit. -/
private theorem normalizer_disjoint_natural_type_pair_of_linearThree_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G))
    (F : BinaryField)
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let K := (L.subgroupOf M).map (internalHom M U hn)
    let ρ := UniqueFactor.imageRepresentation M U hn
    ∃ I J : Subrepresentation (ρ.comp K.subtype),
      IsIrreducible I.toRepresentation ∧ IsIrreducible J.toRepresentation ∧
      Disjoint I.toSubmodule (internalSection U (componentOrbit V (T : Subgroup G))) ∧
      Disjoint J.toSubmodule (internalSection U (componentOrbit V (T : Subgroup G))) ∧
      Nonempty (ActionEquiv I.toRepresentation (linearNatural F 3)) ∧
      Nonempty (ActionEquiv J.toRepresentation (linearNatural F 3)) ∧ ¬ SameModule I J := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let := D.elementary
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let W := componentOrbit V (T : Subgroup G)
  let hn := le_normalizer_componentOrbit V M
  let ρ := UniqueFactor.imageRepresentation M U hn
  let j := internalHom M U hn
  let K := (L.subgroupOf M).map j
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : K.Normal := Normal.map inferInstance j
    (UniqueFactor.actionHom M U hn).rangeRestrict_surjective
  let I₀ : Subrepresentation (ρ.comp K.subtype) := internalImageSubrepresentation hn D.normalizes
  have hi₀ : IsIrreducible I₀.toRepresentation := internalImageSubrepresentation_irreducible
    hn D.normalizes (internalSubrepresentation_irreducible hn L.le_normalizer
      (le_componentOrbit V M) D.normalizes D.ne_bot (D.seed_invariant_subgroup_eq hc))
  obtain ⟨a₀,_⟩ := D.normalizer_component_actionEquiv_of_constituentModel h.toHypothesis1221
    (Or.inl ⟨F,⟨e⟩⟩)
  let a : ActionEquiv I₀.toRepresentation (linearNatural F 3) :=
    ⟨a₀.groupEquiv.trans e.groupEquiv,a₀.linearEquiv.trans e.linearEquiv,by
      intro k v
      exact (congrArg e.linearEquiv (a₀.intertwines k v)).trans
        (e.intertwines (a₀.groupEquiv k) (a₀.linearEquiv v))⟩
  obtain ⟨t,ht,hnt,_,_,hntype,_⟩ := D.normalizer_type_pair_of_moved_of_many h hmany hc hm
  obtain ⟨g,hg,hgtype,hgdis,_⟩ := D.exists_repeated_disjoint_conjugate_of_normalizerOrbit_ne
    h hmany hc hm hne
  let t' : M := ⟨t,D.sylow_normalizes_component ht⟩
  let g' : M := ⟨g,hg⟩
  let c := normalTypeAction ρ K
  let I := c.conjugate (j g') I₀
  let J := c.conjugate (j t') I
  have hVU : V ≤ U := le_componentOrbit V M
  have hconj (x : M) : c.conjugate (j x) I₀ =
      internalImageSubrepresentation hn (normalizes_conjugate D.normalizes x) := by
    apply Subrepresentation.toSubmodule_injective
    change (conjugateSubrepresentationOrderIso ρ K (j x) I₀).toSubmodule = _
    rw [conjugateSubrepresentationOrderIso_toSubmodule]
    exact internalSection_map_action hn hVU x
  have hle (x : M) : V.map (MulAut.conj x.val).toMonoidHom ≤ U :=
    le_iSup (fun y : M => V.map (MulAut.conj y.val).toMonoidHom) x
  have hsame (x : M) : SameModule I₀ (c.conjugate (j x) I₀) ↔
      SameConjugationModule L V (V.map (MulAut.conj x.val).toMonoidHom) := by
    let : IsElementaryAbelian 2 (V.map (MulAut.conj x.val).toMonoidHom) :=
      IsElementaryAbelian.of_le (hle x)
    rw [hconj]
    constructor
    · rintro ⟨d,hd⟩
      apply sameConjugationModule_of_internal hn L.le_normalizer hVU (hle x)
        D.normalizes (normalizes_conjugate D.normalizes x)
      exact ⟨d,fun l v => hd (j.subgroupMap (L.subgroupOf M) l) v⟩
    · intro hs
      obtain ⟨d,hd⟩ := same_internalSubrepresentation hn hVU (hle x)
        D.normalizes (normalizes_conjugate D.normalizes x) hs
      refine ⟨d,?_⟩
      intro k v
      obtain ⟨l,rfl⟩ := j.subgroupMap_surjective (L.subgroupOf M) k
      exact hd l v
  have hItype : SameModule I₀ I := (hsame g').mpr hgtype
  have hnot : ¬ SameModule I J := by
    intro hs
    exact hntype ((hsame t').mp
      (hItype.trans (hs.trans ((c.same (j t') I₀ I).mp hItype).symm)))
  have hi : IsIrreducible I.toRepresentation := c.conjugate_irreducible I₀ hi₀ (j g')
  have hj : IsIrreducible J.toRepresentation := c.conjugate_irreducible I hi (j t')
  have hIdis : Disjoint I.toSubmodule (internalSection U W) := by
    apply Submodule.disjoint_def.mpr
    intro v hv hw
    change v ∈ I.toSubmodule at hv
    have hh : I.toSubmodule = internalSection U (V.map (MulAut.conj g).toMonoidHom) :=
      congrArg Subrepresentation.toSubmodule (hconj g')
    rw [hh] at hv
    exact Additive.toMul.injective (Subtype.ext (hgdis.le ⟨hv,hw⟩))
  have hT := internalSylow_section_stable T M U W hn
    D.sylow_normalizes_component (le_normalizer_componentOrbit V T)
  have htS : j t' ∈ internalSylow T M U hn D.sylow_normalizes_component := by
    exact ⟨t',ht,rfl⟩
  have hJdis : Disjoint J.toSubmodule (internalSection U W) := by
    apply Submodule.disjoint_def.mpr
    intro v hv hw
    change v ∈ (conjugateSubrepresentationOrderIso ρ K (j t') I).toSubmodule at hv
    rw [conjugateSubrepresentationOrderIso_toSubmodule] at hv
    obtain ⟨w,hwI,rfl⟩ := hv
    have hwW : w ∈ internalSection U W := (hT htS w).mp hw
    have hz := (Submodule.disjoint_def.mp hIdis) w hwI hwW
    rw [hz,map_zero]
  let ai := conjugate_linearThree_action ρ K I₀ F a (j g')
  let aj := conjugate_linearThree_action ρ K I F ai (j t')
  exact ⟨I,J,hi,hj,hIdis,hJdis,⟨ai⟩,⟨aj⟩,hnot⟩

/-- In the odd-degree SL₃ branch, a component-faithful starred actor
cannot offend on the literal quotient U/W. Both quotient types are
constructed from the escaping seed and its original Sylow conjugate. -/
theorem normalizer_starred_quotient_not_offender_of_odd_linearThree
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G))
    (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map (internalHom M U hn)
    let S : Subrepresentation (ρ.comp D.normalizerLocalActor.subtype) := D.normalizerLocalSection h.toHypothesis1221
    ∀ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component → A ∈ QhatStar ρ →
      A ⊓ centralizer (K : Set (internalActionImage M U hn)) = ⊥ →
      ¬ IsOffender (imageRepresentation S.quotientRepresentation)
        (actionSubgroup S.quotientRepresentation (A.subgroupOf D.normalizerLocalActor)) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let ρ := UniqueFactor.imageRepresentation M U hn
  let j := internalHom M U hn
  let K := (L.subgroupOf M).map j
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : K.Normal := Normal.map inferInstance j
    (UniqueFactor.actionHom M U hn).rangeRestrict_surjective
  let P : Subgroup (internalActionImage M U hn) := D.normalizerLocalActor
  let S : Subrepresentation (ρ.comp P.subtype) := D.normalizerLocalSection h.toHypothesis1221
  have hKP : K ≤ P := by
    change K ≤ D.normalizerLocalActor
    rw [D.normalizerLocalActor_eq_component_sup_sylow]
    exact le_sup_left
  let Kp := K.subgroupOf P
  let ek : Kp ≃* K := subgroupOfEquivOfLe hKP
  dsimp only
  intro A hAS hA hAC hoff
  obtain ⟨_,_,⟨f,hfk,_,he,_⟩,_,_⟩ :=
    D.normalizer_starred_inner_and_rank_of_odd_linearThree h hmany hc hm hne F ho e A hAS hA
  have hfi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    rw [hfk]
    apply bot_unique
    intro a ha
    exact Subtype.ext (hAC.le ⟨a.property,ha⟩)
  have hAP : A ≤ P := by
    change A ≤ D.normalizerLocalActor
    rw [D.normalizerLocalActor_eq_component_sup_sylow]
    exact hAS.trans le_sup_right
  let B := A.subgroupOf P
  let ea : B ≃* A := subgroupOfEquivOfLe hAP
  let fp : B →* Kp := ek.symm.toMonoidHom.comp (f.comp ea.toMonoidHom)
  have hfpi : Function.Injective fp := ek.symm.injective.comp (hfi.comp ea.injective)
  have hfp (a : B) (k : Kp) : a.val*k.val*a.val⁻¹ =
      (fp a : P)*k.val*(fp a : P)⁻¹ := by
    apply Subtype.ext
    exact he (ea a) (ek k)
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hB : IsElementaryTwo B := by
    refine ⟨?_,IsElementaryAbelian.subgroupOf hAP⟩
    intro hz
    apply hA.1.2.1.1
    change A.subgroupOf P = ⊥ at hz
    rw [←map_subgroupOf_eq_of_le hAP,hz,Subgroup.map_bot]
  have hfaith := (D.normalizer_sections_of_faithful_component_actor h.toHypothesis1221 hc hne
    A hAS hA.1.2.1
    ((actionRatio_le_nat_iff ρ hA.1.2.1 2).mp (hA.1.2.2.2.le.trans hA.1.1)) hAC).2.1
  have hb : IsOffender S.quotientRepresentation B := by
    refine ⟨hB,?_⟩
    have hh := hoff.2
    rw [fixedCodim_actionSubgroup,actionSubgroup_rank S.quotientRepresentation B hfaith] at hh
    exact hh
  obtain ⟨I,J,hi,hj,hIdis,hJdis,⟨ai⟩,⟨aj⟩,hnot⟩ :=
    D.normalizer_disjoint_natural_type_pair_of_linearThree_of_many h hmany hc hm hne F e
  let I' : Subrepresentation ((ρ.comp P.subtype).comp Kp.subtype) := I.compActors ek.toMonoidHom
  let J' : Subrepresentation ((ρ.comp P.subtype).comp Kp.subtype) := J.compActors ek.toMonoidHom
  have hi' : IsIrreducible I'.toRepresentation :=
    (irreducible_comp_surjective_iff ek.toMonoidHom ek.surjective I.toRepresentation).mpr hi
  have hj' : IsIrreducible J'.toRepresentation :=
    (irreducible_comp_surjective_iff ek.toMonoidHom ek.surjective J.toRepresentation).mpr hj
  let ai' : ActionEquiv I'.toRepresentation (linearNatural F 3) :=
    ⟨ek.trans ai.groupEquiv,ai.linearEquiv,fun k v => ai.intertwines (ek k) v⟩
  let aj' : ActionEquiv J'.toRepresentation (linearNatural F 3) :=
    ⟨ek.trans aj.groupEquiv,aj.linearEquiv,fun k v => aj.intertwines (ek k) v⟩
  have hnot' : ¬ SameModule I' J' := by
    rintro ⟨d,hd⟩
    apply hnot
    refine ⟨d,?_⟩
    intro k v
    obtain ⟨k,rfl⟩ := ek.surjective k
    exact hd k v
  exact not_offender_quotient_of_inner_two_natural_types (ρ.comp P.subtype) Kp B hB fp hfpi hfp
    S I' J' hi' hj' hIdis hJdis F ai' aj' hnot' hb

/-- D.3.13 for the actual odd-degree SL₃ branch: every original starred
actor has a nontrivial component centralizer. Both literal FF-section
alternatives have been discharged. -/
theorem normalizer_starred_centralizer_ne_bot_of_odd_linearThree
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G))
    (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map (internalHom M U hn)
    ∀ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component → A ∈ QhatStar ρ →
      A ⊓ centralizer (K : Set (internalActionImage M U hn)) ≠ ⊥ := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let ρ := UniqueFactor.imageRepresentation M U hn
  dsimp only
  intro A hAS hA hAC
  have hsections := (D.normalizer_sections_of_faithful_component_actor h.toHypothesis1221 hc hne
    A hAS hA.1.2.1
    ((actionRatio_le_nat_iff ρ hA.1.2.1 2).mp (hA.1.2.2.2.le.trans hA.1.1)) hAC).2.2.2.2
  exact D.normalizer_starred_quotient_not_offender_of_odd_linearThree h hmany hc hm hne F ho e A hAS hA hAC
    (hsections.resolve_left
      (D.normalizer_starred_local_not_offender_of_odd_linearThree h hmany hc hm hne F ho e A hAS hA hAC))


/-- In the odd-degree SL₃ branch every original starred actor has genuine
component support in the component centralizer. The order-three exclusion
and component-rank results apply to this same actor; no FF-section
alternative or new source premise remains in this branch. -/
theorem normalizer_starred_component_support_of_odd_linearThree
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G))
    (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map (internalHom M U hn)
    let C := centralizer (K : Set (internalActionImage M U hn))
    ∀ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component → A ∈ QhatStar ρ →
      ∃ X J : Subgroup (internalActionImage M U hn),
        X ≤ C ∧ A ≤ normalizer (X : Set _) ∧ X ≠ ⊥ ∧ ⁅X,A ⊓ C⁆ = X ∧
        IsComponent (internalActionImage M U hn) J ∧ J ≤ C ∧ X = componentOrbit J A ∧
        ((¬ 3 ∣ Nat.card J ∧
            (∃ r : ℕ, 0 < r ∧ Nonempty
              (J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r)) ∧
            ¬ A ≤ normalizer (J : Set _)) ∨
          (X = J ∧ J.Normal ∧ primeRank 3 J = 1 ∧ pCore 3 C = ⊥)) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let ρ := UniqueFactor.imageRepresentation M U hn
  let f := internalHom M U hn
  let K := (L.subgroupOf M).map f
  let C := centralizer (K : Set (internalActionImage M U hn))
  let I := (typePart (internalSubrepresentation hn D.normalizes)).toSubmodule
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : K.Normal := Normal.map inferInstance f
    (UniqueFactor.actionHom M U hn).rangeRestrict_surjective
  dsimp only
  intro A hAS hA
  have hAC := D.normalizer_starred_centralizer_ne_bot_of_odd_linearThree
    h hmany hc hm hne F ho e A hAS hA
  obtain ⟨X,hXC,hAX,hXn,hXB,hcase⟩ :=
    D.normalizer_starred_centralizer_three_or_component h.toHypothesis1221 hc A hAS hA hAC
  have hcomp : ∃ J : Subgroup (internalActionImage M U hn),
      IsComponent (internalActionImage M U hn) J ∧ J ≤ C ∧ X = componentOrbit J A := by
    rcases hcase with ⟨hXP,hXcard,hKr,hpos,_,_⟩ | hcomp
    · have hCr := D.normalizer_component_centralizer_three_rank_le_one_of_many h hmany hc hm hKr
      let : X.Normal := normal_of_le_three_core_centralizer_rank_one K hCr X hXP
      let := D.normalizer_component_quasisimple h.toHypothesis1221 hc
      have hXcore : X ≤ pCore 3 (internalActionImage M U hn) := hXP.trans
        (le_sSup ⟨inferInstance,pCore_isPGroup.map C.subtype⟩)
      have hXA : ⁅X,A⁆ = X := le_antisymm
        (le_normalizer_iff_commutator_le_left.mp hAX)
        (hXB.symm.le.trans (commutator_mono le_rfl inf_le_left))
      have hrne : rank A ≠ 1 := fun hr => (ne_of_gt hpos)
        (rank_one_starred_component_centralizer_eq_bot ρ
          (UniqueFactor.imageRepresentation_injective M U hn) K
          (D.normalizer_component_fully_moved h.toHypothesis1221 hc) hA hr)
      have hr : 1 < rank A := by have := hA.1.2.1.rank_pos; omega
      obtain ⟨t,_,_,hcompl,_,hdim,hperm,_⟩ :=
        D.normalizer_starred_isotypic_pair_of_moved_of_many h hmany hc hm hne
      have hneq : I ≠ I.map (ρ (f t)) := by
        intro he
        have hd : Disjoint I (I.map (ρ (f t))) := hcompl.disjoint
        rw [←he] at hd
        have hz : I = ⊥ := disjoint_self.mp hd
        change 2 < Module.finrank (ZMod 2) I at hdim
        rw [hz,finrank_bot] at hdim
        omega
      exact (no_normal_three_support_on_stable_pair ρ
        (UniqueFactor.imageRepresentation_injective M U hn) hA hr X hXcard hXcore hXA
        I (f t) hcompl hneq hperm
        (D.normalizer_starred_stabilizes_isotypic_of_moved_of_many h hmany hc hm hne A hAS hA)).elim
    · exact hcomp
  obtain ⟨J,hJ,hJC,hX⟩ := hcomp
  refine ⟨X,J,hXC,hAX,hXn,hXB,hJ,hJC,hX,?_⟩
  by_cases hd : 3 ∣ Nat.card J
  · obtain ⟨hn,horbit,hr,hcore⟩ :=
      D.normalizer_centralizer_component_structure_of_many h hmany hc hm J A hJ hJC hd
    exact Or.inr ⟨hX.trans horbit,hn,hr,hcore⟩
  · exact Or.inl ⟨hd,D.normalizer_action_component_suzuki_of_three_free h J hJ hd,
      D.normalizer_starred_moved_three_free_component_not_normalized h hc J A hJ hJC hd hA
        (by simpa only [←hX] using hXB)⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
