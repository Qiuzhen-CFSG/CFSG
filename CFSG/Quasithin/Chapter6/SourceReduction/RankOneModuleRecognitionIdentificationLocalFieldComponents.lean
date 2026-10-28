module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFieldCubicAction
public import Theory.GroupTheory.CComponent.RankTwoResidual
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ThreeRank

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.SmallMoved.Catalogue
public import Theory.SpecificGroups.BinaryLinear.OuterTwo
public import Theory.SpecificGroups.BinaryLinear.SmallCubicRank
public import Theory.SpecificGroups.Alternating.SevenComponent
public import Theory.SpecificGroups.Alternating.EightComponent
public import Theory.SpecificGroups.AlternatingSix.OuterSolvable
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.TwoSylowSource
public import Theory.SpecificGroups.SymplecticFour.SplitTorusRank
public import Theory.SpecificGroups.PSL2.OuterSolvable.Models

/-!
# Component restrictions in the original field-plane centralizer

The full normalizer of a nontrivial field plane is SQTK. Its centralizer
is normal, so each actual C-component of the centralizer embeds as a
C-component of that normalizer. The previously constructed cubic lies
outside the centralizer. The proved centerless case of A.3.18 therefore
forces cubic rank at most one whenever the intrinsic two-core quotient
has a two-group outer automorphism group.

Applied to the small-moved B.5 actor list, the actual binary linear,
alternating, and symplectic models leave only A5, PSL3(2), and SL3(4).
All models are isomorphisms of the intrinsic component quotient. The
quotient-action component lift and the final cubic-action exclusions
remain separate obligations; this does not assert the full 6.2.4(6).
The companion Chapter12 module applies the restrictions to its original
whole reduced commutator layer.

Source: Aschbacher--Smith, 6.2.4(6) and 6.2.7, printed pp.680,683,
using the centerless outer-two case of A.3.18, printed pp.51--52.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R U : Subgroup G} {n : ℕ}

/-- The actual fixed-plane normalizer is an SQTK group. -/
theorem local_field_normalizer_sqtk
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hfield : IsInvolutoryFieldFixedSpace L M (layer L R) U n)
    (hUne : U ≠ ⊥) : IsSQTK KnownSimple.IsKnownSimple (normalizer (U : Set G)) := by
  let := h.layer_elementary
  have hUB : U ≤ layer L R := hfield.choose_spec.2.2.1.le.trans inf_le_left
  exact h.simpleQTKE.twoLocal_sqtk ⟨U,hUne,
    (IsElementaryAbelian.isPGroup 2 (layer L R)).to_le hUB,rfl⟩

/-- The actual cubic is outside the centralizer of the fixed plane. -/
theorem field_plane_cubic_outside_centralizer
    (hnat : IsNaturalModule L (layer L R) n)
    (hfield : IsInvolutoryFieldFixedSpace L M (layer L R) U n)
    (hUc : Nat.card U = 4) :
    ∃ d ∈ fieldLocalResidual L U, orderOf d = 3 ∧
      d ∈ normalizer (U : Set G) ∧ d ∉ centralizer (U : Set G) := by
  obtain ⟨d,hd,ho,hfix⟩ := exists_field_plane_cubic hnat hfield hUc
  refine ⟨d,hd,ho,(map_subtype_le _ hd).2,?_⟩
  intro hc
  have hUB : U ≤ layer L R := hfield.choose_spec.2.2.1.le.trans inf_le_left
  have hzero : U = ⊥ := by
    apply le_bot_iff.mp
    intro u hu
    apply hfix.le
    exact ⟨hUB hu,mem_centralizer_singleton_iff.mpr (hc u hu)⟩
  rw [hzero,card_bot] at hUc
  contradiction

omit [Finite G] in
private theorem component_in_normalizer
    {U : Subgroup G} (K : Subgroup (centralizer (U : Set G))) (hK : K.IsCComponent) :
    (K.map (inclusion (Subgroup.centralizer_le_normalizer (U : Set G)))).IsCComponent := by
  let H := centralizer (U : Set G)
  let N := normalizer (U : Set G)
  let H0 := H.subgroupOf N
  have hHN : H ≤ N := Subgroup.centralizer_le_normalizer _
  let : H0.Normal := normal_subgroupOf_of_le_normalizer (normalizer_le_normalizer_centralizer U)
  let e : H ≃* H0 := (subgroupOfEquivOfLe hHN).symm
  have hm := (hK.map_equiv e).map_subtype (inferInstance : H0.Normal).isSubnormal
  rw [map_map] at hm
  exact hm

/-- A centerless two-core quotient with outer automorphism group a two-group
has cubic rank at most one, on every actual C-component of the field centralizer. -/
theorem local_field_component_three_rank_le_one
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hfield : IsInvolutoryFieldFixedSpace L M (layer L R) U n)
    (hUc : Nat.card U = 4)
    (K : Subgroup (centralizer (U : Set G))) (hK : K.IsCComponent)
    (hz : center (K ⧸ pCore 2 K) = ⊥)
    (hout : IsPGroup 2 (MulAut.Outer (K ⧸ pCore 2 K))) :
    primeRank 3 (K ⧸ pCore 2 K) ≤ 1 := by
  let H := centralizer (U : Set G)
  let N := normalizer (U : Set G)
  let j : H →* N := inclusion (Subgroup.centralizer_le_normalizer (U : Set G))
  let K0 := K.map j
  let e : K ≃* K0 := K.equivMapOfInjective j (inclusion_injective _)
  let eq : (K ⧸ pCore 2 K) ≃* (K0 ⧸ pCore 2 K0) :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  have hK0 : K0.IsCComponent := component_in_normalizer K hK
  have hz0 : center (K0 ⧸ pCore 2 K0) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have he : eq.symm x = 1 := hz.le ((centerCongr eq).symm ⟨x,hx⟩).property
    exact eq.symm.map_eq_one_iff.mp he
  have ho0 : IsPGroup 2 (MulAut.Outer (K0 ⧸ pCore 2 K0)) :=
    hout.of_equiv (MulAut.outerCongr eq)
  have hUne : U ≠ ⊥ := by intro he; rw [he,card_bot] at hUc; contradiction
  have hsqtk := local_field_normalizer_sqtk h hfield hUne
  by_contra hr
  have hr0 : 2 ≤ primeRank 3 (K0 ⧸ pCore 2 K0) := by
    rw [←primeRank_congr 3 eq]
    omega
  let : IsQuasisimple (K0 ⧸ pCore 2 K0) :=
    ChapterA.Section03.cComponent_twoCore_quasisimple_of_three_rank hsqtk hK0 (by
      rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 K0) pCore_isPGroup]
      exact hr0)
  have hres := hK0.eq_primeToResidual_three_of_rank_outer_two hz0 hr0
    (hsqtk.stronglyQuasithin 3 Nat.prime_three (by decide)) ho0
  obtain ⟨d,hd,ho,hdN,hdH⟩ := field_plane_cubic_outside_centralizer hnat hfield hUc
  have hdres : (⟨d,hdN⟩ : N) ∈ primeToResidual 3 N := by
    apply mem_primeToResidual_of_pow (n := 1)
    apply Subtype.ext
    simpa only [pow_one,Subgroup.coe_pow,Subgroup.coe_one,←ho] using pow_orderOf_eq_one d
  rw [←hres] at hdres
  obtain ⟨k,hk,he⟩ := hdres
  exact hdH (by
    have hv : (k : G) = d := congrArg Subtype.val he
    rw [←hv]
    exact k.property)

open scoped MatrixGroups
open CFSG.Quasithin.ChapterB.QuasisimpleSource

private theorem center_bot_of_model {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (hz : center Y = ⊥) : center X = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have he : e x = 1 := hz.le ((centerCongr e) ⟨x,hx⟩).property
  exact e.map_eq_one_iff.mp he

private theorem alternating_outer_two {d : ℕ} (hd : d = 6 ∨ d = 7 ∨ d = 8) :
    IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin d))) := by
  rcases hd with rfl | rfl | rfl
  · exact IsPGroup.of_card (n := 2) AlternatingSix.ShadowLocal.outer_card
  · exact alternatingGroup.SevenComponent.outer_two
  · exact alternatingGroup.EightComponent.outer_two

/-- Among the B.5 small-moved actors, a genuine field-centralizer component
can have only the A5, PSL3(2), or SL3(4) intrinsic quotient. -/
theorem local_field_component_small_actor
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hfield : IsInvolutoryFieldFixedSpace L M (layer L R) U n)
    (hUc : Nat.card U = 4)
    (K : Subgroup (centralizer (U : Set G))) (hK : K.IsCComponent)
    (hm : SmallMoved.ActorList (K ⧸ pCore 2 K)) :
    Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* PSL(3,ZMod 2)) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* SL(3,BinaryField.four.Carrier)) := by
  let Q := K ⧸ pCore 2 K
  have hex {X : Type} [Group X] [Finite X] (e : Q ≃* X)
      (hz : center X = ⊥) (hr : 2 ≤ primeRank 3 X)
      (ho : IsPGroup 2 (MulAut.Outer X)) : False := by
    have hh := local_field_component_three_rank_le_one h hnat hfield hUc K hK
      (center_bot_of_model e hz) (ho.of_equiv (MulAut.outerCongr e).symm)
    rw [primeRank_congr 3 e] at hh
    omega
  rcases hm with ⟨d,hd,hu,⟨e⟩⟩ | ⟨d,hd,hu,⟨e⟩⟩ | he | he
  · by_cases h2 : d = 2
    · subst d
      let : Group.IsSolvable PSL(2,ZMod 2) :=
        Theory.PSL2.OuterSolvable.isSolvable_of_card_two (Nat.card_zmod 2)
      let : Group.IsSolvable Q := Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
      let : Group.IsNilpotent (pCore 2 K) := pCore_isNilpotent
      have hs : Group.IsSolvable K :=
        (Group.isSolvable_iff_subgroup_quotient (pCore 2 K)).mpr ⟨inferInstance,inferInstance⟩
      exact (hK.not_isSolvable hs).elim
    · by_cases h3 : d = 3
      · subst d
        exact Or.inr (Or.inl ⟨e⟩)
      · have heq : d = 4 ∨ d = 5 := by omega
        let e' := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (n := d) (by omega))
        exact (hex e' (BinaryLinear.OuterCyclic.binary_center_eq_bot (n := d) (by omega))
          (BinaryLinear.SmallCubicRank.four_or_five heq)
          (BinaryLinear.OuterCyclic.sl_outer_isTwoGroup heq)).elim
  · by_cases h5 : d = 5
    · subst d
      exact Or.inl ⟨e⟩
    · have heq : d = 6 ∨ d = 7 ∨ d = 8 := by omega
      exact (hex e (alternatingGroup.center_eq_bot (by simpa using (show 4 ≤ d by omega)))
        (alternatingGroup.TwoThreeCycles.two_le_primeRank (n := d) (by omega))
        (alternating_outer_two heq)).elim
  · exact Or.inr (Or.inr he)
  · obtain ⟨e⟩ := he
    have hc : Nat.card BinaryField.four.Carrier = 2 ^ 2 := BinaryField.four.card_eq
    have ho : IsPGroup 2 (MulAut.Outer (Matrix.symplecticGroup (Fin 2) BinaryField.four.Carrier)) := by
      apply IsPGroup.of_card (n := 2)
      exact Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.card_outer_eq_two_mul hc (by decide)
    exact (hex e Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot
      (Theory.SpecificGroups.SymplecticFour.split_torus_prime_rank (F := BinaryField.four.Carrier) Nat.prime_three
        (by rw [hc]; decide)) ho).elim

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
