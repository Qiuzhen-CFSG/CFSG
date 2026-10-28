module

public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import CFSG.Quasithin.ChapterA.Section02.Statements
public import CFSG.Quasithin.Models
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.Solvability.SylowProfiles.Held
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.Solvability.SylowModels
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.Solvability
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.LowerBounds
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.Triality.ParabolicCover
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.Suzuki
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock
public import Theory.SpecificGroups.ReeF4.DerivedCarrier
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.SL2.SmallOddComparisons
public import Theory.AtlasPort.ModelFacts
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Theory.SpecificGroups.Held.Model.Relations
public import Theory.SpecificGroups.Janko1.Model.Certification.Order
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates
public import Theory.SpecificGroups.Janko4.Model.Cardinality

/-!
# Source Theorem C model inputs

This module connects the actual A.2.4 model list to the older local-model
solvability calculations.  The connection preserves the source equivalences
and every source constructor; it only derives the small parameter exclusions
needed by the legacy solver from the inherited perfect/simple guard.  The
parity conclusion is proved from actual involutions or the checked order
formula for each carrier.

Source: Aschbacher--Smith, Remark A.2.4 and A.3.9/A.3.12, pp.33,45--48.
-/

@[expose] public section
noncomputable section

universe u

namespace CFSG.Quasithin.ChapterA.Section03.SourceComponents

open CFSG.Quasithin.ChapterA.Section02
open CFSG.Quasithin.Chapter1.Section02.LocalModels
open CFSG.Quasithin.ClassificationModels
open CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterE.ValuesEvenClassical
open CFSG.Quasithin.ChapterE.ExceptionalValues
open Theory.GroupTheory
open Subgroup

private theorem perfect_of_simple_noncomm
    {S : Type*} [Group S] (hsimple : IsSimpleGroup S)
    (hna : ¬ IsMulCommutative S) : Group.IsPerfect S := by
  let : IsSimpleGroup S := hsimple
  refine ⟨(Subgroup.Normal.eq_bot_or_eq_top (H := commutator S) inferInstance).resolve_left ?_⟩
  intro hbot
  exact hna ((commutator_eq_bot_iff S).mp hbot)

private theorem alternating_degree_of_perfect
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S] [Group.IsPerfect S]
    {n : ℕ} (hn : n ≤ 8) (iso : Nonempty (S ≃* alternatingGroup (Fin n))) :
    5 ≤ n := by
  by_contra h5
  have hn4 : n ≤ 4 := by omega
  obtain ⟨e⟩ := iso
  have hs : Group.IsSolvable (alternatingGroup (Fin n)) := by
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    let : Group.IsSolvable (Equiv.Perm (Fin n)) := by
      let i : Fin n ↪ Fin 4 := Fin.castLEEmb hn4
      exact Group.isSolvable_of_isSolvable_injective
        (Equiv.Perm.viaEmbeddingHom_injective i)
    exact Group.isSolvable_of_isSolvable_injective
      (alternatingGroup (Fin n)).subtype_injective
  let : Nontrivial S := inferInstance
  let : Group.IsSolvable S := Group.isSolvable_of_isSolvable_injective
    (f := e.toMonoidHom) e.injective
  exact (Group.IsPerfect.not_isSolvable S) inferInstance

private theorem linear_two_parameter_of_perfect
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S] [Group.IsPerfect S]
    {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : e ≤ 2)
    (iso : ClassicalGroup.IsPSL S 2 (p ^ e)) : 4 ≤ p ^ e := by
  by_contra hq
  have hq_lt : p ^ e < 4 := Nat.lt_of_not_ge hq
  obtain ⟨F, _, _, hF, ⟨f⟩⟩ := iso
  have hFgt : 1 < Nat.card F := Finite.one_lt_card
  have hepos : 0 < e := by
    by_contra he0
    have : e = 0 := Nat.eq_zero_of_not_pos he0
    simp [this] at hq_lt
    have hcard : (1 : ℕ) < p ^ e := hF ▸ hFgt
    rw [this] at hcard
    have hbad : (1 : ℕ) < 1 := hcard
    omega
  have he1 : e = 1 := by
    have he_cases : e = 1 ∨ e = 2 := by omega
    exact he_cases.resolve_right (fun he2 => by
      subst e
      have hp2 : 2 ≤ p := hp.two_le
      have : 9 ≤ p ^ 2 := by nlinarith [hp2]
      omega)
  have hp3 : p = 3 := by
    have hp2 : 2 ≤ p := hp.two_le
    have hp_lt : p < 4 := by simpa [he1] using hq_lt
    have hp_cases : p = 2 ∨ p = 3 := by omega
    exact hp_cases.resolve_left (fun hp2eq => by
      subst p
      have hnot : ¬ Odd (2 : ℕ) := by decide
      exact hnot (by simpa using ho))
  have hperf : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Group.IsPerfect.ofSurjective (f := f.toMonoidHom) f.surjective
  exact Matrix.ProjectiveSpecialLinearGroup.not_perfect_of_card_three
    (by simpa [hp3, he1] using hF) hperf

private theorem source_model_to_local
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S] [Group.IsPerfect S]
    (_hna : ¬ IsMulCommutative S)
    (h : IsTheoremCModel S) : TheoremCModel S := by
  cases h with
  | alternating n hn iso =>
      exact .alternating n ⟨alternating_degree_of_perfect hn iso, hn⟩ iso
  | odd model =>
      cases model with
      | linear_two p e hp ho he iso =>
          have hparam := linear_two_parameter_of_perfect hp ho he iso
          have he' : e = 1 ∨ e = 2 := by
            have he0 : e ≠ 0 := by
              intro he0
              subst e
              simp at hparam
            omega
          exact .linear_odd p e hp ho he' hparam iso
      | linear_three p hp ho iso => exact .three_odd p hp ho false iso
      | unitary_three p hp ho iso => exact .three_odd p hp ho true iso
  | bender model => exact .rank_one model
  | rank_two f model =>
      cases model with
      | linear hf iso => exact .rank_two (.linear f hf iso)
      | symplectic hf iso => exact .rank_two (.symplectic f hf iso)
      | g2 hf iso => exact .rank_two (.g2 f hf iso)
      | triality hf iso => exact .rank_two (.triality f hf iso)
      | ree_f4 m hm hf iso =>
          exact .rank_two (.ree m hm ((ReeF4.exists_localBlockInput_mulEquiv_iff S m).mpr iso))
      | symplectic_derived hf iso => exact .rank_two (.symplectic_derived iso)
      | g2_derived hf iso => exact .rank_two (.g2_derived iso)
      | tits hf iso => exact .rank_two (.tits iso)
  | linear_binary n hn iso => exact .binary_linear n hn iso
  | sporadic model =>
      rcases model with ⟨name, hne, iso⟩ | iso
      · exact .sporadic name hne iso
      · exact .janko_one iso

private theorem even_of_j2 : Even (Nat.card Sporadic.LeechRelated.J2.Carrier) := by
  apply even_iff_two_dvd.mpr
  have ha : Sporadic.LeechRelated.J2.GeneratorPair.a ≠ 1 := by
    intro h
    have h0 := congrArg (fun x : Sporadic.LeechRelated.J2.Carrier =>
      (x : Equiv.Perm (Fin 100)) 0) h
    change Sporadic.LeechRelated.J2.generatorA 0 = 0 at h0
    rw [Sporadic.LeechRelated.J2.GeneratorPair.generatorA_eq_table] at h0
    have : (83 : ℕ) = 0 := congrArg Fin.val h0
    norm_num at this
  have hoa : orderOf Sporadic.LeechRelated.J2.GeneratorPair.a = 2 :=
    orderOf_eq_prime Sporadic.LeechRelated.J2.GeneratorPair.a_pow_two ha
  exact hoa ▸ orderOf_dvd_natCard _

private theorem even_of_sporadic_name (name : SporadicName) (hne : name ≠ .j3) :
    Even (Nat.card name.Carrier) := by
  cases name with
  | m11 =>
      change Even (Nat.card Sporadic.Mathieu.M11)
      rw [AtlasPort.Mathieu.M11_card]
      norm_num [AtlasPort.Mathieu.M11]
  | m12 =>
      change Even (Nat.card Sporadic.Mathieu.M12)
      rw [AtlasPort.Mathieu.M12_card]
      norm_num [AtlasPort.Mathieu.M12]
  | m22 =>
      change Even (Nat.card Sporadic.Mathieu.M22)
      rw [AtlasPort.Mathieu.M22_card]
      norm_num [AtlasPort.Mathieu.M22]
  | m23 =>
      change Even (Nat.card Sporadic.Mathieu.M23)
      rw [AtlasPort.Mathieu.M23_card]
      norm_num [AtlasPort.Mathieu.M23]
  | m24 =>
      change Even (Nat.card Sporadic.Mathieu.M24)
      rw [AtlasPort.Mathieu.M24_card]
      norm_num [AtlasPort.Mathieu.M24]
  | j2 => exact even_of_j2
  | j3 => exact (hne rfl).elim
  | j4 =>
      change Even (Nat.card Janko4.Model)
      rw [Janko4.Cardinality.model_card]
      norm_num
  | hs =>
      change Even (Nat.card Sporadic.LeechRelated.HS.Carrier)
      rw [Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier]
      norm_num
  | he =>
      change Even (Nat.card Held.He)
      apply even_iff_two_dvd.mpr
      exact (Held.orderOf_a ▸ orderOf_dvd_natCard Held.a)
  | ru =>
      change Even (Nat.card Rudvalis.Model)
      apply even_iff_two_dvd.mpr
      exact (Rudvalis.orderOf_a ▸ orderOf_dvd_natCard Rudvalis.a)

private theorem even_of_psp2
    {S : Type*} [Group S] [Finite S] {f : ℕ} (hf : 2 ≤ f)
    (h : ClassicalGroup.IsPSp S 2 (2 ^ f)) : Even (Nat.card S) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let _ : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  rw [Nat.card_congr e.toEquiv]
  rw [← Nat.card_congr (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).toEquiv]
  rw [Theory.SpecificGroups.SymplecticFour.card_sp]
  have hFe : Even (Nat.card F) := by
    rw [hF]
    exact Nat.even_pow.mpr ⟨by decide, by omega⟩
  exact ((Nat.even_pow.mpr ⟨hFe, by decide⟩).mul_right _).mul_right _

private theorem even_of_g2
    {S : Type*} [Group S] [Finite S] {q : ℕ} (h : IsG2At S q)
    (hq : ∃ f : ℕ, q = 2 ^ f ∧ 2 ≤ f) : Even (Nat.card S) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  obtain ⟨f, hq, hf⟩ := hq
  rw [Nat.card_congr e.toEquiv, Atlas.G2.card_Model, hF, hq]
  have hFe : Even (Nat.card F) := by
    rw [hF, hq]
    exact Nat.even_pow.mpr ⟨by decide, by omega⟩
  have he6 : Even ((2 ^ f) ^ 6) := by
    apply Nat.even_pow.mpr
    exact ⟨by simpa [hF, hq] using hFe, by decide⟩
  exact (he6.mul_right ((2 ^ f) ^ 6 - 1)).mul_right ((2 ^ f) ^ 2 - 1)

private theorem even_of_source_model
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S] [Group.IsPerfect S]
    (_hna : ¬ IsMulCommutative S) (h : IsTheoremCModel S) : Even (Nat.card S) := by
  cases h with
  | alternating n hn iso =>
      have hn5 : 5 ≤ n := alternating_degree_of_perfect hn iso
      obtain ⟨e⟩ := iso
      have hn2 : 2 ≤ n := by
        omega
      let : n.AtLeastTwo := ⟨hn2⟩
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      interval_cases n <;> norm_num [Nat.factorial]
  | odd model =>
      cases model with
      | linear_two p e hp ho he iso =>
          exact even_iff_two_dvd.mpr
            (two_dvd_card_of_pslTwo_subgroup (⊤ : Subgroup S)
              (iso.of_mulEquiv Subgroup.topEquiv))
      | linear_three p hp ho iso =>
          exact even_iff_two_dvd.mpr
            (two_dvd_card_of_pslThree_subgroup (⊤ : Subgroup S) ho
              (iso.of_mulEquiv Subgroup.topEquiv))
      | unitary_three p hp ho iso =>
          exact even_iff_two_dvd.mpr
            (two_dvd_card_of_psuThree_subgroup (⊤ : Subgroup S) hp ho
              (iso.of_mulEquiv Subgroup.topEquiv))
  | bender model =>
      cases model with
      | linear f hf iso =>
          exact Nat.not_odd_iff_even.mp
            (ValuesEvenClassical.not_odd_card_of_isPSL2 (⊤ : Subgroup S) hf
              (iso.of_mulEquiv Subgroup.topEquiv))
      | unitary f hf iso =>
          exact Nat.not_odd_iff_even.mp
            (ValuesEvenClassical.not_odd_card_of_isPSU3 (⊤ : Subgroup S) (by omega)
              (iso.of_mulEquiv Subgroup.topEquiv))
      | suzuki m hm iso =>
          obtain ⟨e⟩ := iso
          exact ExceptionalValues.Suzuki.even_card_of_subgroup_equiv (⊤ : Subgroup S)
            hm (Subgroup.topEquiv.trans e)
  | rank_two f model =>
      cases model with
      | linear hf iso =>
          exact Nat.not_odd_iff_even.mp
            (ValuesEvenClassical.not_odd_card_of_isPSL3 (⊤ : Subgroup S) hf
              (iso.of_mulEquiv Subgroup.topEquiv))
      | symplectic hf iso => exact even_of_psp2 hf iso
      | g2 hf iso => exact even_of_g2 iso ⟨f, rfl, hf⟩
      | triality hf iso =>
          exact Nat.not_odd_iff_even.mp
            (ExceptionalValues.Triality.not_odd_card_of_triality (⊤ : Subgroup S)
              (iso.of_mulEquiv Subgroup.topEquiv) (by omega))
      | ree_f4 m hm hf iso =>
          obtain ⟨e⟩ := iso
          rw [Nat.card_congr e.toEquiv]
          exact ReeF4.DerivedCarrier.even_card m
      | symplectic_derived hf iso =>
          obtain ⟨e⟩ := iso
          rw [Nat.card_congr e.toEquiv,
            Nat.card_congr
              (Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix).toEquiv,
            nat_card_alternatingGroup]
          norm_num [Nat.factorial]
      | g2_derived hf iso =>
          obtain ⟨e⟩ := iso
          rw [Nat.card_congr e.toEquiv]
          exact Atlas.G2.DerivedEvenOrder.even_card_derived
            (F := ZMod 2) (f := 1) (by decide)
            (by rw [Nat.card_zmod]; norm_num)
      | tits hf iso =>
          obtain ⟨e⟩ := iso
          rw [Nat.card_congr e.toEquiv, Tits.parrottGroup_card]
          norm_num
  | linear_binary n hn iso =>
      rcases hn with rfl | rfl
      · exact Nat.not_odd_iff_even.mp
          (ValuesEvenClassical.not_odd_card_of_isPSL4_two (⊤ : Subgroup S)
            (iso.of_mulEquiv Subgroup.topEquiv))
      · exact Nat.not_odd_iff_even.mp
          (ValuesEvenClassical.not_odd_card_of_isPSL5_two (⊤ : Subgroup S)
            (iso.of_mulEquiv Subgroup.topEquiv))
  | sporadic model =>
      rcases model with ⟨name, hne, iso⟩ | iso
      · obtain ⟨e⟩ := iso
        rw [Nat.card_congr e.toEquiv]
        exact even_of_sporadic_name name hne
      · obtain ⟨e⟩ := iso
        rw [Nat.card_congr e.toEquiv, Janko1.card_model]
        norm_num

/-- The actual source Theorem C model implies the legacy local model used by
the checked outer-solvability calculations. -/
public theorem sourceTheoremC_to_local
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S] [Group.IsPerfect S]
    (hna : ¬ IsMulCommutative S) (h : IsTheoremCModel S) : TheoremCModel S :=
  source_model_to_local hna h

/-- Guarded outer solvability and even order for every actual source model. -/
public theorem source_model_outer_isSolvable_even
    (hRu : IsSimpleGroup Rudvalis.Model → Group.IsSolvable (MulAut.Outer Rudvalis.Model))
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S] [Group.IsPerfect S]
    (hna : ¬ IsMulCommutative S) (h : IsTheoremCModel S) :
    Group.IsSolvable (MulAut.Outer S) ∧ Even (Nat.card S) := by
  let hHeld : IsSimpleGroup Held.He → Group.IsSolvable (MulAut.Outer Held.He) :=
    fun _ => CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels.held_outer_isSolvable_of_frattini_profile
  exact ⟨CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels.theoremC_outer_isSolvable_of_simple_model_inputs
      hHeld hRu
      (source_model_to_local hna h),
    even_of_source_model hna h⟩

/-- Literal universal source predicate used by the A.3 source assembly. -/
public theorem source_model_inputs
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      IsTheoremCModel X)
    (hRu : IsSimpleGroup Rudvalis.Model → Group.IsSolvable (MulAut.Outer Rudvalis.Model)) :
    ∀ (S : Type u) [Group S] [Finite S], IsSimpleGroup S → ¬ IsMulCommutative S →
      IsSQTK KnownSimple.IsKnownSimple S →
      Group.IsSolvable (MulAut.Outer S) ∧ Even (Nat.card S) := by
  intro S _ _ hsimple hna _hsq
  let : IsSimpleGroup S := hsimple
  let : Group.IsPerfect S := perfect_of_simple_noncomm hsimple hna
  exact source_model_outer_isSolvable_even hRu hna (hC S)

/-- The literal radical quotient of a C-component is an actual semisimple
section, so Theorem A supplies the strong-quasithin and full K-group inputs
needed by the universal source predicate.  This is the source application
used for both the original component and the component of a generated join.
-/
public theorem source_model_inputs_on_cComponent
    {G : Type u} [Group G] [Finite G]
    (hA : TheoremA KnownSimple.IsKnownSimple G)
    (hG : IsStronglyQuasithin G)
    (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (hC : ∀ (X : Type u) [Group X] [Finite X], IsTheoremCModel X)
    (hRu : IsSimpleGroup Rudvalis.Model →
      Group.IsSolvable (MulAut.Outer Rudvalis.Model))
    (L : Subgroup G) (hL : L.IsCComponent) :
    Group.IsSolvable (MulAut.Outer (L ⧸ solvableRadical L)) ∧
      Even (Nat.card (L ⧸ solvableRadical L)) := by
  let Q := L ⧸ solvableRadical L
  let hsimple : IsSimpleGroup Q := hL.isSimpleGroup_quotient_solvableRadical
  let hna : ¬ IsMulCommutative Q := hL.not_isMulCommutative_quotient_solvableRadical
  let hperf : Group.IsPerfect Q := perfect_of_simple_noncomm hsimple hna
  let : IsSimpleGroup Q := hsimple
  let : Group.IsPerfect Q := hperf
  have hcenter : center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Q) inferInstance with h | h
    · exact h
    · exact (hna (center_eq_top_iff.mp h)).elim
  have hsimple_center : IsSimpleGroup (Q ⧸ center Q) :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot |>.isSimpleGroup
  let : IsQuasisimple Q := { toIsPerfect := hperf, simple := hsimple_center }
  have hsection : IsSectionOf Q G :=
    IsSectionOf.quotient_subgroup L (solvableRadical L)
  have hsemi : IsSemisimple Q := by
    apply top_unique
    exact le_sSup
      (show Theory.GroupTheory.IsComponent Q (⊤ : Subgroup Q) from
        ⟨Subgroup.IsSubnormal.top,
          IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm⟩)
  have hstrong : IsStronglyQuasithin Q :=
    hA.stronglyQuasithin_section hG hK hsection hsemi
  have hsq : IsSQTK KnownSimple.IsKnownSimple Q :=
    ⟨hstrong, hsection.isKGroup hK⟩
  exact source_model_inputs hC hRu Q hsimple hna hsq

end CFSG.Quasithin.ChapterA.Section03.SourceComponents
