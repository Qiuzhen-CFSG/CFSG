module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.TwoChiefQuotientExclusions
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size

/-!
# The mixed recognition input at the original small parabolics

Reverse the literal F.1.1 pair so its first factor is the embedded O²(H).
The original ambient Sylow is Sylow in the generated pair, the common Borel
is exactly H ∩ M, and the full first parabolic is H. Thus the independent
mixed A₅/S₃ Sylow bound applies whenever Y₁Rc has cubic core quotient.
The two faithful source chief factors force |T| ≥ 2048, contradicting
that upper bound of 256. Together with the completed cubic exclusion this
gives the S₃-wreath quotient in all marked cubic and Omega action rows.

The size premise is precisely the source contract owned by
qt-d-tensor-mixed-size-bound. Its Borel-recognition version also supplies
that premise. Neither input is proved here: the mixed-recognition owner
must discharge it before these conditional conclusions establish the
corresponding branches of original 15.2.8. The D₁₀/Sz(2) first-factor rows
and the marked-five wreath exclusion remain with qt-e-152-small-parabolic.
No containment T ≤ Y₁Rc is imposed.

Source: Aschbacher--Smith 15.2.6--8, printed pp.1109--1110, and F.1.12,
printed pp.262--264, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Source
variable {G : Type*} [Group G] {A B S : Subgroup G}
private theorem swap_pair (h : HypothesisF11 ![A,B] S) : HypothesisF11 ![B,A] S := by
  refine ⟨h.finite_S,h.S_isP,?_,?_,?_,?_,?_,?_⟩
  · intro i
    fin_cases i
    · exact h.S_normalizes 1
    · exact h.S_normalizes 0
  · intro i
    fin_cases i
    · exact h.sylow 1
    · exact h.sylow 0
  · intro i
    fin_cases i
    · exact h.quotient 1
    · exact h.quotient 0
  · intro i
    fin_cases i
    · exact h.cross 1
    · exact h.cross 0
  · change pCore 2 (B ⊔ A ⊔ S : Subgroup G) = ⊥
    rw [sup_comm B A]
    exact h.twoCore_free
  · intro i
    fin_cases i
    · exact h.characteristic_two 1
    · exact h.characteristic_two 0
end CFSG.Quasithin.ChapterF.Source

open Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource ChapterF.Source
variable {G : Type*} [Group G] [Finite G]

/-- The original pair, in A₅-first order, satisfies every placement and
normalizer premise of the independent mixed recognition theorem. Its full
overlap and second source parabolic are preserved literally. -/
theorem SmallResidualWitness.symmetricFive_mixed_inputs
    {T : Sylow 2 G} {M Mc V Y₁ H : Subgroup G} {h : ChosenSmallSource T M Mc V}
    (hw : SmallResidualWitness h Y₁)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    let A := Y₁ ⊔ (M ⊓ Mc).pCoreIn 2
    let K := (pResidual 2 H).map H.subtype
    let L := ![K,A]
    HypothesisF11 L (T : Subgroup G) ∧
      IsQuasithin (generated L (T : Subgroup G)) ∧
      Chapter1.IsSylowIn 2 (T : Subgroup G) (generated L (T : Subgroup G)) ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) ∧
      borel A (T : Subgroup G) ≤ normalizer (T : Set G) ∧
      commonBorel L (T : Subgroup G) = H ⊓ M ∧
      parabolic L (T : Subgroup G) 0 = H := by
  let A := Y₁ ⊔ (M ⊓ Mc).pCoreIn 2
  let K := (pResidual 2 H).map H.subtype
  let L := ![K,A]
  obtain ⟨hf,hb,hp,_,_,hk⟩ := hw.symmetricFive_pair hH he
  have hg := hw.symmetricFive_geometry hH he
  have hTK : (T : Subgroup G) ≤ generated L (T : Subgroup G) := le_sup_right
  refine ⟨swap_pair hf,h.ambient.quasithin.subgroup _,
    ⟨T.subtype hTK,map_subgroupOf_eq_of_le hTK⟩,hk,?_,?_,hp⟩
  · change borel A (T : Subgroup G) ≤ _
    rw [hb]
    exact inf_le_left.trans (T : Subgroup G).le_normalizer
  · change borel K (T : Subgroup G) ⊔ borel A (T : Subgroup G) ⊔ _ = _
    rw [sup_comm (borel K _) (borel A _)]
    exact hg.1


/-- The existing mixed Borel recognition theorem supplies the exact numerical
contract used below. Its independent producer is qt-d-tensor-mixed-size-bound. -/
theorem mixed_size_of_borel_recognition
    (recognition : MixedA5S3BorelRecognition G) :
    ∀ (K A S : Subgroup G), HypothesisF11 ![K,A] S →
      IsQuasithin (generated ![K,A] S) → Chapter1.IsSylowIn 2 S (generated ![K,A] S) →
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) →
      Nonempty ((A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) →
      borel A S ≤ normalizer (S : Set G) → Nat.card S ≤ 256 := by
  intro K A S hf hqt hsyl hk ha _
  exact mixed_a5_s3_sylow_card_le_of_borel_recognition recognition K A S hf hqt hsyl hk ha

variable (hsize : ∀ (K A S : Subgroup G), HypothesisF11 ![K,A] S →
  IsQuasithin (generated ![K,A] S) → Chapter1.IsSylowIn 2 S (generated ![K,A] S) →
  Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) →
  Nonempty ((A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) →
  borel A S ≤ normalizer (S : Set G) → Nat.card S ≤ 256)
include hsize

/-- Both faithful natural chief factors exclude the single S₅ quotient
once the independent mixed-pair Sylow bound is available. -/
theorem SmallResidualWitness.not_symmetricFive_of_cubic_of_mixed_size
    {T : Sylow 2 G} {M Mc V Y₁ H : Subgroup G} {h : ChosenSmallSource T M Mc V}
    (hw : SmallResidualWitness h Y₁) (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hfirst : Nonempty (((Y₁ ⊔ (M ⊓ Mc).pCoreIn 2 : Subgroup G) ⧸
      pCore 2 (Y₁ ⊔ (M ⊓ Mc).pCoreIn 2 : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    ¬ Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5)) := by
  intro he
  obtain ⟨hf,hqt,hsyl,hk,hb,_,_⟩ := hw.symmetricFive_mixed_inputs hH he
  have hu := hsize _ _ _ hf hqt hsyl hk hfirst hb
  have hl := h.symmetricFive_sylow_card hprior hH he
  omega

/-- Conditional completion of original 15.2.8 in the marked cubic row.
The independent mixed-pair bound is the sole added recognition input. -/
theorem ChosenSmallSource.HStar_wreath_of_marked_cubic_of_mixed_size
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 3 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) := by
  have hw := (h.smallResidualWitness_of_marked_cubic hd).1
  have hq := (h.marked_cubic_residual_selection hd).2.2.1
  exact (h.HStar_quotient_cubic_reduced hprior hd hH).resolve_right
    (hw.not_symmetricFive_of_cubic_of_mixed_size hsize hprior hH hq)

/-- The same conditional conclusion for every Omega support, retaining
the original rank-one selection, including the extraspecial residual row. -/
theorem ChosenSmallSource.HStar_wreath_of_omega_of_mixed_size
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (ho : letI := h.prepared.elementary
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) := by
  obtain ⟨Y₁,hle,hp,hne,hn,hm,hcentral,hquot⟩ := h.omega_rank_one_selection ho
  have hw := (h.smallResidualWitness_of_moved_selection (h.maximal_overgroups_of_omega ho)
    hle hp hne hn hm (Or.inl hquot) hcentral).1
  exact (h.HStar_quotient_omega_reduced hprior ho hH).resolve_right
    (hw.not_symmetricFive_of_cubic_of_mixed_size hsize hprior hH hquot)


/-- With the independent mixed bound, either all original H-star quotients
are S₃ wreath C₂, or the chosen action has its literal marked-five generator. -/
theorem ChosenSmallSource.HStar_wreath_or_marked_five_of_mixed_size
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V) :
    (∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((H ⧸ pCore 2 H) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))) ∨
    (letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2) := by
  let := h.prepared.elementary
  rcases h.small with ⟨l,p,m,hpm,hd⟩ | ho
  · have hm : m = 2 := h.marking_dimension l p m hd
    subst m
    rcases (primeDimensionOptions_iff p 2).mp hpm with ⟨rfl,_⟩ | ⟨rfl,_⟩
    · exact Or.inl (fun H hH =>
        h.HStar_wreath_of_marked_cubic_of_mixed_size hsize hprior ⟨l,hd⟩ hH)
    · exact Or.inr ⟨l,hd⟩
  · exact Or.inl (fun H hH => h.HStar_wreath_of_omega_of_mixed_size hsize hprior ho hH)

end CFSG.Quasithin.Chapter15.Section02
