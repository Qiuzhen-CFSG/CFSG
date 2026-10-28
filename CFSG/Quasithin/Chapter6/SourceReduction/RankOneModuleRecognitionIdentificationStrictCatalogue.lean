module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictInputs
public import CFSG.Quasithin.ChapterG.Section11.Catalogue
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer.ExtraspecialModel
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Imprimitive.AlternatingSevenSource
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Imprimitive
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Symmetric.Source
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.GTwo
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OrthogonalFour
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.TwistedTensor
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Imprimitive.AlternatingSixTensor

/-!
# Eleven catalogue exclusions for the strict-intersection action

The original faithful binary action, commutator form and type-a₂ involution
exclude G.11.2(1), (3)--(12). The normal A₇ and orthogonal actions use the
intrinsic conjugate-product bound; the full G₂(2) action uses its proved
long-root stabilizer calculation. The extraspecial odd center acts on the
original six-space. All four tensor alternatives and the scalar extension
in case (11) retain their actual intertwiners. Cases (8) and (12) use the
literal X-invariant or exchanged summands and component embeddings.

The source application reuses `strict_g11_inputs`, including its involution
in the original crossing image and nontransitivity on the literal moved
plane. The zero-pairing characterization transports type a₂ to the supplied
commutator form without changing the quotient or action.

This is a conditional reduction of the published catalogue to cases (2)
and (13), not the final strict contradiction. Their elimination and the
application of the genuine classifier remain with
qt-d-1222-recognition-strict-elimination; the classifier is owned by
qt-g112-low-rank-symplectic-classification and LocalAnalysis is supplied by
qt-d-1222-rankone-recognition-identification.

Source: Aschbacher--Smith, G.11.2 and proof of 6.2.19, printed pp.364,691
(PDF pp.375,708). The imported model modules give the individual calculations.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open Representation.RankTwo
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.StrictCatalogue
variable {H V : Type*} [Group H] [Finite H]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) H V} {B : LinearMap.BilinForm (ZMod 2) V}
  {X : Subgroup H}

omit [Finite H] in
private theorem exclude_three (hf : Function.Injective ρ)
    (a : H) (ha2 : a ^ 2 = 1)
    (hr : finrank (ZMod 2) (movedSpace ρ a) = 2)
    (hnt : ¬ StabilizerTransitive ρ (movedSpace ρ a))
    (hc : ChapterG.Section11.CaseThree ρ) : False := by
  obtain ⟨hd, K, hK, ⟨e⟩⟩ := hc
  let σ := ρ.comp e.symm.toMonoidHom
  have he (g : H) (w : V) : (LinearEquiv.refl (ZMod 2) V) (ρ g w) =
      σ (e g) ((LinearEquiv.refl (ZMod 2) V) w) := by simp [σ]
  have hsq : e a * e a = 1 := by rw [← map_mul, ← pow_two, ha2, map_one]
  have hr' := (finrank_movedSpace_transport ρ σ e (LinearEquiv.refl _ _) he a).symm.trans hr
  obtain ⟨c, _, _, _, ht⟩ := ExtraspecialModel.model_rank_two K hK σ
    (hf.comp e.symm.injective) hd (e a) hsq hr'
  exact hnt (stabilizerTransitive_transport ρ σ e (LinearEquiv.refl _ _) he a ht)

omit [Finite H] [FiniteDimensional (ZMod 2) V] in
private theorem exclude_nine (a : H) (ha2 : a ^ 2 = 1)
    (hr : finrank (ZMod 2) (movedSpace ρ a) = 2)
    (hnt : ¬ StabilizerTransitive ρ (movedSpace ρ a))
    (hc : ChapterG.Section11.CaseNine ρ) : False := by
  rcases hc.2 with ⟨e, f, hf⟩ | ⟨e, f, hf⟩ | ⟨e, f, hf⟩ | ⟨e, f, hf⟩
  · have hsq : e a * e a = 1 := by rw [← map_mul, ← pow_two, ha2, map_one]
    have hr' := (finrank_movedSpace_transport ρ _ e f hf a).symm.trans hr
    obtain ⟨c, _, _, _, _, ht⟩ := TensorModels.orthogonal_rank_two_cubic (e a) hsq hr'
    exact hnt (stabilizerTransitive_transport ρ _ e f hf a ht)
  · have hsq : e a * e a = 1 := by rw [← map_mul, ← pow_two, ha2, map_one]
    exact TensorModels.orthogonalAlternating_not_rank_two (e a) hsq
      ((finrank_movedSpace_transport ρ _ e f hf a).symm.trans hr)
  · have hsq : e a * e a = 1 := by rw [← map_mul, ← pow_two, ha2, map_one]
    exact TensorModels.natural_not_rank_two (e a) hsq
      ((finrank_movedSpace_transport ρ _ e f hf a).symm.trans hr)
  · have hsq : e a * e a = 1 := by rw [← map_mul, ← pow_two, ha2, map_one]
    exact TensorModels.naturalBase_not_rank_two (e a) hsq
      ((finrank_movedSpace_transport ρ _ e f hf a).symm.trans hr)

omit [Finite H] in
private theorem exclude_eight [IsElementaryAbelian 2 X]
    (a : H) (ha : a ∈ X)
    (hr : finrank (ZMod 2) (movedSpace ρ a) = 2)
    (hc : ChapterG.Section11.CaseEight ρ B X) : False := by
  obtain ⟨_, ⟨e⟩, I, hI, _, hstable, x, hx, _, hsplit⟩ := hc
  have hA : IsComponent (Equiv.Perm (Fin 7)) (alternatingGroup (Fin 7)) := by
    refine ⟨(inferInstance : (alternatingGroup (Fin 7)).Normal).isSubnormal, ?_⟩
    change IsQuasisimple (alternatingGroup (Fin (2 + 5)))
    infer_instance
  have hle : (alternatingGroup (Fin 7)).map e.symm.toMonoidHom ≤ componentLayer H :=
    le_sSup (hA.map_equiv e.symm)
  let P : Subrepresentation (ρ.comp
      (e.symm.toMonoidHom.comp (alternatingGroup (Fin 7)).subtype)) := {
    toSubmodule := I
    apply_mem_toSubmodule := fun g w hw =>
      (hstable (hle (mem_map_of_mem e.symm.toMonoidHom g.property)) w).mpr hw }
  exact Imprimitive.alternatingSeven_decomposition_X_not_rankTwo ρ e P hI X x hx
    (fun g hg => by simpa only [pow_two] using (show g ^ 2 = 1 from elemPow_eq_one_of_isElementaryAbelian g hg))
    (fun g hg k hk => show Commute g k from
      congrArg Subtype.val (mul_comm (⟨g, hg⟩ : X) ⟨k, hk⟩)) hsplit a ha hr

omit [Finite H] [FiniteDimensional (ZMod 2) V] in
private theorem exclude_twelve [IsElementaryAbelian 2 X]
    (a : H) (ha : a ∈ X)
    (hr : finrank (ZMod 2) (movedSpace ρ a) = 2)
    (hc : ChapterG.Section11.CaseTwelve ρ X) : False := by
  open BinaryOffender in
  obtain ⟨_, L, hL, x, hx, _, hsplit, ⟨e, f, hf⟩, hgen, _⟩ := hc
  let Lx := L.map (MulAut.conj x).toMonoidHom
  have hne : L ≠ Lx := by
    intro heq
    have hh := hsplit.disjoint
    change Disjoint (BinaryOffender.subspaceCommutator ρ ⊤ L)
      (BinaryOffender.subspaceCommutator ρ ⊤ Lx) at hh
    rw [← heq] at hh
    have hz := disjoint_self.mp hh
    have hd := f.finrank_eq
    rw [hz, finrank_bot, Imprimitive.OrthogonalA5.finrank_space] at hd
    omega
  have hcentral := commutator_eq_bot_iff_le_centralizer.mp
    (hL.commutator_eq_bot_of_ne (hL.map_equiv (MulAut.conj x)) hne)
  let j : alternatingGroup (Fin 5) →* H := L.subtype.comp e.symm.toMonoidHom
  let k : alternatingGroup (Fin 5) →* H := (MulAut.conj x).toMonoidHom.comp j
  have hj : j.range = L := by
    ext y
    constructor
    · rintro ⟨b, rfl⟩
      exact (e.symm b).property
    · intro hy
      refine ⟨e ⟨y, hy⟩, ?_⟩
      simp [j]
  have hk : k.range = Lx := by
    dsimp only [k]
    rw [MonoidHom.range_comp, hj]
  have hcomm (b c : alternatingGroup (Fin 5)) : Commute (j b) (k c) := by
    have hb : j b ∈ L := hj ▸ (show j b ∈ j.range from ⟨b, rfl⟩)
    have hc : k c ∈ Lx := hk ▸ (show k c ∈ k.range from ⟨c, rfl⟩)
    exact ((mem_centralizer_iff.mp (hcentral hb)) (k c) hc).symm
  let i := j.noncommCoprod k hcomm
  have hleft : (i.comp (MonoidHom.inl _ _)).range = L := by
    simpa only [i, MonoidHom.noncommCoprod_comp_inl] using hj
  have hright : (i.comp (MonoidHom.inr _ _)).range = Lx := by
    simpa only [i, MonoidHom.noncommCoprod_comp_inr] using hk
  have hi : i.range = L ⊔ Lx := by
    dsimp only [i]
    rw [MonoidHom.noncommCoprod_range, hj, hk]
  have hex := Imprimitive.orthogonalA5_commutator_X_not_rankTwo ρ i
  rw [hleft, hright] at hex
  apply hex f X x hx
    (fun g hg => by simpa only [pow_two] using
      (show g ^ 2 = 1 from elemPow_eq_one_of_isElementaryAbelian g hg))
    (fun g hg b hb => show Commute g b from
      congrArg Subtype.val (mul_comm (⟨g, hg⟩ : X) ⟨b, hb⟩))
    ?_ hsplit ?_ (by simpa only [hi] using hgen) a ha hr
  · intro b
    simp [i, k, MulAut.conj_apply]
  · intro b w
    simpa [i, j, k] using hf (e.symm b) w

/-- Eleven of the thirteen literal catalogue alternatives are incompatible with
an intrinsic type-a₂ involution whose moved-plane stabilizer is not transitive.
The two remaining alternatives retain all their original actor and form clauses. -/
theorem remaining_cases [IsElementaryAbelian 2 X]
    (hf : Function.Injective ρ) (hBa : B.IsAlt) (hBn : B.Nondegenerate)
    (hpres : ∀ g x y, B (ρ g x) (ρ g y) = B x y)
    (hd : 4 ≤ finrank (ZMod 2) V)
    (a : H) (ha : a ∈ X) (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1)
    (hr : finrank (ZMod 2) (movedSpace ρ a) = 2)
    (hType : ∀ w, B w (ρ a w) = 0)
    (hnt : ¬ StabilizerTransitive ρ (movedSpace ρ a))
    (hc : ChapterG.Section11.Conclusion ρ B X) :
    ChapterG.Section11.CaseTwo ρ B ∨ ChapterG.Section11.CaseThirteen ρ := by
  have hprod := Symmetric.smallConjugateProducts_of_type_a2 B ρ hBa hBn hf hpres a ha2 hr hType
  rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
  · have := hc.1; omega
  · exact Or.inl hc
  · exact (exclude_three hf a ha2 hr hnt hc).elim
  · obtain ⟨_, e, f, he⟩ := hc
    exact (Symmetric.seven_extension_not_type_a2 (generalizedFitting H) ρ hf e f he
      B hBa hBn hpres a ha2 hr hType).elim
  · obtain ⟨_, q, _, f, _, K, hK, e, he⟩ := hc
    exact (hnt (Symmetric.split_orthogonal_model_stabilizerTransitive_of_type_a2
      ρ hf K hK e f he B hBa hBn hpres a ha2 hr hType)).elim
  · obtain ⟨_, e, f, he⟩ := hc
    exact (GTwo.exclusion_of_equivariant_model ρ e f he a
      (orderOf_eq_prime ha2 ha1) hr hprod hnt).elim
  · obtain ⟨_, _, e, f, he⟩ := hc
    exact (OrthogonalFour.exclusion_of_orthogonal_model ρ (generalizedFitting H)
      e f he a ha2 hr hprod).elim
  · exact (exclude_eight a ha hr hc).elim
  · exact (exclude_nine a ha2 hr hnt hc).elim
  · obtain ⟨_, e, _, _, ⟨f, he⟩, _⟩ := hc
    have hsq : e a * e a = 1 := by rw [← map_mul, ← pow_two, ha2, map_one]
    exact (Imprimitive.AlternatingSixTensor.movedSpace_not_rankTwo (e a) hsq
      ((finrank_movedSpace_transport ρ _ e f he a).symm.trans hr)).elim
  · obtain ⟨_, e, σ, _, _, he⟩ := hc
    have hfour := TwistedTensor.ambient_rank_eq_four σ ρ e he a (orderOf_eq_prime ha2 ha1)
    omega
  · exact (exclude_twelve a ha hr hc).elim
  · exact Or.inr hc

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.StrictCatalogue

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The catalogue reduction for the literal strict actor, crossing subgroup
and commutator form. The catalogue is an explicit conditional input here;
its exhaustive recognition and the two remaining exclusions are still needed. -/
theorem LocalAnalysis.strict_catalogue_remaining_cases
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdres : d ∈ strictCrossingResidual (T : Subgroup G) L R)
    (hdH : d ∉ centralizer ({z} : Set G))
    (hdS : d ∈ normalizer ((T : Subgroup G) ⊓ L : Set G)) (hd3 : orderOf d = 3)
    [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z)]
    [IsElementaryAbelian 2 (strictCrossingImage (T : Subgroup G) L R z d)]
    (B : LinearMap.BilinForm (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z)))
    (v : Additive (StrictVectorQuotient (T : Subgroup G) L R z))
    (h : ChapterG.Section10.Hypothesis (strictRepresentation (T : Subgroup G) L R z) B v
      (strictHatSpace (T : Subgroup G) L R z (strictCrossingIntersection (T : Subgroup G) L R z d))
      (strictCrossingImage (T : Subgroup G) L R z d)
      ((strictCrossingCenterImage (T : Subgroup G) L R z d).subgroupOf
        (strictCrossingImage (T : Subgroup G) L R z d)))
    (hB : ∀ u w : sourceClosure (T : Subgroup G) L R z,
      B (strictHatElement (T : Subgroup G) L R z u)
        (strictHatElement (T : Subgroup G) L R z w) = 0 ↔ Commute u w)
    (hc : ChapterG.Section11.Conclusion (strictRepresentation (T : Subgroup G) L R z) B
      (strictCrossingImage (T : Subgroup G) L R z d)) :
    ChapterG.Section11.CaseTwo (strictRepresentation (T : Subgroup G) L R z) B ∨
      ChapterG.Section11.CaseThirteen (strictRepresentation (T : Subgroup G) L R z) := by
  obtain ⟨he', hX', B', v', _, _, hB', hd, _, _, _, _,
      a, ha, ha1, ha2, _, hr, _, htype, hnt⟩ :=
    A.strict_g11_inputs h611 hnatural hz horder hTH hstrict hdres hdH hdS hd3
  have hzero (u w : Additive (StrictVectorQuotient (T : Subgroup G) L R z)) :
      B u w = 0 ↔ B' u w = 0 := by
    obtain ⟨u', hu⟩ := QuotientGroup.mk'_surjective
      (center (sourceClosure (T : Subgroup G) L R z)) u.toMul
    obtain ⟨w', hw⟩ := QuotientGroup.mk'_surjective
      (center (sourceClosure (T : Subgroup G) L R z)) w.toMul
    simpa only [strictHatElement, hu, hw, ofMul_toMul] using
      (hB u' w').trans (hB' u' w').symm
  exact StrictCatalogue.remaining_cases h.faithful h.alternating h.nondegenerate h.preserves
    hd a ha ha1 ha2 hr (fun w => (hzero w _).mpr (htype w)) hnt hc

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
