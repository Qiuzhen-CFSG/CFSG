module
public import CFSG.Quasithin.Chapter14.Section06.SourceSingletonCompatibility.Reduction
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NineAmbient
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.FixedComplement

/-!
# The literal elementary-nine quotient and critical images

The four-dimensional residual support retains the original faithful action
and cubic ratio two. Its two cubic supports bound the quotient order by72;
the singleton endpoint contributes a subgroup of order18. If the whole
quotient had order18, inversion would make a cubic subgroup of the odd
residual normal, contradicting its original minimal normality. The ratio
bound excludes order72, leaving order36 and cyclic Sylow groups of order4.

The same original critical spans therefore have quotient image of order2
and intersect the opposite two-core in index2. The final theorem adds these
facts to the literal odd-core counterexample reduction, preserving its
quotient, factor embeddings and reciprocal endpoints. It does not exclude
the elementary-nine branch or complete original14.6.12.

Source: Aschbacher--Smith14.6.11--12, printed pp.1030--1031;
D.2.17(3), p.188, and the elementary-nine extension in15.1.2(5), p.1086.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hu hmany hcard e hab


universe u
omit hG T hempty hM hu hmany hcard e hab in
private theorem nine_endpoint_normal_cubic
    {A W : Type u} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) A W}
    (l : ChapterD.CyclicSource.LocalGeneration ρ) :
    letI := Representation.BinaryGroupAction.action ρ
    letI : Finite W := Module.finite_of_finite (ZMod 2)
    letI : IsElementaryAbelian 2 (Multiplicative W) := Representation.BinaryGroupAction.elementary
    letI := l.normal
    ChapterD.Section02.ElementaryNineEndpoint (V := Multiplicative W) l.kernel l.involution →
    ∃ B : Subgroup A, B.Normal ∧ B ≤ l.kernel ∧ Nat.card B = 3 := by
  let := Representation.BinaryGroupAction.action ρ
  let : Finite W := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative W) := Representation.BinaryGroupAction.elementary
  let := l.normal
  intro h9
  let := h9.kernel_elementary
  obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' (G := l.kernel) 3
    (by rw [h9.card_kernel]; decide)
  let B := (zpowers b).map l.kernel.subtype
  have hB : B ≤ l.kernel := map_subtype_le _
  have hKN : l.kernel ≤ normalizer (B : Set A) := by
    let : CommGroup l.kernel := IsMulCommutative.instCommGroup
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype]
      using (zpowers b).le_normalizer_map l.kernel.subtype
  have htN : l.involution ∈ normalizer (B : Set A) := by
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      rw [h9.inverts ⟨x,hB hx⟩]
      exact B.inv_mem hx
    · intro hx
      have hn : l.involution ∈ normalizer (l.kernel : Set A) := le_normalizer_of_normal (mem_top _)
      have hxK := (mem_normalizer_iff.mp hn x).mpr (hB hx)
      rw [h9.inverts ⟨x,hxK⟩] at hx
      exact B.inv_mem_iff.mp hx
  refine ⟨B,normalizer_eq_top_iff.mp (top_unique ?_),hB,?_⟩
  · rw [←l.generated]
    exact sup_le hKN (zpowers_le.mpr htN)
  · rw [card_map_of_injective l.kernel.subtype_injective,Nat.card_zpowers,hb]

/-- The surviving elementary-nine singleton has literal quotient order36
and cyclic Sylow two-subgroups of order four. -/
theorem source_singleton_nine_quotient_structure
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hone : Nat.card d.Index = 1)
    (hnine : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9) :
    Nat.card (J ⧸ pCore 2 J) = 36 ∧
      (∀ S : Sylow 2 (J ⧸ pCore 2 J), IsCyclic S ∧ Nat.card S = 4) := by
  classical
  let := hs
  let K := ChapterD.Jhat a.representation
  let : K.Normal := ChapterD.Jhat_normal a.representation
  let P := pResidual 2 (J ⧸ pCore 2 J)
  obtain ⟨i,hi⟩ := Nat.card_eq_one_iff_exists.mp hone
  have hc := source_singleton_factor_star_cyclic hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d hd hone i
  obtain ⟨_,_,_,hcover,_,_⟩ := Section02.source_lemma_14_2_2_8_minimal
    hG T hempty hM hu hmany hcard e J hJ
  have hq := source_ratio_singleton_nine_ratio_two hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d hd i hi hc hnine
  obtain ⟨l⟩ := f.factor_cyclic_localGeneration d (pCore_quotient_pCore_eq_bot 2)
    hq.le hd hcover (QuotientGroup.mk' (pCore 2 J)) (QuotientGroup.mk'_surjective _) i hc
  let g : (d.factor i).Carrier →* (J ⧸ pCore 2 J) :=
    K.subtype.comp (d.factor i).embedding.groupMap
  have hg : Function.Injective g := K.subtype_injective.comp (d.factor i).embedding.group_injective
  have he : l.kernel.map g = P := source_ratio_singleton_kernel_eq_residual
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d i hi l
  have hcKernel : Nat.card l.kernel = 9 :=
    (card_map_of_injective hg).symm.trans (he ▸ hnine)
  let := Representation.BinaryGroupAction.action (d.factor i).action
  let : Finite (d.factor i).Space := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative (d.factor i).Space) :=
    Representation.BinaryGroupAction.elementary
  let := l.normal
  have h9 : ChapterD.Section02.ElementaryNineEndpoint
      (V := Multiplicative (d.factor i).Space) l.kernel l.involution := by
    rcases l.endpoints (d.factor i).faithful with h3 | h5 | h9 | h27
    · have hh := Nat.card_congr h3.kernel_equiv.some.toEquiv
      rw [hcKernel] at hh
      norm_num at hh
    · have hh := Nat.card_congr h5.kernel_equiv.some.toEquiv
      rw [hcKernel] at hh
      norm_num at hh
    · exact h9
    · have hh := h27.card_kernel
      omega
  let := h9.kernel_elementary
  let : IsElementaryAbelian 3 P := he ▸ (IsElementaryAbelian.map g : IsElementaryAbelian 3 (l.kernel.map g))
  have hcF : Nat.card (d.factor i).Carrier = 18 := by
    have hh := l.kernel.card_mul_index
    rw [hcKernel,l.kernel_index_two] at hh
    omega
  have hcK : Nat.card K = 18 :=
    (Nat.card_congr (f.unique_factor_equiv d i hi).toEquiv).symm.trans hcF
  let U := subspaceCommutator a.representation ⊤ P
  have hU : (⊤ : Subgroup (J ⧸ pCore 2 J)) ≤ subspaceStabilizer a.representation U :=
    subspaceCommutator_invariant_normalizer a.representation
      (le_subspaceStabilizer a.representation ⊤ (by intros; trivial)) le_normalizer_of_normal
  let W : Subrepresentation a.representation := {
    toSubmodule := U
    apply_mem_toSubmodule := fun g _ hv => (hU (mem_top g) _).mpr hv }
  have hspan := source_rankTwo_span_decomposition hG T hempty hM hu hmany hcard e hab J hJ.1 a
  have hfW : Function.Injective W.toRepresentation :=
    ChapterD.SourceReduction.subrepresentation_faithful_of_fixed_complement a.representation a.faithful W hspan
  have hqW : cubicRatio W.toRepresentation = 2 :=
    (ChapterD.RatioDecomposition.fixed_complement_transport a.representation W hspan).1.trans hq
  have hdim : Module.finrank (ZMod 2) W.toSubmodule = 4 := by
    change Module.finrank (ZMod 2) U = 4
    rw [f.unique_factor_finrank d i hi]
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := (d.factor i).Space)
    have hh' : Nat.card (d.factor i).Space = 16 :=
      (Nat.card_congr Multiplicative.toAdd).symm.trans h9.card_module
    rw [hh',Nat.card_zmod] at hh
    exact Nat.pow_right_injective (by decide : 1 < 2) hh.symm
  have hm : subspaceCommutator W.toRepresentation ⊤ P = ⊤ := by
    apply Submodule.map_injective_of_injective U.subtype_injective
    have hh := subspaceCommutator_map_embedding a.representation W.toRepresentation
      (MonoidHom.id _) U.subtype (fun _ _ => rfl) P ⊤
    have hm := NormalOddSeed.odd_moved_self a.representation P (hnine ▸ (by decide : Odd 9))
    change subspaceCommutator a.representation U P = U at hm
    simpa only [Submodule.map_top,Submodule.range_subtype,Subgroup.map_id,hm] using hh.symm
  obtain ⟨s⟩ := ChapterD.FittingConfigurations.supportFactors_of_nine_four_moved
    W.toRepresentation hfW P hnine hdim hm
  have hupper := ChapterD.CyclicSource.SmallThree.two_supports_card_dvd_seventy_two
    W.toRepresentation hfW P s
  have hlower : 18 ∣ Nat.card (J ⧸ pCore 2 J) := hcK ▸ K.card_subgroup_dvd_card
  have hneq : Nat.card (J ⧸ pCore 2 J) ≠ 18 := by
    intro h18
    have hrange : g.range = ⊤ := by
      have hr : g.range = K := f.unique_factor_actor d i hi
      rw [hr]
      exact eq_top_of_card_eq K (hcK.trans h18.symm)
    have honto : Function.Surjective g := MonoidHom.range_eq_top.mp hrange
    obtain ⟨B,hBn,hBP,hBc⟩ := nine_endpoint_normal_cubic l h9
    let := hBn
    let : (B.map g).Normal := hBn.map g honto
    obtain ⟨_,_,_,_,_,hmin⟩ := source_solvable_minimal_elementary_residual
      hG T hempty hM hu hmany hcard e hab J hJ hs
    have hcB : Nat.card (B.map g) = 3 := (card_map_of_injective hg).trans hBc
    rcases hmin (B.map g) inferInstance ((map_mono hBP).trans_eq he) with hz | hz
    · rw [hz,card_bot] at hcB
      omega
    · rw [hz,hnine] at hcB
      omega
  have hcG : Nat.card (J ⧸ pCore 2 J) = 36 := by
    obtain ⟨n,hn⟩ := hlower
    have hd : n ∣ 4 := by
      apply (Nat.mul_dvd_mul_iff_left (by decide : 0 < 18)).mp
      simpa only [hn] using hupper
    have hnpos : 0 < n := by have := Nat.card_pos (α := J ⧸ pCore 2 J); omega
    have hnle : n ≤ 4 := Nat.le_of_dvd (by decide) hd
    interval_cases n
    · omega
    · omega
    · norm_num at hd
    · have hS := ChapterD.CyclicSource.nine_sylow_card_le_four hfW P hnine hdim hm hqW
        (Classical.choice (inferInstance : Nonempty (Sylow 2 (J ⧸ pCore 2 J))))
      rw [Sylow.card_eq_multiplicity,hn] at hS
      norm_num only [show 18*4=72 from rfl,show Nat.factorization 72 2 = 3 from by decide +kernel] at hS
  refine ⟨hcG,?_⟩
  intro S
  have hcS : Nat.card S = 4 := by rw [Sylow.card_eq_multiplicity,hcG]; decide +kernel
  have hnot : ¬ IsElementaryAbelian 2 S :=
    fun hS => no_elementary_four_of_four_dimensional_cubicRatio_two W.toRepresentation hdim hqW (S : Subgroup _) hS hcS
  refine ⟨?_,hcS⟩
  by_contra hn
  apply hnot
  let : IsMulCommutative S := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hcS
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro b
  have hd := orderOf_dvd_natCard b
  rw [hcS] at hd
  have h4 : orderOf b ≠ 4 := fun h => hn (isCyclic_of_orderOf_eq_card b (h.trans hcS.symm))
  have hdiv : orderOf b ∣ 2 := by
    obtain ⟨i,hi,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show orderOf b ∣ 2^2 by simpa using hd)
    rw [he]
    interval_cases i <;> norm_num at he h4 ⊢; omega
  exact orderOf_dvd_iff_pow_eq_one.mp hdiv
/-- Every nontrivial elementary subgroup of the literal nine quotient has order two. -/
theorem source_singleton_nine_elementary_card_two
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hone : Nat.card d.Index = 1)
    (hnine : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9)
    (A : Subgroup (J ⧸ pCore 2 J)) [IsElementaryAbelian 2 A] (hne : A ≠ ⊥) :
    Nat.card A = 2 := by
  obtain ⟨S,hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  let := (source_singleton_nine_quotient_structure hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d hd hone hnine).2 S |>.1
  let : IsCyclic A := isCyclic_of_injective (inclusion hAS) (inclusion_injective hAS)
  have hd := IsElementaryAbelian.exponent_dvd_p (p := 2) (G := A)
  rw [IsCyclic.exponent_eq_card] at hd
  exact ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left (fun hc => hne (card_eq_one.mp hc))

/-- At every original critical endpoint, the conjugate span has image of
order two and intersects the original two-core in index two. -/
theorem source_singleton_nine_critical_image
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hone : Nat.card d.Index = 1)
    (hnine : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis
      hG T hempty hM hu hmany hcard e hab J hJ.1
    ∀ i : h.CriticalEndpoint,
      Nat.card (((i.conjugate D.UH).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) = 2 ∧
        (i.conjugate D.UH ⊓ D.QH).relIndex (i.conjugate D.UH) = 2 := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis
    hG T hempty hM hu hmany hcard e hab J hJ.1
  obtain ⟨hq,hb,_,_⟩ := source_singleton_nine_critical_reciprocity
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine
  change ∀ i : h.CriticalEndpoint, _
  intro i
  let A := i.conjugate D.UH
  have hAJ : A ≤ J := i.large_le hb
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)›
  have hA : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  let := hA
  let B := A.subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hAJ
  let : IsElementaryAbelian 2 (B.map q) := IsElementaryAbelian.map q
  have hne : B.map q ≠ ⊥ := by
    intro hz
    have hBQ : B ≤ pCore 2 J := by
      rw [←QuotientGroup.ker_mk' (pCore 2 J)]
      exact (Subgroup.map_eq_bot_iff B).mp hz
    have hAQ : A ≤ D.QH := by
      intro x hx
      exact ⟨⟨x,hAJ hx⟩,hBQ hx,rfl⟩
    exact source_rankTwo_critical_core_escape_of_ratio_two
      hG T hempty hM hu hmany hcard e hab J hJ.1 a hq i hAQ
  have hc := source_singleton_nine_elementary_card_two hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d hd hone hnine (B.map q) hne
  refine ⟨hc,?_⟩
  have hi := relIndex_ker B q
  rw [QuotientGroup.ker_mk',hc] at hi
  have hm := relIndex_map_map_of_injective (pCore 2 J) B J.subtype_injective
  rw [map_subgroupOf_eq_of_le hAJ] at hm
  change D.QH.relIndex A = (pCore 2 J).relIndex B at hm
  exact (inf_relIndex_left A D.QH).trans (hm.trans hi)
/-- The original odd-core reduction retains quotient order36, cyclic Sylow4,
and image order2 at the same reciprocal critical endpoint in its nine branch. -/
theorem source_oddCore_counterexample_nine_quotient_reduction
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hne : pPrimeCore 2 (H ⧸ pCore 2 H) ≠ ⊥) :
    ∃ (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M),
      J ≤ H ∧ Group.IsSolvable J ∧
      ∃ _hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J),
      ∃ a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T),
      ∃ f : ChapterD.RatioDecomposition.FactorData a.representation
          (ChapterD.Jhat a.representation)
          (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))),
      ∃ d : ChapterD.RatioDecomposition.Decomposition f.representation,
        d.FittingFull ∧
        (Nat.card d.Index = 2 ∨
          (Nat.card d.Index = 1 ∧
            (ClassificationModels.IsTheoremEModel G ∨
              ((T : Subgroup G).relIndex J = 5 ∧
                ChapterF.Source.HypothesisF11
                  ![J, sourceResidual M Mc ⊔ (T : Subgroup G)] (T : Subgroup G) ∧
                (Nat.card (conjugateSpanBy (localModule T M) J) = 32 ∨
                  Nat.card (conjugateSpanBy (localModule T M) J) = 64)) ∨
              (IsElementaryAbelian 3 (pResidual 2 (J ⧸ pCore 2 J)) ∧
                Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9 ∧
                Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤
                  (pResidual 2 (J ⧸ pCore 2 J))) = 4 ∧
                cubicRatio a.representation = 2 ∧
                Nat.card (J ⧸ pCore 2 J) = 36 ∧
                (∀ S : Sylow 2 (J ⧸ pCore 2 J), IsCyclic S ∧ Nat.card S = 4) ∧
                (let D : ChapterF.Section09.Setup G :=
                   ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
                 let h : D.Hypothesis := source_rankTwo_f9_hypothesis
                   hG T hempty hM hu hmany hcard e hab J hJ.1
                 3 ≤ h.b ∧ Odd h.b ∧
                   ∃ i : h.CriticalEndpoint,
                     i.representative ∉ Mc ∧ ¬ i.conjugate D.UH ≤ D.QH ∧
                     Nat.card (((i.conjugate D.UH).subgroupOf J).map
                       (QuotientGroup.mk' (pCore 2 J))) = 2 ∧
                     (i.conjugate D.UH ⊓ D.QH).relIndex (i.conjugate D.UH) = 2 ∧
                     ∃ j : h.CriticalEndpoint, ∀ A : Subgroup G,
                       J ≤ normalizer (A : Set G) →
                       (i.conjugate A).map (MulAut.conj j.representative).toMonoidHom = A))))) := by
  obtain ⟨J,hJ,hJH,hs,hU,a,f,d,hd,hcases⟩ :=
    source_oddCore_counterexample_singleton_reduction hG T hempty hM hu hmany hcard e hab H hH hne
  let := hU
  refine ⟨J,hJ,hJH,hs,hU,a,f,d,hd,?_⟩
  rcases hcases with htwo | ⟨hone,hcases⟩
  · exact Or.inl htwo
  refine Or.inr ⟨hone,?_⟩
  rcases hcases with hmodel | hquintic | ⟨he,hnine,hdim,hq,hb,ho,i,hi,hout,j,hj⟩
  · exact Or.inl hmodel
  · exact Or.inr (Or.inl hquintic)
  obtain ⟨horder,hSylow⟩ := source_singleton_nine_quotient_structure
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine
  obtain ⟨himage,hindex⟩ := source_singleton_nine_critical_image
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i
  exact Or.inr (Or.inr
    ⟨he,hnine,hdim,hq,horder,hSylow,hb,ho,i,hi,hout,himage,hindex,j,hj⟩)

end CFSG.Quasithin.Chapter14.Section06
