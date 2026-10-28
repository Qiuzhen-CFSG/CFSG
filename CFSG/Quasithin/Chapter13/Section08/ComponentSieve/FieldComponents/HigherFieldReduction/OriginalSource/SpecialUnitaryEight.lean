module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.ProjectiveUnitary
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.UnitaryEight.CentralCube
public import CFSG.Quasithin.Chapter13.Section07.SpanGrowth

/-!
# The original SU₃(8) exclusion through its scalar center

The true Borel lies in H intersected with M. The original overlap equality
and V₃=[V,O₂(H)] make it preserve V₃/V₁, a four-element subspace of the
literal U_H/V₁. In any binary representation, the SU₃(8) Borel's order-nine
element has cube acting trivially on that subspace. This cube generates the
full scalar center. The component is normal in H*, so its center is normal;
its fixed space is H*-invariant and contains the generating seed. The source
faithfulness then gives a contradiction.

The argument retains the special-unitary center and needs neither L₁≤K nor
natural-module recognition. The actual component equivalence transports it
to K/O₂(K), and the KL₁T reduction applies it to unrestricted original
overgroups. The remaining higher-field carriers are PSL₂(4) and SL₃(4),
with all original Borel, cubic and inverter marks preserved.
Their contradictions, the binary exclusion and final 13.8.19–21 assembly
remain with qt-d-138-fields-source. Earlier original inputs retain their
producers through qt-d-1381-source.
Source: Aschbacher–Smith 13.8.20, printed pp.954–955, using 13.7.3(6), p.936.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Matrix BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open LinearThree.Geometry
open HermitianForm.OddPrimeSylow.NormalizedOuter
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- The source Borel preserves the literal four-element seed. Its central
cube fixes the seed, and normality of the component center propagates
fixation to the entire source action, contradicting faithfulness. -/
theorem source_no_special_unitaryThree_eight_star
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁) :
    ¬ Chapter1.Section02.LocalModels.IsSU (Source.starImage H K) 3 8 := by
  intro hm
  let : (Source.starImage H K).Normal :=
    c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  let e₀ := Components.componentStarEquiv H K hKH c.component.component
  have hfield : HigherFieldAlternative (K ⧸ pCore 2 K) := by
    obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
    exact ⟨3,by decide,Or.inr (Or.inl ⟨true,Or.inr ⟨F,hF,hfin,J,hcard,hconj,⟨e₀.trans e⟩⟩⟩)⟩
  obtain ⟨_,hT,hBM,_⟩ := source_borel_alternatives c hfield
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨eK⟩⟩ := hm
  have hfixed : Nat.card {x : F // J.conj x = x} = 8 :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 3 (by decide) hcard hconj
  obtain ⟨C,hC⟩ := FormTransport.exists_standard_basis J 8 hcard hfixed
  let J' := FormTransport.standardForm J
  let e := eK.trans (FormTransport.specialEquiv J C hC)
  let Ks := Source.starImage H K
  let B := LocalBorel.borel H K (T : Subgroup G) hKH hT
  have hBH : B ≤ H := (LocalBorel.borel_le_component H K T hKH hT).trans hKH
  have hBNV : B ≤ normalizer (V : Set G) := by
    have hh : B ≤ H ⊓ M := le_inf hBH hBM
    rw [source_overlap_normalizer c] at hh
    exact hh.trans inf_le_right
  have hF9 := c.f9 H c.component.local_overgroup
  have hseed := (Section07.source_commutator_conclusions (localNaturalSetup c.localSetup)
    hF9 c.component.local_overgroup.2.1 c.noncentral_core).1
  have hBN : B ≤ normalizer (V₃ : Set G) := by
    rw [←hseed]
    intro b hb
    have hv := mem_normalizer_iff_map_conj_eq.mp (hBNV hb)
    have hq := mem_normalizer_iff_map_conj_eq.mp
      (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH
        (D := Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H) (hBH hb))
    change (Source.QH H).map (MulAut.conj b).toMonoidHom = Source.QH H at hq
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,hv]
    exact congrArg (fun Q : Subgroup G => ⁅V,Q⁆) hq
  let W := seedSpace H V₃ V₁
  let : IsElementaryAbelian 2 V₃ := IsElementaryAbelian.of_le
    (show V₃ ≤ Source.UH H V₃ from le_conjugateSpanBy V₃ H)
  have hW : Nat.card W = 4 := ParabolicMarking.seed_card_of_source_orders H V₃ V₁
    (c.localSetup.line_le_plane.trans c.localSetup.plane_le_seed)
    c.localSetup.line_card c.localSetup.seed_card
  let S := LocalBorel.sourceSylow H K (T : Subgroup G) hT
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let σ := act.representation.comp (Ks.subtype.comp e.symm.toMonoidHom)
  have hs : (pResidual 2 (normalizer (P : Set J'.specialSubgroup))).map
      (normalizer (P : Set J'.specialSubgroup)).subtype ≤ subspaceStabilizer σ W := by
    intro b hb
    have hm := TorusModels.Assembly.residualAt_map e S
    obtain ⟨k,hk,rfl⟩ := show b ∈ (TorusModels.Assembly.residualAt S).map e.toMonoidHom by
      rw [hm]; exact hb
    have hkB : k.val ∈ Source.starImage H B := by
      rw [LocalBorel.borel_star_intrinsic]
      exact ⟨k,hk,rfl⟩
    have hh := (le_subspaceStabilizer act.representation W
      (seedSpace_invariant H V₃ V₁ act B hBN)) hkB
    change ∀ v, act.representation k.val v ∈ W ↔ v ∈ W at hh
    change ∀ v, act.representation (e.symm (e k)).val v ∈ W ↔ v ∈ W
    simpa only [MulEquiv.symm_apply_apply] using hh
  have hZ := ExceptionalFields.UnitaryEight.center_fixes_four_space J' rfl hcard hfixed
    P σ W hW hs
  let Z := (center Ks).map Ks.subtype
  have hfix : W ≤ fixedSpace act.representation Z := by
    intro v hv z
    rcases z with ⟨z,hz⟩
    obtain ⟨k,hk,rfl⟩ := hz
    have hh := hZ hv (centerCongr e ⟨k,hk⟩)
    change act.representation (e.symm (e k)).val v = v at hh
    change act.representation k.val v = v
    simpa only [MulEquiv.symm_apply_apply] using hh
  have htop : fixedSpace act.representation Z = ⊤ :=
    seedSpace_generates H V₃ V₁ act _
      (fun g v hv => (fixedSpace_stable_of_normal act.representation Z (mem_top g) v).2 hv) hfix
  have hf := f9_section_faithful _ hF9 (Comparison.sourceSection act hF9.H_centralizes)
  obtain ⟨t,_,hto,htz⟩ := ExceptionalFields.UnitaryEight.sylow_borel_central_cube
    J' rfl hcard hfixed P
  have htZ : e.symm (t^3) ∈ center Ks := by
    exact (centerCongr e.symm ⟨t^3,htz ▸ mem_zpowers _⟩).property
  have he : act.representation (e.symm (t^3)).val = 1 := by
    ext v
    exact (show v ∈ fixedSpace act.representation Z from by rw [htop]; trivial)
      ⟨(e.symm (t^3)).val,⟨e.symm (t^3),htZ,rfl⟩⟩
  have he₁ : (e.symm (t^3)).val = 1 := hf (he.trans (map_one act.representation).symm)
  have ht₁ : t^3 = 1 := by
    have he₂ : e.symm (t^3) = 1 := Subtype.ext he₁
    simpa using congrArg e he₂
  have hd := orderOf_dvd_of_pow_eq_one ht₁
  rw [hto] at hd
  norm_num at hd
/-- The two remaining exceptional linear carriers retain the original local marks;
all unitary and projective degree-three alternatives are excluded. -/
theorem source_borel_exceptional_linear
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁)
    (hfield : HigherFieldAlternative (K ⧸ pCore 2 K)) :
    letI : (Source.starImage H K).Normal :=
      c.component.normal.map _ (QuotientGroup.mk'_surjective _)
    ∃ (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 (T : Subgroup G) H),
      LocalBorel.borel H K (T : Subgroup G) hKH hT ≤ M ∧
      ∃ (X : Subgroup G) (t : ((T : Subgroup G) ⊓ L : Subgroup G)),
        ((Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = one L T V₁) ∨
          (Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
            X = plus L T V₁ ∧ coreAction (zero L) ⟨t.val,L_normalizes_zero L t.property.2⟩ = 1)) ∧
        LocalBorel.CentralizingCalculation.InvertsTwoCoreQuotient X t.val ∧ V₃ = ⁅V₃,X⁆ ∧
        (ClassicalGroup.IsPSL (Source.starImage H K) 2 4 ∨
          Chapter1.Section02.LocalModels.IsSL (Source.starImage H K) 3 4) ∧
        OuterStarAction H K
          (QuotientGroup.mk' (pCore 2 H)
            ⟨t.val,c.component.local_overgroup.1.2 (mem_sup_right t.property.1)⟩) := by
  let : (Source.starImage H K).Normal :=
    c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  obtain ⟨hKH,hT,hBM,X,t,hlocal,hinv,hseed,hm,ho⟩ :=
    source_borel_exceptional_three c act hfield
  have hremaining : ClassicalGroup.IsPSL (Source.starImage H K) 2 4 ∨
      Chapter1.Section02.LocalModels.IsSL (Source.starImage H K) 3 4 := by
    rcases hm with hm | hm | hm
    · exact Or.inl hm
    · exact Or.inr hm
    · exact (source_no_special_unitaryThree_eight_star c act hm).elim
  exact ⟨hKH,hT,hBM,X,t,hlocal,hinv,hseed,hremaining,ho⟩

/-- The intrinsic component two-core quotient cannot be SU₃(8), under
exactly the preceding original source context. -/
theorem source_no_special_unitaryThree_eight
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K) :
    ¬ Chapter1.Section02.LocalModels.IsSU (K ⧸ pCore 2 K) 3 8 := by
  intro hm
  let : IsElementaryAbelian 2 (Source.UH H V₃) :=
    c.localSetup.uh_elementary c.component.local_overgroup
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  have hF9 := c.f9 H c.component.local_overgroup
  let act := Comparison.conjugationAction (c.localSetup.line_le_uh H) hF9.plus_le_H
    (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    hF9.commutator_UH_QH_le_point
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
  exact source_no_special_unitaryThree_eight_star c act
    ⟨F,hF,hfin,J,hcard,hconj,
      ⟨(Components.componentStarEquiv H K hKH c.component.component).symm.trans e⟩⟩

/-- The intrinsic higher-field component quotient is now one of the two
remaining linear carriers; the special-unitary center has been retained and excluded. -/
theorem source_higher_field_linear_list
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hfield : HigherFieldAlternative (K ⧸ pCore 2 K)) :
    ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4 ∨
      Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 4 := by
  rcases source_higher_field_exceptional_list c hfield with hm | hm | hm
  · exact Or.inl hm
  · exact Or.inr hm
  · exact (source_no_special_unitaryThree_eight c hm).elim

/-- Apply the special-unitary exclusion to each component of an unrestricted
original overgroup; H=KL₁T is supplied only inside the reduced context. -/
theorem original_no_special_unitaryThree_eight
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9 : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) :
    ¬ Chapter1.Section02.LocalModels.IsSU (K ⧸ pCore 2 K) 3 8 := by
  let c := Overgroups.context_of_original d h hF9 hcentral hcomm hH
  exact source_no_special_unitaryThree_eight (Overgroups.reducedContext c K hKH hK)

/-- The two remaining linear carriers for every component of an unrestricted
original overgroup. Its reduction to KL₁T does not change K/O₂(K). -/
theorem original_higher_field_linear_list
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9 : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hfield : HigherFieldAlternative (K ⧸ pCore 2 K)) :
    ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4 ∨
      Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 4 := by
  let c := Overgroups.context_of_original d h hF9 hcentral hcomm hH
  exact source_higher_field_linear_list (Overgroups.reducedContext c K hKH hK) hfield


end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
