module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.SporadicSieve
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.LocalGeneration
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowGeometry
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.SylowNormalizerReduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoFour.Adequate
public import Theory.SpecificGroups.Rudvalis.Model.SylowInvariantPair
public import Theory.SpecificGroups.Rudvalis.Model.CoreQuotients.Max4Image
public import Theory.SpecificGroups.Rudvalis.ComponentFacts

/-!
# Excluding HS, J₄ and Rudvalis from the moved-component quotient

The characteristic Sylow geometry puts the full Sylow normalizer inside
the literal HS eight-normalizer, J₄ max1, or Rudvalis max4. Their actual
quotients by two-group kernels are SL₃(2), M₂₄ and PSL₃(2), respectively.
Sylow self-normalization in these quotients lifts through the kernels and
then to the ambient carriers. Together with their proved outer two-group
bounds, this contradicts the nontrivial odd Sylow action of the original
moved component.

The source application retains the whole component two-core quotient,
the odd classical covers, both nonquasisimple alternatives, and every
A.3.6 common clause. J₂ and J₁ are the only remaining sporadic carriers.
Recognition, intersection escape and terminal geometry remain obligations
of qt-d-1222-natural-line-action.

Source: Aschbacher–Smith 3.3.12 (**), printed p.589; GLS3 Tables 5.3i,m,r.
The imported concrete local calculations retain their ATLAS provenance.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer

private theorem self_normalizing_of_equiv {H M : Type*} [Group H] [Group M] [Finite H]
    (e : H ≃* M) (hM : ∀ P : Sylow 2 M, normalizer (P : Set M) = (P : Subgroup M))
    (P : Sylow 2 H) : normalizer (P : Set H) = (P : Subgroup H) := by
  apply map_injective (f := e.toMonoidHom) e.injective
  change (normalizer ((P : Subgroup H) : Set H)).map e.toMonoidHom = _
  rw [map_equiv_normalizer_eq]
  exact hM (P.mapSurjective (f := e.toMonoidHom) e.surjective)

private theorem self_normalizing_of_one {H : Type*} [Group H] [Finite H]
    (P : Sylow 2 H) (hP : normalizer (P : Set H) = (P : Subgroup H))
    (Q : Sylow 2 H) : normalizer (Q : Set H) = (Q : Subgroup H) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H P Q
  have he : (P : Subgroup H).map (MulAut.conj g).toMonoidHom = (Q : Subgroup H) :=
    congrArg Sylow.toSubgroup hg
  change normalizer ((Q : Subgroup H) : Set H) = _
  rw [←he,←map_equiv_normalizer_eq,P.coe_coe,hP]

private theorem self_normalizing_of_two_ker {H M : Type*} [Group H] [Group M]
    [Finite H] (q : H →* M) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (hM : ∀ P : Sylow 2 M, normalizer (P : Set M) = (P : Subgroup M))
    (P : Sylow 2 H) : normalizer (P : Set H) = (P : Subgroup H) := by
  have hker : q.ker ≤ (P : Subgroup H) := hk.le_sylow_of_normal P
  apply le_antisymm _ (P : Subgroup H).le_normalizer
  have hh := (P : Subgroup H).le_normalizer_map q
  have hl : (normalizer (P : Set H)).map q ≤ (P : Subgroup H).map q := by
    have he := hM (P.mapSurjective hq)
    rw [←Sylow.coe_coe,Sylow.coe_mapSurjective] at he
    rw [←he]
    simpa only [P.coe_coe] using hh
  simpa only [comap_map_eq_self hker,P.coe_coe] using map_le_iff_le_comap.mp hl

private theorem self_normalizing_in_local {H : Type*} [Group H] [Finite H]
    (P : Sylow 2 H) (B : Subgroup H) (hPB : (P : Subgroup H) ≤ B)
    (hNB : normalizer (P : Set H) ≤ B)
    (hB : ∀ S : Sylow 2 B, normalizer (S : Set B) = (S : Subgroup B)) :
    normalizer (P : Set H) = (P : Subgroup H) := by
  apply le_antisymm _ (P : Subgroup H).le_normalizer
  intro g hg
  have hi : (⟨g,hNB hg⟩ : B) ∈ normalizer ((P : Subgroup H).subgroupOf B : Set B) := by
    rw [←subgroupOf_normalizer_eq hPB]
    exact hg
  have he := hB (P.subtype hPB)
  rw [←Sylow.coe_coe,Sylow.coe_subtype] at he
  rw [he] at hi
  exact hi

private theorem binary_three_self_normalizing (P : Sylow 2 SL(3,ZMod 2)) :
    normalizer (P : Set SL(3,ZMod 2)) = (P : Subgroup SL(3,ZMod 2)) := by
  open Theory.SpecificGroups.LinearSylowNormalizers in
    have hb : borel 3 (ZMod 2) = unipotent 3 (ZMod 2) := by
      apply le_antisymm _ (unipotent_le_borel 3 (ZMod 2))
      intro g hg
      rw [mem_unipotent]
      refine ⟨hg,fun i => ?_⟩
      have hd := g.property
      rw [Matrix.det_of_isUpperTriangular ((mem_borel 3 (ZMod 2) g).mp hg)] at hd
      have hp : (∏ j, g.val j j) ≠ 0 := by rw [hd]; exact one_ne_zero
      exact (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _
        ((Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i))
    apply self_normalizing_of_one (standardSylow 3 (ZMod 2) (by decide)) _ P
    change normalizer ((standardSylow 3 (ZMod 2) (by decide) : Subgroup SL(3,ZMod 2)) : Set SL(3,ZMod 2)) = _
    rw [coe_standardSylow,normalizer_unipotent,hb]

private theorem hs_self_normalizing (P : Sylow 2 Sporadic.LeechRelated.HS.Carrier) :
    normalizer (P : Set Sporadic.LeechRelated.HS.Carrier) = (P : Subgroup Sporadic.LeechRelated.HS.Carrier) := by
  open Sporadic.LeechRelated.HS in
    open BlockNormalizer in
      apply self_normalizing_of_one baseSylow _ P
      apply self_normalizing_in_local baseSylow baseNormalizer baseSylow_le_normalizer
      · intro g hg
        exact mem_normalizer_iff_map_conj_eq.mpr
          (baseElementary_invariant (MulAut.conj g) (mem_normalizer_iff_map_conj_eq.mp hg))
      · let q := QuotientGroup.mk' (pCore 2 baseNormalizer)
        apply self_normalizing_of_two_ker q (QuotientGroup.mk'_surjective _)
        · change IsPGroup 2 (QuotientGroup.mk' (pCore 2 baseNormalizer)).ker
          rw [QuotientGroup.ker_mk']
          exact pCore_isPGroup
        · exact self_normalizing_of_equiv LocalGeneration.secondQuotient binary_three_self_normalizing

private theorem mathieu_twentyfour_self_normalizing (P : Sylow 2 Sporadic.Mathieu.M24) :
    normalizer (P : Set Sporadic.Mathieu.M24) = (P : Subgroup Sporadic.Mathieu.M24) := by
  open Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer in
    exact le_antisymm
      (sylow_normalizer_le candidate_card (candidate_automorphisms_isPGroup candidate_card) P)
      (P : Subgroup Sporadic.Mathieu.M24).le_normalizer

private theorem janko_four_self_normalizing (P : Sylow 2 Janko4.Model) :
    normalizer (P : Set Janko4.Model) = (P : Subgroup Janko4.Model) := by
  open Janko4 Janko4.Cardinality Janko4.OuterReduction.OddIndex Janko4.Max1AmalgamRigidity in
    apply le_antisymm _ (P : Subgroup Janko4.Model).le_normalizer
    apply LocalStructure.SymmetricLinear.sylowNormalizer_le_of_max1Normalizer _
      (fun S => (mathieu_twentyfour_self_normalizing S).le) P
    intro g hg
    have hM : M.map (MulAut.conj g).toMonoidHom = M :=
      LocalStructure.max1_invariant_of_sylow_image_invariant localSylow (MulAut.conj g)
        (mem_normalizer_iff_map_conj_eq.mp hg)
    have hgM : g ∈ normalizer (M : Set Model) := mem_normalizer_iff_map_conj_eq.mpr hM
    apply LocalStructure.normalizer_embedded_localKernel_le_max1
    have hk := normalizer_le_normalizer_characteristic_image M (pCore 2 M) hgM
    rwa [←LocalStructure.localKernel_eq_twoCore matrixA_mul_self matrixB_pow_four] at hk

private theorem rudvalis_self_normalizing (P : Sylow 2 Rudvalis.Model) :
    normalizer (P : Set Rudvalis.Model) = (P : Subgroup Rudvalis.Model) := by
  open Rudvalis Rudvalis.SylowInvariantPair Rudvalis.SylowOvergroups
    Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover in
    apply self_normalizing_of_one sylow _ P
    apply self_normalizing_in_local sylow max4 localP_le_max4
    · intro g hg
      have he := elementary_two_invariant (MulAut.conj g)
        (mem_normalizer_iff_map_conj_eq.mp hg)
      have hn := mem_normalizer_iff_map_conj_eq.mpr he
      rw [←first_eq_normalizer] at hn
      exact hn
    · let q := QuotientGroup.mk' (pCore 2 max4)
      apply self_normalizing_of_two_ker q (QuotientGroup.mk'_surjective _)
      · change IsPGroup 2 (QuotientGroup.mk' (pCore 2 max4)).ker
        rw [QuotientGroup.ker_mk']
        exact pCore_isPGroup
      · exact self_normalizing_of_equiv
          (CoreQuotients.max4QuotientEquiv.trans Matrix.PSL3Two.equiv.symm)
          binary_three_self_normalizing

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c} {A : OddSupplement T}
namespace MovedComponent
variable (E : MovedComponent S f A)

/-- The HS quotient cannot support the original nontrivial odd Sylow action. -/
theorem quotient_not_higman_sims :
    ¬ Nonempty ((E.component ⧸ pCore 2 E.component) ≃* Sporadic.LeechRelated.HS.Carrier) := by
  open Sporadic.LeechRelated.HS in
    exact E.quotient_not_equiv_self_normalizing_outer_two hs_self_normalizing
      (outer_isPGroup_two_of_pointStabilizer_map pointStabilizer_map normalizer_relIndex_dvd_two_pow)

/-- Simplicity inherited from the source row supplies the actual J₄ outer bound. -/
theorem quotient_not_janko_four (hs : IsSimpleGroup (E.component ⧸ pCore 2 E.component)) :
    ¬ Nonempty ((E.component ⧸ pCore 2 E.component) ≃* Janko4.Model) := by
  rintro ⟨e⟩
  let := hs
  let : IsSimpleGroup Janko4.Model := e.symm.isSimpleGroup
  let : Group.IsPerfect (⊤ : Subgroup (E.component ⧸ pCore 2 E.component)) :=
    E.componentQuotient_isCComponent.perfect
  let : Group.IsPerfect (E.component ⧸ pCore 2 E.component) :=
    Group.IsPerfect.ofSurjective
      (f := (topEquiv : (⊤ : Subgroup (E.component ⧸ pCore 2 E.component)) ≃* _).toMonoidHom)
      topEquiv.surjective
  let : Group.IsPerfect Janko4.Model := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  exact E.quotient_not_equiv_self_normalizing_outer_two janko_four_self_normalizing
    Chapter1.XiEmbedding.OuterModels.jankoFour_outer_isPGroup_two ⟨e⟩

/-- The Rudvalis source row likewise contradicts the original odd Sylow action. -/
theorem quotient_not_rudvalis (hs : IsSimpleGroup (E.component ⧸ pCore 2 E.component)) :
    ¬ Nonempty ((E.component ⧸ pCore 2 E.component) ≃* Rudvalis.Model) := by
  rintro ⟨e⟩
  let := hs
  let : IsSimpleGroup Rudvalis.Model := e.symm.isSimpleGroup
  exact E.quotient_not_equiv_self_normalizing_outer_two rudvalis_self_normalizing
    Rudvalis.outer_isPGroup_two ⟨e⟩

end MovedComponent

open Chapter1.Section02 Chapter1.Section02.LocalModels

/-- The full source alternatives after the self-normalizing sporadic rows are
removed. Both nonquasisimple rows and the whole cubic covers are retained. -/
inductive SourceCasesAfterLargeSporadic (Q : Type*) [Group Q] [Finite Q] : Prop
  | simple (simple : IsSimpleGroup Q)
      (model : (∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ unitary : Bool, IsPSLSign Q unitary 3 p) ∨
        Nonempty (Q ≃* Sporadic.LeechRelated.J2.Carrier) ∨ Nonempty (Q ≃* Janko1.Model))
  | cover (quasisimple : IsQuasisimple Q)
      (center : Nonempty (Subgroup.center Q ≃* Multiplicative (ZMod 3)))
      (model : ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ unitary : Bool, IsSLSign Q unitary 3 p)
  | natural (data : A36Natural (⊤ : Subgroup Q))
  | nilpotent (data : A36Nilpotent (⊤ : Subgroup Q))

namespace MovedComponent
variable (E : MovedComponent S f A)

/-- The literal A.3.6 catalogue now leaves only J₂ and J₁ among sporadic
quotients; its common data and all other surviving alternatives are unchanged. -/
theorem source_cases_after_large_sporadic :
    SourceCasesAfterLargeSporadic (E.component ⧸ pCore 2 E.component) ∧
      A36Common (⊤ : Subgroup (E.component ⧸ pCore 2 E.component)) := by
  obtain ⟨hc,hcommon⟩ := E.source_cases_after_sporadic_sieve
  refine ⟨?_,hcommon⟩
  cases hc with
  | simple hs hm =>
    apply SourceCasesAfterLargeSporadic.simple hs
    rcases hm with h | ⟨name,hname,he⟩ | h
    · exact .inl h
    · rcases hname with rfl | rfl | rfl | rfl
      · exact .inr (.inl he)
      · exact (E.quotient_not_higman_sims he).elim
      · exact (E.quotient_not_rudvalis hs he).elim
      · exact (E.quotient_not_janko_four hs he).elim
    · exact .inr (.inr h)
  | cover hq hz hm => exact .cover hq hz hm
  | natural h => exact .natural h
  | nilpotent h => exact .nilpotent h

end MovedComponent

/-- Apply the exclusions to the same component supplied by the original
escaping supplement, with the full quotient and A.3.6 common clauses. -/
theorem exists_moved_component_after_large_sporadic (f : InvariantFlag c) (A : OddSupplement T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ∃ E : MovedComponent S f A,
      SourceCasesAfterLargeSporadic (E.component ⧸ pCore 2 E.component) ∧
      A36Common (⊤ : Subgroup (E.component ⧸ pCore 2 E.component)) := by
  obtain ⟨E⟩ := exists_movedComponent f A hescape
  exact ⟨E,E.source_cases_after_large_sporadic⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
