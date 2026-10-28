module
public import Theory.SpecificGroups.QuinticPermutation
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.SourceComponent.LargeRows
import all CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.SourceComponent.FourDimensional
import all CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.SourceComponent.LargeRows

/-!
# Excluding the remaining marked permutation rows

The original first factor acts by inner automorphisms on an A₇ or A₈ star
component. Its two-core has trivial image, so that image has order five.
The faithful permutation embedding of the full star quotient retains the
radical and the component marking. Radical normalizer control then gives
the forbidden mutual normalization from QuinticPermutation.

This removes both remaining marked symmetric rows while retaining all six
B.5.1 clauses. The classical comparisons, exchanged module geometry,
original index premise and p=3 assembly remain with qt-e-14615-quintic-exclusion;
earlier 14.6.12--14 discharge stays with qt-e-suitable-odd-normalizer.
The internal imports reuse the existing self-centralizing extension lemma
and alternating automorphism calculations without widening their APIs.
Source: Aschbacher--Smith 14.6.15, printed p.1035, using C.2.7 and B.5.1.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open ComponentExclusion ComponentExtraction ComponentExclusion.ContainedComparison
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)
local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))
variable (d : NormalizerGeometry (T : Subgroup G) Mc H H1 H2
      (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)
      (firstSupport a H1) (firstSupport a H2) s.critical.endpoint.representative)
    (j : SourceEscapingComponent Mc (residualClosure H Mc) d.K1 d.K2 (Mc.pCoreIn 2))

/-- Exclude the actual alternating-seven/eight star component, including
the rows in which the radical image is outer. -/
theorem source_no_large_alternating_star {n : ℕ} (hn : n = 7 ∨ n = 8)
    (e : starImage j.J (Mc.pCoreIn 2) j.J ≃* alternatingGroup (Fin n)) : False := by
  let R := Mc.pCoreIn 2
  let C := starImage j.J R j.J
  let U := starImage j.J R R
  have hi := source_component_input s d j
  have hn' : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := Or.inr (Or.inr hn)
  have hz : center C = ⊥ := small_alternating_centerless hn' e
  have ho : IsPGroup 2 (MulAut.Outer C) := small_alternating_outer_two_of_equiv hn' e
  have hin := source_first_star_inner_of_outer_two s d j ho
  let fa := (starComponentAction j.J R).comp
    (inclusion (source_first_le_common_normalizer s d j))
  have hconj : Function.Injective (MulAut.conj : C →* MulAut C) :=
    Theory.GroupTheory.conj_injective_of_center_eq_bot hz
  let ce : C ≃* MulAut.innerSubgroup C := MonoidHom.ofInjective hconj
  let f : d.K1 →* C := ce.symm.toMonoidHom.comp
    (fa.codRestrict (MulAut.innerSubgroup C) (fun x => hin ⟨x,rfl⟩))
  have hcf (x : d.K1) : MulAut.conj (f x) = fa x :=
    MonoidHom.apply_ofInjective_symm hconj _
  let g := e.toMonoidHom.comp f
  obtain ⟨k,hk,_,ha⟩ := source_component_star_quintic s d j hi.normalizes
  let y : d.K1 := ⟨k,hk⟩
  have hy : orderOf (g y) = 5 := by
    rw [show g y = e (f y) from rfl,e.orderOf_eq,
      ←orderOf_injective (MulAut.conj : C →* MulAut C) hconj,hcf]
    exact ha
  have h5 : 5 ∣ Nat.card g.range := by
    have hh := orderOf_dvd_natCard (g.rangeRestrict y)
    rw [Subgroup.orderOf_mk] at hh
    exact hy ▸ hh
  have hm := source_normalizer_geometry_residual_models s d
  obtain ⟨em⟩ := hm.2.2.1
  have hquot : Nat.card (d.K1 ⧸ pCore 2 d.K1) = 5 := by
    rw [Nat.card_congr em.toEquiv]
    simp
  have hgc := Theory.SpecificGroups.QuinticPermutation.range_card_five hn g hquot h5
  obtain ⟨b,hb,hbe⟩ := alternating_star_embedding hi (by omega) (by omega) e
  let Q := U.map b
  let P := g.range.map (alternatingGroup (Fin n)).subtype
  have hQ : IsPGroup 2 Q :=
    (((isPGroup_pCoreIn 2 Mc).comap_subtype.map (QuotientGroup.mk' (starKernel j.J R))).map b)
  let : (j.J.subgroupOf (j.J ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le j.J.le_normalizer hi.normalizes)
  let : C.Normal := Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hQne : Q ≠ ⊥ := fun he => star_radical_ne_bot (source_join_input hi)
    ((U.map_eq_bot_iff_of_injective hb).mp he)
  have hP : Nat.card P = 5 := by
    rw [show P = g.range.map (alternatingGroup (Fin n)).subtype from rfl,
      card_map_of_injective (alternatingGroup (Fin n)).subtype_injective,hgc]
  have hPe : P ≤ alternatingGroup (Fin n) := map_subtype_le _
  have hfN (x : d.K1) : (f x : StarQuotient j.J R) ∈ normalizer (U : Set _) := by
    let l := inclusion (source_first_le_common_normalizer s d j) x
    let α := starNormalizerAut j.J R l l.property.1 l.property.2
    have hα (c : C) : α c = (f x : StarQuotient j.J R) * c * (f x : StarQuotient j.J R)⁻¹ := by
      have he := starComponentAut_coe j.J R l l.property.1 l.property.2 c
      rw [←starComponentAction_apply,←show MulAut.conj (f x) = starComponentAction j.J R l from hcf x] at he
      exact he.symm
    have he : α = MulAut.conj (f x : StarQuotient j.J R) :=
      inner_on_self_centralizing C (centerless_star_centralizer s d j hz) α (f x) hα
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [←he]
    exact starNormalizerAut_image j.J R R l l.property.1 l.property.2 l.property.2
  have hPQ : P ≤ normalizer (Q : Set (Equiv.Perm (Fin n))) := by
    rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
    change (e (f x) : Equiv.Perm (Fin n)) ∈ _
    rw [←hbe]
    exact U.le_normalizer_map b (mem_map_of_mem b (hfN x))
  have hN : alternatingGroup (Fin n) ⊓ normalizer (Q : Set (Equiv.Perm (Fin n))) ≤
      normalizer (P : Set (Equiv.Perm (Fin n))) := by
    rintro σ ⟨hσ,hσN⟩
    let x : C := e.symm ⟨σ,hσ⟩
    have hx : b (x : StarQuotient j.J R) = σ := by rw [hbe]; exact congrArg Subtype.val (e.apply_symm_apply _)
    have hxN : (x : StarQuotient j.J R) ∈ normalizer (U : Set _) := by
      have hh := le_normalizer_comap b (show b (x : StarQuotient j.J R) ∈ normalizer (Q : Set _) from hx ▸ hσN)
      rwa [U.comap_map_eq_self_of_injective hb] at hh
    have hr : primeRank 5 j.J = 1 :=
      source_component_rank_one_of_star_outer_card s d j hi.normalizes
        (fun hd => by
          obtain ⟨k,hk⟩ := ho.exists_card_eq
          rw [hk] at hd
          have hh := (by decide : Nat.Prime 5).dvd_of_dvd_pow hd
          norm_num at hh)
    let := j.rank_one_normal hr
    have hxB := star_radical_normalizer_control hi ⟨x.property,hxN⟩
    have hB := source_borel_normalizes_first_actor s d j hi.normalizes
    have hfr : fa.range = (d.K1.subgroupOf
        (normalizer (j.J : Set G) ⊓ normalizer (R : Set G))).map
          (starComponentAction j.J R) := by rw [MonoidHom.range_comp,inclusion_range]
    rw [←hfr] at hB
    have hxA : MulAut.conj x ∈ normalizer (fa.range : Set (MulAut C)) :=
      hB (mem_map_of_mem MulAut.conj hxB)
    have he : (MulAut.conj : C →* MulAut C).comp f = fa := MonoidHom.ext hcf
    have hfa : fa.range = f.range.map (MulAut.conj : C →* MulAut C) := by
      rw [←MonoidHom.range_comp,he]
    have hxf : x ∈ normalizer (f.range : Set C) := by
      have hh := le_normalizer_comap (MulAut.conj : C →* MulAut C) hxA
      rwa [hfa,f.range.comap_map_eq_self_of_injective hconj] at hh
    let t := (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom
    have hP' : f.range.map t = P := by
      calc
        f.range.map t = (f.range.map e.toMonoidHom).map
            (alternatingGroup (Fin n)).subtype := (map_map _ _ _).symm
        _ = P := congrArg (map (alternatingGroup (Fin n)).subtype)
          (MonoidHom.range_comp e.toMonoidHom f).symm
    have hh := f.range.le_normalizer_map t (mem_map_of_mem t hxf)
    rw [hP'] at hh
    change (e x : Equiv.Perm (Fin n)) ∈ _ at hh
    simpa only [x,e.apply_symm_apply] using hh
  exact Theory.SpecificGroups.QuinticPermutation.no_mutual_normalizer hn Q P hQ hQne hP hPe hPQ hN

/-- The surviving classical models, retaining the actual field and component. -/
inductive RemainingClassicalQuinticRow {D : Type*} [Group D] (L : Subgroup D) : Prop
  | linearThree (F : BinaryField) (degree : ¬4 ∣ F.degree) (e : L ≃* SL(3,F.Carrier))
  | symplectic (F : BinaryField) (large : 1 < F.degree) (degree : Odd F.degree)
      (e : L ≃* Matrix.symplecticGroup (Fin 2) F.Carrier)
  | g2 (F : BinaryField) (large : 1 < F.degree) (degree : Odd F.degree)
      (field_five : 5 ∣ F.degree) (e : L ≃* Atlas.G2.Model F.Carrier)

/-- The complete source classifier now leaves only its three classical rows. -/
theorem source_component_remaining_classical_row_reduction
    (hCJ : starImage j.J (Mc.pCoreIn 2) j.J ≤
      offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((starRepresentation j.J (Mc.pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))).subtype)
      ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
        (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))))) :
    RemainingClassicalQuinticRow
      ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
        (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))) := by
  cases source_component_large_row_reduction s d j hCJ c with
  | linearThree F hd e => exact .linearThree F hd e
  | symplectic F hl hd e => exact .symplectic F hl hd e
  | g2 F hl hd h5 e => exact .g2 F hl hd h5 e
  | symmetric n hn e =>
    exact (source_no_large_alternating_star s d j hn
      ((subgroupOfEquivOfLe hCJ).symm.trans e.subgroupEquiv)).elim

/-- Retain all six original B.5.1 clauses alongside the reduced component list. -/
theorem source_component_remaining_classical_moved_rows :
    ∃ (_hCJ : starImage j.J (Mc.pCoreIn 2) j.J ≤
      offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))
      (_c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((starRepresentation j.J (Mc.pCoreIn 2)).comp
          (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))).subtype)
        ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
          (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))))),
      RemainingClassicalQuinticRow
        ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
          (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))) := by
  have hi := source_component_input s d j
  have hc := star_moved_section_from_source hi
  let c := Classical.choice hc.2
  exact ⟨hc.1,c,source_component_remaining_classical_row_reduction s d j hc.1 c⟩

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic



