module
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalBender
public import BenderSuzuki.External.Huppert.II.theorem_10_13
public import Theory.GroupTheory.SimplePairSolvability
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormSylow

/-!
# Solvable Sylow overgroups of Bender component joins

The intrinsic Bender quotient is the component image modulo the ambient
two-core. In that quotient, a normal component is a normal supplement;
a component with two conjugates gives an exchanged simple pair. Concrete
rank-one Borels make every proper Sylow overgroup solvable in both cases.
The ambient two-core lies in the Sylow, so properness and solvability lift
through the literal quotient map.

Source: Aschbacher--Smith 10.3.3, printed p.756, using 1.2.1(3) and F.1.3(1).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Bender
open ChapterF.Source
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem bender_simple (h : ClassificationModels.IsBenderModel G) : IsSimpleGroup G := by
  have four_le {n : ℕ} (hn : 2 ≤ n) : 4 ≤ 2 ^ n :=
    (by norm_num : 4 = 2 ^ 2) ▸ Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn
  cases h with
  | linear n hn h =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
    let := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := F) (hF ▸ four_le hn)
    exact e.isSimpleGroup
  | unitary n hn h =>
    obtain ⟨F, _, _, J, hF, hc, ⟨e⟩⟩ := h
    have hf := Unitary.fixed_card J n (by omega) hF hc
    let := BenderSuzuki.External.huppert_II_10_13 J (2 ^ n)
      (by have := four_le hn; omega) hF hf
    exact e.isSimpleGroup
  | suzuki m hm h =>
    obtain ⟨e⟩ := h
    let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).1
    exact e.isSimpleGroup

private theorem bender_sylow_interval (S : Sylow 2 G) (A : Subgroup G)
    (hs : A.IsSubnormal) (hm : ClassificationModels.IsBenderModel A) :
    Order.HasUniqueMaximalOver (A ⊓ (S : Subgroup G)) A ∧
    A ⊓ (S : Subgroup G) ≠ ⊥ ∧
    ∀ P : Subgroup G, A ⊓ (S : Subgroup G) ≤ P → P < A → Group.IsSolvable P := by
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_subnormal A hs
  have hf := ChapterE.Structure.bender_sylow_facts hm R
  have hRm : (R : Subgroup A).map A.subtype = (S : Subgroup G) ⊓ A := by
    rw [hR,subgroupOf_map_subtype]
  have hb := rankOneBorelFacts_of_sylow A (S : Subgroup G) R hRm hf
  have hSB : A ⊓ (S : Subgroup G) ≤ borel A (S : Subgroup G) := by
    change _ ≤ A ⊓ normalizer (((S : Subgroup G) ⊓ A : Subgroup G) : Set G)
    exact le_inf inf_le_left (by simpa only [inf_comm A] using ((S : Subgroup G) ⊓ A).le_normalizer)
  have hc : borel A (S : Subgroup G) ⋖ A := by
    refine ⟨hb.proper,?_⟩
    intro P hBP hPA
    exact hBP.not_ge (hb.unique_maximal P (by simpa only [inf_comm A] using hSB.trans hBP.le) hPA)
  refine ⟨⟨hSB.trans_lt hb.proper, _, ⟨hSB,hc⟩, ?_⟩, ?_, ?_⟩
  · intro P hP
    have hPB := hb.unique_maximal P (by simpa only [inf_comm A] using hP.1) hP.2.lt
    exact ((hP.2.eq_or_eq hPB hb.proper.le).resolve_right hb.proper.ne).symm
  · intro he
    have hRbot : (R : Subgroup A) = ⊥ := by
      apply (map_eq_bot_iff_of_injective _ A.subtype_injective).mp
      rw [hRm,inf_comm,he]
    have h := hf.proper.ne
    change normalizer ((R : Subgroup A) : Set A) ≠ ⊤ at h
    rw [hRbot] at h
    exact h (normalizer_eq_top (⊥ : Subgroup A))
  · intro P hSP hPA
    let := hb.solvable
    exact Group.isSolvable_of_isSolvable_injective
      (f := inclusion (hb.unique_maximal P (by simpa only [inf_comm A] using hSP) hPA))
      (inclusion_injective _)

private theorem bender_simple_pair_overgroup (S : Sylow 2 G) (A : Subgroup G)
    (hA : A.IsCComponent) (hm : ClassificationModels.IsBenderModel A)
    (hi : (normalizer (A : Set G)).index = 2)
    (V : Subgroup G) (hSV : (S : Subgroup G) ≤ V)
    (hV : V < A ⊔ (S : Subgroup G)) : Group.IsSolvable V := by
  have hs : ¬ (S : Subgroup G) ≤ normalizer (A : Set G) := by
    intro hs
    have hd := index_dvd_of_le hs
    rw [hi] at hd
    exact S.not_dvd_index hd
  obtain ⟨s,hs,hsn⟩ := Set.not_subset.mp hs
  let B := A.map (MulAut.conj s).toMonoidHom
  have hne : B ≠ A := fun he => hsn (mem_normalizer_iff_map_conj_eq.mpr he)
  have hB : B.IsCComponent := hA.map_equiv (MulAut.conj s)
  have hmB : ClassificationModels.IsBenderModel B :=
    hm.of_mulEquiv ((MulAut.conj s).subgroupMap A).symm
  let := bender_simple hm
  let := bender_simple hmB
  let := hA.perfect
  have hc : B ≤ centralizer (A : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (by
      rw [commutator_comm]
      exact simple_subnormal_commute_of_ne A B hA.subnormal hB.subnormal hne.symm)
  obtain ⟨huA,hneA,hsolA⟩ := bender_sylow_interval S A hA.subnormal hm
  obtain ⟨huB,hneB,hsolB⟩ := bender_sylow_interval S B hB.subnormal hmB
  have horbit := fun g (_ : g ∈ (S : Subgroup G)) =>
    NormPair.conjugate_eq_or_eq_of_normalizer_index_two hi hne g
  have hperm := conjugate_pair_permutation A B (S : Subgroup G) hne.symm horbit s hs rfl
  have hBsup : B ≤ A ⊔ (S : Subgroup G) := by
    rintro x ⟨a,ha,rfl⟩
    exact (A ⊔ (S : Subgroup G)).mul_mem
      ((A ⊔ (S : Subgroup G)).mul_mem (mem_sup_right hs) (mem_sup_left ha))
      ((A ⊔ (S : Subgroup G)).inv_mem (mem_sup_right hs))
  have hsup : (A ⊔ B) ⊔ (S : Subgroup G) = A ⊔ (S : Subgroup G) :=
    le_antisymm (sup_le (sup_le le_sup_left hBsup) le_sup_right)
      (sup_le_sup le_sup_left le_rfl)
  let : Group.IsNilpotent S := S.isPGroup'.isNilpotent
  exact isSolvable_of_simple_pair_proper_overgroup A B (S : Subgroup G) V
    hc huA huB hneA hneB hperm ⟨s,hs,rfl⟩ hsolA hsolB hSV (hsup.symm ▸ hV)

private theorem bender_model_overgroup (S : Sylow 2 G) (A : Subgroup G)
    (hA : A.IsCComponent) (hm : ClassificationModels.IsBenderModel A)
    (hidx : A.Normal ∨ (normalizer (A : Set G)).index = 2)
    (V : Subgroup G) (hSV : (S : Subgroup G) ≤ V)
    (hV : V < A ⊔ (S : Subgroup G)) : Group.IsSolvable V := by
  rcases hidx with hn | hi
  · let := hn
    let : Group.IsNilpotent S := S.isPGroup'.isNilpotent
    have hsol := (bender_sylow_interval S A hA.subnormal hm).2.2
    exact isSolvable_proper_overgroup_of_normalizes A (S : Subgroup G) V
      le_normalizer_of_normal hsol hSV hV
  · exact bender_simple_pair_overgroup S A hA hm hi V hSV hV

/-- Both local component alternatives yield solvability in the original
Sylow interval; the intrinsic two-core quotient is the actual model. -/
theorem bender_component_proper_overgroup_solvable
    (S : Sylow 2 G) (A : Subgroup G) (hA : A.IsCComponent)
    (hm : ClassificationModels.IsBenderModel (A ⧸ pCore 2 A))
    (hidx : A.Normal ∨ (normalizer (A : Set G)).index = 2)
    (V : Subgroup G) (hSV : (S : Subgroup G) ≤ V)
    (hV : V < A ⊔ (S : Subgroup G)) : Group.IsSolvable V := by
  let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
  let q := QuotientGroup.mk' (pCore 2 G)
  let Abar := A.map q
  let Sbar := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let Vbar := V.map q
  have hAb : Abar.IsCComponent := hA.map_quotient (pCore 2 G)
  have hmb : ClassificationModels.IsBenderModel Abar :=
    hm.of_mulEquiv (cComponentTwoCoreQuotientEquiv hA).symm
  have hNP : pCore 2 G ≤ V := (pCore_isPGroup.le_sylow_of_normal S).trans hSV
  have hpre : Vbar.comap q = V := by
    rw [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hNP]
  have hVb : Vbar < Abar ⊔ (Sbar : Subgroup (G ⧸ pCore 2 G)) := by
    change V.map q < A.map q ⊔ (S : Subgroup G).map q
    rw [← Subgroup.map_sup]
    refine lt_of_le_of_ne (map_mono hV.le) ?_
    intro he
    have hle : A ⊔ (S : Subgroup G) ≤ Vbar.comap q := map_le_iff_le_comap.mp he.ge
    rw [hpre] at hle
    exact hV.not_ge hle
  have hSVb : (Sbar : Subgroup (G ⧸ pCore 2 G)) ≤ Vbar := map_mono hSV
  have hidxb : Abar.Normal ∨ (normalizer (Abar : Set (G ⧸ pCore 2 G))).index = 2 := by
    rcases hidx with hn | hi
    · exact Or.inl (Subgroup.Normal.map hn q (QuotientGroup.mk'_surjective _))
    · exact Or.inr ((cComponent_normalizer_index_quotient hA (pCore 2 G)).trans hi)
  let := bender_model_overgroup Sbar Abar hAb hmb hidxb Vbar hSVb hVb
  let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  have hsol := isSolvable_comap_of_solvable_ker q Vbar
  rwa [hpre] at hsol

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Bender
