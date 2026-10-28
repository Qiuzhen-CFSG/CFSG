module
public import Theory.SpecificGroups.SL2.NormalBorelCore
public import Theory.GroupTheory.CenterlessSupplementCentralizer
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalBender
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.LinearTwo.Source
public import Theory.ElementaryAbelian.GeneratorRank

/-!
# Placement and the original linear normal-Bender witness

In a normal binary SL₂ supplement, every element of the original maximal
subgroup's two-core acts trivially on its Borel torus quotient. Concrete
semilinear rigidity makes the actor inner. The two-core-free Sylow extension
has trivial layer centralizer, so the whole maximal two-core lies in K.
The original V therefore lies in the abelian Sylow intersection. The genuine
linear pair is transported through the same inclusion K → H, retaining the
original unique maximal subgroup and its Borel marking.

Source: Aschbacher–Smith E.2.7, printed p.218, normal linear Bender case.
-/

public section
noncomputable section
open Subgroup Matrix
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
variable {H : Type*} {F : Type} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]

/-- The original maximal two-core lies in the actual normal linear supplement. -/
theorem source_linear_core_le (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hcore : pCore 2 H = ⊥)
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2^n) (e : K ≃* SL(2,F)) :
    (ChapterB.minimalParabolicMax T hP).pCoreIn 2 ≤ K := by
  have hZ : center K = ⊥ := by
    apply (center K).eq_bot_iff_forall.mpr
    intro x hx
    have hh : e x ∈ center SL(2,F) := (centerCongr e ⟨x,hx⟩).property
    rw [Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot,mem_bot] at hh
    exact e.injective (hh.trans e.map_one.symm)
  have hC : centralizer (K : Set H) = ⊥ := by
    have hCT := centralizer_le_sylow_of_centerless_supplement K T hgen hZ
    have hCp : centralizer (K : Set H) ≤ pCore 2 H :=
      le_sSup ⟨inferInstance,T.isPGroup'.to_le hCT⟩
    exact le_bot_iff.mp (hCp.trans hcore.le)
  let ep := e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F))
  have hm : ClassificationModels.IsBenderModel K :=
    .linear n hn ⟨F,inferInstance,inferInstance,hF,⟨ep⟩⟩
  obtain ⟨S,hS⟩ := T.exists_subgroupOf_eq_of_normal K
  have hB : (ChapterB.minimalParabolicMax T hP).subgroupOf K = normalizer (S : Set K) := by
    have h := (Structure.source_normal_bender_conclusions T hP K hgen hm).1
    rw [← hS] at h
    exact h
  exact ProjectiveSpecialLinearGroup.normal_borel_twoCore_le hF K ep T _
    (ChapterB.minimalParabolicMax_spec T hP).2 S hS hB hC

/-- The original elementary V has central placement and a fully marked pair
inside the same normal linear supplement. -/
theorem source_linear (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hcore : pCore 2 H = ⊥)
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2^n) (e : K ≃* SL(2,F))
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hVcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hrank : 1 < primeRank 2 V) :
    V ≤ K ∧ (∃ S : Sylow 2 K,
      (S : Subgroup K) = (T : Subgroup H).subgroupOf K ∧
      V.subgroupOf K ≤ (center S).map (S : Subgroup K).subtype) ∧
    Nonempty (LinearTwo.Witness T (ChapterB.minimalParabolicMax T hP) V n) := by
  have hVK := hVcore.trans (source_linear_core_le T hP K hgen hcore hn hF e)
  let M := ChapterB.minimalParabolicMax T hP
  obtain ⟨S,hS⟩ := T.exists_subgroupOf_eq_of_normal K
  have hVS : V.subgroupOf K ≤ (S : Subgroup K) := by rw [hS]; exact comap_mono hVT
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let se : S ≃* Multiplicative F :=
    ((S : Subgroup K).equivMapOfInjective e.toMonoidHom e.injective).trans
      (SpecialLinearGroup.sylowEquivAdditive F 2 Q).symm
  let : IsMulCommutative S := ⟨⟨fun x y => se.injective (by simp only [map_mul,mul_comm])⟩⟩
  have hVZ : V.subgroupOf K ≤ (center S).map (S : Subgroup K).subtype := by
    rw [center_eq_top,← MonoidHom.range_eq_map,range_subtype]
    exact hVS
  let ep := e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F))
  have hB : M.subgroupOf K = normalizer (S : Set K) := by
    have h := (Structure.source_normal_bender_conclusions T hP K hgen
      (.linear n hn ⟨F,inferInstance,inferInstance,hF,⟨ep⟩⟩)).1
    rw [← hS] at h
    exact h
  have hVc : 4 ≤ Nat.card V := by
    by_contra hh
    have hc : Nat.card V ≤ 2 := by
      have hp : IsPGroup 2 V := IsElementaryAbelian.isPGroup 2 V
      obtain ⟨r,hr⟩ := hp.exists_card_eq
      rw [hr]
      have hncard : 2^r < 4 := hr ▸ Nat.lt_of_not_ge hh
      have hr2 : r < 2 := by
        by_contra hh
        have := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (Nat.le_of_not_gt hh)
        omega
      interval_cases r <;> norm_num
    have hr := IsElementaryAbelian.primeRank_le_of_card_le (p := 2) (n := 1) V
      (by simpa only [pow_one] using hc)
    omega
  have hVKc : 4 ≤ Nat.card (V.subgroupOf K) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hVK).toEquiv]
    exact hVc
  obtain ⟨w⟩ := SpecialLinearGroup.TwoConjugateWitness.exists_of_equiv hF e S
    (V.subgroupOf K) hVS hVKc
  have wm := w.map K.subtype K.subtype_injective (T : Subgroup H) M hS.symm hB
  rw [map_subgroupOf_eq_of_le hVK] at wm
  exact ⟨hVK,⟨S,hS,hVZ⟩,⟨LinearTwo.of_model_witness wm⟩⟩

end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
