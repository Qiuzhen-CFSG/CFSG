module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape.LinearThree.Covers
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape.LinearThree.Actors
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted.Source
public import Theory.SpecificGroups.PSL3.FullTorusGraphEscape.Borel

/-!
# Full-Hall escape in the linear three graph row

An actual Hall actor preserving the prescribed odd subgroup induces a graph
actor on the marked PSL₃ quotient. The scalar lift and Borel graph calculation
produce normalizer escape, which lifts through the original two-core quotient.
Source: Aschbacher–Smith 4.4.13(1), printed pp.623–624.
-/
public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape
open MarkedModels MarkedModels.DiagramHall ChapterB
open Matrix.PSL3 Matrix.PSL3.LinearThree
variable {X : Type*} [Group X] [Finite X]
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Every prescribed odd-primary subgroup permuting with the original Sylow
subgroup escapes the maximal subgroup in the marked linear graph row. -/
theorem linear_original_escape_all_odd {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2^n)
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X)
    (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hc : SingleClauses (minimalParabolicMax S hP) K S)
    (e : sourceImage (minimalParabolicMax S hP) K ≃* PSL(3,F))
    (he : (componentOverlap (minimalParabolicMax S hP) K).map e.toMonoidHom = borel F)
    (hm : MovesDiagram (minimalParabolicMax S hP) K S e (pointParabolic F) (lineParabolic F))
    (Y A : Subgroup X) (hYM : Y ≤ minimalParabolicMax S hP)
    (hHall : IsHallSubgroup oddPrimes (Y.subgroupOf (minimalParabolicMax S hP)))
    (hAY : A ≤ Y) (hperm : (A : Set X) * (S : Set X) = (S : Set X) * (A : Set X))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hA : IsPGroup p A) :
    ¬ normalizer (A : Set X) ≤ minimalParabolicMax S hP := by
  let M := minimalParabolicMax S hP
  let q := QuotientGroup.mk' (pCore 2 X)
  let qJ := QuotientGroup.mk' (sourceKernel M)
  let : K.Normal := single_component_normal S hK hc
  let : (sourceImage M K).Normal := LinearThree.single_sourceImage_normal S hK hc
  let : (actorImage K).Normal := (single_component_normal S hK hc).map q
    (QuotientGroup.mk'_surjective _)
  have hAK : A ≤ K := by
    rw [← single_component_eq_twoResidual S hK hc]
    intro a ha
    apply mem_pResidual_of_orderOf_coprime
    simpa only [Subgroup.orderOf_mk] using
      (hA.orderOf_coprime hp.coprime_two_right (⟨a,ha⟩ : A)).symm
  obtain ⟨t,htS,htY,htA,htD,htB,htU,htout⟩ :=
    LinearThree.exists_hall_diagram_actor hn hF S hP K hK hc e he hm
      Y A hYM hHall hAY hperm
  let α : MulAut (actorImage K) := MulAut.conjNormal (q t)
  let β : MulAut PSL(3,F) := LinearThree.sourceModelAction M K e t
  let r := e.toMonoidHom.comp (linearSourceComparison S hP K)
  have hr : Function.Surjective r :=
    e.surjective.comp (linearSourceComparison_surjective S hP K)
  obtain ⟨k,hks,hk⟩ := linear_source_scalar_lift hn hF S hP K hK hqK e
  let Aq : Subgroup (actorImage K) := (A.map q).subgroupOf (actorImage K)
  have hAqK : A.map q ≤ actorImage K := map_mono hAK
  have hpre : (borel F).comap r = (M.map q).subgroupOf (actorImage K) :=
    Inverted.comparison_borel_preimage S hP K e _ he
  have hAqB : Aq ≤ (borel F).comap r := by
    rw [hpre]
    intro a ha
    exact map_mono (hAY.trans hYM) ha
  have hAq : IsPGroup p Aq := (hA.map q).comap_subtype
  have hstable : Aq.map α.toMonoidHom = Aq := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨a,ha,rfl⟩
      have htq : q t ∈ normalizer (A.map q : Set _) :=
        A.le_normalizer_map q (mem_map_of_mem q htA)
      change q t * (a : X ⧸ pCore 2 X) * (q t)⁻¹ ∈ A.map q
      exact (mem_normalizer_iff.mp htq a).mp ha
    · exact le_of_eq (card_map_of_injective (K := Aq)
        (f := α.toMonoidHom) α.injective).symm
  have hcomm : ∀ a, r (α a) = β (r a) := by
    intro a
    change e (linearSourceComparison S hP K (α a)) =
      LinearThree.sourceModelAction M K e t (e (linearSourceComparison S hP K a))
    rw [LinearThree.sourceModelAction_apply]
    apply congrArg e
    apply Subtype.ext
    change QuotientGroup.map (pCore 2 X) (sourceKernel M) (MonoidHom.id X)
      (twoCore_le_sourceKernel S hP) (q t * (a : X ⧸ pCore 2 X) * (q t)⁻¹) =
      qJ t * _ * (qJ t)⁻¹
    simp only [map_mul, map_inv]
    rfl
  have hesc := FullTorusGraphEscape.normalizer_escape_of_borel_graph_stable hn hF
    r hr k hks hk α β hcomm htU htout hp Aq hAq hAqB hstable
  have hout : ¬ normalizer (A.map q : Set _) ≤ M.map q := by
    intro hN
    apply hesc
    rw [hpre]
    intro a ha
    have hh := Aq.le_normalizer_map (actorImage K).subtype
      (mem_map_of_mem (actorImage K).subtype ha)
    have hmap : Aq.map (actorImage K).subtype = A.map q := map_subgroupOf_eq_of_le hAqK
    rw [hmap] at hh
    exact hN hh
  have hq : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  exact Theory.GroupTheory.normalizer_not_le_of_two_kernel q
    (QuotientGroup.mk'_surjective _) hq M A hp hA hout

/-- The literal full-Hall generation conclusion in the linear three graph row. -/
theorem linear_original_generation {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2 ^ n)
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X)
    (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hc : SingleClauses (minimalParabolicMax S hP) K S)
    (e : sourceImage (minimalParabolicMax S hP) K ≃* PSL(3, F))
    (he : (componentOverlap (minimalParabolicMax S hP) K).map e.toMonoidHom = borel F)
    (hm : MovesDiagram (minimalParabolicMax S hP) K S e (pointParabolic F) (lineParabolic F))
    (Y : Subgroup X) (hYM : Y ≤ minimalParabolicMax S hP)
    (hHall : IsHallSubgroup oddPrimes (Y.subgroupOf (minimalParabolicMax S hP)))
    (p : ℕ) (hp : p.Prime) (A : Subgroup X) (hA : IsElementaryAbelian p A)
    (hAY : A ≤ Y) (hperm : (A : Set X) * (S : Set X) = (S : Set X) * (A : Set X)) :
    minimalParabolicMax S hP ⊔ normalizer (A : Set X) = ⊤ := by
  by_cases hbot : A = ⊥
  · rw [hbot, normalizer_eq_top, sup_top_eq]
  let : Fact p.Prime := ⟨hp⟩
  let : IsElementaryAbelian p A := hA
  have hAp : IsPGroup p A := IsElementaryAbelian.isPGroup p A
  have hYodd : Odd (Nat.card Y) := by
    have ho := OddHall.odd_hall_odd hHall
    rwa [Nat.card_congr (subgroupOfEquivOfLe hYM).toEquiv] at ho
  have hAodd : Odd (Nat.card A) := hYodd.of_dvd_nat (card_dvd_of_le hAY)
  have hpodd : Odd p := hAodd.of_dvd_nat
    (hAp.card_eq_or_dvd.resolve_left (fun hh => hbot (eq_bot_of_card_eq A hh)))
  have hesc := linear_original_escape_all_odd hn hF S hP K hK hqK hc e he hm
    Y A hYM hHall hAY hperm hpodd hAp
  apply (minimalParabolicMax_spec S hP).1.lt_iff.mp
  exact left_lt_sup.mpr hesc
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape
