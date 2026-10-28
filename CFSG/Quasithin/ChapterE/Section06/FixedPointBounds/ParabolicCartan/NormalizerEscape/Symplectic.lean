module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted.Source
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.BenderHall.Reduction
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrimary
public import Theory.GroupTheory.CyclicHallNormalizerEscape
public import Theory.SpecificGroups.SymplecticFour.FullTorusNormalizer

/-!
# Full-Hall normalizer escape in the symplectic source branch

The longest Weyl element inverts the full rank-two split torus of Sp₄ in
characteristic two. Borel conjugacy therefore gives an escaping normalizer
for every prescribed odd-primary subgroup of the Borel. The literal marked
derived carrier is transported by its proved matrix-inclusion equivalence.

The actual component image in X/O₂(X) is a perfect central cover of this
matrix model. The existing odd-primary kernel exclusion makes its kernel
coprime to the prescribed prime, so normalizer escape lifts to that image.
Lifting through the original two-core then gives escape for the original A.
The final source application retains the full Hall, elementary, permutation
and diagram data and concludes generation by M and N_X(A). Full torus
inversion makes the permutation and diagram premises unnecessary in this
particular branch.

Source: Aschbacher–Smith, E.2.2(2b), printed pp.215–216, and the symplectic
case (ii) in the proof of 4.4.13(1), printed pp.623–624.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape
open MarkedModels MarkedModels.DiagramHall ChapterB
open Theory.SpecificGroups.SymplecticFour
open scoped Pointwise
variable {X : Type*} [Group X] [Finite X]
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Escape in the actual component image modulo the two-core. The source
central cover and every odd-primary kernel obstruction are discharged. -/
theorem symplectic_actorImage_escape
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X)
    (hK : K.IsCComponent) (hc : SingleClauses (minimalParabolicMax S hP) K S)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : sourceImage (minimalParabolicMax S hP) K ≃* Sp4Derived F)
    (he : (componentOverlap (minimalParabolicMax S hP) K).map e.toMonoidHom =
      sp4DerivedBorel F)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (A : Subgroup (actorImage K))
    (hA : IsPGroup p A)
    (hAM : A ≤ ((minimalParabolicMax S hP).map
      (QuotientGroup.mk' (pCore 2 X))).subgroupOf (actorImage K)) :
    ¬ normalizer (A : Set (actorImage K)) ≤ ((minimalParabolicMax S hP).map
      (QuotientGroup.mk' (pCore 2 X))).subgroupOf (actorImage K) := by
  have hq : 2 < Nat.card F := by
    rw [hF]
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) hn
  let d := derivedEquivFull_of_card_gt_two hq
  let e' := e.trans d
  have hd : d.toMonoidHom = (commutator (Sp F)).subtype := by
    apply MonoidHom.ext
    intro x
    exact derivedEquivFull_of_card_gt_two_apply hq x
  have hdb : (sp4DerivedBorel F).map d.toMonoidHom = borel := by
    rw [hd]
    change (borel.subgroupOf (commutator (Sp F))).map (commutator (Sp F)).subtype = borel
    let : Group.IsPerfect (Sp F) := perfect_of_card_gt_two hq
    rw [subgroupOf_map_subtype, Group.IsPerfect.commutator_eq_top, inf_top_eq]
  have he' : (componentOverlap (minimalParabolicMax S hP) K).map e'.toMonoidHom = borel := by
    change (componentOverlap (minimalParabolicMax S hP) K).map
      (d.toMonoidHom.comp e.toMonoidHom) = borel
    rw [← map_map, he, hdb]
  let : Group.IsPerfect K := hK.perfect
  let : Group.IsPerfect (actorImage K) := Group.IsPerfect.ofSurjective
    (f := (QuotientGroup.mk' (pCore 2 X)).subgroupMap K)
    ((QuotientGroup.mk' (pCore 2 X)).subgroupMap_surjective K)
  let r := e'.toMonoidHom.comp (linearSourceComparison S hP K)
  have hr : Function.Surjective r := e'.surjective.comp (linearSourceComparison_surjective S hP K)
  have hk : r.ker ≤ center (actorImage K) := by
    intro a ha
    apply linearSourceComparison_central S hP K hc
    exact e'.injective (ha.trans e'.map_one.symm)
  have hp2 : p ≠ 2 := by intro hh; subst p; norm_num at hp
  have hcop : Nat.Coprime p (Nat.card r.ker) :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      (CentralCovers.OddPrimary.not_dvd_card_kernel hp2 r hr hk)
  have hpre : borel.comap r = ((minimalParabolicMax S hP).map
      (QuotientGroup.mk' (pCore 2 X))).subgroupOf (actorImage K) :=
    Inverted.comparison_borel_preimage S hP K e' _ he'
  rw [← hpre] at hAM ⊢
  apply normalizer_not_le_of_coprime_image r hr (borel.comap r) A hA hcop
  rw [map_comap_eq_self_of_surjective hr]
  exact FullTorusNormalizer.odd_normalizer_not_le_borel hq hp (A.map r) (hA.map r)
    (map_le_iff_le_comap.mpr hAM)

/-- Every prescribed odd-primary subgroup of the original maximal subgroup
has an escaping normalizer in the marked symplectic source branch. -/
theorem symplectic_original_escape_all_odd
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X)
    (hK : K.IsCComponent) (hc : SingleClauses (minimalParabolicMax S hP) K S)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : sourceImage (minimalParabolicMax S hP) K ≃* Sp4Derived F)
    (he : (componentOverlap (minimalParabolicMax S hP) K).map e.toMonoidHom =
      sp4DerivedBorel F)
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup X) (hA : IsPGroup p A) (hAM : A ≤ minimalParabolicMax S hP) :
    ¬ normalizer (A : Set X) ≤ minimalParabolicMax S hP := by
  have hAK : A ≤ K := by
    rw [BenderHall.SingleClauses.component_eq_residual hc hK]
    intro a ha
    apply mem_pResidual_of_orderOf_coprime
    simpa only [Subgroup.orderOf_mk] using
      (hA.orderOf_coprime hp.coprime_two_right (⟨a,ha⟩ : A)).symm
  let q := QuotientGroup.mk' (pCore 2 X)
  let Aq : Subgroup (actorImage K) := (A.map q).subgroupOf (actorImage K)
  have hAqK : A.map q ≤ actorImage K := map_mono hAK
  have hAqM : Aq ≤ ((minimalParabolicMax S hP).map q).subgroupOf (actorImage K) := by
    intro a ha
    exact map_mono hAM ha
  have hAq : IsPGroup p Aq := (hA.map q).comap_subtype
  have hesc := symplectic_actorImage_escape S hP K hK hc hn hF e he hp Aq hAq hAqM
  have hout : ¬ normalizer (A.map q : Set _) ≤ (minimalParabolicMax S hP).map q := by
    intro hN
    apply hesc
    intro a ha
    have hh := Aq.le_normalizer_map (actorImage K).subtype
      (mem_map_of_mem (actorImage K).subtype ha)
    rw [map_subgroupOf_eq_of_le hAqK] at hh
    exact hN hh
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  exact normalizer_not_le_of_two_kernel q (QuotientGroup.mk'_surjective _) hk
    (minimalParabolicMax S hP) A hp hA hout

/-- The symplectic branch of the literal full-Hall 4.4.13(1) generation
statement, retaining the given elementary subgroup and diagram marking. -/
theorem symplectic_original_generation
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X)
    (hK : K.IsCComponent) (hc : SingleClauses (minimalParabolicMax S hP) K S)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : sourceImage (minimalParabolicMax S hP) K ≃* Sp4Derived F)
    (he : (componentOverlap (minimalParabolicMax S hP) K).map e.toMonoidHom =
      sp4DerivedBorel F)
    (_hmove : MovesDiagram (minimalParabolicMax S hP) K (S : Subgroup X) e
      ((pointParabolic (F := F)).subgroupOf (Sp4Derived F))
      ((planeParabolic (F := F)).subgroupOf (Sp4Derived F)))
    (Y : Subgroup X) (hYM : Y ≤ minimalParabolicMax S hP)
    (hHall : IsHallSubgroup oddPrimes (Y.subgroupOf (minimalParabolicMax S hP)))
    (p : ℕ) (hp : p.Prime) (A : Subgroup X) (hA : IsElementaryAbelian p A)
    (hAY : A ≤ Y) (_hperm : (A : Set X) * (S : Set X) = (S : Set X) * (A : Set X)) :
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
  have hesc := symplectic_original_escape_all_odd S hP K hK hc hn hF e he
    hpodd A hAp (hAY.trans hYM)
  apply (minimalParabolicMax_spec S hP).1.lt_iff.mp
  exact left_lt_sup.mpr hesc

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape
