module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Basic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.Basic
public import Theory.ThreeSubgroups

/-!
# Local reductions for rank-one recognition

The rank-one hypothesis selects the second choice of 15.3.10. Once
`Y₊ ≤ L` and `I = LS` have been established, residual monotonicity verifies
the nontrivial-action hypothesis of 15.3.11(12), proving 15.3.29 from the
explicit earlier conclusions.

The component relation descends to the actual action quotient, where it
rules out centralization by `Y₊*`. Containment also makes `L` perfect.
Relative normality and the three-subgroup lemma then identify
`Q = [O₂(L), L]` with `[O₂(I), L]`. In the abelian cases of 15.3.31,
normalization of `DQ` propagates centralization from `Q ∩ Y₊` to its
`L`-conjugates.

These are reductions, not the classification 15.3.27–31. The component
normality and containment, marked parabolic alternatives, block recognition,
and covering-module calculation remain to be proved. In particular no
centralizer equality or symmetric-group recognition is assumed here as a
source theorem.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.27–31, printed pp.1130–1132 (PDF pp.1147–1149).
-/

@[expose] public section

open Subgroup
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration

variable {G : Type*} [Group G]

/-- The three-rank of `Y` excludes the first choice in 15.3.10.
The lower bound is supplied by the genuine residual alternatives 15.3.7. -/
theorem rank_one_choice (d : LocalData G)
    (hRank : primeRank 3 d.Yplus = 1) (hYRank : 2 ≤ primeRank 3 d.Y) :
    Chapter4.UniqueMaximalOvergroup (d.Y ⊔ d.S) d.M ∧
      d.Yplus = Stellmacher.twoResidualAmbient
        (d.Y ⊓ centralizer (d.V₁ : Set G)) := by
  rcases d.choice with heq | hcase
  · change d.Yplus = d.Y at heq
    rw [← heq, hRank] at hYRank
    omega
  · exact hcase

private theorem residual_intersection_eq [Finite G]
    {Y A I L : Subgroup G} (hA : A = Stellmacher.twoResidualAmbient (Y ⊓ I))
    (hAL : A ≤ L) (hLI : L ≤ I) :
    A = Stellmacher.twoResidualAmbient (Y ⊓ L) := by
  rw [ComponentIntersection.twoResidualAmbient_eq_map_pResidual] at hA ⊢
  have hp : IsPPerfect 2 A := hA ▸ isPPerfect_embedded_pResidual 2 (Y ⊓ I)
  have hAY : A ≤ Y := hA ▸ (map_subtype_le _).trans inf_le_left
  apply le_antisymm ?_ ((embedded_pResidual_mono 2 (inf_le_inf_left Y hLI)).trans_eq hA.symm)
  have hm := embedded_pResidual_mono 2 (le_inf hAY hAL)
  rw [(pResidual_eq_top_iff 2 A).mpr hp, ← MonoidHom.range_eq_map, range_subtype] at hm
  exact hm

/-- Both clauses of 15.3.29, after 15.3.27 has supplied containment and
`I = LS`. The hypotheses `h11_3` and `h11_12` are the indicated earlier
implications, not assumptions of the characteristic-subgroup conclusion
for this component. The residual identity needed to apply (12) is proved. -/
theorem lemma_15_3_29_of_containment [Finite G]
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hRank : primeRank 3 d.Yplus = 1) (hYRank : 2 ≤ primeRank 3 d.Y)
    (hYL : d.Yplus ≤ c.L) (hI : I = c.L ⊔ d.S)
    (hVact : ⁅d.V, d.Yplus⁆ ≠ ⊥)
    (h11_3 : (Chapter4.UniqueMaximalOvergroup (d.Y ⊔ d.S) d.M ∧
        d.Yplus = Stellmacher.twoResidualAmbient (d.Y ⊓ centralizer (d.V₁ : Set G))) →
      d.Yplus = Stellmacher.twoResidualAmbient (d.Y ⊓ I) ∧
        normalizer (d.V₁ : Set G) ≤ d.M)
    (h11_12 : ∀ J : Subgroup G, J ≤ I →
      ⁅d.V, Stellmacher.twoResidualAmbient (d.Y ⊓ J)⁆ ≠ ⊥ → ¬ J ≤ d.M →
      ∀ C : Subgroup d.S, C.Characteristic → C ≠ ⊥ →
        ¬ ((C.map d.S.subtype).subgroupOf (J ⊔ d.S)).Normal) :
    (∀ C : Subgroup d.S, C.Characteristic → C ≠ ⊥ →
      ¬ ((C.map d.S.subtype).subgroupOf I).Normal) ∧
      normalizer (d.V₁ : Set G) ≤ d.M ∧
      d.V₁ ≤ centralizer (d.Yplus : Set G) := by
  have hcase := rank_one_choice d hRank hYRank
  obtain ⟨hres, hnorm⟩ := h11_3 hcase
  have hresL := residual_intersection_eq hres hYL (component_le c)
  refine ⟨?_, hnorm, ?_⟩
  · intro C hchar hne
    rw [hI]
    exact h11_12 c.L (component_le c) (hresL ▸ hVact) c.outside C hchar hne
  · apply le_centralizer_iff.mpr
    rw [hcase.2]
    exact (map_subtype_le _).trans inf_le_right

private theorem normalizes_join_of_commutator_le {D Q L : Subgroup G}
    (hLQ : L ≤ normalizer (Q : Set G)) (hDL : ⁅D, L⁆ ≤ Q) :
    L ≤ normalizer ((D ⊔ Q : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro l hl x hx
  have hm : (D ⊔ Q).map (MulAut.conj l).toMonoidHom ≤ D ⊔ Q := by
    rw [Subgroup.map_sup]
    apply sup_le
    · rintro _ ⟨a, ha, rfl⟩
      have hc : ⁅l, a⁆ ∈ Q := hDL (by
        rw [commutator_comm]
        exact commutator_mem_commutator hl ha)
      have h := (D ⊔ Q).mul_mem (mem_sup_right hc) (mem_sup_left ha)
      change l * a * l⁻¹ ∈ D ⊔ Q
      simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using h
    · rintro _ ⟨q, hq, rfl⟩
      exact mem_sup_right ((hLQ hl q).mp hq)
  exact hm (mem_map_of_mem _ hx)

private theorem centralizes_conjugate_span {D Q L Y : Subgroup G}
    (hLQ : L ≤ normalizer (Q : Set G)) (hDL : ⁅D, L⁆ ≤ Q)
    (hQab : IsMulCommutative Q) (hDY : D ≤ centralizer (Y : Set G))
    (hgen : Q ≤ conjugateSpanBy (Q ⊓ Y) L) : D ≤ centralizer (Q : Set G) := by
  have hDQnorm := normalizes_join_of_commutator_le hLQ hDL
  have hQcent : Q ≤ centralizer (Q : Set G) :=
    le_centralizer_iff_isMulCommutative.mpr hQab
  have hstart : Q ⊓ Y ≤ centralizer ((D ⊔ Q : Subgroup G) : Set G) := by
    apply le_centralizer_iff.mpr
    exact sup_le (hDY.trans (centralizer_le inf_le_right))
      (hQcent.trans (centralizer_le inf_le_left))
  have hspan : conjugateSpanBy (Q ⊓ Y) L ≤ centralizer ((D ⊔ Q : Subgroup G) : Set G) :=
    conjugateSpanBy_le hstart
      (hDQnorm.trans (normalizer_le_normalizer_centralizer _))
  exact le_sup_left.trans (le_centralizer_iff.mp (hgen.trans hspan))

/-- The component relation survives passage to `I/C_I(U_I)`.
Both subgroups are first restricted to `I`; no ambient quotient is used. -/
theorem component_star_commutator (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hYI : d.Yplus ≤ I) :
    d.starImage I c.L = ⁅d.starImage I c.L, d.starImage I d.Yplus⁆ := by
  have hsub : c.L.subgroupOf I = ⁅c.L.subgroupOf I, d.Yplus.subgroupOf I⁆ := by
    apply map_injective I.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le (component_le c),
      map_subgroupOf_eq_of_le hYI]
    exact c.commutator_eq
  change (c.L.subgroupOf I).map (d.starMap I) = _
  rw [hsub, map_commutator]
  rfl

/-- Quasisimplicity of the actual component image makes it nontrivial. -/
theorem component_star_ne_bot (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) : d.starImage I c.L ≠ ⊥ := by
  let := c.star_quasisimple.simple
  have hn : Nontrivial (d.starImage I c.L) :=
    (QuotientGroup.mk'_surjective (center (d.starImage I c.L))).nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot _).mp hn

/-- The contradiction used for the even-parameter `SL₃` and triple-cover
cases once their centralizer calculation is established. -/
theorem component_star_not_centralizing (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hYI : d.Yplus ≤ I) :
    ¬ d.starImage I d.Yplus ≤ centralizer (d.starImage I c.L : Set (d.Star I)) := by
  intro hc
  apply component_star_ne_bot d c
  rw [component_star_commutator d c hYI]
  exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc)

/-- The subgroup `Q = [O₂(L), L]` in 15.3.31, using the intrinsic
normal two-core embedded in the ambient group. -/
def extensionCore (L : Subgroup G) : Subgroup G := ⁅L.pCoreIn 2, L⁆

private theorem extensionCore_eq_map (L : Subgroup G) :
    (⁅pCore 2 L, (⊤ : Subgroup L)⁆).map L.subtype = extensionCore L := by
  rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  rfl

/-- Every normalizer of `L` normalizes its core commutator. -/
theorem normalizes_extensionCore {X L : Subgroup G}
    (hXL : X ≤ normalizer (L : Set G)) :
    X ≤ normalizer (extensionCore L : Set G) := by
  rw [← extensionCore_eq_map]
  exact hXL.trans (normalizer_le_normalizer_characteristic_image L
    ⁅pCore 2 L, (⊤ : Subgroup L)⁆)

/-- Containment turns `L = [L,Y₊]` into perfectness of `L`. -/
theorem component_isPerfect_of_containment (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hYL : d.Yplus ≤ c.L) : Group.IsPerfect c.L := by
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm (commutator_le_self _)
  exact c.commutator_eq.le.trans (commutator_mono le_rfl hYL)

/-- The equality `Q = [O₂(I), L]` used in 15.3.31. It follows from
relative normality and perfectness, without any model-specific assumption. -/
theorem extensionCore_eq_overgroup (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hYL : d.Yplus ≤ c.L)
    (hnormal : (c.L.subgroupOf I).Normal) :
    extensionCore c.L = ⁅I.pCoreIn 2, c.L⁆ := by
  have hLI := component_le c
  have hIL : I ≤ normalizer (c.L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hLI).mp hnormal
  have hIO : I ≤ normalizer (I.pCoreIn 2 : Set G) :=
    I.le_normalizer.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hIc : I ≤ normalizer (c.L.pCoreIn 2 : Set G) :=
    hIL.trans (normalizer_le_normalizer_characteristic_image c.L (pCore 2 c.L))
  have hcore : c.L.pCoreIn 2 ≤ I.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 c.L)
      ((pCoreIn_le 2 c.L).trans hLI) hIc
  have hcomm : ⁅I.pCoreIn 2, c.L⁆ ≤ c.L.pCoreIn 2 := by
    apply le_trans ?_ (inf_pCoreIn_le_of_le 2 hLI)
    exact le_inf
      (le_normalizer_iff_commutator_le_right.mp ((pCoreIn_le 2 I).trans hIL))
      (le_normalizer_iff_commutator_le_left.mp (hLI.trans hIO))
  have hIQ := normalizes_extensionCore hIL
  have hrot : ⁅⁅I.pCoreIn 2, c.L⁆, c.L⁆ ≤ extensionCore c.L :=
    commutator_mono hcomm le_rfl
  have hrot' : ⁅⁅c.L, I.pCoreIn 2⁆, c.L⁆ ≤ extensionCore c.L := by
    rwa [commutator_comm c.L (I.pCoreIn 2)]
  have hthree := commutator_commutator_le_of_rotate_of_le_normalizer
    (hLI.trans hIQ) (hLI.trans hIQ) ((pCoreIn_le 2 I).trans hIQ) hrot' hrot
  have hperfect := Subgroup.isPerfect_iff.mp (component_isPerfect_of_containment d c hYL)
  rw [hperfect, commutator_comm] at hthree
  exact le_antisymm (commutator_mono hcore le_rfl) hthree

/-- The conjugate-generation argument for the abelian cases (1) and (2)
of C.1.34 in 15.3.31. The actual module calculation must establish `hgen`
from its hyperplane intersections and prove the commutator bound `hDL`. -/
theorem centralizes_extensionCore_of_conjugate_generation
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hQab : IsMulCommutative (extensionCore c.L))
    (hDL : ⁅I ⊓ centralizer (d.Yplus : Set G), c.L⁆ ≤ extensionCore c.L)
    (hgen : extensionCore c.L ≤
      localSpan (extensionCore c.L ⊓ d.Yplus) c.L) :
    I ⊓ centralizer (d.Yplus : Set G) ≤ centralizer (extensionCore c.L : Set G) :=
  centralizes_conjugate_span
    (normalizes_extensionCore c.L.le_normalizer) hDL hQab inf_le_right hgen

/-- Once `D` centralizes `Q`, its commutators with `L` that lie in `Q`
lie in `Z(Q) = Q ∩ C_G(Q)`. The subsequent covering-module calculation
must still eliminate this central action; it is not asserted here. -/
theorem extension_commutator_le_center
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hDL : ⁅I ⊓ centralizer (d.Yplus : Set G), c.L⁆ ≤ extensionCore c.L)
    (hDQ : I ⊓ centralizer (d.Yplus : Set G) ≤
      centralizer (extensionCore c.L : Set G)) :
    ⁅I ⊓ centralizer (d.Yplus : Set G), c.L⁆ ≤
      extensionCore c.L ⊓ centralizer (extensionCore c.L : Set G) := by
  refine le_inf hDL ?_
  exact (commutator_mono hDQ le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp
      ((normalizes_extensionCore c.L.le_normalizer).trans
        (normalizer_le_normalizer_centralizer _)))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration

end
