module
public import CFSG.Quasithin.ChapterF.Section01.SourceFaithfulTriple
public import CFSG.Quasithin.ChapterF.Section01.SourceLocalResidual
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.Quasithin.Rank

/-!
# The reduced source pair over O₂(B)

Set S₀ = O₂(B) for the full original Borel B. Both original local
Sylows S ∩ Lᵢ lie in S₀, so replacing S by S₀ leaves the local Borels
and quotient markings unchanged. The reduced parabolics are normal in
the original parabolics and have the same two-cores. The reduced generated
group is normal in G₀, with two-group quotient; characteristic two and
trivial generated two-core pass to it. Thus the original local factors
still satisfy all six clauses of F.1.1, now with normal common Sylow S₀.

The displayed starred-Borel product is exactly the reduction in DGS85,
Part II, pp.95–96 and (15.1), p.226. Both starred factors and solvable
residuals are preserved. The overlap includes both full original odd
Borel factors. No arbitrary-pair recognition or containment is assumed.
This is the reduction preceding the Suzuki branch, Chapters 8 and 12,
used in Aschbacher–Smith F.1.12, pp.262–264.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.SuzukiContainment
variable {G : Type*} [Group G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}

@[expose] def reducedSylow (L : Fin 2 → Subgroup G) (S : Subgroup G) : Subgroup G :=
  twoCore (commonBorel L S)

private theorem normalizes_core (A : Subgroup G) :
    A ≤ normalizer (twoCore A : Set G) :=
  A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A))

theorem reducedSylow_le (h : HypothesisF11 L S) : reducedSylow L S ≤ S := by
  obtain ⟨T, hT⟩ := h.sylow_commonBorel
  exact (pCoreIn_le_sylow _ T).trans_eq hT

theorem localSylow_le_reducedSylow (h : HypothesisF11 L S) (i : Fin 2) :
    S ⊓ L i ≤ reducedSylow L S := by
  rw [← (h.rankOneBorelFacts i).twoCore_eq]
  exact pCoreIn_mono_of_normalizes (borel_le_commonBorel i)
    (h.commonBorel_normalizes_borel i)

theorem reducedSylow_inf (h : HypothesisF11 L S) (i : Fin 2) :
    reducedSylow L S ⊓ L i = S ⊓ L i :=
  le_antisymm (inf_le_inf_right _ (reducedSylow_le h))
    (le_inf (localSylow_le_reducedSylow h i) inf_le_right)

theorem reduced_borel (h : HypothesisF11 L S) (i : Fin 2) :
    borel (L i) (reducedSylow L S) = borel (L i) S := by
  unfold borel
  rw [reducedSylow_inf h i]

theorem reduced_commonBorel_le (h : HypothesisF11 L S) :
    commonBorel L (reducedSylow L S) ≤ commonBorel L S := by
  unfold commonBorel
  rw [reduced_borel h 0, reduced_borel h 1]
  exact sup_le le_sup_left ((reducedSylow_le h).trans le_sup_right)

private theorem normalizes_reducedSylow :
    commonBorel L S ≤ normalizer (reducedSylow L S : Set G) := normalizes_core _

theorem parabolic_core_le_reducedSylow (h : HypothesisF11 L S) (i : Fin 2) :
    twoCore (parabolic L S i) ≤ reducedSylow L S :=
  le_pCoreIn_of_normalizes (pCore_isPGroup.map _)
    ((h.parabolic_core_le_S i).trans le_sup_right)
    ((commonBorel_le_parabolic i).trans (normalizes_core _))

theorem reduced_parabolic_le (h : HypothesisF11 L S) (i : Fin 2) :
    parabolic L (reducedSylow L S) i ≤ parabolic L S i := by
  rw [parabolic_eq_sup_commonBorel, parabolic_eq_sup_commonBorel]
  exact sup_le_sup_left (reduced_commonBorel_le h) _

private theorem commonBorel_normalizes_reducedBorel (h : HypothesisF11 L S) :
    commonBorel L S ≤ normalizer (commonBorel L (reducedSylow L S) : Set G) := by
  unfold commonBorel
  rw [reduced_borel h 0, reduced_borel h 1]
  exact (le_inf ((le_inf (h.commonBorel_normalizes_borel 0)
    (h.commonBorel_normalizes_borel 1)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _))
    normalizes_reducedSylow).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

private theorem normalizes_reduced_parabolic (h : HypothesisF11 L S) (i : Fin 2) :
    parabolic L S i ≤ normalizer (parabolic L (reducedSylow L S) i : Set G) := by
  rw [parabolic_eq_sup_commonBorel, parabolic_eq_sup_commonBorel]
  exact sup_le (le_sup_left.trans (L i ⊔ commonBorel L (reducedSylow L S)).le_normalizer)
    ((le_inf (h.commonBorel_normalizes_local i)
      (commonBorel_normalizes_reducedBorel h)).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _))

theorem reduced_parabolic_core (h : HypothesisF11 L S) (i : Fin 2) :
    twoCore (parabolic L (reducedSylow L S) i) = twoCore (parabolic L S i) := by
  apply le_antisymm
  · exact pCoreIn_mono_of_normalizes (reduced_parabolic_le h i)
      (normalizes_reduced_parabolic h i)
  · exact le_pCoreIn_of_normalizes (pCore_isPGroup.map _)
      ((parabolic_core_le_reducedSylow h i).trans (le_sup_right.trans le_sup_left))
      ((reduced_parabolic_le h i).trans (normalizes_core _))

theorem reduced_generated_le (h : HypothesisF11 L S) :
    generated L (reducedSylow L S) ≤ generated L S :=
  sup_le le_sup_left ((reducedSylow_le h).trans le_sup_right)

private theorem normalizes_reduced_generated (h : HypothesisF11 L S) :
    generated L S ≤ normalizer (generated L (reducedSylow L S) : Set G) := by
  apply sup_le (le_sup_left.trans (generated L (reducedSylow L S)).le_normalizer)
  exact ((le_inf ((le_inf (h.S_normalizes 0) (h.S_normalizes 1)).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _))
    (le_sup_right.trans normalizes_reducedSylow)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _))

/-- The original factors satisfy F.1.1 with the smaller common two-subgroup. -/
theorem reduced_hypothesis (h : HypothesisF11 L S) :
    HypothesisF11 L (reducedSylow L S) := by
  let := h.finite_commonBorel
  let : Finite (reducedSylow L S) := Finite.of_injective
    (inclusion (show reducedSylow L S ≤ commonBorel L S from map_subtype_le _))
    (inclusion_injective _)
  refine ⟨inferInstance, pCore_isPGroup.map _, ?_, ?_, h.quotient, ?_, ?_, ?_⟩
  · exact fun i => (reducedSylow_le h).trans (h.S_normalizes i)
  · intro i
    rw [reducedSylow_inf h i]
    exact h.sylow i
  · intro i
    rw [reduced_borel h (other i)]
    exact h.cross i
  · have hc := pCoreIn_mono_of_normalizes (p := 2) (reduced_generated_le h)
      (normalizes_reduced_generated h)
    have hz : twoCore (generated L (reducedSylow L S)) = ⊥ := by
      apply le_bot_iff.mp
      simpa only [pCoreIn, twoCore, h.twoCore_free, Subgroup.map_bot] using hc
    exact (map_eq_bot_iff_of_injective _ (generated L (reducedSylow L S)).subtype_injective).mp hz
  · intro i
    let := h.finite_parabolic i
    let : Finite (parabolic L (reducedSylow L S) i) := Finite.of_injective
      (inclusion (reduced_parabolic_le h i)) (inclusion_injective _)
    let P := parabolic L S i
    let U := parabolic L (reducedSylow L S) i
    let N := U.subgroupOf P
    let : N.Normal := normal_subgroupOf_of_le_normalizer (normalizes_reduced_parabolic h i)
    have hc := normal_core_selfCentralizing
      ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp (h.characteristic_two i)) N
    apply (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2
      (subgroupOfEquivOfLe (reduced_parabolic_le h i))).mp hc

/-- The reduced overlap has its actual common Sylow subgroup normal. -/
theorem reduced_sylow_normal (h : HypothesisF11 L S) :
    ((reducedSylow L S).subgroupOf (commonBorel L (reducedSylow L S))).Normal :=
  normal_subgroupOf_of_le_normalizer
    ((reduced_commonBorel_le h).trans normalizes_reducedSylow)

/-- The overlap reduction retains the whole original odd Borel factors. -/
theorem reduced_borel_core (h : HypothesisF11 L S) :
    twoCore (commonBorel L (reducedSylow L S)) = reducedSylow L S := by
  apply le_antisymm (reducedSylow_le (reduced_hypothesis h))
  exact le_pCoreIn_of_normalizes (pCore_isPGroup.map _) le_sup_right
    ((reduced_commonBorel_le h).trans normalizes_reducedSylow)

/-- The smaller completion is normal in the original generated group. -/
theorem reduced_generated_normal (h : HypothesisF11 L S) :
    ((generated L (reducedSylow L S)).subgroupOf (generated L S)).Normal :=
  normal_subgroupOf_of_le_normalizer (normalizes_reduced_generated h)

/-- The original common two-subgroup supplements the smaller completion. -/
theorem reduced_generated_supplement (h : HypothesisF11 L S) :
    generated L (reducedSylow L S) ⊔ S = generated L S := by
  change (L 0 ⊔ L 1 ⊔ reducedSylow L S) ⊔ S = L 0 ⊔ L 1 ⊔ S
  rw [sup_assoc, sup_eq_right.mpr (reducedSylow_le h)]


/-- Both starred parabolics, and thus both intrinsic marked quotients, are unchanged. -/
theorem reduced_starredParabolic (h : HypothesisF11 L S) (i : Fin 2) :
    starredParabolic L (reducedSylow L S) i = starredParabolic L S i := by
  unfold starredParabolic
  rw [reduced_parabolic_core h i]

/-- The literal DGS reduced-Borel formula; no odd factor is removed. -/
theorem reduced_borel_product (h : HypothesisF11 L S) :
    commonBorel L (reducedSylow L S) =
      (starredParabolic L S 0 ⊓ commonBorel L S) ⊔
      (starredParabolic L S 1 ⊓ commonBorel L S) ⊔ reducedSylow L S := by
  rw [h.starredParabolic_borel_product 0, h.starredParabolic_borel_product 1]
  change borel (L 0) (reducedSylow L S) ⊔ borel (L 1) (reducedSylow L S) ⊔
    reducedSylow L S = _
  rw [reduced_borel h 0, reduced_borel h 1]
  apply le_antisymm
  · exact sup_le (sup_le (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_right)
      |>.trans le_sup_left) le_sup_right
  · exact sup_le (sup_le
      (sup_le ((parabolic_core_le_reducedSylow h 0).trans le_sup_right)
        (le_sup_left.trans le_sup_left))
      (sup_le ((parabolic_core_le_reducedSylow h 1).trans le_sup_right)
        (le_sup_right.trans le_sup_left))) le_sup_right

/-- Each reduced parabolic has exactly the original solvable residual. -/
theorem reduced_parabolic_residual (h : HypothesisF11 L S) (i : Fin 2) :
    (solvableResidual (parabolic L (reducedSylow L S) i)).map
        (parabolic L (reducedSylow L S) i).subtype =
      (solvableResidual (parabolic L S i)).map (parabolic L S i).subtype :=
  ((reduced_hypothesis h).local_residual_eq_parabolic i).symm.trans
    (h.local_residual_eq_parabolic i)

/-- The quotient of the actual generated group by the smaller generated group
is a two-group. This is relative normality in G₀, not ambient normality in G. -/
theorem reduced_generated_quotient (h : HypothesisF11 L S) :
    letI := reduced_generated_normal h
    IsPGroup 2 ((generated L S) ⧸
      (generated L (reducedSylow L S)).subgroupOf (generated L S)) := by
  let := reduced_generated_normal h
  apply isPGroup_quotient_of_sup_eq_top _ (S.subgroupOf (generated L S)) h.S_isP.comap_subtype
  rw [← subgroupOf_sup (reduced_generated_le h) (show S ≤ generated L S from le_sup_right),
    reduced_generated_supplement h]
  exact subgroupOf_self _

/-- Quasithinness of the literal source completion survives the reduction. -/
theorem reduced_quasithin [Finite G] (h : HypothesisF11 L S)
    (hqt : IsQuasithin (generated L S)) :
    IsQuasithin (generated L (reducedSylow L S)) :=
  (isQuasithin_congr
    (subgroupOfEquivOfLe (reduced_generated_le h))).mp
      (hqt.subgroup ((generated L (reducedSylow L S)).subgroupOf (generated L S)))

end CFSG.Quasithin.ChapterF.Source.SuzukiContainment
