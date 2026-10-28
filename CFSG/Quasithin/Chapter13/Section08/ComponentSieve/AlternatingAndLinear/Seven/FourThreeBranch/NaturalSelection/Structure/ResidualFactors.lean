module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection.Structure.ThetaImage
public import Theory.GroupTheory.PResidual.PerfectCover
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection.LocalData

/-!
# The unordered residual marking in the four-plus-three branch

The local fixing/inverting actor separates the two cubic lines of
L₁/O₂(L₁). Each coordinate subgroup of the partition stabilizer is invariant
under this actor. Pulling it back to L₁ and taking its two-residual gives an
invariant, nontrivial, proper two-perfect subgroup. The elementary-nine
residual-lift theorem therefore identifies it with L₀ or X. Residuals commute
with the surjective restriction to the coordinate subgroup, so these two
identifications give the actual permutation images. The coordinate residuals
are distinct, which fixes the unordered pair.

Only the genuine intrinsic data in `LocalResidualData`, the theta-image
equality, and containment in the partition stabilizer are used. In particular,
this helper does not need surjectivity or faithfulness of the action, or a
Sylow witness. It assumes no coordinate identification of either source
factor. The four-point factor retains its definition using O², not O₂.
The small coordinate certificates range over S₄ × S₃ and are kernel checked.

This is the residual-marking step, not the full source theorem or the later
natural-seed ordering. Source: Aschbacher–Smith, Notation 13.2.1, 13.2.2(3),
the proof of 13.7.5(7), and 13.8.24, printed pp.877–878, 938 and 958–959
(combined manuscript, 1 March 2004).
-/

open Equiv Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection.ResidualFactors

private theorem component_le_stabilizer : fourPointComponent ≤ fourThreeStabilizer := by
  intro g hg
  rw [mem_fourThreeStabilizer_iff, fourBlock_eq]
  intro i hi
  have hf := (mem_fixingSubgroup_iff S7).mp hg.2
  by_contra hn
  have hm : g i ∈ ({4, 5, 6} : Set (Fin 7)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    have : (g i).val = 4 ∨ (g i).val = 5 ∨ (g i).val = 6 := by
      have := (g i).isLt
      change ¬ (g i).val < 4 at hn
      omega
    rcases this with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  have he : g i = i := g.injective (hf _ hm)
  apply hn
  rw [he]
  exact hi

private theorem component_coordinates (p : FourThree) :
    fourThreeHom p ∈ fourPointComponent ↔ p.1 ∈ alternatingGroup (Fin 4) ∧ p.2 = 1 := by
  simp only [fourPointComponent, mem_inf, mem_fixingSubgroup_iff,
    Perm.mem_alternatingGroup, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq]
  revert p
  decide +kernel

private theorem component_normalized : fourThreeStabilizer ≤ normalizer (fourPointComponent : Set S7) := by
  apply le_normalizer_iff.mpr
  rintro g ⟨p, rfl⟩ x hx
  obtain ⟨q, rfl⟩ := component_le_stabilizer hx
  rw [← map_inv, ← map_mul, ← map_mul, component_coordinates]
  obtain ⟨hq, he⟩ := (component_coordinates q).mp hx
  constructor
  · exact (inferInstance : (alternatingGroup (Fin 4)).Normal).conj_mem _ hq _
  · simp [he]

private theorem component_le_theta : fourPointComponent ≤ fourThreeTheta := by
  let f : Perm (Fin 4) →* S7 := fourThreeHom.comp (MonoidHom.inl _ _)
  have hf : Function.Injective f := fourThreeHom_injective.comp (fun _ _ h => congrArg Prod.fst h)
  have hmap : (alternatingGroup (Fin 4)).map f ≤ fourThreeTheta := by
    rw [← Perm.closure_three_cycles_eq_alternating, MonoidHom.map_closure, closure_le]
    rintro _ ⟨a, ha, rfl⟩
    apply Subgroup.subset_closure
    exact ⟨⟨(a, 1), rfl⟩, (orderOf_injective f hf a).trans ha.orderOf⟩
  intro g hg
  obtain ⟨p, rfl⟩ := component_le_stabilizer hg
  obtain ⟨hp, he⟩ := (component_coordinates p).mp hg
  exact hmap ⟨p.1, hp, by change fourThreeHom (p.1, 1) = fourThreeHom p; rw [← he]⟩

private theorem three_le_theta : threeFactor ≤ fourThreeTheta := by
  apply zpowers_le.mpr
  exact subset_closure ⟨by decide +kernel, cycle456_isThreeCycle.orderOf⟩

private theorem theta_le_stabilizer : fourThreeTheta ≤ fourThreeStabilizer := by
  exact (closure_le _).mpr fun _ h => h.1

private theorem three_conjugate (p : FourThree) :
    fourThreeHom p * cycle456 * (fourThreeHom p)⁻¹ = cycle456 ∨
    fourThreeHom p * cycle456 * (fourThreeHom p)⁻¹ = cycle456⁻¹ := by
  revert p
  decide +kernel

private theorem three_normalized : fourThreeStabilizer ≤ normalizer (threeFactor : Set S7) := by
  apply le_normalizer_iff.mpr
  rintro g ⟨p, rfl⟩ x hx
  have hc : fourThreeHom p * cycle456 * (fourThreeHom p)⁻¹ ∈ threeFactor := by
    rcases three_conjugate p with h | h
    · rw [h]; exact mem_zpowers _
    · rw [h]; exact inv_mem (mem_zpowers _)
  have hle : threeFactor ≤ threeFactor.comap (MulAut.conj (fourThreeHom p)).toMonoidHom :=
    zpowers_le.mpr hc
  exact hle hx

private theorem three_residual : (pResidual 2 threeFactor).map threeFactor.subtype = threeFactor := by
  apply le_antisymm (map_subtype_le _)
  apply zpowers_le.mpr
  refine ⟨⟨cycle456, mem_zpowers _⟩, mem_pResidual_of_orderOf_coprime ?_, rfl⟩
  rw [← orderOf_coe, cycle456_isThreeCycle.orderOf]
  decide

private theorem cycle012_not_three : cycle012 ∉ threeFactor := by
  have hf : threeFactor ≤ fixingSubgroup S7 ({0} : Set (Fin 7)) := by
    apply zpowers_le.mpr
    apply (mem_fixingSubgroup_iff S7).mpr
    intro i hi
    have hi : i = 0 := hi
    subst i
    decide +kernel
  intro h
  have he := (mem_fixingSubgroup_iff S7).mp (hf h) 0 (by simp)
  exact (by decide +kernel : cycle012 0 ≠ 0) he

private theorem cycle456_not_component : cycle456 ∉ fourPointComponent := by
  intro h
  have he := (mem_fixingSubgroup_iff S7).mp h.2 4 (by simp)
  exact (by decide +kernel : cycle456 4 ≠ 4) he

private theorem three_ne_bot : threeFactor ≠ ⊥ := by
  intro he
  have h : cycle456 ∈ (⊥ : Subgroup S7) := he ▸ mem_zpowers cycle456
  exact cycle456_isThreeCycle.ne_one h

private theorem four_ne_bot : fourResidualFactor ≠ ⊥ := by
  intro he
  have h : cycle012 ∈ (⊥ : Subgroup S7) := he ▸ cycle012_mem_fourResidualFactor
  exact cycle012_isThreeCycle.ne_one h

private theorem three_ne_theta : threeFactor ≠ fourThreeTheta := by
  intro he
  apply cycle012_not_three
  rw [he]
  exact component_le_theta ((map_subtype_le _) cycle012_mem_fourResidualFactor)

private theorem four_ne_theta : fourResidualFactor ≠ fourThreeTheta := by
  intro he
  apply cycle456_not_component
  apply map_subtype_le (pResidual 2 fourPointComponent)
  change cycle456 ∈ fourResidualFactor
  rw [he]
  exact three_le_theta (mem_zpowers _)

private theorem factors_distinct : threeFactor ≠ fourResidualFactor := by
  intro he
  exact cycle012_not_three (he.symm ▸ cycle012_mem_fourResidualFactor)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection.ResidualFactors

open Equiv Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection.ResidualFactors
open Theory.GroupTheory.ElementaryNineMarkedResiduals
variable {G E : Type*} [Group G] [Finite G] [Group E]

private theorem image_eq_first_or_second
    (L₁ L₀ X T : Subgroup G) (d : LocalResidualData L₁ L₀ X T)
    (f : L₁ →* E) (F : Subgroup E)
    (hle : F ≤ f.range) (hn : f.range ≤ normalizer (F : Set E))
    (hτ : ∀ a : L₁, a ∈ F.comap f → L₁.normalizerMonoidHom d.actor a ∈ F.comap f)
    (hne : (pResidual 2 F).map F.subtype ≠ ⊥)
    (hproper : (pResidual 2 F).map F.subtype ≠ f.range) :
    (pResidual 2 F).map F.subtype = (L₀.subgroupOf L₁).map f ∨
    (pResidual 2 F).map F.subtype = (X.subgroupOf L₁).map f := by
  have h₀le : L₀ ≤ L₁ := le_sup_left.trans_eq d.generated
  have hXle : X ≤ L₁ := le_sup_right.trans_eq d.generated
  have hp₀ : IsPPerfect 2 (L₀.subgroupOf L₁) :=
    d.first_perfect.of_surjective (subgroupOfEquivOfLe h₀le).symm.toMonoidHom
      (subgroupOfEquivOfLe h₀le).symm.surjective
  have hpX : IsPPerfect 2 (X.subgroupOf L₁) :=
    d.second_perfect.of_surjective (subgroupOfEquivOfLe hXle).symm.toMonoidHom
      (subgroupOfEquivOfLe hXle).symm.surjective
  have hgen : L₀.subgroupOf L₁ ⊔ X.subgroupOf L₁ = ⊤ := by
    rw [← subgroupOf_sup h₀le hXle, d.generated, subgroupOf_self]
  have hp₁ : IsPPerfect 2 L₁ := by
    apply (pResidual_eq_top_iff 2 L₁).mp
    apply top_unique
    rw [← hgen]
    exact sup_le (le_pResidual_of_isPPerfect _ hp₀) (le_pResidual_of_isPPerfect _ hpX)
  have hn₀ : pCore 2 L₁ ≤ normalizer (L₀.subgroupOf L₁ : Set L₁) := by
    rw [← subgroupOf_normalizer_eq h₀le]
    intro a ha
    exact d.core_normalizes_first ⟨a, ha, rfl⟩
  have hnX : pCore 2 L₁ ≤ normalizer (X.subgroupOf L₁ : Set L₁) := by
    rw [← subgroupOf_normalizer_eq hXle]
    intro a ha
    exact d.core_normalizes_second ⟨a, ha, rfl⟩
  let N := F.comap f
  let Y := (pResidual 2 N).map N.subtype
  have hNm : N.map f = F := map_comap_eq_self hle
  have hYm : Y.map f = (pResidual 2 F).map F.subtype := by
    rw [map_embedded_pResidual, hNm]
  have hNn : N.Normal := by
    constructor
    intro a ha b
    change f (b * a * b⁻¹) ∈ F
    rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp (hn ⟨b, rfl⟩) (f a)).mp ha
  let := hNn
  have hYn : Y.Normal := inferInstance
  let := hYn
  have hYne : Y ≠ ⊥ := by
    intro he
    apply hne
    rw [← hYm, he, Subgroup.map_bot]
  have hYproper : Y ≠ ⊤ := by
    intro he
    apply hproper
    rw [← hYm, he, ← MonoidHom.range_eq_map]
  have hYτ : ∀ a ∈ Y, L₁.normalizerMonoidHom d.actor a ∈ Y := by
    let t : N →* N :=
      { toFun := fun a => ⟨L₁.normalizerMonoidHom d.actor a, hτ a a.property⟩
        map_one' := Subtype.ext (map_one _)
        map_mul' := fun a b => Subtype.ext (map_mul (L₁.normalizerMonoidHom d.actor) a.val b.val) }
    rintro a ⟨b, hb, rfl⟩
    exact ⟨t b, map_pResidual_le 2 t ⟨b, hb, rfl⟩, rfl⟩
  have he := eq_marked_of_elementaryNine d.quotient hp₁
    (L₀.subgroupOf L₁) (X.subgroupOf L₁) Y hp₀ hpX
    (isPPerfect_embedded_pResidual 2 N) hn₀ hnX
    le_normalizer_of_normal hgen d.first_card d.second_card
    (L₁.normalizerMonoidHom d.actor) d.fixes_first d.inverts_second hYτ hYne hYproper
  rcases he with he | he
  · exact Or.inl (hYm.symm.trans (congrArg (fun K : Subgroup L₁ => K.map f) he))
  · exact Or.inr (hYm.symm.trans (congrArg (fun K : Subgroup L₁ => K.map f) he))

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection.ResidualFactors
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection.ResidualFactors
open Equiv Subgroup PairsBranch.LocalRank
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem restricted_image (H L₁ Y : Subgroup G) (hLH : L₁ ≤ H) (hYL : Y ≤ L₁)
    (φ : Source.Hstar H →* S7) :
    (Y.subgroupOf L₁).map (φ.comp (starRestriction H L₁ hLH)) =
      (Source.starImage H Y).map φ := by
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨starRestriction H L₁ hLH a, ⟨inclusion hLH a, ha, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨⟨a.val, hYL ha⟩, ha, rfl⟩

/-- The intrinsic residual data identify the two literal coordinate residuals.
Only containment of the local action in the partition stabilizer is needed:
the supplied source actor already separates the two marked cubic lines. -/
public theorem markedFactors_of_localResidualData
    (H L₁ L₀ X T : Subgroup G) (hbase : L₁ ⊔ T ≤ H)
    (φ : Source.Hstar H →* S7)
    (hP : Source.starImage H (L₁ ⊔ T) ≤ fourThreeStabilizer.comap φ)
    (d : LocalResidualData L₁ L₀ X T)
    (him : (Source.starImage H L₁).map φ = fourThreeTheta) :
    MarkedFactors φ (Source.starImage H L₀) (Source.starImage H X) := by
  have hLH : L₁ ≤ H := le_sup_left.trans hbase
  let f := φ.comp (starRestriction H L₁ hLH)
  have hfr : f.range = fourThreeTheta := by
    rw [MonoidHom.range_comp, starRestriction_range, him]
  let q := φ.comp (QuotientGroup.mk' (pCore 2 H))
  have htbase : d.actor.val ∈ L₁ ⊔ T := (show T ≤ L₁ ⊔ T from le_sup_right) d.actor_mem
  let t : H := ⟨d.actor.val, hbase htbase⟩
  have ht : q t ∈ fourThreeStabilizer :=
    hP ⟨t, htbase, rfl⟩
  have heq (a : L₁) : f (L₁.normalizerMonoidHom d.actor a) = q t * f a * (q t)⁻¹ := by
    have he : inclusion hLH (L₁.normalizerMonoidHom d.actor a) =
        t * inclusion hLH a * t⁻¹ := rfl
    change q (inclusion hLH (L₁.normalizerMonoidHom d.actor a)) =
      q t * q (inclusion hLH a) * (q t)⁻¹
    rw [he, map_mul, map_mul, map_inv]
  have identify (F : Subgroup S7) (hle : F ≤ fourThreeTheta)
      (hn : fourThreeStabilizer ≤ normalizer (F : Set S7))
      (hne : (pResidual 2 F).map F.subtype ≠ ⊥)
      (hproper : (pResidual 2 F).map F.subtype ≠ fourThreeTheta) :
      (pResidual 2 F).map F.subtype = (Source.starImage H L₀).map φ ∨
      (pResidual 2 F).map F.subtype = (Source.starImage H X).map φ := by
    have h := image_eq_first_or_second L₁ L₀ X T d f F
      (hfr.symm ▸ hle) (hfr.symm ▸ (theta_le_stabilizer.trans hn))
      (fun a ha => by
        change f (L₁.normalizerMonoidHom d.actor a) ∈ F
        rw [heq]
        exact (mem_normalizer_iff.mp (hn ht) (f a)).mp ha)
      hne (hfr.symm ▸ hproper)
    simpa only [f, restricted_image H L₁ L₀ hLH (le_sup_left.trans_eq d.generated),
      restricted_image H L₁ X hLH (le_sup_right.trans_eq d.generated)] using h
  have hthree := identify threeFactor three_le_theta three_normalized
    (three_residual.symm ▸ three_ne_bot) (three_residual.symm ▸ three_ne_theta)
  rw [three_residual] at hthree
  have hfour := identify fourPointComponent component_le_theta component_normalized
    four_ne_bot four_ne_theta
  change fourResidualFactor = _ ∨ fourResidualFactor = _ at hfour
  rcases hthree with h₀ | hX <;> rcases hfour with h₀' | hX'
  · exact (factors_distinct (h₀.trans h₀'.symm)).elim
  · exact Or.inl ⟨h₀.symm, hX'.symm⟩
  · exact Or.inr ⟨h₀'.symm, hX.symm⟩
  · exact (factors_distinct (hX.trans hX'.symm)).elim

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection.ResidualFactors
