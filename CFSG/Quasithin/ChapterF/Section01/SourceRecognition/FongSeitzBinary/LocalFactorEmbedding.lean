module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UniformRoots
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RootLocalCover

/-!
# Embedding the canonical local root group in the original factor quotient

For a perfect original factor L_i, both its simple root and the reflected
root lie in the SAME marked factor image. Lift their generated group R_i
through that injective factor map and project to L_i/O₂(L_i). The original
two-core image lies in U intersect K_i; the proved (5C)(a) separation of
R_i from this radical makes the projection injective. This argument needs
no (2B) remainder-containment hypothesis.

If the simple root maps onto the original quotient Sylow, the projection
is also onto: a proper image would lie in that Sylow's unique maximal
normalizer, placing all of R_i in B, contrary to the reflected root.
The resulting equivalence retains the literal lifted representatives.
The linear companion discharges Sylow surjectivity by its proved root count.

Source: Fong--Seitz I (5C), printed pp.25--26, specialized using the
original rank-one factors of Aschbacher--Smith F.1.1--3, pp.259--260.
This is local recognition; nonlinear regularity, nonperfect factors and
the seven marked rank-two comparisons remain separate obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2)

private theorem simpleLift_mem_endpoint :
    (representative (Q.simple i) : X ⧸ Q.D) ∈ Q.tits.standardParabolic {Q.simple i} :=
  Q.tits.bruhatCell_subset_standardParabolic_of_mem (Set.mem_singleton _)
    (Q.tits.representative_mem_bruhatCell _ _ (representative_spec _))

include h in
/-- Both canonical roots lie in the same original perfect factor image. -/
theorem rankOne_le_factor (hp : Group.IsPerfect (L i)) :
    rankOne Q split i ≤ (factorMap Q e i).range := by
  apply sup_le (simpleRoot_le_factor Q e h split i hp)
  have hc := comap_mono (f := (MulAut.conj
    (representative (Q.simple i) : X ⧸ Q.D)).toMonoidHom)
    (simpleRoot_le_factor Q e h split i hp)
  change rootAt Q split i (Q.simple i) ≤ rightConjugate (factorMap Q e i).range _ at hc
  rwa [rightConjugate_eq_self _
    (factor_parabolic_normalizes Q e h i (simpleLift_mem_endpoint Q i))] at hc

include h in
/-- The original factor two-core acts trivially on the full marked panel. -/
theorem factorCore_le_localKernel :
    (pCore 2 (L i)).map (factorMap Q e i) ≤ localKernel Q i := by
  let C := (pCore 2 (L i)).map (factorMap Q e i)
  let M := Q.tits.standardParabolic {Q.simple i}
  let : (C.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer
    (factorCore_normalizes Q e h i)
  have hc : C.subgroupOf M ≤ (Q.tits.B.subgroupOf M).normalCore :=
    normal_le_normalCore.mpr (subgroupOf_mono _ (factorCore_le_borel Q e h i))
  intro x hx
  exact ⟨⟨x,Q.tits.B_le_standardParabolic _ (factorCore_le_borel Q e h i hx)⟩,
    hc hx,rfl⟩

include h in
theorem rankOne_disjoint_factorCore :
    Disjoint (rankOne Q split i) ((pCore 2 (L i)).map (factorMap Q e i)) := by
  apply (RootLocalCover.rankOne_disjoint_radical Q split i).mono_right
  exact le_inf (two_subgroup_le_unipotent split _ (pCore_isPGroup.map _)
    (factorCore_le_borel Q e h i)) (factorCore_le_localKernel Q e h i)

/-- The actual lift through the injective original factor map. -/
def rankOneLift (hp : Group.IsPerfect (L i)) : rankOne Q split i →* L i :=
  (MonoidHom.ofInjective (factorMap_injective Q e i)).symm.toMonoidHom.comp
    (inclusion (rankOne_le_factor Q e h split i hp))

@[simp] theorem factorMap_rankOneLift (hp : Group.IsPerfect (L i)) (r : rankOne Q split i) :
    factorMap Q e i (rankOneLift Q e h split i hp r) = (r : X ⧸ Q.D) :=
  congrArg Subtype.val
    ((MonoidHom.ofInjective (factorMap_injective Q e i)).apply_symm_apply
      (inclusion (rankOne_le_factor Q e h split i hp) r))

/-- Project that lift by the original two-core quotient map. -/
def rankOneProjection (hp : Group.IsPerfect (L i)) :
    rankOne Q split i →* (L i) ⧸ pCore 2 (L i) :=
  (QuotientGroup.mk' (pCore 2 (L i))).comp (rankOneLift Q e h split i hp)

@[simp] theorem rankOneProjection_apply (hp : Group.IsPerfect (L i)) (r : rankOne Q split i) :
    rankOneProjection Q e h split i hp r =
      QuotientGroup.mk' (pCore 2 (L i)) (rankOneLift Q e h split i hp r) := by rfl

theorem rankOneProjection_injective (hp : Group.IsPerfect (L i)) :
    Function.Injective (rankOneProjection Q e h split i hp) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro r hr
  have hc : rankOneLift Q e h split i hp r ∈ pCore 2 (L i) :=
    (QuotientGroup.eq_one_iff _).mp hr
  have hm : (r : X ⧸ Q.D) ∈ (pCore 2 (L i)).map (factorMap Q e i) := by
    rw [← factorMap_rankOneLift Q e h split i hp r]
    exact mem_map_of_mem _ hc
  exact Subtype.ext ((disjoint_def.mp (rankOne_disjoint_factorCore Q e h split i)) r.property hm)

@[simp] theorem rankOneProjection_simpleRoot (hp : Group.IsPerfect (L i))
    (r : simpleRoot Q split i) :
    rankOneProjection Q e h split i hp
      (inclusion (show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left) r) =
      simpleRootProjection Q e h split i hp r := by
  rw [simpleRootProjection_apply]
  apply congrArg (QuotientGroup.mk' (pCore 2 (L i)))
  apply factorMap_injective Q e i
  rw [factorMap_rankOneLift, factorMap_simpleRootLift]
  rfl

private theorem rankOne_not_le_borel : ¬ rankOne Q split i ≤ Q.tits.B := by
  intro hB
  have hc := comap_mono (f := (MulAut.conj
    (representative (Q.simple i) : X ⧸ Q.D)).toMonoidHom) hB
  change rightConjugate (rankOne Q split i) _ ≤ borelConjugate (Q.simple i) at hc
  rw [rankOne_conjugate Q split i _ (representative_spec _)] at hc
  apply simpleRoot_ne_bot Q split i
  apply eq_bot_iff.mpr
  intro x hx
  exact mem_bot.mpr ((disjoint_def.mp (simpleRoot_disjoint_conjugateBorel Q split i))
    hx (hc ((show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left) hx)))

/-- A full quotient Sylow and the reflected root force the entire original quotient. -/
theorem rankOneProjection_surjective [Finite (L i)] (hp : Group.IsPerfect (L i))
    (T : Sylow 2 (L i)) (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i)
    (hroot : Function.Surjective (simpleRootSylowProjection Q e h split i hp T hT)) :
    Function.Surjective (rankOneProjection Q e h split i hp) := by
  apply MonoidHom.range_eq_top.mp
  by_contra he
  have hTle : (quotientSylow T : Subgroup ((L i) ⧸ pCore 2 (L i))) ≤
      (rankOneProjection Q e h split i hp).range := by
    intro t ht
    obtain ⟨r,hr⟩ := hroot ⟨t,ht⟩
    refine ⟨inclusion (show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left) r, ?_⟩
    rw [rankOneProjection_simpleRoot]
    simpa only [simpleRootSylowProjection_coe] using congrArg Subtype.val hr
  have hN := (h.quotient i).rankOneSylowFacts (quotientSylow T)
  have hle := hN.unique_maximal _ hTle (lt_top_iff_ne_top.mpr he)
  apply rankOne_not_le_borel Q split i
  intro x hx
  let r : rankOne Q split i := ⟨x,hx⟩
  have hn := hle (show rankOneProjection Q e h split i hp r ∈
    (rankOneProjection Q e h split i hp).range from ⟨r,rfl⟩)
  have hn' : rankOneLift Q e h split i hp r ∈ normalizer (T : Set (L i)) := by
    change rankOneLift Q e h split i hp r ∈
      (normalizer ((quotientSylow T : Subgroup ((L i) ⧸ pCore 2 (L i))) : Set _)).comap
        (QuotientGroup.mk' (pCore 2 (L i))) at hn
    rwa [quotientSylow_normalizer_comap] at hn
  have hb : rankOneLift Q e h split i hp r ∈ (borel (L i) S).subgroupOf (L i) := by
    rw [borel_subgroupOf_eq_sylowNormalizer (L i) S T hT]
    exact hn'
  rw [← factor_borel_comap Q e h i] at hb
  change factorMap Q e i (rankOneLift Q e h split i hp r) ∈ Q.tits.B at hb
  simpa only [factorMap_rankOneLift] using hb

def rankOneQuotientEquiv [Finite (L i)] (hp : Group.IsPerfect (L i))
    (T : Sylow 2 (L i)) (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i)
    (hroot : Function.Surjective (simpleRootSylowProjection Q e h split i hp T hT)) :
    rankOne Q split i ≃* (L i) ⧸ pCore 2 (L i) :=
  MulEquiv.ofBijective (rankOneProjection Q e h split i hp)
    ⟨rankOneProjection_injective Q e h split i hp,
      rankOneProjection_surjective Q e h split i hp T hT hroot⟩

@[simp] theorem rankOneQuotientEquiv_apply [Finite (L i)] (hp : Group.IsPerfect (L i))
    (T : Sylow 2 (L i)) (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i)
    (hroot : Function.Surjective (simpleRootSylowProjection Q e h split i hp T hT))
    (r : rankOne Q split i) :
    rankOneQuotientEquiv Q e h split i hp T hT hroot r =
      QuotientGroup.mk' (pCore 2 (L i)) (rankOneLift Q e h split i hp r) := by rfl

theorem rankOneQuotientEquiv_projection [Finite (L i)] (hp : Group.IsPerfect (L i))
    (T : Sylow 2 (L i)) (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i)
    (hroot : Function.Surjective (simpleRootSylowProjection Q e h split i hp T hT))
    (r : rankOne Q split i) :
    rankOneQuotientEquiv Q e h split i hp T hT hroot r =
      rankOneProjection Q e h split i hp r := by rfl

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
