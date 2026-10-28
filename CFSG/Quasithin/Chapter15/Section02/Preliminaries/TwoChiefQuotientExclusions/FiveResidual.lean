module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.TwoChiefQuotientExclusions.Five
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.Representation.BinaryPermutationNaturalStructure
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Homogeneity
public import Theory.GroupTheory.NoncentralChiefRefinement.ResidualRestriction.ChiefSurvival
public import Theory.GroupTheory.NoncentralChiefRefinement.Homogeneous

/-!
# Both five-point chief factors inside the literal rank-one residual

In the single S₅ branch, restrict both natural chief actions to R = O²(H).
Their images are the characteristic A₅ subgroup, acting irreducibly on the
same natural four-spaces. Restriction of the ambient two-core identifies
their kernels with O₂(R).

Intersect the original chief intervals with R. The actual inclusion maps
of the relative quotients are surjective, and their conjugation equivariance
transports irreducibility and the kernels. Thus both intersections remain
noncentral chief factors of order sixteen. Their positions in the original
series make the intervals disjoint, giving |U_H ∩ R| ≥ 256 and |O₂(R)| ≥ 256.
Transport through H's subtype applies these bounds to the actual embedded
factor K used in the F.1.1 pair [Y₁Rc,K], whose full second parabolic is H.

This supplies the two-factor input for the remaining mixed-pair exclusion;
it does not assert recognition or the final S₃-wreath quotient. Those source
obligations remain with qt-e-152-small-parabolic. SmallSourcePrior retains
only the permitted earlier source assumptions.

Source: Aschbacher--Smith 15.1.12 and 15.2.8, printed pp.1090,1109--1110;
B.3.1 for the natural alternating action and F.1.1 for the rank-one factors.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterB.QuasisimpleSource

private theorem five_residual_coordinates
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)
    (hk : (actionHom ρ).ker = pCore 2 D)
    (e : ActionEquiv (imageRepresentation ρ) (BinaryPermutation.naturalRepresentation (Fin 5))) :
    let R := pResidual 2 D
    ∃ (q : R →* alternatingGroup (Fin 5)) (c : W ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5)),
      Function.Surjective q ∧ q.ker = pCore 2 R ∧
      (∀ (g : R) v, c (ρ (g : D) v) = BinaryPermutation.alternatingNaturalRepresentation (Fin 5) (q g) (c v)) ∧
      (actionHom (ρ.comp R.subtype)).ker = pCore 2 R ∧
      IsIrreducible (ρ.comp R.subtype) := by
  let R := pResidual 2 D
  let f : D →* Equiv.Perm (Fin 5) := e.groupEquiv.toMonoidHom.comp (actionHom ρ)
  have hf : Function.Surjective f := e.groupEquiv.surjective.comp ρ.asGroupHom.rangeRestrict_surjective
  have hfk : f.ker = pCore 2 D := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.groupEquiv.injective, hk]
  have hr : R.map f = alternatingGroup (Fin 5) :=
    (map_pResidual_of_surjective 2 f hf).trans (Equiv.Perm.twoResidual_eq_alternating (Fin 5))
  let q : R →* alternatingGroup (Fin 5) :=
    (MulEquiv.subgroupCongr hr).toMonoidHom.comp (f.subgroupMap R)
  have hq : Function.Surjective q :=
    (MulEquiv.subgroupCongr hr).surjective.comp (f.subgroupMap_surjective R)
  have hqk : q.ker = pCore 2 R := by
    rw [pCore_eq_comap_of_normal]
    ext x
    change q x = 1 ↔ (x : D) ∈ pCore 2 D
    rw [←hfk]
    exact ⟨fun hh => congrArg Subtype.val hh, fun hh => Subtype.ext hh⟩
  have hact (g : R) (v : W) : e.linearEquiv (ρ (g : D) v) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 5) (q g) (e.linearEquiv v) :=
    e.intertwines (actionHom ρ g) v
  have hkR : (actionHom (ρ.comp R.subtype)).ker = pCore 2 R := by
    rw [pCore_eq_comap_of_normal, ←hk]
    ext x
    rw [MonoidHom.mem_ker, actionHom_eq_one_iff]
    change (∀ v, ρ (x : D) v = v) ↔ actionHom ρ (x : D) = 1
    exact (actionHom_eq_one_iff ρ x).symm
  have hi : IsIrreducible (ρ.comp R.subtype) := by
    let σ := BinaryPermutation.alternatingNaturalRepresentation (Fin 5)
    let ε : ActionEquiv (ρ.comp R.subtype) (σ.comp q) :=
      ⟨MulEquiv.refl _, e.linearEquiv, hact⟩
    exact ExtensionConsequences.irreducible_of_equiv ε
      ((irreducible_comp_surjective_iff q hq σ).mpr
        (BinaryPermutation.alternatingNatural_isIrreducible (by decide)))
  exact ⟨q,e.linearEquiv,hq,hqk,hact,hkR,hi⟩

open NoncentralChiefRefinement

private theorem residual_chief_interval
    {D : Type*} [Group D] [Finite D] {U : Subgroup D} [U.Normal]
    [IsElementaryAbelian 2 U] (s : SeriesOn U) (i : Fin s.series.length)
    (hn : ¬ s.Central i)
    (hi : IsIrreducible ((s.factorRepresentation i).comp (pResidual 2 D).subtype))
    (hk : (actionHom ((s.factorRepresentation i).comp (pResidual 2 D).subtype)).ker =
      pCore 2 (pResidual 2 D)) :
    restrictNormalNode (pResidual 2 D) (s.lower i) ⋖
      restrictNormalNode (pResidual 2 D) (s.upper i) ∧
    IsNoncentralTwo (restrictNormalNode (pResidual 2 D) (s.lower i))
      (restrictNormalNode (pResidual 2 D) (s.upper i)) ∧
    Nat.card (Section (restrictNormalNode (pResidual 2 D) (s.lower i))
      (restrictNormalNode (pResidual 2 D) (s.upper i))) = Nat.card (s.Factor i) ∧
    (sectionAction (restrictNormalNode (pResidual 2 D) (s.lower i))
      (restrictNormalNode (pResidual 2 D) (s.upper i))).ker = pCore 2 (pResidual 2 D) := by
  let R := pResidual 2 D
  let A := restrictNormalNode R (s.lower i)
  let B := restrictNormalNode R (s.upper i)
  let ρ := (s.factorRepresentation i).comp R.subtype
  have hb : IsNoncentralTwo (s.lower i) (s.upper i) :=
    ⟨IsElementaryAbelian.isPGroup 2 (s.Factor i),hn⟩
  have hr := isNoncentralTwo_restrict_pResidual _ _ (s.series.step i) hb
  change IsNoncentralTwo A B at hr
  let e := restrictionSectionEquivOfTwoQuotient R (isPGroup_quotient_pResidual 2)
    (s.lower i) (s.upper i) (s.series.step i) hb
  have he (r : R) (x : Section A B) :
      e (sectionAction A B r x) = s.action i (r : D) (e x) := by
    calc
      _ = restrictionSectionMap R (s.lower i) (s.upper i) (sectionAction A B r x) :=
        restrictionSectionEquivOfTwoQuotient_apply R (isPGroup_quotient_pResidual 2)
          (s.lower i) (s.upper i) (s.series.step i) hb _
      _ = s.action i (r : D) (restrictionSectionMap R (s.lower i) (s.upper i) x) :=
        restrictionSectionMap_equivariant R (s.lower i) (s.upper i) r x
      _ = _ := congrArg (s.action i (r : D))
        (restrictionSectionEquivOfTwoQuotient_apply R (isPGroup_quotient_pResidual 2)
          (s.lower i) (s.upper i) (s.series.step i) hb x).symm
  let c : SectionCoordinates A B ρ 1 := {
    equiv := {
      toFun := fun x => Multiplicative.ofAdd (fun _ => Additive.ofMul (e x))
      invFun := fun v => e.symm ((v.toAdd 0).toMul)
      left_inv := fun x => e.symm_apply_apply x
      right_inv := by
        intro v
        apply Multiplicative.toAdd.injective
        funext j
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        exact congrArg Additive.ofMul (e.apply_symm_apply _)
      map_mul' := by
        intro x y
        apply Multiplicative.toAdd.injective
        funext j
        exact congrArg Additive.ofMul (e.map_mul x y) }
    equivariant := fun r x _ => congrArg Additive.ofMul (he r x) }
  have hmove : ∃ r v, ρ r v ≠ v := by
    by_contra! hh
    apply hr.2
    rw [isCentral_iff_action]
    intro r x
    apply e.injective
    exact (he r x).trans (congrArg Additive.toMul (hh r (Additive.ofMul (e x))))
  have hker : (sectionAction A B).ker = pCore 2 R := by
    rw [←hk]
    ext r
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, actionHom_eq_one_iff]
    constructor
    · intro ha v
      obtain ⟨x,hx⟩ := e.surjective v.toMul
      apply Additive.toMul.injective
      change s.action i (r : D) v.toMul = v.toMul
      rw [←hx, ←he]
      exact congrArg e (MulEquiv.congr_fun ha x)
    · intro ha
      apply MulEquiv.ext
      intro x
      apply e.injective
      exact (he r x).trans (congrArg Additive.toMul (ha (Additive.ofMul (e x))))
  let := hi
  exact ⟨c.covBy ((restrictNormalNode_monotone R) (s.series.step i).le) hmove,
    hr,Nat.card_congr e.toEquiv,hker⟩

variable {G : Type*} [Group G] [Finite G]
open Section01 Section03 ChapterD ChapterD.UniqueFactor

/-- Both literal natural chief factors survive in the actual two-residual,
with irreducible alternating actions and the intrinsic core as kernel. -/
theorem ChosenSmallSource.symmetricFive_residual_chief_actions
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    letI := h.prepared.elementary
    let U := (conjugateSpan H V).subgroupOf H
    letI := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      (show conjugateSpan H V ≤ H by
        rw [UniqueFactor.conjugateSpan_eq]
        exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
    let R := pResidual 2 H
    ∀ s : SeriesOn U, ∃ i j : Fin s.series.length, i ≠ j ∧
      ∀ k ∈ ({i,j} : Finset (Fin s.series.length)),
        restrictNormalNode R (s.lower k) ⋖ restrictNormalNode R (s.upper k) ∧
        IsNoncentralTwo (restrictNormalNode R (s.lower k)) (restrictNormalNode R (s.upper k)) ∧
        Nat.card (Section (restrictNormalNode R (s.lower k)) (restrictNormalNode R (s.upper k))) = 16 ∧
        (sectionAction (restrictNormalNode R (s.lower k)) (restrictNormalNode R (s.upper k))).ker = pCore 2 R ∧
        (Representation.BinaryOffender.actionHom ((s.factorRepresentation k).comp R.subtype)).ker = pCore 2 R ∧
        IsIrreducible ((s.factorRepresentation k).comp R.subtype) ∧
        ∃ (q : R →* alternatingGroup (Fin 5))
          (c : Additive (s.Factor k) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5)),
          Function.Surjective q ∧ q.ker = pCore 2 R ∧
          ∀ (g : R) v, c (s.factorRepresentation k (g : H) v) =
            BinaryPermutation.alternatingNaturalRepresentation (Fin 5) (q g) (c v) := by
  let := h.prepared.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
  dsimp only
  intro s
  obtain ⟨i,j,hij,hs⟩ := h.symmetricFive_chief_actions hprior hH he s
  refine ⟨i,j,hij,?_⟩
  intro k hk
  obtain ⟨hn,hker,⟨e⟩,hcard⟩ := hs k hk
  obtain ⟨q,c,hq,hqk,hact,hkR,hirr⟩ := five_residual_coordinates (s.factorRepresentation k) hker e
  obtain ⟨hc,hb,hnat,hkerSection⟩ := residual_chief_interval s k hn hirr hkR
  exact ⟨hc,hb,hnat.trans hcard,hkerSection,hkR,hirr,q,c,hq,hqk,hact⟩

/-- Both surviving intervals lie in the literal intersection of the
original H-span with its two-residual. -/
theorem ChosenSmallSource.symmetricFive_residual_span_card
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    256 ≤ Nat.card (((conjugateSpan H V).subgroupOf H).subgroupOf (pResidual 2 H)) := by
  classical
  let := h.prepared.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
  let R := pResidual 2 H
  obtain ⟨s⟩ := SeriesOn.exists_series U
  obtain ⟨i,j,hij,hs⟩ := h.symmetricFive_residual_chief_actions hprior hH he s
  have bound (a b : Fin s.series.length) (hab : a < b)
      (ha : a ∈ ({i,j} : Finset (Fin s.series.length)))
      (hb : b ∈ ({i,j} : Finset (Fin s.series.length))) :
      256 ≤ Nat.card (U.subgroupOf R) := by
    let A := restrictNormalNode R (s.lower a)
    let B := restrictNormalNode R (s.upper a)
    let C := restrictNormalNode R (s.lower b)
    let D := restrictNormalNode R (s.upper b)
    have hAB : A ≤ B := (hs a ha).1.le
    have hCD : C ≤ D := (hs b hb).1.le
    have hBC : B ≤ C := (restrictNormalNode_monotone R)
      (s.series.strictMono.monotone (show a.succ ≤ b.castSucc from by
        apply Fin.le_iff_val_le_val.mpr
        exact hab))
    have hD : D.val ≤ U.subgroupOf R := subgroupOf_mono R (s.upper_le b)
    have hcA := section_card_mul A B hAB
    have hcC := section_card_mul C D hCD
    rw [(hs a ha).2.2.1] at hcA
    rw [(hs b hb).2.2.1] at hcC
    have hpos := Nat.card_pos (α := A.val)
    have hbc := card_le_of_le hBC
    have hd := card_le_of_le hD
    omega
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact bound i j hij (by simp) (by simp)
  · exact bound j i hji (by simp) (by simp)

/-- The intrinsic residual core contains both natural chief factors. -/
theorem ChosenSmallSource.symmetricFive_residual_core_card
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    256 ≤ Nat.card (pCore 2 (pResidual 2 H)) := by
  have hc := card_le_of_le
    (subgroupOf_mono (pResidual 2 H) (h.HStar_span_le_core hH))
  rw [show (pCore 2 H).subgroupOf (pResidual 2 H) = pCore 2 (pResidual 2 H) from
    (pCore_eq_comap_of_normal 2 (pResidual 2 H)).symm] at hc
  exact (h.symmetricFive_residual_span_card hprior hH he).trans hc

/-- In the original ambient group, both factors survive on the intersection
of the elementary H-span with the embedded O²(H). -/
theorem ChosenSmallSource.symmetricFive_embedded_residual_span_card
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    256 ≤ Nat.card (conjugateSpan H V ⊓ (pResidual 2 H).map H.subtype : Subgroup G) := by
  let U := (conjugateSpan H V).subgroupOf H
  let R := pResidual 2 H
  have hUH : conjugateSpan H V ≤ H := by
    rw [UniqueFactor.conjugateSpan_eq]
    exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H))
  have hm : ((U.subgroupOf R).map R.subtype).map H.subtype =
      conjugateSpan H V ⊓ R.map H.subtype := by
    rw [subgroupOf_map_subtype,map_inf _ _ _ H.subtype_injective,
      map_subgroupOf_eq_of_le hUH]
  have hc := card_map_of_injective (K := U.subgroupOf R)
    (f := H.subtype.comp R.subtype) (H.subtype_injective.comp R.subtype_injective)
  change Nat.card ((U.subgroupOf R).map (H.subtype.comp R.subtype)) = _ at hc
  rw [←map_map,hm] at hc
  rw [hc]
  exact h.symmetricFive_residual_span_card hprior hH he

/-- The literal embedded residual used as the F.1.1 factor retains both
chief sections through its intrinsic two-core; their bound is not merely
an estimate for the larger H-core. -/
theorem SmallResidualWitness.symmetricFive_pair_residual_core
    {T : Sylow 2 G} {M Mc V Y₁ H : Subgroup G} {h : ChosenSmallSource T M Mc V}
    (hw : SmallResidualWitness h Y₁) (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    let K := (pResidual 2 H).map H.subtype
    let L := ![Y₁ ⊔ (M ⊓ Mc).pCoreIn 2,K]
    ChapterF.Source.HypothesisF11 L (T : Subgroup G) ∧
      ChapterF.Source.parabolic L (T : Subgroup G) 1 = H ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) ∧
      256 ≤ Nat.card (pCore 2 K) ∧
      256 ≤ Nat.card (conjugateSpan H V ⊓ K : Subgroup G) := by
  have hp := hw.symmetricFive_pair hH he
  refine ⟨hp.1,hp.2.2.1,hp.2.2.2.2.2,?_,
    h.symmetricFive_embedded_residual_span_card hprior hH he⟩
  let e := equivMapOfInjective (pResidual 2 H) H.subtype H.subtype_injective
  have hc : Nat.card (pCore 2 ((pResidual 2 H).map H.subtype)) =
      Nat.card (pCore 2 (pResidual 2 H)) := by
    rw [←pCore_map_iso 2 e,card_map_of_injective e.injective]
  rw [hc]
  exact h.symmetricFive_residual_core_card hprior hH he

end CFSG.Quasithin.Chapter15.Section02
