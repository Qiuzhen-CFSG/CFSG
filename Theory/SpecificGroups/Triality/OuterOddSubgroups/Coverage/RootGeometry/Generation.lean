module

public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootFrame
public import Theory.SpecificGroups.Triality.ConcreteBruhat.RelativeNormalizer
public import Theory.SpecificGroups.Triality.RadicalCoordinates.LeviCommutators.FoldedRoots

/-!
# Generation by the four signed simple-root groups

The central reflection sends the first short root to the second; the arm
reflection sends the second to the third, cyclically rotating its Frobenius
parameters. The two reflections likewise generate all three long roots.
These are identities between the actual Geck curves, transported through the
faithful elementary central quotient. The positive coordinate factorization
therefore puts the full unipotent subgroup in the signed-root closure.

The fixed torus consists of explicit six-root words. The concrete Bruhat
coverage by B and N then proves generation of the genuine carrier, for every
positive binary exponent, including one. No simplicity hypothesis is used.

Source: Steinberg, Theorem 36 and Theorem 30(1),
`refs/KGroup/GLS3/Chapter2St1.tex`; GLS3 §§2.3–2.4,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section
namespace Triality.Standard.OuterOdd.Coverage.RootGeometry
open Parabolics ConcreteBruhat PositiveCoordinates
open Theory.AlgebraicGroup.StandardRootSystem
open PositiveCoordinates.SumExchangeData
open RadicalCoordinates.LeviCommutators

private theorem conjugate_mul {G : Type*} [Group G] (g x y : G) :
    g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group

private theorem simple_curve (P : Parameters) (hp : P.prime = 2)
    (a : Node) (i j : Fin 12)
    (h : (foldedRootReflection a).val (rootIndex i) = rootIndex j)
    (t : ExtensionField P) :
    elementaryInclusion P (simpleElementary P hp a) * curve P i t *
      (elementaryInclusion P (simpleElementary P hp a))⁻¹ = curve P j t := by
  let D := InputRealization.inputs P hp
  have hn : D.lift (foldedRootReflection a) =
      elementaryInclusion P (simpleElementary P hp a) := by
    cases a
    · simp only [foldedRootReflection, map_mul, SplitNormalForm.Inputs.lift_simple,
        elementaryInclusion_simple_arms]
    · simp only [foldedRootReflection, SplitNormalForm.Inputs.lift_simple,
        elementaryInclusion_simple_central]
  have hc : D.lift (foldedRootReflection a) * curve P i t *
      (D.lift (foldedRootReflection a))⁻¹ =
      SplitNormalForm.rootCurve P ((foldedRootReflection a).val (rootIndex i)) t :=
    D.conjugate_root (foldedRootReflection a) (rootIndex i) t
  exact (congrArg (fun n : SplitGroup P => n * curve P i t * n⁻¹) hn.symm).trans
    (hc.trans (congrArg (fun r => SplitNormalForm.rootCurve P r t) h))

private theorem central_short_table (i : Fin 3) :
    (foldedRootReflection .central).val (rootIndex (shortPosition 0 i)) =
      rootIndex (shortPosition 1 i) := by
  change rootReflection 1 _ = _
  rw [← rootEnumeration_positiveIndex, rootReflection, ← rootEnumeration_reflectionTable,
    ← rootEnumeration_positiveIndex]
  congr 1
  fin_cases i <;> decide +kernel

private theorem arms_short_table (i : Fin 3) :
    (foldedRootReflection .arms).val (rootIndex (shortPosition 1 i)) =
      rootIndex (shortPosition 2 (i + 1)) := by
  change rootReflection 0 (rootReflection 2 (rootReflection 3 _)) = _
  rw [← rootEnumeration_positiveIndex, rootReflection, rootReflection, rootReflection,
    ← rootEnumeration_reflectionTable, ← rootEnumeration_reflectionTable,
    ← rootEnumeration_reflectionTable, ← rootEnumeration_positiveIndex]
  congr 1
  fin_cases i <;> decide +kernel

private theorem arms_long_table :
    (foldedRootReflection .arms).val (rootIndex 3) = rootIndex 10 := by
  change rootReflection 0 (rootReflection 2 (rootReflection 3 _)) = _
  rw [← rootEnumeration_positiveIndex, rootReflection, rootReflection, rootReflection,
    ← rootEnumeration_reflectionTable, ← rootEnumeration_reflectionTable,
    ← rootEnumeration_reflectionTable, ← rootEnumeration_positiveIndex]
  congr 1

private theorem central_long_table :
    (foldedRootReflection .central).val (rootIndex 10) = rootIndex 11 := by
  change rootReflection 1 _ = _
  rw [← rootEnumeration_positiveIndex, rootReflection, ← rootEnumeration_reflectionTable,
    ← rootEnumeration_positiveIndex]
  congr 1

private theorem conjugate_short_zero (P : Parameters) (hp : P.prime = 2)
    (t : ExtensionField P) :
    elementaryInclusion P (simpleElementary P hp .central) * shortSplit P 0 t *
      (elementaryInclusion P (simpleElementary P hp .central))⁻¹ = shortSplit P 1 t := by
  simp only [shortSplit, conjugate_mul,
    simple_curve P hp .central _ _ (central_short_table _)]

private theorem conjugate_short_one (P : Parameters) (hp : P.prime = 2)
    (t : ExtensionField P) :
    elementaryInclusion P (simpleElementary P hp .arms) * shortSplit P 1 t *
      (elementaryInclusion P (simpleElementary P hp .arms))⁻¹ =
        shortSplit P 2 (fieldFrobenius P (fieldFrobenius P t)) := by
  simp only [shortSplit, conjugate_mul,
    simple_curve P hp .arms _ _ (arms_short_table _), fieldFrobenius_three]
  change curve P 8 t * curve P 9 (fieldFrobenius P t) *
      curve P 7 (fieldFrobenius P (fieldFrobenius P t)) =
    curve P 7 (fieldFrobenius P (fieldFrobenius P t)) * curve P 8 t *
      curve P 9 (fieldFrobenius P t)
  have h78 := curve_diagram_commute P 7
    (fieldFrobenius P (fieldFrobenius P t)) t
  have h97 := curve_diagram_commute P 9
    (fieldFrobenius P t) (fieldFrobenius P (fieldFrobenius P t))
  change Commute (curve P 7 _) (curve P 8 _) at h78
  change Commute (curve P 9 _) (curve P 7 _) at h97
  rw [← (h78.mul_right h97.symm).eq, mul_assoc]

theorem rootElement_mem_closure (P : Parameters) (hp : P.prime = 2)
    (s : Bool) (a : Node) (t : RootField P a) :
    ConcreteBruhat.rootElement P hp s a t ∈ Subgroup.closure (rootGenerators P hp) :=
  Subgroup.subset_closure ⟨s, a, t, rfl⟩

theorem simpleRepresentative_mem_closure (P : Parameters) (hp : P.prime = 2) (a : Node) :
    simpleRepresentative P hp a ∈ Subgroup.closure (rootGenerators P hp) := by
  rw [simpleRepresentative_eq_root_word]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _
    (rootElement_mem_closure P hp true a 1) (rootElement_mem_closure P hp false a 1))
    (rootElement_mem_closure P hp true a 1)

private theorem short_zero_eq (P : Parameters) (hp : P.prime = 2)
    (t : ExtensionField P) :
    short P hp 0 t = ConcreteBruhat.rootElement P hp true .arms t := by
  have hc : shortSplit P 0 t = elementaryInclusion P (rootElementary P hp true .arms t) :=
    congrArg₂ (· * ·)
      (congrArg₂ (· * ·) (curve_simple P 0 t) (curve_simple P 2 (fieldFrobenius P t)))
      (curve_simple P 3 (fieldFrobenius P (fieldFrobenius P t)))
  exact congrArg (toCarrier P) (elementaryInclusion_injective P
    ((shortElementary_val P hp 0 t).trans hc))

private theorem long_zero_eq (P : Parameters) (hp : P.prime = 2)
    (t : fixedField P) :
    long P hp 0 t = ConcreteBruhat.rootElement P hp true .central t := by
  have hc : longSplit P 0 t = elementaryInclusion P (rootElementary P hp true .central t) :=
    curve_simple P 1 t.val
  exact congrArg (toCarrier P) (elementaryInclusion_injective P
    ((longElementary_val P hp 0 t).trans hc))

private theorem short_mem_closure (P : Parameters) (hp : P.prime = 2)
    (i : Fin 3) (t : ExtensionField P) :
    short P hp i t ∈ Subgroup.closure (rootGenerators P hp) := by
  have hzero (u : ExtensionField P) : short P hp 0 u ∈ Subgroup.closure (rootGenerators P hp) := by
    rw [short_zero_eq]
    exact rootElement_mem_closure P hp true .arms u
  have hstep (a : Node) (j k : Fin 3) (u v : ExtensionField P)
      (h : elementaryInclusion P (simpleElementary P hp a) * shortSplit P j u *
        (elementaryInclusion P (simpleElementary P hp a))⁻¹ = shortSplit P k v)
      (hj : short P hp j u ∈ Subgroup.closure (rootGenerators P hp)) :
      short P hp k v ∈ Subgroup.closure (rootGenerators P hp) := by
    have he : simpleRepresentative P hp a * short P hp j u *
        (simpleRepresentative P hp a)⁻¹ = short P hp k v := by
      apply FixedDescent.carrierToSplit_injective P hp
      simpa only [map_mul, map_inv, simpleRepresentative, short,
        FixedDescent.carrierToSplit_toCarrier, shortElementary_val] using h
    rw [← he]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (simpleRepresentative_mem_closure P hp a) hj)
      (Subgroup.inv_mem _ (simpleRepresentative_mem_closure P hp a))
  have hone (u : ExtensionField P) :=
    hstep .central 0 1 u u (conjugate_short_zero P hp u) (hzero u)
  fin_cases i
  · exact hzero t
  · exact hone t
  · change short P hp 2 t ∈ Subgroup.closure (rootGenerators P hp)
    have h := hstep .arms 1 2 (fieldFrobenius P t)
      (fieldFrobenius P (fieldFrobenius P (fieldFrobenius P t)))
      (conjugate_short_one P hp _) (hone _)
    simpa only [fieldFrobenius_three] using h

private theorem long_mem_closure (P : Parameters) (hp : P.prime = 2)
    (i : Fin 3) (t : fixedField P) :
    long P hp i t ∈ Subgroup.closure (rootGenerators P hp) := by
  have hzero : long P hp 0 t ∈ Subgroup.closure (rootGenerators P hp) := by
    rw [long_zero_eq]
    exact rootElement_mem_closure P hp true .central t
  have hstep (a : Node) (j k : Fin 3)
      (h : (foldedRootReflection a).val (rootIndex (longPosition j)) =
        rootIndex (longPosition k))
      (hj : long P hp j t ∈ Subgroup.closure (rootGenerators P hp)) :
      long P hp k t ∈ Subgroup.closure (rootGenerators P hp) := by
    have he : simpleRepresentative P hp a * long P hp j t *
        (simpleRepresentative P hp a)⁻¹ = long P hp k t := by
      apply FixedDescent.carrierToSplit_injective P hp
      simpa only [map_mul, map_inv, simpleRepresentative, long,
        FixedDescent.carrierToSplit_toCarrier, longElementary_val, longSplit] using
        simple_curve P hp a _ _ h t.val
    rw [← he]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (simpleRepresentative_mem_closure P hp a) hj)
      (Subgroup.inv_mem _ (simpleRepresentative_mem_closure P hp a))
  have hone := hstep .arms 0 1 arms_long_table hzero
  fin_cases i
  · exact hzero
  · exact hone
  · exact hstep .central 1 2 central_long_table hone

private theorem positive_coordinates (f : ℕ) (hf : 0 < f)
    (x : ElementaryGroup (binaryParameters f hf))
    (hx : elementaryInclusion (binaryParameters f hf) x ∈ positiveSubgroup (binaryParameters f hf)) :
    ∃ v : OrbitParameters (binaryParameters f hf),
      orderedProduct (binaryParameters f hf) (expand (binaryParameters f hf) v) =
        elementaryInclusion (binaryParameters f hf) x := by
  let P := binaryParameters f hf
  let e := orbitPositiveEquiv_binary f hf
  let y : (positiveSubgroup P).comap (fixedSubgroup P).subtype := ⟨x.val, hx⟩
  let v := e.symm y
  have hv := congrArg (fun z => z.val.val) (e.apply_symm_apply y)
  exact ⟨v, (orbitPositiveEquiv_binary_val f hf v).symm.trans hv⟩

private theorem positive_factorization (P : Parameters) (hp : P.prime = 2)
    (x : ElementaryGroup P) (v : OrbitParameters P)
    (hs : orderedProduct P (expand P v) = elementaryInclusion P x) :
    toCarrier P x = short P hp 0 (v.1 0) * long P hp 0 (v.2 0) *
      short P hp 1 (v.1 1) * short P hp 2 (v.1 2) *
        long P hp 1 (v.2 1) * long P hp 2 (v.2 2) := by
  have hx' : x = shortElementary P hp 0 (v.1 0) * longElementary P hp 0 (v.2 0) *
      shortElementary P hp 1 (v.1 1) * shortElementary P hp 2 (v.1 2) *
      longElementary P hp 1 (v.2 1) * longElementary P hp 2 (v.2 2) := by
    apply elementaryInclusion_injective P
    simp only [map_mul, shortElementary_val P hp, longElementary_val P hp]
    exact hs.symm.trans (orderedProduct_expand P v)
  exact (congrArg (toCarrier P) hx').trans (by simp only [map_mul]; rfl)

/-- All six positive folded root factors are generated by the four signed
simple-root curves in the actual central quotient. -/
theorem unipotent_le_rootGenerators_closure (f : ℕ) (hf : 0 < f) :
    unipotent (binaryParameters f hf) ≤
      Subgroup.closure (rootGenerators (binaryParameters f hf) rfl) := by
  let P := binaryParameters f hf
  change unipotent P ≤ Subgroup.closure (rootGenerators P rfl)
  intro g hg
  obtain ⟨x, hx, he⟩ := hg
  obtain ⟨v, hv⟩ := positive_coordinates f hf x hx
  have hm : short P rfl 0 (v.1 0) * long P rfl 0 (v.2 0) *
      short P rfl 1 (v.1 1) * short P rfl 2 (v.1 2) *
      long P rfl 1 (v.2 1) * long P rfl 2 (v.2 2) ∈ Subgroup.closure (rootGenerators P rfl) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (short_mem_closure P rfl 0 _) (long_mem_closure P rfl 0 _))
      (short_mem_closure P rfl 1 _)) (short_mem_closure P rfl 2 _))
      (long_mem_closure P rfl 1 _)) (long_mem_closure P rfl 2 _)
  exact ((positive_factorization P rfl x v hv).symm.trans he) ▸ hm

private theorem foldedWeyl_mem_closure (P : Parameters) (hp : P.prime = 2)
    (a : Node) (t : RootField P a) :
      toCarrier P (TorusCoordinates.foldedWeylElementary P hp a t) ∈
        Subgroup.closure (rootGenerators P hp) := by
    simp only [TorusCoordinates.foldedWeylElementary, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (rootElement_mem_closure P hp true a t)
      (rootElement_mem_closure P hp false a (-t⁻¹)))
      (rootElement_mem_closure P hp true a t)
private theorem foldedTorus_mem_closure (P : Parameters) (hp : P.prime = 2)
    (a : Node) (t : (RootField P a)ˣ) :
      toCarrier P (TorusCoordinates.foldedTorusElementary P hp a t) ∈
        Subgroup.closure (rootGenerators P hp) := by
    change toCarrier P (TorusCoordinates.foldedWeylElementary P hp a t.val *
      TorusCoordinates.foldedWeylElementary P hp a (-1)) ∈ _
    rw [map_mul]
    exact Subgroup.mul_mem _ (foldedWeyl_mem_closure P hp a t.val)
      (foldedWeyl_mem_closure P hp a (-1))

private theorem torus_word (P : Parameters) (hp : P.prime = 2)
    (g : Carrier P) (hg : g ∈ torus P) :
    ∃ v : TorusCoordinates.OrbitParameters P, toCarrier P
      (TorusCoordinates.foldedTorusElementary P hp .arms v.1) * toCarrier P
      (TorusCoordinates.foldedTorusElementary P hp .central v.2) = g := by
  let e := TorusCoordinates.torusMulEquiv P hp
  let v := e.symm ⟨g, hg⟩
  have hv := e.apply_symm_apply ⟨g, hg⟩
  have he : toCarrier P (TorusCoordinates.orbitElementary P hp v) = g :=
    (TorusCoordinates.torusMulEquiv_val P hp v).symm.trans (congrArg Subtype.val hv)
  exact ⟨v, (map_mul (toCarrier P) _ _).symm.trans he⟩

/-- The fixed torus consists of explicit products of signed simple-root words. -/
theorem torus_le_rootGenerators_closure (P : Parameters) (hp : P.prime = 2) :
    torus P ≤ Subgroup.closure (rootGenerators P hp) := by
  intro g hg
  obtain ⟨v, he⟩ := torus_word P hp g hg
  rw [← he]
  exact Subgroup.mul_mem _ (foldedTorus_mem_closure P hp .arms v.1)
    (foldedTorus_mem_closure P hp .central v.2)

/-- The literal signed simple-root elements generate the genuine carrier,
including the binary endpoint. -/
theorem rootGenerators_closure_eq_top (f : ℕ) (hf : 0 < f) :
    Subgroup.closure (rootGenerators (binaryParameters f hf) rfl) = ⊤ := by
  let P := binaryParameters f hf
  apply top_unique
  rw [← RelativeNormalizer.borel_sup_normalizer f hf]
  have hb : borel P ≤ Subgroup.closure (rootGenerators P rfl) := by
    intro g hg
    obtain ⟨u, hu, t, ht, rfl⟩ := (borel_eq_mul P rfl).le hg
    exact Subgroup.mul_mem _ (unipotent_le_rootGenerators_closure f hf hu)
      (torus_le_rootGenerators_closure P rfl ht)
  refine sup_le hb (sup_le (torus_le_rootGenerators_closure P rfl) ?_)
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨a, rfl⟩
  exact simpleRepresentative_mem_closure P rfl a

end Triality.Standard.OuterOdd.Coverage.RootGeometry
