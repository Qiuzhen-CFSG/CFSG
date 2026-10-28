module
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.RankOne
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.SplitFactorization.RootNormalization
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.MatrixExchanges

/-!
# Radical and torus actions for the Suzuki Ree panel

Positive root exchanges preserve the Suzuki radical: every correction root
has a nonzero coefficient outside the middle Levi subsystem. The four middle
reflections also preserve this support. The actual middle Weyl word therefore
normalizes the radical, and its exchange of the complete signed Suzuki words
shows that the negative block normalizes the radical for every field parameter.

Diagonal conjugation scales each root curve in the negative block. Conjugating
the generating coroot words by the middle Weyl word reflects their roots with
unchanged parameters. Thus the radical and torus both conjugate into the root
Borel. Equality of the coroot and diagonal tori is needed only for the torus
action on the negative block; no Borel-generation or Gauss identity is used.

Source: GLS3, 2.3.8(a,b), Table 2.4 type V, and 2.6.5(g),
`refs/KGroup/GLS3/chapter2.tex`. The positive-exchange argument adapts
`BinaryLocals/SuzukiProjection/SplitFactorization/RootNormalization.lean`
from the binary field to arbitrary Ree coefficient fields, and the torus
argument follows `LocalIndices/LinearCover/Normalization.lean`.
-/

public section
noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.LocalIndices
open Subgroup LargeLocalSeeds Parabolics BlockParameters.FieldRecovery
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RadicalCoordinates
open BinarySuzuki.RootNormalization
private local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
variable {m : ℕ}

private theorem conj_radical_of_matrixExchange
    (r s : F4Chevalley.Root) (a b : CoefficientField m)
    (hr : typeF4RootPairing_base.IsPos r) (hs : IsRadicalRoot .suzuki s)
    (h : MatrixExchange s r b (-a)) :
    rootGeneratorInGroup m r a * rootGeneratorInGroup m s b *
      (rootGeneratorInGroup m r a)⁻¹ ∈ splitRadical m .suzuki := by
  obtain ⟨c, hc, he⟩ := h
  let W := (c.map (fun z => rootGeneratorInGroup m z.1 z.2)).prod
  have hW : W ∈ splitRadical m .suzuki := by
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact subset_closure ⟨_, _, positiveCone_radical_left hs hr (hc z hz), rfl⟩
  have hWval : W.val.val =
      (c.map (fun z => (F4Chevalley.rootCurve z.1 z.2).val)).prod := by
    let ρ : SplitGroup m →* MatrixCarrier m :=
      (Units.coeHom (MatrixCarrier m)).comp (SplitGroup m).subtype
    change ρ ((c.map (fun z => rootGeneratorInGroup m z.1 z.2)).prod) = _
    rw [map_list_prod, List.map_map]
    rfl
  have he' : rootGeneratorInGroup m s b * rootGeneratorInGroup m r (-a) =
      rootGeneratorInGroup m r (-a) * rootGeneratorInGroup m s b * W := by
    apply Subtype.ext
    apply Units.ext
    change (F4Chevalley.rootCurve s b).val * (F4Chevalley.rootCurve r (-a)).val =
      (F4Chevalley.rootCurve r (-a)).val * (F4Chevalley.rootCurve s b).val * W.val.val
    rw [hWval]
    exact he
  have hinv : rootGeneratorInGroup m r (-a) = (rootGeneratorInGroup m r a)⁻¹ :=
    (Subtype.ext (F4Chevalley.rootCurve_inv r a)).symm
  rw [hinv] at he'
  have he'' : rootGeneratorInGroup m r a * rootGeneratorInGroup m s b *
      (rootGeneratorInGroup m r a)⁻¹ = rootGeneratorInGroup m s b * W := by
    calc
      _ = rootGeneratorInGroup m r a *
        (rootGeneratorInGroup m s b * (rootGeneratorInGroup m r a)⁻¹) := by group
      _ = rootGeneratorInGroup m r a *
        ((rootGeneratorInGroup m r a)⁻¹ * rootGeneratorInGroup m s b * W) := by rw [he']
      _ = _ := by group
  rw [he'']
  exact (splitRadical m .suzuki).mul_mem (subset_closure ⟨s, b, hs, rfl⟩) hW

private theorem mem_radical_normalizer_of_conj_roots (g : SplitGroup m)
    (h : ∀ (r : F4Chevalley.Root) (t : CoefficientField m),
      IsRadicalRoot .suzuki r →
      g * rootGeneratorInGroup m r t * g⁻¹ ∈ splitRadical m .suzuki) :
    g ∈ normalizer (splitRadical m .suzuki) := by
  have hle : splitRadical m .suzuki ≤
      (splitRadical m .suzuki).comap (MulAut.conj g).toMonoidHom := by
    apply (closure_le _).mpr
    rintro _ ⟨r, t, hr, rfl⟩
    exact h r t hr
  exact mem_normalizer_fintype fun _ hx => hle hx

private theorem positive_root_mem_radical_normalizer (r : F4Chevalley.Root)
    (a : CoefficientField m) (hr : typeF4RootPairing_base.IsPos r) :
    rootGeneratorInGroup m r a ∈ normalizer (splitRadical m .suzuki) := by
  by_cases hR : IsRadicalRoot .suzuki r
  · exact (splitRadical m .suzuki).le_normalizer (subset_closure ⟨r, a, hR, rfl⟩)
  apply mem_radical_normalizer_of_conj_roots
  intro s b hs
  have hsr : s ≠ r := fun h => hR (h ▸ hs)
  by_cases hsum : typeF4RootPairing.root s + typeF4RootPairing.root r ∈
      Set.range typeF4RootPairing.root
  · apply conj_radical_of_matrixExchange r s a b hr hs
    by_cases hlen : IsLongRoot s ↔ IsLongRoot r
    · exact matrixExchange_of_equal_length_sum m s r hs.1 hr hsr hlen hsum b (-a)
    · exact matrixExchange_of_mixed_length_sum m s r hs.1 hr hsr hlen hsum b (-a)
  · have hc := rootGenerator_commute_of_no_sum m
      (k := .positive) ⟨s, hs.1⟩ ⟨r, hr⟩ hsum b a
    rw [← hc.eq, mul_assoc, mul_inv_cancel, mul_one]
    exact subset_closure ⟨s, b, hs, rfl⟩

private theorem positive_le_radical_normalizer (d : LocalBlockInput m) :
    standardUnipotent d ≤ normalizer (suzukiPanelRadical d) := by
  have h : splitUnipotent m ≤ normalizer (splitRadical m .suzuki) := by
    apply (closure_le _).mpr
    rintro _ ⟨r, t, hr, rfl⟩
    exact positive_root_mem_radical_normalizer r t hr
  exact (Subgroup.comap_mono h).trans (Subgroup.le_normalizer_comap d.fixedGroup.subtype)

private theorem panelWeyl_mem_radical_normalizer (d : LocalBlockInput m) :
    suzukiPanelWeyl d ∈ normalizer (suzukiPanelRadical d) := by
  apply Subgroup.le_normalizer_comap d.fixedGroup.subtype
  apply mem_radical_normalizer_of_conj_roots
  intro r t hr
  change (suzukiPanelWeyl d).val * rootGeneratorInGroup m r t *
    (suzukiPanelWeyl d).val⁻¹ ∈ splitRadical m .suzuki
  rw [suzukiPanelWeyl_conj_root]
  apply Subgroup.subset_closure
  refine ⟨_, t, ?_, rfl⟩
  change IsRadicalRoot .suzuki
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 1)
      (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 2)
        (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 1)
          (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 2) r))))
  exact isRadicalRoot_simpleReflection
    (isRadicalRoot_simpleReflection
      (isRadicalRoot_simpleReflection
        (isRadicalRoot_simpleReflection hr (by simp [leviNodes]))
        (by simp [leviNodes])) (by simp [leviNodes])) (by simp [leviNodes])

/-- The complete negative Suzuki block normalizes the prescribed positive radical. -/
theorem suzuki_negative_le_radical_normalizer (d : LocalBlockInput m)
    (C : SuzukiCoordinates d) :
    simpleBlock d .suzuki false ≤ normalizer (suzukiPanelRadical d) := by
  intro x hx
  obtain ⟨t, u, rfl⟩ := C.element_cover false hx
  rw [← suzukiPanelWeyl_conj_positive d C t u]
  have hn := panelWeyl_mem_radical_normalizer d
  have hp := positive_le_radical_normalizer d
    (simpleBlock_positive_le d .suzuki (C.element_mem true t u))
  exact mul_mem (mul_mem hn hp) (inv_mem hn)

private theorem diagonalTorus_le_block_normalizer (m : ℕ) (s : Side) (p : Bool) :
    diagonalTorus m ≤ normalizer (splitSimpleBlock m s p) := by
  unfold splitSimpleBlock
  rw [le_normalizer_closure_iff]
  intro z hz x hx
  change z.val ∈ (diagonalTorusHom m).range at hz
  obtain ⟨u, hu⟩ := hz
  obtain ⟨r, t, hr, rfl⟩ := hx
  apply Subgroup.subset_closure
  refine ⟨r, ((integralChevalleyRootScale (P := typeF4RootPairing) u⁻¹ r :
    (CoefficientField m)ˣ) : CoefficientField m) * t, hr, ?_⟩
  apply Subtype.ext
  change z.val * F4Chevalley.rootCurve r t * z.val⁻¹ = _
  rw [← hu]
  have he := F4Chevalley.rootCurve_torus_conjugation u⁻¹ r t
  simpa only [← diagonalTorusHom_apply, map_inv, inv_inv, rootGeneratorInGroup_coe] using he

/-- The fixed coroot torus normalizes the negative Suzuki block whenever the
coroot-word torus is the diagonal torus. -/
theorem suzukiPanelTorus_le_negative_normalizer (d : LocalBlockInput m)
    (hT : splitTorus m = diagonalTorus m) :
    suzukiPanelTorus d ≤ normalizer (simpleBlock d .suzuki false) := by
  have h := hT.le.trans (diagonalTorus_le_block_normalizer m .suzuki false)
  exact (Subgroup.comap_mono h).trans (Subgroup.le_normalizer_comap d.fixedGroup.subtype)

/-- Conjugation by the middle Weyl word carries the radical into the root
Borel, with convention `n * x * n⁻¹`. -/
theorem suzukiPanelRadical_le_borel_comap_weyl (d : LocalBlockInput m) :
    suzukiPanelRadical d ≤ (rootBorel d).comap
      (MulAut.conj (suzukiPanelWeyl d)).toMonoidHom := by
  intro x hx
  exact suzukiPanelRadical_le_borel d
    ((mem_normalizer_iff.mp (panelWeyl_mem_radical_normalizer d) x).mp hx)

private theorem reflection_neg (i r : F4Chevalley.Root) :
    typeF4RootPairing.reflectionPerm i (-r) =
      -typeF4RootPairing.reflectionPerm i r := by
  apply typeF4RootPairing.root.injective
  have hneg (r : F4Chevalley.Root) :
      typeF4RootPairing.root (-r) = -typeF4RootPairing.root r := by
    change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm r r) = _
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  calc
    _ = typeF4RootPairing.reflection i (typeF4RootPairing.root (-r)) :=
      typeF4RootPairing.root_reflectionPerm i (-r)
    _ = -typeF4RootPairing.reflection i (typeF4RootPairing.root r) := by
      rw [hneg, map_neg]
    _ = _ := by rw [hneg, RootPairing.root_reflectionPerm]

private theorem panelWeyl_conj_torusWord (d : LocalBlockInput m)
    (r : F4Chevalley.Root) (t : (CoefficientField m)ˣ) :
    MulAut.conj (suzukiPanelWeyl d).val (torusWord m r t) =
      torusWord m (suzukiPanelReflection r) t := by
  simp only [torusWord, weylWord, map_mul, MulAut.conj_apply,
    suzukiPanelWeyl_conj_root, suzukiPanelReflection, Equiv.Perm.mul_apply, reflection_neg]

/-- Conjugating the generating coroot words carries the fixed torus into the
root Borel, with convention `n * x * n⁻¹`. -/
theorem suzukiPanelTorus_le_borel_comap_weyl (d : LocalBlockInput m) :
    suzukiPanelTorus d ≤ (rootBorel d).comap
      (MulAut.conj (suzukiPanelWeyl d)).toMonoidHom := by
  have h : splitTorus m ≤ (splitTorus m).comap
      (MulAut.conj (suzukiPanelWeyl d).val).toMonoidHom := by
    apply (closure_le _).mpr
    rintro _ ⟨r, t, rfl⟩
    change MulAut.conj (suzukiPanelWeyl d).val (torusWord m r t) ∈ splitTorus m
    rw [panelWeyl_conj_torusWord]
    exact subset_closure ⟨_, t, rfl⟩
  intro x hx
  apply suzukiPanelTorus_le_borel d
  exact h hx

end ReeF4.LocalBlockInput.PairRigidity.LocalIndices
