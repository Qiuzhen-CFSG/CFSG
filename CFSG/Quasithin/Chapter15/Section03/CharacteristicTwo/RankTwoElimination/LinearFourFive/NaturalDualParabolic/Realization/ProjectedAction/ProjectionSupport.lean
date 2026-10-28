module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.ProjectedAction.Coordinates
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Splitting

/-!
# Nonzero dual support of the projected centre

The full splitting W = [W,L] C_W(L) transfers the zero fixed space of
plane theta on the natural-plus-dual model to C_W(Y₊) = C_W(L). In the
second choice of Hypothesis 15.3.10 this forces L to centralize V₁,
contradicting the earlier bound on its normalizer.

In the first choice, V = ⟨Z^Y⟩ and Y ≤ L give W = ⟨Z^L⟩. If every
projected coordinate had zero dual component, Z would lie in the sum
of the natural summand and C_W(L). This sum is L-invariant, so it would
contain W. Its intersection with [W,L] is just the natural summand,
contradicting the full natural-plus-dual coordinate equivalence.

This proves the conditional support input for the projected-centre action.
The plane-theta fixed-space calculation remains an explicit model premise;
the parent action theorem must discharge it and prove residual noncentrality.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.11(3),(6), 15.3.16–17 and 15.3.24, printed pp.1123–1130.
-/

public section

open Subgroup BinaryLinear.OuterCyclic
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.ProjectedAction.ProjectionSupport
open Preparation
variable {G : Type*} [Group G] {d : LocalData G} {L : Subgroup G}

private def dualCoordinate (h : NaturalDual d L) :
    spanCommutator d L →* Multiplicative (Module.Dual (ZMod 2) (Space 4)) where
  toFun u := Multiplicative.ofAdd (h.coordinates u).toAdd.2
  map_one' := by simp
  map_mul' u v := by simp

private def naturalPart (h : NaturalDual d L) : Subgroup G :=
  (dualCoordinate h).ker.map (spanCommutator d L).subtype

private theorem mem_naturalPart (h : NaturalDual d L) (u : spanCommutator d L) :
    (u : G) ∈ naturalPart h ↔ (h.coordinates u).toAdd.2 = 0 := by
  constructor
  · rintro ⟨v, hv, he⟩
    have hvu : v = u := Subtype.ext he
    subst v
    exact congrArg Multiplicative.toAdd hv
  · intro hu
    exact ⟨u, congrArg Multiplicative.ofAdd hu, rfl⟩

private theorem naturalPart_le (h : NaturalDual d L) :
    naturalPart h ≤ spanCommutator d L := map_subtype_le _

private theorem normalizes_naturalPart (h : NaturalDual d L) :
    L ≤ normalizer (naturalPart h : Set G) := by
  apply le_normalizer_iff.mpr
  intro l hl u hu
  let v : spanCommutator d L := ⟨u, naturalPart_le h hu⟩
  change (commutatorAction d L ⟨l, hl⟩ v : G) ∈ naturalPart h
  apply (mem_naturalPart h _).mpr
  rw [h.equivariant]
  apply LinearMap.ext
  intro x
  rw [BinaryLinear.NaturalDualFlag.action_snd, (mem_naturalPart h v).mp hu]
  rfl

private theorem span_eq_center_span (hYL : d.Y ≤ L)
    (hspan : localSpan d.Z d.Y = d.V) :
    d.componentSpan L = localSpan d.Z L := by
  apply le_antisymm
  · apply conjugateSpanBy_le _ (le_normalizer_conjugateSpanBy d.Z L)
    rw [← hspan]
    exact conjugateSpanBy_mono le_rfl hYL
  · exact conjugateSpanBy_mono (le_conjugateSpanBy _ _) le_rfl

private theorem fixed_in_span [Finite G] {I : Subgroup G}
    (c : ComponentWitness d I) (h : NaturalDual d c.L)
    (plane : PlaneParabolic d c.L h.model)
    [IsElementaryAbelian 2 (d.componentSpan c.L)]
    (hYL : d.Yplus ≤ c.L) (hθ : theta (d.MI I) = d.Yplus)
    (hcore : c.L.pCoreIn 2 ≤ d.R) (hR : d.R ≤ centralizer (d.V : Set G))
    (hfixed : ∀ v : Space 4 × Module.Dual (ZMod 2) (Space 4),
      (∀ g ∈ theta (BinaryLinear.parabolic plane.plane),
        BinaryLinear.NaturalDualFlag.action g v = v) → v = 0) :
    d.componentSpan c.L ⊓ centralizer (d.Yplus : Set G) =
      d.componentSpan c.L ⊓ centralizer (c.L : Set G) := by
  apply le_antisymm _ (inf_le_inf_left _ (centralizer_le hYL))
  intro w hw
  have hsplit := FourModules.naturalDual_span_split hcore hR h
  let C := d.componentSpan c.L ⊓ centralizer (c.L : Set G)
  have hn : C ≤ normalizer (spanCommutator d c.L : Set G) :=
    (inf_le_left.trans ((d.componentSpan c.L).le_centralizer.trans
      (centralizer_le (spanCommutator_le_span d c.L)))).trans
        (Subgroup.centralizer_le_normalizer _)
  have hp : w ∈ (spanCommutator d c.L : Set G) * (C : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hn]
    exact hsplit ▸ hw.1
  obtain ⟨u, hu, z, hz, rfl⟩ := hp
  have huc : u ∈ centralizer (d.Yplus : Set G) := by
    have hzc := centralizer_le hYL hz.2
    exact (mul_mem_cancel_right hzc).mp hw.2
  let v : spanCommutator d c.L := ⟨u, hu⟩
  have hv : (h.coordinates v).toAdd = 0 := by
    apply hfixed
    intro g hg
    rw [← modelImage_yplus c h plane hYL hθ] at hg
    obtain ⟨l, hl, rfl⟩ := hg
    have he : commutatorAction d c.L l v = v := by
      apply Subtype.ext
      change (l : G) * u * (l : G)⁻¹ = u
      rw [huc l hl, mul_inv_cancel_right]
    rw [← h.equivariant, he]
  have hv1 : v = 1 := by
    apply h.coordinates.injective
    apply Multiplicative.toAdd.injective
    simpa using hv
  have hu1 : u = 1 := congrArg Subtype.val hv1
  change u * z ∈ C
  rw [hu1, one_mul]
  exact hz

private theorem first_choice_support (h : NaturalDual d L)
    [IsElementaryAbelian 2 (d.componentSpan L)]
    (hYL : d.Y ≤ L) (hspan : localSpan d.Z d.Y = d.V)
    (hsplit : spanCommutator d L ⊔ d.Z = spanCommutator d L ⊔ centralSupplement d L) :
    ∃ u : spanCommutator d L, (u : G) ∈ projectedCenter d L ∧
      (h.coordinates u).toAdd.2 ≠ 0 := by
  classical
  by_contra! hn
  let K := naturalPart h
  let C := d.componentSpan L ⊓ centralizer (L : Set G)
  have hZC : centralSupplement d L ≤ C :=
    le_inf (inf_le_left.trans (sup_le (spanCommutator_le_span d L)
      ((le_conjugateSpanBy _ _).trans (le_conjugateSpanBy d.V L)))) inf_le_right
  have hZK : projectedCenter d L ≤ K := by
    intro u hu
    exact (mem_naturalPart h ⟨u, hu.1⟩).mpr (hn ⟨u, hu.1⟩ hu)
  have hZ : d.Z ≤ K ⊔ C :=
    (center_le_projected_sup d L hsplit).trans (sup_le_sup hZK hZC)
  have hLC : L ≤ normalizer (C : Set G) :=
    (le_centralizer_iff.mp (show C ≤ centralizer (L : Set G) from inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hLN : L ≤ normalizer ((K ⊔ C : Subgroup G) : Set G) :=
    (le_inf (normalizes_naturalPart h) hLC).trans
      (normalizer_inf_normalizer_le_normalizer_sup K C)
  have hWN : d.componentSpan L ≤ K ⊔ C := by
    rw [span_eq_center_span hYL hspan]
    exact conjugateSpanBy_le hZ hLN
  have hCN : C ≤ normalizer (K : Set G) :=
    (inf_le_left.trans ((d.componentSpan L).le_centralizer.trans
      (centralizer_le ((naturalPart_le h).trans (spanCommutator_le_span d L))))).trans
        (Subgroup.centralizer_le_normalizer _)
  have hUK : spanCommutator d L ≤ K := by
    intro u hu
    have hp : u ∈ (K : Set G) * (C : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ hCN]
      exact hWN (spanCommutator_le_span d L hu)
    obtain ⟨k, hk, z, hz, rfl⟩ := hp
    have hzu : z ∈ spanCommutator d L :=
      (mul_mem_cancel_left (naturalPart_le h hk)).mp hu
    have hz1 : z = 1 := by
      have hmem : z ∈ spanCommutator d L ⊓ centralizer (L : Set G) := ⟨hzu, hz.2⟩
      rw [h.centralizer_eq_bot] at hmem
      exact hmem
    simpa [hz1] using hk
  obtain ⟨f, hf⟩ := exists_ne (0 : Module.Dual (ZMod 2) (Space 4))
  let u := h.coordinates.symm (Multiplicative.ofAdd (0, f))
  have he := (mem_naturalPart h u).mp (hUK u.property)
  rw [h.coordinates.apply_symm_apply] at he
  exact hf he

/-- The actual projected centre has a nonzero dual coordinate, under both
choices of 15.3.10. Only the independent plane-theta fixed-space calculation
is left as a model premise; no projected support or moving vector is assumed. -/
theorem exists_nonzero_dual_support [Finite G] {I : Subgroup G}
    (c : ComponentWitness d I) (h : NaturalDual d c.L)
    (plane : PlaneParabolic d c.L h.model)
    [IsElementaryAbelian 2 (d.componentSpan c.L)]
    (hYL : d.Yplus ≤ c.L) (hθ : theta (d.MI I) = d.Yplus)
    (hcore : c.L.pCoreIn 2 ≤ d.R) (hR : d.R ≤ centralizer (d.V : Set G))
    (hspan : localSpan d.Z d.Y = d.V)
    (hsplit : spanCommutator d c.L ⊔ d.Z =
      spanCommutator d c.L ⊔ centralSupplement d c.L)
    (hnormalizer : OutsideStructure.SecondChoice d → normalizer (d.V₁ : Set G) ≤ d.M)
    (hfixed : ∀ v : Space 4 × Module.Dual (ZMod 2) (Space 4),
      (∀ g ∈ theta (BinaryLinear.parabolic plane.plane),
        BinaryLinear.NaturalDualFlag.action g v = v) → v = 0) :
    ∃ u : spanCommutator d c.L, (u : G) ∈ projectedCenter d c.L ∧
      (h.coordinates u).toAdd.2 ≠ 0 := by
  rcases d.choice with hfirst | hsecond
  · exact first_choice_support h (by simpa only [hfirst] using hYL) hspan hsplit
  · exfalso
    apply c.outside
    have hYV : d.Yplus ≤ centralizer (d.V₁ : Set G) := by
      rw [hsecond.2]
      exact (map_subtype_le _).trans inf_le_right
    have hV : d.V₁ ≤ d.componentSpan c.L ⊓ centralizer (d.Yplus : Set G) :=
      le_inf ((d.action.plane_le 1).trans (le_conjugateSpanBy d.V c.L))
        (le_centralizer_iff.mp hYV)
    rw [fixed_in_span c h plane hYL hθ hcore hR hfixed] at hV
    exact ((le_centralizer_iff.mp (hV.trans inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)).trans (hnormalizer hsecond)
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.ProjectedAction.ProjectionSupport

end
