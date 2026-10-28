module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.ExceptionalActions.G2Placement.Parabolic
public import Theory.AtlasPort.LinearGroups.G2.OddSubgroupPlacement
public import Theory.AtlasPort.LinearGroups.G2.SolvableParabolic

/-!
# Simultaneous G₂ Sylow and split-torus placement

The actual Sylow three-complement pair is placed in a proper parabolic by
`G2Placement.Parabolic`. For q > 2, `SolvableParabolic.normalizes` proves that
every solvable overgroup of a Sylow two-subgroup inside either full parabolic
normalizes that Sylow subgroup. Thus the complement lies in its Borel
normalizer. Sylow conjugacy then identifies the Sylow with the positive-root
subgroup, and conjugacy inside the Borel puts the three-group in the split
torus without moving that positive-root subgroup.

`g2_placement` assembles this argument with no additional geometric premise.
`g2_placement_of_card_eq_two_pow` uses the source parameters q = 2^f, f ≥ 2,
deriving characteristic two from the field order. Automorphism coverage and
the action calculation belong to the existing `ExceptionalActions.G2` consumer.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528). The argument applies at p = 3 and does not invoke A.3.15's
p > 3 classification.
-/

@[expose] public section

open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.ExceptionalActions
variable {Q F : Type*} [Group Q] [Finite Q] [Field F] [Finite F] [CharP F 2]
variable {S : Sylow 2 Q} {R : Subgroup Q}

private theorem g2_sylow_placement (S : Sylow 2 Q) (e : Q ≃* Model F) :
    ∃ e' : Q ≃* Model F, (S : Subgroup Q).map e'.toMonoidHom = unipotent := by
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Model F) T (sylow (F := F))
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  change (S : Subgroup Q).map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
  rw [← map_map]
  exact congrArg Sylow.toSubgroup hg

/-- Once the complement normalizes the Sylow subgroup, Sylow conjugacy followed
by conjugacy inside the Borel places the two subgroups simultaneously. -/
theorem g2_placement_of_normalizes (h : PairInput S R) (e : Q ≃* Model F)
    (hN : R ≤ normalizer (S : Set Q)) :
    ∃ e' : Q ≃* Model F,
      (S : Subgroup Q).map e'.toMonoidHom = unipotent ∧
      R.map e'.toMonoidHom ≤ splitTorus := by
  obtain ⟨e₀, hS⟩ := g2_sylow_placement S e
  have hRb : R.map e₀.toMonoidHom ≤ Atlas.G2.borel := by
    rw [← SylowNormalizer.normalizer_unipotent, ← hS, ← map_equiv_normalizer_eq]
    exact map_mono hN
  obtain ⟨g, hg, hRg⟩ := OddSubgroupPlacement.conjugate_borel_pSubgroup_into_torus
    (R.map e₀.toMonoidHom) (h.oddComplement.isPGroup.map e₀.toMonoidHom)
    (by decide : 3 ≠ 2) hRb
  have hU : (unipotent (K := F)).map (MulAut.conj g).toMonoidHom = unipotent := by
    apply mem_normalizer_iff_map_conj_eq.mp
    rwa [SylowNormalizer.normalizer_unipotent]
  refine ⟨e₀.trans (MulAut.conj g), ?_, ?_⟩
  · change (S : Subgroup Q).map ((MulAut.conj g).toMonoidHom.comp e₀.toMonoidHom) = _
    rw [← map_map, hS, hU]
  · change R.map ((MulAut.conj g).toMonoidHom.comp e₀.toMonoidHom) ≤ _
    rw [← map_map]
    exact hRg

/-- The remaining geometric input is confined to solvable overgroups inside
the actual parabolics. Proper-parabolic containment and torus conjugacy are
proved here. This conditional theorem does not discharge that input. -/
theorem g2_placement_of_parabolic_normalization (h : PairInput S R) (e : Q ≃* Model F)
    (hrefine : ∀ (T : Sylow 2 (Model F)) (H : Subgroup (Model F)),
      (T : Subgroup (Model F)) ≤ H → Group.IsSolvable H →
      (H ≤ parabolic₁ ∨ H ≤ parabolic₂) → H ≤ normalizer (T : Set (Model F))) :
    ∃ e' : Q ≃* Model F,
      (S : Subgroup Q).map e'.toMonoidHom = unipotent ∧
      R.map e'.toMonoidHom ≤ splitTorus := by
  obtain ⟨e₀, he⟩ := g2_product_parabolic h e
  let H := R ⊔ (S : Subgroup Q)
  let T := S.mapSurjective (f := e₀.toMonoidHom) e₀.surjective
  let K := H.map e₀.toMonoidHom
  have hTK : (T : Subgroup (Model F)) ≤ K := map_mono le_sup_right
  let _ : Group.IsSolvable H := product_solvable h
  have hK : Group.IsSolvable K :=
    Group.isSolvable_of_surjective
      (f := (H.equivMapOfInjective e₀.toMonoidHom e₀.injective).toMonoidHom)
      (H.equivMapOfInjective e₀.toMonoidHom e₀.injective).surjective
  have hnorm := hrefine T K hTK hK he
  apply g2_placement_of_normalizes h e₀
  have hR : R.map e₀.toMonoidHom ≤ normalizer (T : Set (Model F)) :=
    (map_mono (show R ≤ H from le_sup_left)).trans hnorm
  change R.map e₀.toMonoidHom ≤
    normalizer (((S : Subgroup Q).map e₀.toMonoidHom) : Set (Model F)) at hR
  rw [← map_equiv_normalizer_eq] at hR
  exact (map_le_map_iff_of_injective e₀.injective).mp hR

/-- Over a finite field of characteristic two and order greater than two, the
actual pair admits simultaneous positive-root Sylow and split-torus coordinates.
Proper-parabolic containment, Borel refinement, and torus conjugacy are all
discharged from the pair and the actual model equivalence. -/
theorem g2_placement (h : PairInput S R) (e : Q ≃* Model F)
    (hq : 2 < Nat.card F) :
    ∃ e' : Q ≃* Model F,
      (S : Subgroup Q).map e'.toMonoidHom = unipotent ∧
      R.map e'.toMonoidHom ≤ splitTorus :=
  g2_placement_of_parabolic_normalization h e (SolvableParabolic.normalizes hq)

omit [CharP F 2] in
/-- Source-parameter form of simultaneous placement for G₂(2^f), f ≥ 2.
The field cardinality supplies characteristic two; no Borel, parabolic, or
normalization hypothesis is required. -/
theorem g2_placement_of_card_eq_two_pow (h : PairInput S R) (e : Q ≃* Model F)
    {f : ℕ} (hf : 2 ≤ f) (hF : Nat.card F = 2 ^ f) :
    ∃ e' : Q ≃* Model F,
      (S : Subgroup Q).map e'.toMonoidHom = unipotent ∧
      R.map e'.toMonoidHom ≤ splitTorus := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  apply g2_placement h e
  calc
    2 < 2 ^ 2 := by decide
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by decide) hf
    _ = Nat.card F := hF.symm

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.ExceptionalActions
