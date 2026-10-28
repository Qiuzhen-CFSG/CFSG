module
public import Theory.Representation.SymplecticConjugatePair.Ambient.TwoGeometry.ScalarKernel.NormalForm
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.OuterReduction

/-!
# Scalar kernel of the standard paired symplectic enlargement

The coefficient kernel is the commuting product of the separate scalars and
the full symplectic image. Conjugation identifies the symplectic factor because
Sp₄ in characteristic two has trivial center. A square-one element has trivial
scalar factor, since a characteristic-two field has no nontrivial square roots
of one. Diagram preservation detects exactly the summand-preserving subgroup;
the kernel of conjugation consists of the two independent scalar groups and
therefore has odd order.

Source: Aschbacher–Smith H.7, printed pp.388–389 of `refs/quasithin.pdf`.
The full Sp₄(2) image is retained throughout.
-/
@[expose] public section
open Representation BinaryOffender Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms
namespace SymplecticConjugatePair.Ambient
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] [Finite F] [CharP F 2]

lemma standardCoefficient_eq_one_iff_exists_scalar_full (g : standardPreserving (F := F)) :
    standardCoefficient g = 1 ↔
      ∃ (p : Fˣ × Fˣ) (x : Sp F), g.val = scalarHom p * fullHom x := by
  constructor
  · exact standard_coefficient_kernel_normalForm g
  · rintro ⟨p,x,h⟩
    have hg : g = scalarPreservingHom p * fullPreservingHom x := Subtype.ext h
    rw [hg, map_mul, standardCoefficient_scalarPreservingHom,
      standardCoefficient_fullPreservingHom, one_mul]

/-- On the preserving subgroup the coefficient is trivial exactly for inner conjugation. -/
theorem standardCoefficient_eq_one_iff_inner (g : standardPreserving (F := F)) :
    standardCoefficient g = 1 ↔ standardConjugation g.val ∈ MulAut.innerSubgroup (Sp F) := by
  obtain ⟨p,x,h⟩ := standard_coefficient_normalForm g
  have hc : standardConjugation g.val =
      MulAut.conj x * fieldAutomorphism (standardCoefficient g) := by
    rw [h, map_mul, map_mul, standardConjugation_scalarHom,
      standardConjugation_fullHom, standardConjugation_fieldHom, one_mul]
  constructor
  · intro hg
    rw [hc, hg, show fieldAutomorphism (1 : F ≃+* F) = 1 from fieldAutomorphismHom.map_one,
      mul_one]
    exact ⟨x,rfl⟩
  · intro hg
    apply field_eq_one_of_inner
    rw [hc] at hg
    exact (MulAut.innerSubgroup (Sp F)).mul_mem_cancel_left (show MulAut.conj x ∈
      MulAut.innerSubgroup (Sp F) from ⟨x,rfl⟩) |>.mp hg

omit [Algebra (ZMod 2) F] in
private lemma units_square_one (a : Fˣ) (ha : a^2 = 1) : a = 1 := by
  apply Units.ext
  apply (frobeniusEquiv F 2).injective
  change (a : F)^2 = (1 : F)^2
  simpa only [Units.val_pow_eq_pow_val, Units.val_one, one_pow] using congrArg Units.val ha

/-- The precise unconditional kernel interface consumed by the H.7 reductions. -/
theorem standard_square_one_coefficient_kernel_le_full
    (g : standardPreserving (F := F)) (hg : g^2 = 1) (hc : standardCoefficient g = 1) :
    g.val ∈ fullHom.range := by
  obtain ⟨p,x,h⟩ := standard_coefficient_kernel_normalForm g hc
  have hsq : g.val^2 = 1 := congrArg Subtype.val hg
  have hx : x^2 = 1 := by
    apply inner_injective
    have he := congrArg standardConjugation hsq
    simpa only [h, map_pow, map_mul, standardConjugation_scalarHom,
      standardConjugation_fullHom, one_mul, map_one] using he
  have hp : p^2 = 1 := by
    apply scalarHom_injective
    rw [map_pow, map_one]
    rw [h, (scalarHom_commute_fullHom p x).mul_pow 2, ← map_pow fullHom, hx, map_one,
      mul_one] at hsq
    exact hsq
  have hp1 : p = 1 := Prod.ext
    (units_square_one p.1 (congrArg Prod.fst hp))
    (units_square_one p.2 (congrArg Prod.snd hp))
  exact ⟨x, by simpa only [hp1, map_one, one_mul] using h.symm⟩

private lemma subgroup_map_aut_mul {G : Type*} [Group G] (P : Subgroup G)
    (a b : MulAut G) :
    P.map (a*b).toMonoidHom = (P.map b.toMonoidHom).map a.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private lemma subgroup_map_conj_aut {G : Type*} [Group G] (P : Subgroup G)
    (a : MulAut G) (x : G) :
    (P.map (MulAut.conj x).toMonoidHom).map a.toMonoidHom =
      (P.map a.toMonoidHom).map (MulAut.conj (a x)).toMonoidHom := by
  simp only [Subgroup.map_map]
  congr 1
  ext y
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

omit [Algebra (ZMod 2) F] [Finite F] [CharP F 2] in
private lemma preservesParabolicClass_mul (a b : MulAut (Sp F)) (P : Subgroup (Sp F))
    (ha : PreservesParabolicClass a P) (hb : PreservesParabolicClass b P) :
    PreservesParabolicClass (a*b) P := by
  obtain ⟨x,hx⟩ := ha
  obtain ⟨y,hy⟩ := hb
  refine ⟨a y * x, ?_⟩
  rw [subgroup_map_aut_mul, hy, subgroup_map_conj_aut, hx,
    ← subgroup_map_aut_mul, ← map_mul]

omit [Algebra (ZMod 2) F] [Finite F] [CharP F 2] in
private lemma preservesDiagram_mul (a b : MulAut (Sp F))
    (ha : PreservesDiagram a) (hb : PreservesDiagram b) : PreservesDiagram (a*b) :=
  ⟨preservesParabolicClass_mul a b _ ha.1 hb.1,
    preservesParabolicClass_mul a b _ ha.2 hb.2⟩

omit [Algebra (ZMod 2) F] [Finite F] [CharP F 2] in
private lemma inner_field_preservesDiagram (x : Sp F) (σ : F ≃+* F) :
    PreservesDiagram (MulAut.conj x * fieldAutomorphism σ) :=
  preservesDiagram_mul _ _ (inner_preservesDiagram x) (field_preservesDiagram σ)

omit [Algebra (ZMod 2) F] in
private lemma inner_field_graph_not_preservesDiagram (x : Sp F) (σ : F ≃+* F) :
    ¬ PreservesDiagram (MulAut.conj x * fieldAutomorphism σ * graphAut) := by
  intro h
  have hback : PreservesDiagram ((MulAut.conj x * fieldAutomorphism σ)⁻¹) := by
    rw [mul_inv_rev, ← map_inv MulAut.conj]
    change PreservesDiagram ((fieldAutomorphismHom σ)⁻¹ * MulAut.conj x⁻¹)
    rw [← map_inv]
    exact preservesDiagram_mul _ _ (field_preservesDiagram σ⁻¹) (inner_preservesDiagram x⁻¹)
  have hc := preservesDiagram_mul _ _ hback h
  rw [inv_mul_cancel_left] at hc
  exact graphAut_not_preservesDiagram hc

/-- The diagram action records precisely whether an operator interchanges the summands. -/
theorem standardConjugation_preservesDiagram_iff (s : standardAmbient (F := F)) :
    PreservesDiagram (standardConjugation s) ↔ s ∈ standardPreserving := by
  obtain ⟨p,x,σ,h | h⟩ := standard_normalForm s
  · have hc : standardConjugation s = MulAut.conj x * fieldAutomorphism σ := by
      simp only [h, map_mul, standardConjugation_scalarHom,
        standardConjugation_fullHom, standardConjugation_fieldHom, one_mul]
    exact iff_of_true (hc ▸ inner_field_preservesDiagram x σ) (h ▸ standard_diagonal_mem p x σ)
  · have hc : standardConjugation s = MulAut.conj x * fieldAutomorphism σ * graphAut := by
      simp only [h, map_mul, standardConjugation_scalarHom,
        standardConjugation_fullHom, standardConjugation_fieldHom,
        standardConjugation_graphActor, one_mul]
    have hn : s ∉ standardPreserving := by
      rw [h, standardPreserving.mul_mem_cancel_left (standard_diagonal_mem p x σ)]
      exact swapping_not_mem_stabilizer standardAction graphActor_swapsSummands
    exact iff_of_false (hc ▸ inner_field_graph_not_preservesDiagram x σ) hn

/-- Conjugation has exactly the two independent scalar groups as its kernel. -/
theorem standardConjugation_ker :
    (standardConjugation (F := F)).ker = scalarHom.range := by
  apply le_antisymm
  · intro s hs
    have hs1 : standardConjugation s = 1 := hs
    have hn : s ∈ standardPreserving :=
      (standardConjugation_preservesDiagram_iff s).mp (by
        rw [hs1, ← map_one MulAut.conj]
        exact inner_preservesDiagram 1)
    let g : standardPreserving (F := F) := ⟨s,hn⟩
    have hg : standardCoefficient g = 1 :=
      (standardCoefficient_eq_one_iff_inner g).mpr (by
        change standardConjugation s ∈ _
        rw [hs1]
        exact Subgroup.one_mem _)
    obtain ⟨p,x,h⟩ := standard_coefficient_kernel_normalForm g hg
    have hx : x = 1 := by
      apply inner_injective
      have he := congrArg standardConjugation h
      change standardConjugation s = _ at he
      simpa only [hs1, map_mul, standardConjugation_scalarHom,
        standardConjugation_fullHom, one_mul, map_one] using he.symm
    exact ⟨p, by simpa only [hx, map_one, mul_one] using h.symm⟩
  · rintro _ ⟨p,rfl⟩
    exact standardConjugation_scalarHom p

lemma standardConjugation_kernel_card :
    Nat.card (standardConjugation (F := F)).ker = (Nat.card F - 1)^2 := by
  rw [standardConjugation_ker,
    ← Nat.card_congr (MonoidHom.ofInjective (scalarHom_injective (F := F))).toEquiv,
    Nat.card_prod, Nat.card_units, pow_two]

theorem standardConjugation_kernel_odd : Odd (Nat.card (standardConjugation (F := F)).ker) := by
  let _ := Fintype.ofFinite F
  obtain ⟨n,_,hn⟩ := FiniteField.card F 2
  have he : Even (Nat.card F) := by
    rw [Nat.card_eq_fintype_card, hn]
    exact (even_iff_two_dvd.mpr (dvd_pow_self 2 n.ne_zero))
  have hp : 0 < Nat.card F := Nat.card_pos
  have ho : Odd (Nat.card F - 1) := by
    rw [Nat.odd_iff]
    have h := even_iff_two_dvd.mp he
    omega
  rw [standardConjugation_kernel_card]
  exact ho.pow
end SymplecticConjugatePair.Ambient
