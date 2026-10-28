module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.OddThreeLift
public import Theory.SpecificGroups.GL2.SylowNormalizedFive
public import Theory.SpecificGroups.SU3.UnitaryTwoSylowNormalizedFive
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.CoverSeparation

/-!
# The original SL₂(5) odd ternary parameter branch

The binary SL₂(5) alternative retains its central involution. The full
Sylow normalizer centralizes this involution, so the actual odd ternary
involution centralizer lifts to GL₂ or GU₂ through its cubic scalar kernel.
The determinant kernel preserves the smaller cover and the full Sylow.
Prime-field PGL₂ recognition then forces the odd ternary parameter to be
five, retaining the signed model on the literal larger quotient.

Source: Aschbacher–Smith A.3.12(9), pp.47–48, C.5.12, p.163.
-/

public section
open Subgroup Matrix Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem sl2_five_equiv_zmod (h : IsSL G 2 5) : Nonempty (G ≃* SL(2,ZMod 5)) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
  let : Fintype F := Fintype.ofFinite F
  let a : F ≃+* ZMod 5 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card,hF,ZMod.card])
  exact ⟨e.trans (GorensteinWalter.sl2RingEquiv a)⟩

omit [Finite G] in
private theorem sl2_transport {H : Type*} [Group H] (e : G ≃* H) (h : IsSL G 2 5) :
    IsSL H 2 5 := by
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := h
  exact ⟨F,inferInstance,inferInstance,hF,⟨e.symm.trans a⟩⟩

/-- The actual projective-linear ternary centralizer reduction, with its
full Sylow and smaller cover, forces characteristic five. -/
theorem projective_linear_sl2_five_parameter
    {F : Type*} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hF : Nat.card F = p)
    (T : Sylow 2 (PSL(3,F))) (B : Subgroup (PSL(3,F))) [IsQuasisimple B]
    (hB : IsSL B 2 5)
    (hTB : (T : Subgroup (PSL(3,F))) ≤ normalizer (B : Set (PSL(3,F)))) : p = 5 := by
  let : Fact p.Prime := ⟨hp⟩
  have h2 := Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card ho
    (k := 1) (by simpa using hF)
  obtain ⟨S,A,⟨a⟩,_,hSA⟩ := projective_linear_sl2_five_rank_one_lift h2 T B hB hTB
  obtain ⟨b⟩ := sl2_five_equiv_zmod hB
  exact GeneralLinearGroup.prime_eq_five_of_sylow_normalizes_sl2_five ho hF S A
    ⟨a.trans b⟩ hSA

/-- The intrinsic form is invariant under the source's actual marked
projective-linear model isomorphism. -/
theorem linear_three_projective_sl2_five_parameter
    (T : Sylow 2 G) (B : Subgroup G) [IsQuasisimple B]
    (hB : IsSL B 2 5) (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hm : ClassicalGroup.IsPSL G 3 p) : p = 5 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let S := T.mapSurjective (f := e.toMonoidHom) e.surjective
  let A := B.map e.toMonoidHom
  let a : B ≃* A := B.equivMapOfInjective e.toMonoidHom e.injective
  let : IsQuasisimple A := IsQuasisimple.of_mulEquiv a
  exact projective_linear_sl2_five_parameter hp ho hF S A (sl2_transport a hB)
    ((map_mono hTB).trans (B.le_normalizer_map e.toMonoidHom))


/-- A cubic central projectivization retains the smaller SL₂(5), the
original full Sylow, and normalization, with no quotient identification
assumed for the smaller subgroup. -/
private theorem central_cube_projection_sl2_five
    {H : Type*} [Group H] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) (hk : f.ker ≤ center G)
    (h3 : ∀ x ∈ f.ker, x ^ 3 = 1)
    (T : Sylow 2 G) (B : Subgroup G) [IsQuasisimple B]
    (hB : IsSL B 2 5) (hTB : (T : Subgroup G) ≤ normalizer (B : Set G)) :
    let A := B.map f
    IsQuasisimple A ∧ IsSL A 2 5 ∧
      (T.mapSurjective hf : Subgroup H) ≤ normalizer (A : Set H) := by
  let e := MulEquiv.ofBijective (f.subgroupMap B)
    ⟨Theory.SpecificGroups.OddThreeLevi.injective_on_subgroup_of_center_two f hk h3 B
      (sl2_five_center_card hB),f.subgroupMap_surjective B⟩
  exact ⟨IsQuasisimple.of_mulEquiv e,sl2_transport e hB,
    (map_mono hTB).trans (B.le_normalizer_map f)⟩

/-- Special linear degree three has the same prime-five restriction;
the actual projection has a cubic central kernel and preserves SL₂(5). -/
theorem special_linear_sl2_five_parameter
    {F : Type*} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hF : Nat.card F = p)
    (T : Sylow 2 (SL(3,F))) (B : Subgroup (SL(3,F))) [IsQuasisimple B]
    (hB : IsSL B 2 5)
    (hTB : (T : Subgroup (SL(3,F))) ≤ normalizer (B : Set (SL(3,F)))) : p = 5 := by
  let f := PSL3.projection F
  have hk : f.ker ≤ center (SL(3,F)) := by rw [PSL3.projection_ker]
  have h3 : ∀ x ∈ f.ker, x ^ 3 = 1 := by
    intro x hx
    have hd := (orderOf_dvd_natCard (⟨x,hk hx⟩ : center (SL(3,F)))).trans
      (SL3.card_center_dvd_three F)
    exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp hd)
  obtain ⟨hA,hm,hn⟩ := central_cube_projection_sl2_five f (PSL3.projection_surjective F)
    hk h3 T B hB hTB
  let : IsQuasisimple (B.map f) := hA
  exact projective_linear_sl2_five_parameter hp ho hF
    (T.mapSurjective (PSL3.projection_surjective F)) (B.map f) hm hn

/-- Both linear ternary markings force five for a full-Sylow-normalized
SL₂(5) subgroup. -/
theorem linear_three_sl2_five_parameter
    (T : Sylow 2 G) (B : Subgroup G) [IsQuasisimple B]
    (hB : IsSL B 2 5) (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL G 3 p ∨ IsSL G 3 p) : p = 5 := by
  rcases hm with hm | hm
  · exact linear_three_projective_sl2_five_parameter T B hB hTB hp ho hm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let S := T.mapSurjective (f := e.toMonoidHom) e.surjective
    let A := B.map e.toMonoidHom
    let a : B ≃* A := B.equivMapOfInjective e.toMonoidHom e.injective
    let : IsQuasisimple A := IsQuasisimple.of_mulEquiv a
    exact special_linear_sl2_five_parameter hp ho hF S A (sl2_transport a hB)
      ((map_mono hTB).trans (B.le_normalizer_map e.toMonoidHom))


/-- The actual projective-unitary ternary centralizer reduction forces
characteristic five through the full GU₂ Sylow normalizer. -/
theorem projective_unitary_sl2_five_parameter
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (F : Type*) [Field F] [Finite F] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (T : Sylow 2 (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J))
    (B : Subgroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)) [IsQuasisimple B]
    (hB : IsSL B 2 5)
    (hTB : (T : Subgroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)) ≤
      normalizer (B : Set (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J))) : p = 5 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨S,A,⟨a⟩,_,hSA⟩ := projective_unitary_sl2_five_rank_one_lift p ho F J hcard hc T B hB hTB
  obtain ⟨b⟩ := sl2_five_equiv_zmod hB
  exact ABG.GU2_prime_eq_five_of_sylow_normalizes_sl2_five p ho S A ⟨a.trans b⟩ hSA

/-- Special unitary projectivization has central cubic kernel and preserves
the full-Sylow-normalized SL₂(5) subgroup faithfully. -/
theorem special_unitary_sl2_five_parameter
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (F : Type*) [Field F] [Finite F] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (T : Sylow 2 J.specialSubgroup) (B : Subgroup J.specialSubgroup) [IsQuasisimple B]
    (hB : IsSL B 2 5)
    (hTB : (T : Subgroup J.specialSubgroup) ≤ normalizer (B : Set J.specialSubgroup)) : p = 5 := by
  let f := J.specialToProjective
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective f J.specialToProjective_surjective
  have h3 : ∀ x ∈ f.ker, x ^ 3 = 1 := fun x hx =>
    congrArg Subtype.val (J.specialToProjective_ker_cube ⟨x,hx⟩)
  obtain ⟨hA,hm,hn⟩ := central_cube_projection_sl2_five f J.specialToProjective_surjective
    J.specialToProjective_ker_le_center h3 T B hB hTB
  let : IsQuasisimple (B.map f) := hA
  exact projective_unitary_sl2_five_parameter hp ho F J hcard hc
    (T.mapSurjective J.specialToProjective_surjective) (B.map f) hm hn

/-- Every signed odd ternary group containing a full-Sylow-normalized
SL₂(5) subgroup has the prime-field parameter five. -/
theorem odd_three_sl2_five_parameter
    (T : Sylow 2 G) (B : Subgroup G) [IsQuasisimple B]
    (hB : IsSL B 2 5) (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool)
    (hm : IsPSLSign G u 3 p ∨ IsSLSign G u 3 p) : p = 5 := by
  cases u with
  | false => exact linear_three_sl2_five_parameter T B hB hTB hp ho hm
  | true =>
    rcases hm with hm | hm
    · obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
      let S := T.mapSurjective (f := e.toMonoidHom) e.surjective
      let A := B.map e.toMonoidHom
      let a : B ≃* A := B.equivMapOfInjective e.toMonoidHom e.injective
      let : IsQuasisimple A := IsQuasisimple.of_mulEquiv a
      exact projective_unitary_sl2_five_parameter hp ho F J hF hc S A (sl2_transport a hB)
        ((map_mono hTB).trans (B.le_normalizer_map e.toMonoidHom))
    · obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
      let S := T.mapSurjective (f := e.toMonoidHom) e.surjective
      let A := B.map e.toMonoidHom
      let a : B ≃* A := B.equivMapOfInjective e.toMonoidHom e.injective
      let : IsQuasisimple A := IsQuasisimple.of_mulEquiv a
      exact special_unitary_sl2_five_parameter hp ho F J hF hc S A (sl2_transport a hB)
        ((map_mono hTB).trans (B.le_normalizer_map e.toMonoidHom))

/-- The actual containing-group interface restricts the full original
Sylow, so no faithful-action or A.3.12 premise is added. -/
theorem odd_three_containing_sl2_five_parameter
    (T : Sylow 2 G) (B D : Subgroup G) [IsQuasisimple B]
    (hBD : B ≤ D) (hD : D.IsSubnormal)
    (hB : IsSL B 2 5) (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool)
    (hm : IsPSLSign D u 3 p ∨ IsSLSign D u 3 p) : p = 5 := by
  obtain ⟨S,hS⟩ := T.exists_subgroupOf_eq_of_subnormal D hD
  let e := subgroupOfEquivOfLe hBD
  let : IsQuasisimple (B.subgroupOf D) := IsQuasisimple.of_mulEquiv e.symm
  apply odd_three_sl2_five_parameter S (B.subgroupOf D) (sl2_transport e.symm hB) ?_ hp ho u hm
  rw [hS,← subgroupOf_normalizer_eq hBD]
  exact subgroupOf_mono D hTB


open ConjugateSource.RankOne Chapter1.Section02

/-- The odd ternary branch on the original larger-span image has parameter
five, with both the binary smaller-image obstruction and the central-cover
alternative discharged from the actual source data. -/
theorem source_larger_odd_three_parameter
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hUT : U K ≤ T) (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hVC : conjugateSpanBy (U K) X ≤ centralizer (U K : Set G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool)
    (hm : let E := ((conjugateSpanBy K X).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
      IsPSLSign E u 3 p ∨ IsSLSign E u 3 p) : p = 5 := by
  have hKX : K ≤ X := le_sup_left.trans hAX
  let r := QuotientGroup.mk' (pCore 2 X)
  let B := (K.subgroupOf X).map r
  let D := conjugateSpanBy K X
  let E := (D.subgroupOf X).map r
  let Q := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))
  have hsmall := noncubic_twoCore_small_models_with_quotient
    K T X hK h3 hUT hT hTK hKX hX S hS hVC
  let : IsQuasisimple B := hsmall.1
  have hB := (source_larger_odd_three_forces_small_cover hG K T X hK h3 hUT hT hTK
    hAX hX S hS hVC hp ho u hm).2
  have hD := source_larger_span_component_knownSimple hG K T X hK h3 hTK hAX hX S hS
  let := pCore_isNilpotent (p := 2) (G := X)
  have hE : E.IsCComponent := hD.map_quotient (pCore 2 X)
  apply odd_three_containing_sl2_five_parameter Q B E
    (map_mono (subgroupOf_mono X (le_conjugateSpanBy K X))) hE.subnormal hB ?_ hp ho u hm
  change (S : Subgroup X).map r ≤ normalizer (B : Set (X ⧸ pCore 2 X))
  apply (map_mono (f := r) ?_).trans (le_normalizer_map _)
  rw [← subgroupOf_normalizer_eq hKX]
  intro s hs
  exact hTK (hS ▸ mem_map_of_mem X.subtype hs)

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
