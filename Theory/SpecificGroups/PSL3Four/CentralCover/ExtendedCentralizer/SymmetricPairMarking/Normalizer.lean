module


public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.Geometry

/-!
# Packing the actual common normalizer

Marked coordinates on the order36 common normalizer supply the precise
NormalizerGeometry record. Its normal cubic subgroup is the Sylow
three-group, and the literal component intersection identifies its linear
factor. The existential theorem preserves both original involutions.

Source: Aschbacher–Smith15.3.38, printed pp.1136–1137.
-/

public noncomputable section
open Subgroup
namespace Matrix.PSL3Four.ExtendedCentralizer.SymmetricPairMarking
variable {I : Type*} [Group I] {L : Subgroup I} [L.Normal]

private def CubicPair : Subgroup (SymmetricThree × SymmetricThree) :=
  (zpowers rotation).prod (zpowers rotation)
private abbrev LinearCubic : Subgroup (SymmetricThree × SymmetricThree) :=
  (zpowers rotation).prod ⊥
private def DiagonalCubic : Subgroup (SymmetricThree × SymmetricThree) :=
  (⊥ : Subgroup SymmetricThree).prod (zpowers rotation)

private theorem cubicPair_characterization (x : SymmetricThree × SymmetricThree) :
    x ∈ CubicPair ↔ x ^ 3 = 1 := by
  have hrot : orderOf rotation = 3 := orderOf_eq_prime_iff.mpr ⟨by decide +kernel, by decide +kernel⟩
  have hclass : ∀ y : SymmetricThree,
      y ^ 3 = 1 → y = 1 ∨ y = rotation ∨ y = rotation ^ 2 := by decide +kernel
  have h (y : SymmetricThree) : y ∈ zpowers rotation ↔ y ^ 3 = 1 := by
    constructor
    · intro hy
      apply orderOf_dvd_iff_pow_eq_one.mp
      simpa only [hrot] using orderOf_dvd_of_mem_zpowers hy
    · intro hy
      rcases hclass y hy with rfl | rfl | rfl
      · exact one_mem _
      · exact mem_zpowers _
      · exact pow_mem (mem_zpowers _) _
  change (x.1 ∈ zpowers rotation ∧ x.2 ∈ zpowers rotation) ↔ _
  rw [h, h]
  exact ⟨fun hs => Prod.ext hs.1 hs.2,
    fun hs => ⟨congrArg Prod.fst hs, congrArg Prod.snd hs⟩⟩

private instance cubicPair_normal : CubicPair.Normal := by
  refine ⟨?_⟩
  intro x hx g
  apply (cubicPair_characterization _).mpr
  change ((MulAut.conj g) x) ^ 3 = 1
  rw [← map_pow, (cubicPair_characterization _).mp hx, map_one]

private theorem cubicPair_card : Nat.card CubicPair = 9 := by
  rw [CubicPair, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,
    Nat.card_prod, Nat.card_zpowers]
  have h : orderOf rotation = 3 := orderOf_eq_prime_iff.mpr ⟨by decide +kernel, by decide +kernel⟩
  rw [h]

/-- Coordinates on the actual order-thirty-six normalizer suffice to package
extended-centralizer geometry. The larger solvable source subgroup need not
be retained in this auxiliary record. -/
def of_marked_normalizer (d : Overgroup L) (N : Subgroup I)
    (e : N ≃* (SymmetricThree × SymmetricThree))
    (tau field : N) (ht : e tau = (1, reflection))
    (hf : e field = (reflection, reflection))
    (hlinear : (L.comap N.subtype).map e.toMonoidHom = (zpowers rotation).prod ⊥)
    (hgraph : IsConj (projectiveAction L d.cover tau) (PSL3.OuterSolvable.graph F))
    (hfield : IsConj (projectiveAction L d.cover field) pslFrobenius)
    (hcenter : ((tau : I) * (field : I)) ∈
      centralizer ((center L).map L.subtype : Set I)) : NormalizerGeometry d := by
  let C : Subgroup N := CubicPair.comap e.toMonoidHom
  let D : Subgroup N := DiagonalCubic.comap e.toMonoidHom
  let : Finite N := Finite.of_equiv _ e.symm.toEquiv
  have hCcard : Nat.card C = 9 := by
    let j := e.subgroupMap C
    have hm : C.map e.toMonoidHom = CubicPair :=
      map_comap_eq_self_of_surjective e.surjective CubicPair
    exact (Nat.card_congr (j.trans (MulEquiv.subgroupCongr hm)).toEquiv).trans cubicPair_card
  have hNcard : Nat.card N = 36 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  let X : Sylow 3 N := Sylow.ofCard C (by rw [hCcard, hNcard]; decide +kernel)
  have hX : (X : Subgroup N) = C := rfl
  let : C.Normal := inferInstanceAs (CubicPair.comap e.toMonoidHom).Normal
  have hn : normalizer (X : Set N) = ⊤ := by
    change normalizer (C : Set N) = ⊤
    exact C.normalizer_eq_top
  let q : normalizer (X : Set N) ≃* (SymmetricThree × SymmetricThree) :=
    ((MulEquiv.subgroupCongr hn).trans topEquiv).trans e
  have hmap (A : Subgroup N) :
      (A.subgroupOf (normalizer (X : Set N))).map q.toMonoidHom = A.map e.toMonoidHom := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, by rw [hn]; exact mem_top a⟩, ha, rfl⟩
  have hLC : L.comap N.subtype ≤ C := by
    intro x hx
    have hm := mem_map_of_mem e.toMonoidHom hx
    rw [hlinear] at hm
    refine ⟨hm.1, ?_⟩
    have he : (e x).2 = 1 := hm.2
    change (e x).2 ∈ zpowers rotation
    rw [he]
    exact one_mem _
  refine {
    YS := N
    X := X
    XD := D
    XD_le_three := ?_
    coordinates := q
    tau := ⟨tau, by rw [hn]; exact mem_top tau⟩
    field := ⟨field, by rw [hn]; exact mem_top field⟩
    tau_coordinates := ht
    field_coordinates := hf
    three_coordinates := ?_
    linear_coordinates := ?_
    diagonal_coordinates := ?_
    tau_graph := hgraph
    field_frobenius := hfield
    graphField_centralizes_center := hcenter }
  · intro x hx
    change x ∈ C
    refine ⟨?_, hx.2⟩
    have he : (e x).1 = 1 := hx.1
    change (e x).1 ∈ zpowers rotation
    rw [he]
    exact one_mem _
  · rw [hmap, hX]
    exact map_comap_eq_self_of_surjective e.surjective CubicPair
  · rw [hmap, hX, inf_eq_right.mpr hLC, hlinear]
  · rw [hmap]
    exact map_comap_eq_self_of_surjective e.surjective DiagonalCubic

theorem exists_of_marked_normalizer (d : Overgroup L) (N : Subgroup I)
    (e : N ≃* (SymmetricThree × SymmetricThree))
    (tau field : N) (ht : e tau = (1, reflection))
    (hf : e field = (reflection, reflection))
    (hlinear : (L.comap N.subtype).map e.toMonoidHom = (zpowers rotation).prod ⊥)
    (hgraph : IsConj (projectiveAction L d.cover tau) (PSL3.OuterSolvable.graph F))
    (hfield : IsConj (projectiveAction L d.cover field) pslFrobenius)
    (hcenter : ((tau : I) * (field : I)) ∈
      centralizer ((center L).map L.subtype : Set I)) :
    ∃ n : NormalizerGeometry d, n.tauI = (tau : I) ∧ n.fieldI = (field : I) := by
  exact ⟨of_marked_normalizer d N e tau field ht hf hlinear hgraph hfield hcenter, rfl, rfl⟩

end Matrix.PSL3Four.ExtendedCentralizer.SymmetricPairMarking
end
