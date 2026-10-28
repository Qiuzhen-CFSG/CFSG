module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Reduction
public import Theory.SpecificGroups.SL3.SplitMonomial

/-!
# Sylow placement and transport for the extraspecial split pair

Permutability gives |RS:R| = |S|, so R is Sylow three in RS. Its local
three-core therefore lies in R, and restriction to R does not change the
core's order. Actual model equivalences preserve this order and carry S
to a full Sylow two-subgroup of the model.

`MonomialPlacement` specifies the remaining geometric witness using the
actual linear or projective monomial subgroup. It does not assert that
the witness exists. The geometric placement and the monomial core order
are separate inputs to the final assembly.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, proof
of Proposition 1.3.4, printed p.511 (PDF p.528); GLS3, proof of Theorem
6.5.3, cases (a)–(d), in `refs/KGroup/GLS3/chapter6.tex`.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split.Extraspecial

universe u v
variable {Q : Type u} [Group Q]

/-- An actual model equivalence placing the indicated subgroup in a split
monomial subgroup. Changing the model equivalence allows a change of basis. -/
def MonomialPlacement (p : ℕ) (H : Subgroup Q) : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ∧
    ∃ e : Q ≃* Matrix.SpecialLinearGroup (Fin 3) F,
      H.map e.toMonoidHom ≤ Matrix.SL3.SplitMonomial.linear F) ∨
  (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ∧
    ∃ e : Q ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F,
      H.map e.toMonoidHom ≤ Matrix.SL3.SplitMonomial.projective F)

variable [Finite Q] {S : Sylow 2 Q} {R : Subgroup Q}

omit [Finite Q] in
/-- The order-27 alternative supplies both extraspeciality and exponent
three; neither is an additional assumption on the pair. -/
theorem extraspecial_and_exponent (h : PairInput S R) (hc : Nat.card R = 27) :
    IsExtraspecial 3 R ∧ Monoid.exponent R = 3 := by
  rcases h.oddComplement with ⟨_, hcard⟩ | ⟨he, _, hexp⟩
  · norm_num at hcard
    omega
  · exact ⟨he, hexp⟩

/-- The index is computed inside RS, without assuming that R is normal. -/
theorem complement_index (h : PairInput S R) :
    (R.subgroupOf (R ⊔ (S : Subgroup Q))).index = Nat.card S := by
  have hc := (R.subgroupOf (R ⊔ (S : Subgroup Q))).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show R ≤ R ⊔ (S : Subgroup Q) from
    le_sup_left)).toEquiv, EvenRankTwo.product_card h] at hc
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hc

/-- R, viewed in the actual product subgroup, is Sylow three there. -/
noncomputable def complementSylow (h : PairInput S R) : Sylow 3 ↥(R ⊔ (S : Subgroup Q)) :=
  (show IsPGroup 3 (R.subgroupOf (R ⊔ (S : Subgroup Q))) from
    h.oddComplement.isPGroup.comap_subtype).toSylow (by
    rw [complement_index h]
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    rw [hn]
    intro hd
    have hh := Nat.prime_three.dvd_of_dvd_pow hd
    norm_num at hh)

theorem complementSylow_coe (h : PairInput S R) :
    (complementSylow h : Subgroup ↥(R ⊔ (S : Subgroup Q))) =
      R.subgroupOf (R ⊔ (S : Subgroup Q)) := rfl

/-- The three-core is normal in RS, so it lies in the Sylow subgroup R. -/
theorem local_core_le_complement (h : PairInput S R) :
    (R ⊔ (S : Subgroup Q)).pCoreIn 3 ≤ R := by
  have hh := (R ⊔ (S : Subgroup Q)).pCoreIn_le_sylow (complementSylow h)
  simpa only [complementSylow_coe, map_subgroupOf_eq_of_le le_sup_left] using hh

/-- Restriction to R and inclusion in Q both preserve the local core's order. -/
theorem local_core_intersection_card (h : PairInput S R) :
    Nat.card (((R ⊔ (S : Subgroup Q)).pCoreIn 3).subgroupOf R) =
      Nat.card (pCore 3 ↥(R ⊔ (S : Subgroup Q))) := by
  rw [Nat.card_congr (subgroupOfEquivOfLe (local_core_le_complement h)).toEquiv]
  exact card_map_of_injective (R ⊔ (S : Subgroup Q)).subtype_injective

variable {G : Type v} [Group G]

/-- Transport the intrinsic core of RS through an actual model equivalence. -/
theorem local_core_intersection_card_of_equiv (h : PairInput S R) (e : Q ≃* G) :
    Nat.card (((R ⊔ (S : Subgroup Q)).pCoreIn 3).subgroupOf R) =
      Nat.card (pCore 3 ((R ⊔ (S : Subgroup Q)).map e.toMonoidHom)) := by
  rw [local_core_intersection_card h]
  let eH := e.subgroupMap (R ⊔ (S : Subgroup Q))
  exact Nat.card_congr ((eH.subgroupMap (pCore 3 ↥(R ⊔ (S : Subgroup Q)))).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 3 eH))).toEquiv

/-- The transported product has order 27 times the full Sylow two-order. -/
theorem model_product_card (h : PairInput S R) (hc : Nat.card R = 27)
    (e : Q ≃* G) :
    Nat.card ((R ⊔ (S : Subgroup Q)).map e.toMonoidHom) =
      27 * Nat.card (S.mapSurjective (f := e.toMonoidHom) e.surjective) := by
  rw [card_map_of_injective e.injective, EvenRankTwo.product_card h, hc]
  congr 1
  exact Nat.card_congr (S.toSubgroup.equivMapOfInjective e.toMonoidHom e.injective).toEquiv

/-- The image of S is a full ambient Sylow subgroup contained in the product. -/
theorem model_sylow_le_product (e : Q ≃* G) :
    (S.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup G) ≤
      (R ⊔ (S : Subgroup Q)).map e.toMonoidHom :=
  map_mono le_sup_right

omit [Finite Q] in
/-- The transported product contains a nonabelian three-subgroup. This
excludes products whose entire odd part lies in the diagonal torus. -/
theorem model_nonabelian_three_subgroup (h : PairInput S R) (hc : Nat.card R = 27)
    (e : Q ≃* G) :
    ∃ U : Subgroup G, U ≤ (R ⊔ (S : Subgroup Q)).map e.toMonoidHom ∧
      IsPGroup 3 U ∧ ¬ IsMulCommutative U := by
  refine ⟨R.map e.toMonoidHom, map_mono le_sup_left, h.oddComplement.isPGroup.map _, ?_⟩
  have he := (extraspecial_and_exponent h hc).1.of_mulEquiv
    (R.equivMapOfInjective e.toMonoidHom e.injective)
  intro ha
  let _ := ha
  exact (QuotientGroup.nontrivial_iff.mp he.quotient_nontrivial)
    (center_eq_top (G := R.map e.toMonoidHom))

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split.Extraspecial
