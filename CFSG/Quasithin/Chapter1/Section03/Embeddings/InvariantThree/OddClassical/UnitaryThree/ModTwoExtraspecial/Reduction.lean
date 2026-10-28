module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.Reduction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Reduction
public import Theory.SpecificGroups.SU3.OddThreeLocal.Monomial
public import Theory.ElementaryAbelian.ExtraspecialEquiv

/-!
# Local cores and actual unitary models for extraspecial pairs

Permutability gives |RS:R| = |S|, so R is Sylow three in RS. Its intrinsic
three-core therefore lies in R. Restriction to R and transport through a
group equivalence preserve the order of this core. The transported product
contains a nonabelian three-subgroup, excluding an entirely diagonal odd part.

`PrimeCover` records precisely the universal cover consequence used from
I.1.3. It has no pair or action hypothesis. `MonomialPlacement` is the separate,
as yet unproved geometric obligation: an actual special or projective unitary
equivalence carries RS into the stabilizer of three orthogonal lines.
Both models are retained; the central projection is never treated as injective.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511 (PDF p.528),
and I.1.3(2), printed p.407 (PDF p.418); GLS3, proof of Theorem 6.5.3(a)–(d).
-/

@[expose] public section

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial

universe u v
variable {Q : Type u} [Group Q]

/-- Both actual degree-three unitary models allowed by the covering theorem. -/
def Model (p : ℕ) (Q : Type u) [Group Q] : Prop :=
  CFSG.Quasithin.Chapter1.Section02.LocalModels.IsSU Q 3 p ∨
    ClassicalGroup.IsPSU Q 3 p

/-- The universal earlier cover input, independent of the local pair. -/
def PrimeCover : Prop :=
  ∀ (p : ℕ), p.Prime → Odd p → 3 < p → p % 3 = 2 →
    ∀ (K : Type u) [Group K] [Finite K], IsQuasisimple K →
      ClassicalGroup.IsPSU (K ⧸ center K) 3 p → Model p K

/-- Actual matrix equivalences placing the product in an orthogonal monomial
subgroup. The field order and conjugation use the unitary conventions. -/
def MonomialPlacement (p : ℕ) (H : Subgroup Q) : Prop :=
  (∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
    Nat.card E = p ^ 2 ∧ (∀ x, J.conj x = x ^ p) ∧ J.form = 1 ∧
      ∃ e : Q ≃* J.specialSubgroup,
        H.map e.toMonoidHom ≤ HermitianForm.OddThreeLocal.Monomial.special J) ∨
  (∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
    Nat.card E = p ^ 2 ∧ (∀ x, J.conj x = x ^ p) ∧ J.form = 1 ∧
      ∃ e : Q ≃* ProjectiveSpecialUnitaryMatrixGroup J,
        H.map e.toMonoidHom ≤ HermitianForm.OddThreeLocal.Monomial.projective J)

variable [Finite Q] {S : Sylow 2 Q} {R : Subgroup Q}

omit [Finite Q] in
/-- Extraspeciality and exponent three come from the actual pair input. -/
theorem extraspecial_and_exponent (h : PairInput S R) (hc : Nat.card R = 27) :
    IsExtraspecial 3 R ∧ Monoid.exponent R = 3 := by
  rcases h.oddComplement with ⟨_, hcard⟩ | ⟨he, _, hexp⟩
  · norm_num at hcard
    omega
  · exact ⟨he, hexp⟩

/-- The relative index in RS is the full Sylow two-order. -/
theorem complement_index (h : PairInput S R) :
    (R.subgroupOf (R ⊔ (S : Subgroup Q))).index = Nat.card S := by
  have hc := (R.subgroupOf (R ⊔ (S : Subgroup Q))).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show R ≤ R ⊔ (S : Subgroup Q) from
    le_sup_left)).toEquiv, EvenRankTwo.product_card h] at hc
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hc

/-- R is Sylow three in RS; it need not be normal there. -/
noncomputable def complementSylow (h : PairInput S R) :
    Sylow 3 ↥(R ⊔ (S : Subgroup Q)) :=
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

/-- The three-core normal in RS lies in its Sylow three-subgroup R. -/
theorem local_core_le_complement (h : PairInput S R) :
    (R ⊔ (S : Subgroup Q)).pCoreIn 3 ≤ R := by
  have hh := (R ⊔ (S : Subgroup Q)).pCoreIn_le_sylow (complementSylow h)
  simpa only [complementSylow_coe, map_subgroupOf_eq_of_le le_sup_left] using hh

/-- The exact intersection needed by the reducibility theorem has the same
order as the intrinsic local core. -/
theorem local_core_intersection_card (h : PairInput S R) :
    Nat.card (((R ⊔ (S : Subgroup Q)).pCoreIn 3).subgroupOf R) =
      Nat.card (pCore 3 ↥(R ⊔ (S : Subgroup Q))) := by
  rw [Nat.card_congr (subgroupOfEquivOfLe (local_core_le_complement h)).toEquiv]
  exact card_map_of_injective (R ⊔ (S : Subgroup Q)).subtype_injective

variable {G : Type v} [Group G]

/-- Transport the local core through an actual equivalence, not a quotient
map with a possibly nontrivial central kernel. -/
theorem local_core_intersection_card_of_equiv (h : PairInput S R) (e : Q ≃* G) :
    Nat.card (((R ⊔ (S : Subgroup Q)).pCoreIn 3).subgroupOf R) =
      Nat.card (pCore 3 ((R ⊔ (S : Subgroup Q)).map e.toMonoidHom)) := by
  rw [local_core_intersection_card h]
  let eH := e.subgroupMap (R ⊔ (S : Subgroup Q))
  exact Nat.card_congr ((eH.subgroupMap (pCore 3 ↥(R ⊔ (S : Subgroup Q)))).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 3 eH))).toEquiv

theorem model_product_card (h : PairInput S R) (hc : Nat.card R = 27)
    (e : Q ≃* G) :
    Nat.card ((R ⊔ (S : Subgroup Q)).map e.toMonoidHom) =
      27 * Nat.card (S.mapSurjective (f := e.toMonoidHom) e.surjective) := by
  rw [card_map_of_injective e.injective, EvenRankTwo.product_card h, hc]
  congr 1
  exact Nat.card_congr (S.toSubgroup.equivMapOfInjective e.toMonoidHom e.injective).toEquiv

theorem model_sylow_le_product (e : Q ≃* G) :
    (S.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup G) ≤
      (R ⊔ (S : Subgroup Q)).map e.toMonoidHom :=
  map_mono le_sup_right

omit [Finite Q] in
/-- The odd part of the product does not lie entirely in an abelian torus. -/
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

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial
