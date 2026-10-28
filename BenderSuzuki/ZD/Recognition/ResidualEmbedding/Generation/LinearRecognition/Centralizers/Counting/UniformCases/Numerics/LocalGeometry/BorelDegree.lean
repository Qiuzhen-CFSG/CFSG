module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.LocalRecognition.Counts.Models
public import Theory.SpecificGroups.Suzuki.SylowOmegaGeometry

/-!
# Degrees of the three Bender Borel actions

The normal Sylow two-subgroup of a Borel acts regularly away from the base
coset. Thus the Borel index is its Sylow order plus one. The actual root
groups give the orders q, q² and q³; in the unitary case q is the fixed-field
order, whereas the matrix field has order q².

Source: GLS4, Chapter 4, Lemma 3.2(a–c), used in Chapter 2, Lemma 12.8.
-/

noncomputable section
namespace BenderSuzuki.ZD.LocalGeometry
open Subgroup PFAppendixIII
open _root_.BenderSuzuki.MatrixGroups
universe u

private theorem regular_card
    {H X : Type*} [Group H] [MulAction H X]
    (S : Subgroup H) (A : Set X) (a : X) (ha : a ∈ A)
    (hstable : ∀ s : S, ∀ x ∈ A, (s : H) • x ∈ A)
    (hreg : IsRegularOn S A) : Nat.card S = Nat.card A := by
  let f : S → A := fun s => ⟨(s : H) • a, hstable s a ha⟩
  apply Nat.card_congr (Equiv.ofBijective f ?_)
  constructor
  · intro s t hst
    obtain ⟨r, _, hr⟩ := hreg ha (hstable s a ha)
    exact (hr s rfl).trans (hr t (congrArg Subtype.val hst).symm).symm
  · intro b
    obtain ⟨s, hs, _⟩ := hreg ha b.property
    exact ⟨s, Subtype.ext hs⟩

/-- The degree of a Borel action is one more than the ambient Sylow order. -/
public theorem borel_index_eq_sylow_card_add_one
    {H : Type u} [Group H] [Finite H] {B : Subgroup H}
    (hb : IsBorelSubgroup B) (hm : IsSimpleBenderGroup H)
    (P : Sylow 2 H) : B.index = Nat.card P + 1 := by
  classical
  have hBne : B ≠ ⊤ := by
    intro htop
    let : Group.IsSolvable B := hb.1
    have hsurj : Function.Surjective B.subtype := by
      intro x
      exact ⟨⟨x, htop ▸ mem_top x⟩, rfl⟩
    let : Group.IsSolvable H := Group.isSolvable_of_surjective (f := B.subtype) hsurj
    let : IsSimpleGroup H := hm.isSimple
    obtain ⟨n, hn, hnmodel⟩ := hm.exists_exponent
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial H).ne (hnmodel.isPerfect hn)
  obtain ⟨Q, _, hreg⟩ := simpleBender_borel_normalSylow_regular hb hm
  let QH : Subgroup H := (Q : Subgroup B).map B.subtype
  let a : H ⧸ B := QuotientGroup.mk 1
  let A : Set (H ⧸ B) := {x | x ≠ a}
  obtain ⟨g, hg⟩ : ∃ g : H, g ∉ B := by
    by_contra h
    push Not at h
    exact hBne (top_unique (fun x _ => h x))
  have hga : (QuotientGroup.mk g : H ⧸ B) ∈ A := by
    intro he
    exact hg (by simpa [a] using QuotientGroup.eq.mp he.symm)
  have hstable : ∀ s : QH, ∀ x ∈ A, (s : H) • x ∈ A := by
    intro s x hx he
    apply hx
    calc
      x = (s : H)⁻¹ • ((s : H) • x) := by simp
      _ = (s : H)⁻¹ • a := by rw [he]
      _ = a := by
        apply MulAction.mem_stabilizer_iff.mp
        rw [baseCoset_stabilizer B]
        obtain ⟨q, _, hq⟩ := s.property
        exact B.inv_mem (hq ▸ q.property)
  have hQA := regular_card QH A (QuotientGroup.mk g) hga hstable hreg
  obtain ⟨S, hS⟩ := hb.2
  have hSB : (S : Subgroup H) ≤ B := by rw [hS]; exact le_normalizer
  have hQP : Nat.card QH = Nat.card P := by
    rw [card_map_of_injective B.subtype_injective]
    exact (Nat.card_congr (Sylow.equiv Q (S.subtype hSB)).toEquiv).trans
      ((Nat.card_congr (subgroupOfEquivOfLe hSB).toEquiv).trans
        (Nat.card_congr (Sylow.equiv S P).toEquiv))
  have hAc : Nat.card A = Nat.card (H ⧸ B) - 1 := by
    change Nat.card ↥(({a} : Set (H ⧸ B))ᶜ) = _
    rw [Nat.card_coe_set_eq, Set.ncard_compl, Set.ncard_singleton]
  rw [hQP, hAc] at hQA
  rw [B.index_eq_card]
  have hp : 0 < Nat.card (H ⧸ B) := Nat.card_pos
  omega

/-- The linear root has order equal to the binary field order. -/
public theorem psl2_borel_index {n : ℕ} (hn : 2 ≤ n)
    {B : Subgroup (PSL2BinaryMatrixGroup n)} (hb : IsBorelSubgroup B) :
    B.index = 2 ^ n + 1 := by
  let K := BinaryGaloisField n
  let U := Matrix.SpecialLinearGroup.upperUnipotentSylow K 2
  let P : Sylow 2 (PSL2BinaryMatrixGroup n) :=
    U.mapSurjective (f := Converse.pi K) Converse.pi_surjective
  rw [borel_index_eq_sylow_card_add_one hb
    (.isPSL2 ⟨n, hn, ⟨MulEquiv.refl _⟩⟩) P]
  have hc : Nat.card P = 2 ^ n := by
    change Nat.card ((U : Subgroup _).map (Converse.pi K)) = _
    rw [card_map_of_injective (Converse.pi_injective (F := K))]
    change Nat.card (Matrix.SpecialLinearGroup.upperUnipotent K) = _
    rw [Matrix.SpecialLinearGroup.card_upperUnipotent]
    exact GaloisField.card 2 n (by omega)
  rw [hc]

/-- The Suzuki root has order q², with odd source exponent. -/
public theorem suzuki_borel_index {m : ℕ} (hm : 1 ≤ m)
    {B : Subgroup (SuzukiMatrixGroup m)} (hb : IsBorelSubgroup B) :
    B.index = (2 ^ (2 * m + 1)) ^ 2 + 1 := by
  let P : Sylow 2 (SuzukiMatrixGroup m) := Classical.choice inferInstance
  rw [borel_index_eq_sylow_card_add_one hb
    (.isSuzuki ⟨m, hm, ⟨MulEquiv.refl _⟩⟩) P,
    suzukiSylow_card hm (MulEquiv.refl _) P]

private instance {E : Type*} [Field E] [Finite E] :
    Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

/-- The unitary root has order q³ for fixed-field order q. -/
public theorem psu3_borel_index {E : Type} [Field E] [Finite E]
    (J : HermitianForm 3 E) [Finite (ProjectiveSpecialUnitaryMatrixGroup J)]
    {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hc : Nat.card E = (2 ^ n) ^ 2)
    (hf : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    {B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)} (hb : IsBorelSubgroup B) :
    B.index = (2 ^ n) ^ 3 + 1 := by
  let P := HermitianForm.EvenTwoRank.rootSylow J hJ (by omega : 0 < n) hc hf
  rw [borel_index_eq_sylow_card_add_one hb
    (.isPSU3 ⟨n, hn, E, inferInstance, inferInstance, J, hJ, hc, hf,
      ⟨MulEquiv.refl _⟩⟩) P]
  congr 1
  exact HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage.rootGroup_card J hJ _ hc hf

/-- The Borel degree and its permitted exponent for any of the actual models. -/
public theorem bender_borel_index_atExponent
    {H : Type u} [Group H] [Finite H] {n : ℕ} (hn : 2 ≤ n)
    (hm : IsSimpleBenderGroupAtExponent n H)
    {B : Subgroup H} (hb : IsBorelSubgroup B) :
    ∃ i : ℕ, (i = 1 ∨ i = 2 ∨ i = 3) ∧ (i = 2 → Odd n) ∧
      B.index = (2 ^ n) ^ i + 1 := by
  cases hm with
  | isPSL2 he =>
    obtain ⟨e⟩ := he
    refine ⟨1, Or.inl rfl, by omega, ?_⟩
    simpa only [pow_one] using
      (B.index_map_equiv e).symm.trans (psl2_borel_index hn (hb.map_mulEquiv e))
  | isSuzuki he =>
    obtain ⟨m, rfl, e⟩ := he
    refine ⟨2, Or.inr (Or.inl rfl), fun _ => ⟨m, rfl⟩, ?_⟩
    exact (B.index_map_equiv e.some).symm.trans
      (suzuki_borel_index (by omega) (hb.map_mulEquiv e.some))
  | isPSU3 he =>
    obtain ⟨E, _, _, J, hJ, hc, hf, e⟩ := he
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv H e.some.toEquiv
    refine ⟨3, Or.inr (Or.inr rfl), by omega, ?_⟩
    exact (B.index_map_equiv e.some).symm.trans
      (psu3_borel_index J hn hJ hc hf (hb.map_mulEquiv e.some))

end BenderSuzuki.ZD.LocalGeometry
