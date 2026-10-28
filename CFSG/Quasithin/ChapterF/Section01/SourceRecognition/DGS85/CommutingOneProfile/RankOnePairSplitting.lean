module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryPairActor
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.PairDirectFactor

/-!
# Coprime splitting for every Chapter 11 rank-one pair

For either unitary beta carrier, the actual center-pair actor is the
fixed-degree SL₂ block. Its two Sylow fixed spaces are the complementary
seed images. The cubic matrix has no nonzero fixed vector on this section;
an odd lift in the original center pair splits the beta core with exact
intersection. The binary unitary cases use the existing rank-one argument.

Combining this with the linear, Suzuki and D10 proofs gives the splitting
for the entire earlier quotient catalogue, without selecting alpha or beta.
The resulting quotient Q_beta/(Q_alpha intersect Q_gamma) is the product
of its literal elementary pair image and its coprime fixed factor, with
multiplication retained as the equivalence. The source omega-containment
step eliminating that second factor, (11.4), and alpha selection remain open.
Source: DGS85, Groups and Graphs (1985), (11.3)(h), pp.170–171,
using the complementary-fixed-space result (5.11), p.112.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

open Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open scoped Pointwise IsMulCommutative commutatorElement

private theorem pair_splitting_of_linear_actor
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (hHK : (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b ≤ d.localGroup b)
    (f : ((Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b : Subgroup G) →* SL(2,k))
    (hf : Function.Surjective f)
    (hk : f.ker = (Q (family P) b).subgroupOf ((Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b))
    (R T : Sylow 2 SL(2,k))
    (ha : ((Z (family P) a).subgroupOf ((Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b)).map f = R)
    (hc' : ((Z (family P) c).subgroupOf ((Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b)).map f = T) :
    let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
    let J := Z (family P) a ⊓ Z (family P) c
    ∃ y ∈ Z (family P) a ⊔ Z (family P) c, Odd (orderOf y) ∧ y ≠ 1 ∧
      Q (family P) b = V ⊔ (Q (family P) b ⊓ centralizer (zpowers y : Set G)) ∧
      V ⊓ centralizer (zpowers y : Set G) = J := by
  let := finite_endpoints h
  let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
  let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
  let J := Z (family P) a ⊓ Z (family P) c
  let D₀ := Q (family P) a ⊓ Q (family P) c
  obtain ⟨hJ,hE,hQ,σ₀,s₀,_⟩ := source_rankOne_pair_section h hB d hc hb hbc hac Ma Mb
  let := hJ
  let := hE
  have hinter : D₀ ⊓ V = J := source_rankOne_pair_core_intersection h hB d hc hb hbc hac Mb
  have hn := source_pair_core_normalizers h (source_critical_one_adjacent hc hb) hbc
  have hHJ : H ≤ normalizer (J : Set G) := by
    rw [←hinter]
    exact (le_inf hn.2.1 hn.2.2.1).trans inf_normalizer_le_normalizer_inf
  have hdisp : ⁅Q (family P) b,V⁆ ≤ J := by
    rw [←hinter]
    exact le_inf (source_rankOne_pair_core_action h hB d hc hb hbc Ma Mb)
      (le_normalizer_iff_commutator_le_right.mp (le_sup_right.trans hn.2.2.1))
  obtain ⟨σ,s,_⟩ := exists_descended_actor H V J s₀.section_le s₀.kernel_le
    hn.2.2.1 hHJ f hf (by
      intro y hy x hx
      have hyker : y ∈ f.ker := hy
      rw [hk] at hyker
      exact hdisp (commutator_mem_commutator hyker hx))
  have hfixed := source_rankOne_pair_fixed_spaces h hB d hc hb hbc Mb f hf hk σ s
  have hJQ : J ≤ Q (family P) b := s.kernel_le.trans (pairSpan_le_core _ _ _)
  have he : J = (Z (family P) a ⊓ Q (family P) b) ⊓ (Z (family P) c ⊓ Q (family P) b) :=
    le_antisymm (le_inf (le_inf inf_le_left hJQ) (le_inf inf_le_right hJQ))
      (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
  have hcompl := s.isCompl_imageSpace (Z (family P) a ⊓ Q (family P) b)
    (Z (family P) c ⊓ Q (family P) b) rfl he
  rw [←hfixed.2.1,←hfixed.2.2,ha,hc'] at hcompl
  let : Finite V := Finite.of_injective (inclusion ((pairSpan_le_core _ _ _).trans (Q_le_stabilizer _ b))) (inclusion_injective _)
  let : Finite (V ⧸ J.subgroupOf V) := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  let y₀ := Representation.QuadraticFourGroup.TensorClassification.cubicMatrix k
  have hy₀ : orderOf y₀ = 3 := Representation.QuadraticFourGroup.TensorClassification.cubicMatrix_order k
  apply source_pair_coprime_splitting_of_odd_actor h d hc hb hbc hHK f hf hk s.kernel_le y₀
    (hy₀ ▸ (by decide : Odd (3:ℕ))) (fun he => by simp only [he,orderOf_one] at hy₀; omega)
  intro y hy x hx
  have hz := sl2_odd_fixed_eq_bot_of_complement σ R T hcompl y₀
    (hy₀ ▸ (by decide : Odd (3:ℕ))) (pow_orderOf_eq_one y₀)
    (fun he => by simp only [he,orderOf_one] at hy₀; omega)
  rw [←s.fixed_coordinate_iff_commutator_mem y ⟨x,hx⟩]
  change σ (f y) (s.coordinates ⟨x,hx⟩).toAdd = (s.coordinates ⟨x,hx⟩).toAdd ↔ _
  rw [hy,←mem_fixedSpace_zpowers_iff,hz,Submodule.mem_bot]
  exact s.coordinates_eq_one_iff ⟨x,hx⟩

/-- Every unitary beta degree supplies the actual coprime decomposition,
including both binary carriers, before any alpha row is selected. -/
theorem source_unitary_pair_coprime_splitting
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    {n : ℕ} (hn : 0 < n)
    (hi : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n)) :
    let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
    let J := Z (family P) a ⊓ Z (family P) c
    ∃ y ∈ Z (family P) a ⊔ Z (family P) c, Odd (orderOf y) ∧ y ≠ 1 ∧
      Q (family P) b = V ⊔ (Q (family P) b ⊓ centralizer (zpowers y : Set G)) ∧
      V ⊓ centralizer (zpowers y : Set G) = J := by
  have Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) :=
    hi.elim (.projective_unitary n hn) (.special_unitary n hn)
  by_cases hn2 : 2 ≤ n
  · obtain ⟨hHK,f,hf,hk,R,T,ha,hc'⟩ := source_unitary_pair_linear_actor h hB d hc hb hbc hac hn2 hi
    exact pair_splitting_of_linear_actor h hB d hc hb hbc hac Ma Mb hHK f hf hk R T ha hc'
  · have hn1 : n=1 := by omega
    have hs : IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 2 ∨
        ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 2 := by
      simpa only [hn1,pow_one] using hi.symm
    exact source_small_models_pair_coprime_splitting h hB d hc hb hbc hac Ma Mb (.inr (.inr hs))


/-- Coprime splitting for the complete binary Chapter 6 quotient catalogue.
Neither endpoint model is preselected, and no odd actor is assumed. -/
theorem source_rankOne_pair_coprime_splitting
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b))) :
    let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
    let J := Z (family P) a ⊓ Z (family P) c
    ∃ y ∈ Z (family P) a ⊔ Z (family P) c, Odd (orderOf y) ∧ y ≠ 1 ∧
      Q (family P) b = V ⊔ (Q (family P) b ⊓ centralizer (zpowers y : Set G)) ∧
      V ⊓ centralizer (zpowers y : Set G) = J := by
  cases Mb with
  | linear n hn hi =>
    have Mb := IsRankOneModel.linear n hn hi
    obtain ⟨k,_,_,hcard,⟨eb⟩⟩ := hi
    let : Fintype k := Fintype.ofFinite k
    let : CharP k 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    let ep : SL(2,k) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
      MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
        ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
    exact source_linear_pair_coprime_splitting h hB d hc hb hbc hac Ma Mb (eb.trans ep.symm)
  | suzuki m hi =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact source_small_models_pair_coprime_splitting h hB d hc hb hbc hac Ma
        (.suzuki 0 hi) (.inr (.inl hi))
    · exact source_suzuki_pair_coprime_splitting h hB d hc hb hbc hac Ma
        (.suzuki m hi) hm hi.some
  | projective_unitary n hn hi =>
    exact source_unitary_pair_coprime_splitting h hB d hc hb hbc hac Ma hn (.inl hi)
  | special_unitary n hn hi =>
    exact source_unitary_pair_coprime_splitting h hB d hc hb hbc hac Ma hn (.inr hi)
  | dihedral hi =>
    exact source_small_models_pair_coprime_splitting h hB d hc hb hbc hac Ma (.dihedral hi) (.inl hi)

/-- The literal beta-core quotient is the direct product of its elementary
pair image and its coprime fixed factor, for every original rank-one row.
Multiplication of the quotient images is the displayed equivalence. -/
theorem source_rankOne_pair_core_direct_product
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b))) :
    let Q₀ := Q (family P) b
    let D := Q (family P) a ⊓ Q (family P) c
    let V := pairSpan (Z (family P) a) (Z (family P) c) Q₀
    ∃ hD : (D.subgroupOf Q₀).Normal, letI := hD
      let π := QuotientGroup.mk' (D.subgroupOf Q₀)
      let A := (V.subgroupOf Q₀).map π
      ∃ y ∈ Z (family P) a ⊔ Z (family P) c, Odd (orderOf y) ∧ y ≠ 1 ∧
        let C := ((Q₀ ⊓ centralizer (zpowers y : Set G)).subgroupOf Q₀).map π
        IsElementaryAbelian 2 A ∧ Disjoint A C ∧
          ∃ e : A × C ≃* (Q₀ ⧸ D.subgroupOf Q₀),
            ∀ x z, e (x,z) = (x : Q₀ ⧸ D.subgroupOf Q₀) * (z : Q₀ ⧸ D.subgroupOf Q₀) := by
  exact source_pair_core_direct_product_of_splitting h hB d hc hb hbc hac Ma Mb
    (source_rankOne_pair_coprime_splitting h hB d hc hb hbc hac Ma Mb)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
