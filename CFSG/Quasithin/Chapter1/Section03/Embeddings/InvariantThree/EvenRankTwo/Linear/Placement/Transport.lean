module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Reduction
public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.PSL3.LinearThreeSylow

/-!
# Central-quotient transport for the binary PSL₃ placement

A Sylow normalizer lifts exactly through a surjective central homomorphism.
Indeed, the inverse image of the projected Sylow is the product of the Sylow
with the central kernel. The Sylow is normal, hence characteristic, in this
product. This argument includes even central kernels.

The coordinate adapter below conjugates the actual projected Sylow to UT₃.
Solvability of RS survives this surjection. The remaining model argument must
place this solvable overgroup in the Borel; it is an explicit input here.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`).
-/

public section
open Subgroup
open scoped Pointwise IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear.Placement

/-- Sylow normalizers lift exactly through every finite central cover. -/
theorem normalizer_comap_of_central {G D : Type*} [Group G] [Group D] [Finite G]
    {p : ℕ} [Fact p.Prime] (S : Sylow p G) (q : G →* D)
    (hq : Function.Surjective q) (hc : q.ker ≤ center G) :
    (normalizer ((S : Subgroup G).map q)).comap q = normalizer (S : Set G) := by
  let K := ((S : Subgroup G).map q).comap q
  have hSK : (S : Subgroup G) ≤ K := le_comap_map q _
  have hKN : K ≤ normalizer (S : Set G) := by
    dsimp [K]
    rw [comap_map_eq]
    exact sup_le le_normalizer (hc.trans (center_le_normalizer _))
  let S' := S.subtype hSK
  have hn : (S' : Subgroup K).Normal :=
    normal_subgroupOf_of_le_normalizer hKN
  let _ : (S' : Subgroup K).Characteristic := S'.characteristic_of_normal hn
  have hNK : normalizer K ≤ normalizer (S : Set G) := by
    have hh := normalizer_le_normalizer_characteristic_image K (S' : Subgroup K)
    simpa only [S', Sylow.coe_subtype, map_subgroupOf_eq_of_le hSK, Sylow.coe_coe] using hh
  apply le_antisymm
  · rw [comap_normalizer_eq_of_surjective _ hq]
    exact hNK
  · exact (map_le_iff_le_comap).mp ((S : Subgroup G).le_normalizer_map q)

open Matrix.PSL3 Matrix.PSL3.LinearThree

/-- The actual central quotient map followed by the chosen matrix equivalence. -/
@[expose] def modelProjection {Q : Type*} [Group Q] {F : Type*} [Field F]
    (e : Q ⧸ center Q ≃* PSL(3,F)) : Q →* PSL(3,F) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (center Q))

theorem modelProjection_surjective {Q : Type*} [Group Q] {F : Type*} [Field F]
    (e : Q ⧸ center Q ≃* PSL(3,F)) : Function.Surjective (modelProjection e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

@[simp] theorem modelProjection_ker {Q : Type*} [Group Q] {F : Type*} [Field F]
    (e : Q ⧸ center Q ≃* PSL(3,F)) : (modelProjection e).ker = center Q := by
  ext x
  change e (QuotientGroup.mk' (center Q) x) = 1 ↔ x ∈ center Q
  rw [← e.map_one, e.injective.eq_iff]
  exact QuotientGroup.eq_one_iff _

/-- Conjugating the given model equivalence puts the genuine projected Sylow in UT₃. -/
theorem exists_sylow_coordinates {Q : Type*} [Group Q] [Finite Q]
    (S : Sylow 2 Q) {F : Type*} [Field F] [Finite F]
    {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f)
    (e : Q ⧸ center Q ≃* PSL(3,F)) :
    ∃ e' : Q ⧸ center Q ≃* PSL(3,F),
      (S : Subgroup Q).map (modelProjection e') = unipotent F := by
  let T := S.mapSurjective (modelProjection_surjective e)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F) T (unipotentSylow F hf hF)
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  have he := congrArg (fun U : Sylow 2 PSL(3,F) => (U : Subgroup PSL(3,F))) hg
  change ((S : Subgroup Q).map (modelProjection e)).map
    (MulAut.conj g).toMonoidHom = unipotent F at he
  rw [map_map] at he
  exact he

/-- The product remains solvable in these actual matrix coordinates. -/
theorem model_product_solvable {Q : Type*} [Group Q] [Finite Q]
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    {F : Type*} [Field F] [Finite F] (e : Q ⧸ center Q ≃* PSL(3,F))
    (hS : (S : Subgroup Q).map (modelProjection e) = unipotent F) :
    Group.IsSolvable (R.map (modelProjection e) ⊔ unipotent F : Subgroup PSL(3,F)) := by
  let H : Subgroup Q := R ⊔ (S : Subgroup Q)
  let _ : Group.IsSolvable H := product_solvable h
  have hm : Group.IsSolvable (H.map (modelProjection e)) :=
    Group.isSolvable_of_surjective (f := (modelProjection e).subgroupMap H)
      ((modelProjection e).subgroupMap_surjective H)
  rw [← hS, ← Subgroup.map_sup]
  exact hm

/-- The concrete image of the source pair, before any geometric placement. -/
structure ProjectiveInput (F : Type*) [Field F] [Finite F]
    (B : Subgroup PSL(3,F)) : Prop where
  three : IsPGroup 3 B
  card_le : Nat.card B ≤ 27
  permutes : (B : Set PSL(3,F)) * (unipotent F : Set PSL(3,F)) =
    (unipotent F : Set PSL(3,F)) * (B : Set PSL(3,F))
  solvable : Group.IsSolvable (B ⊔ unipotent F : Subgroup PSL(3,F))

/-- Central projection supplies all the small three-complement inputs. -/
theorem projectiveInput_of_pair {Q : Type*} [Group Q] [Finite Q]
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    {F : Type*} [Field F] [Finite F] (e : Q ⧸ center Q ≃* PSL(3,F))
    (hS : (S : Subgroup Q).map (modelProjection e) = unipotent F) :
    ProjectiveInput F (R.map (modelProjection e)) := by
  refine ⟨h.oddComplement.isPGroup.map _, ?_, ?_, model_product_solvable h e hS⟩
  · have hR : Nat.card R ≤ 27 := by
      rcases h.oddComplement with ⟨_,hc⟩ | ⟨_,hc,_⟩ <;> omega
    exact (Nat.le_of_dvd Nat.card_pos (card_map_dvd _ _)).trans hR
  · have hp := congrArg (fun A : Set Q => (modelProjection e) '' A) h.permutes
    have hSset : (modelProjection e) '' (S : Set Q) = (unipotent F : Set PSL(3,F)) :=
      congrArg (fun K : Subgroup PSL(3,F) => (K : Set PSL(3,F))) hS
    simpa only [Set.image_mul, hSset, ← coe_map] using hp

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear.Placement
