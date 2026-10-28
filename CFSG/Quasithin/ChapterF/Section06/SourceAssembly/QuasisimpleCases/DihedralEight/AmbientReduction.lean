module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DihedralEight.SourceComponent
public import Theory.SpecificGroups.Classical.SmallSylowEightOrders

/-!
# Promoting the order-eight component models to the original ambient group

If the normal component already has order divisible by eight, a nontrivial
two-group quotient above it would force sixteen to divide the ambient order.
Thus every alternating or triple-cover component is the whole group. The
remaining PSL2 component has Sylow order four or eight, with the exact
field congruences supplied by its order formula and dihedral Sylow model.

Source: Aschbacher--Smith F.6.18(5)--(7), printed pp.309--310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
open ComponentSieve
variable {G : Type*} [Group G] [Finite G]

/-- A normal subgroup already using the ambient two-part admits no
nontrivial two-group quotient. -/
theorem normal_eq_top_of_sylow_eight_of_eight_dvd
    (T : Sylow 2 G) (hT : Nat.card T = 8) (K : Subgroup G) [K.Normal]
    (hquot : IsPGroup 2 (G ⧸ K)) (h8 : 8 ∣ Nat.card K) : K = ⊤ := by
  apply Subgroup.index_eq_one.mp
  obtain ⟨n, hn⟩ := hquot.exists_card_eq
  change K.index = 2 ^ n at hn
  cases n with
  | zero => simpa using hn
  | succ n =>
    exfalso
    apply not_sixteen_dvd_of_sylow_le_eight T hT.le
    have h2 : 2 ∣ K.index := by rw [hn]; exact dvd_pow_self 2 (by omega)
    simpa only [K.card_mul_index] using Nat.mul_dvd_mul h8 h2

private theorem ambient_equiv_of_eight_dvd_model
    (T : Sylow 2 G) (hT : Nat.card T = 8) (K : Subgroup G) [K.Normal]
    (hquot : IsPGroup 2 (G ⧸ K)) {M : Type*} [Group M] [Finite M]
    (j : K ≃* M) (hM : 8 ∣ Nat.card M) : Nonempty (G ≃* M) := by
  have hK := normal_eq_top_of_sylow_eight_of_eight_dvd T hT K hquot
    (by rwa [Nat.card_congr j.toEquiv])
  exact ⟨(topEquiv.symm.trans (MulEquiv.subgroupCongr hK).symm).trans j⟩

/-- In the alternating and triple-cover cases, the normal component is
already the entire original ambient group. -/
theorem ambient_alternating_models_of_component
    (T : Sylow 2 G) (hT : Nat.card T = 8) (K : Subgroup G) [K.Normal]
    (hquot : IsPGroup 2 (G ⧸ K))
    (hm : Nonempty (K ≃* Atlas.Codes.HexEvenAutomorphisms) ∨
      Nonempty (K ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (K ≃* GLS3.Chapter5.OddCentralCovers.TripleSeven)) :
    Nonempty (G ≃* Atlas.Codes.HexEvenAutomorphisms) ∨
      Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (G ≃* GLS3.Chapter5.OddCentralCovers.TripleSeven) := by
  rcases hm with hm | hm | hm
  · obtain ⟨j⟩ := hm
    exact .inl (ambient_equiv_of_eight_dvd_model T hT K hquot j (by
      rw [Atlas.Codes.hexEven_card]; norm_num))
  · obtain ⟨j⟩ := hm
    exact .inr (.inl (ambient_equiv_of_eight_dvd_model T hT K hquot j (by
      rw [nat_card_alternatingGroup, Nat.card_fin]; norm_num)))
  · obtain ⟨j⟩ := hm
    apply Or.inr ∘ Or.inr
    apply ambient_equiv_of_eight_dvd_model T hT K hquot j
    exact (show 8 ∣ Nat.card (alternatingGroup (Fin 7)) by
      rw [nat_card_alternatingGroup, Nat.card_fin]; norm_num).trans
      (Subgroup.card_dvd_of_surjective
        GLS3.Chapter5.OddCentralCovers.tripleSevenProjection
        GLS3.Chapter5.OddCentralCovers.tripleSevenProjection_surjective)

universe u
variable {A B : Type u} [Group A] [Finite A] [Group B] [Finite B]
    {κ : GroupClass.{u}} {A₁ A₂ : Subgroup A}

/-- The quasisimple source residual either is an actual odd PSL2 component,
or the original ambient group is one of the three alternating covers. -/
theorem source_dihedral_eight_residual_models
    (hA : ChapterA.Section02.TheoremA κ B)
    (hC : ChapterA.Section02.TheoremC κ ((pResidual 2 A) ⧸ center (pResidual 2 A)))
    (hB : IsSQTK κ B) (e : A ≃* (B ⧸ pPrimeCore 3 B))
    (h : IsGoldschmidtTriple A₁ A₂) (hq : IsQuasisimple (pResidual 2 A))
    (eT : (A₁ ⊓ A₂ : Subgroup A) ≃* DihedralGroup 4) :
    (∃ p f : ℕ, p.Prime ∧ Odd p ∧ 1 ≤ f ∧ f ≤ 2 ∧
      ClassicalGroup.IsPSL (pResidual 2 A) 2 (p ^ f)) ∨
    Nonempty (A ≃* Atlas.Codes.HexEvenAutomorphisms) ∨
    Nonempty (A ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (A ≃* GLS3.Chapter5.OddCentralCovers.TripleSeven) := by
  let : IsQuasisimple (pResidual 2 A) := hq
  have hK : IsComponent A (pResidual 2 A) :=
    ⟨(inferInstance : (pResidual 2 A).Normal).isSubnormal, hq⟩
  obtain ⟨T, hT⟩ := h.intersection_sylow
  let jT : T ≃* DihedralGroup 4 := (MulEquiv.subgroupCongr hT.symm).trans eT
  rcases component_models_of_dihedral_eight hA hC hB e hK T jT with hm | hm
  · exact .inl hm
  · exact .inr (ambient_alternating_models_of_component T
      (by rw [Nat.card_congr jT.toEquiv, DihedralGroup.nat_card])
      (pResidual 2 A) (isPGroup_quotient_pResidual 2) hm)

end CFSG.Quasithin.ChapterF.SourceAssembly
