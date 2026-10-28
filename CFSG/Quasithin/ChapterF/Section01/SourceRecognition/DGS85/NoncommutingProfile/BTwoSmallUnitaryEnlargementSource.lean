module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalParabolicsSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallSpecialUnitaryEnlargement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallProjectiveUnitaryEnlargement
public import Theory.SpecificGroups.GL2.ThreeSylowNormalElementary

/-!
# Original small-unitary exclusions through the genuine enlargements

The shared Chapter 6 producer identifies the actual enlargement of an
SU₃(2) endpoint. Transport through the original completion inclusion gives
the graph quotient marking, where the Sylow Frattini obstruction excludes
this row. For PSU₃(2), the same obstruction removes the unchanged marking
alternative. In the remaining order-144 quotient, the original starred
three-core gives an actual normal elementary nine. Its Sylow complement
embeds in GL₂(3), so every normal elementary Sylow subgroup lies in Frattini.
The normality of the central seed therefore excludes this last alternative.

The earlier intermediate interfaces retain their projective alternative.
BTwoSmallUnitaryExclusionSource applies the final exclusion to exhaustive
beta selection, saturation and exceptional recognition. Both full endpoints,
the full Borel, quotient kernels and the literal D subgroup are preserved.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
Chapter 6 enlargement, pp.118--119, and (10.7)--(10.9), pp.158--163;
Aschbacher--Smith F.1.9 original endpoint maps, printed pp.261--262.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
open BenderSuzuki.MatrixGroups Theory.GroupTheory
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local instance smallUnitarySourceAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

/-- The actual original SU₃(2) quotient is excluded using its proved enlargement. -/
theorem original_bTwo_not_small_special_beta
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (hm : IsSU (L 1 ⧸ pCore 2 (L 1)) 3 2) : False := by
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := original_small_special_enlarged_marking h 1 hm
  let := hF
  let := hfin
  exact c.not_special_unitary_beta (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hb hactor hcentral ht hne hcomm hnot J (n := 1)
    (by decide) hcard hconj ((reduced_graphEnlargementQuotient h true).trans e)

/-- An original PSU₃(2) marking forces the remaining enlarged quotient to have order 144. -/
theorem original_bTwo_small_projective_enlarged_order
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (hm : ClassicalGroup.IsPSU (L 1 ⧸ pCore 2 (L 1)) 3 2) :
    Nat.card (enlargedEndpoint L S 1 ⧸ pCore 2 (enlargedEndpoint L S 1)) = 144 := by
  rcases original_small_projective_enlarged_marking_or_card h 1 hm with he | he
  · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := he
    let := hF
    let := hfin
    exact (c.not_projective_unitary_beta (reduced_triple h) (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hb hactor hcentral ht hne hcomm hnot J (n := 1)
      (by decide) hcard hconj ((reduced_graphEnlargementQuotient h true).trans e)).elim
  · exact he

/-- Exhaustive original beta selection with only the order-144 projective enlargement remaining. -/
theorem original_bTwo_beta_linear_or_projective144
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) :
    (∃ n, 0 < n ∧ ClassicalGroup.IsPSL (L 1 ⧸ pCore 2 (L 1)) 2 (2^n)) ∨
      (ClassicalGroup.IsPSU (L 1 ⧸ pCore 2 (L 1)) 3 2 ∧
        Nat.card (enlargedEndpoint L S 1 ⧸ pCore 2 (enlargedEndpoint L S 1)) = 144) := by
  rcases original_bTwo_beta_linear_or_small_unitary h hb c hactor hcentral ht hne
    hcomm hnot E with hl | hp | hs
  · exact Or.inl hl
  · exact Or.inr ⟨hp,original_bTwo_small_projective_enlarged_order h hb c hactor hcentral
      ht hne hcomm.le hnot hp⟩
  · exact (original_bTwo_not_small_special_beta h hb c hactor hcentral ht hne
      hcomm.le hnot hs).elim


/-- Saturation and the field power now retain only the strict projective enlargement row. -/
theorem original_bTwo_central_core_field_or_projective144
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype
    (ClassicalGroup.IsPSU (L 1 ⧸ pCore 2 (L 1)) 3 2 ∧
      Nat.card (enlargedEndpoint L S 1 ⧸ pCore 2 (enlargedEndpoint L S 1)) = 144) ∨
      ∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL (L 1 ⧸ pCore 2 (L 1)) 2 (2^n) ∧
        (∃ r : ℕ, 0 < r ∧ 2^n = Nat.card k ^ r) ∧
        (centralSeed F₀ α β t).map (G₀ L S).subtype = Q₀ ∧
        P₀ L S 0 ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
        B₀ L S ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
        ∃ hN : (D₀.subgroupOf Q₀).Normal, letI := hN
          IsElementaryAbelian 2 (Q₀ ⧸ D₀.subgroupOf Q₀) ∧
          Nat.card (Q₀ ⧸ D₀.subgroupOf Q₀) = (2^n)^2 := by
  rcases original_bTwo_central_core_field_or_small_unitary h hb c hactor hcentral ht hne
    hcomm hnot E with hp | hs | hl
  · exact Or.inl ⟨hp,original_bTwo_small_projective_enlarged_order h hb c hactor hcentral
      ht hne hcomm.le hnot hp⟩
  · exact (original_bTwo_not_small_special_beta h hb c hactor hcentral ht hne
      hcomm.le hnot hs).elim
  · exact Or.inr hl


/-- Apply the genuine small-unitary enlargement to the original exceptional recognition. -/
theorem original_bTwo_exceptional_parabolics_or_projective144
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let Q₁ := (parabolic L S 1).pCoreIn 2
    (ClassicalGroup.IsPSU (L 1 ⧸ pCore 2 (L 1)) 3 2 ∧
      Nat.card (enlargedEndpoint L S 1 ⧸ pCore 2 (enlargedEndpoint L S 1)) = 144) ∨
      ∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL (L 1 ⧸ pCore 2 (L 1)) 2 (2^n) ∧
        Nat.card k = 2 ∧
        ((2^n = 2 ∧ Nat.card Q₀ = 16 ∧ Nat.card Q₁ = 16 ∧
          (∀ i : Fin 2, enlargedEndpoint L S i = parabolic L S i) ∧
          commonBorel L S = (commonBorel L S).pCoreIn 2 ∧
          Nat.card (commonBorel L S) = 32 ∧
          Nonempty (RankTwoAmalgam.ParabolicEquiv
            (RankTwoAmalgam.ofSubgroups (parabolic L S 1) (commonBorel L S)
              (parabolic L S 0) (commonBorel_le_parabolic 1)
              (commonBorel_le_parabolic 0)) Atlas.G2.BinaryParabolicPair.derivedAmalgam)) ∨
          (2^n = 4 ∧ Nat.card Q₀ = 64 ∧ Nat.card Q₁ = 32)) := by
  rcases original_bTwo_exceptional_parabolics_or_small_unitary h hb c hactor hcentral
    ht hne hcomm hnot hD E with hp | hs | hl
  · exact Or.inl ⟨hp,original_bTwo_small_projective_enlarged_order h hb c hactor hcentral
      ht hne hcomm.le hnot hp⟩
  · exact (original_bTwo_not_small_special_beta h hb c hactor hcentral ht hne
      hcomm.le hnot hs).elim
  · exact Or.inr hl

variable {k₁ W₁ : Type*} [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₁] [Module (ZMod 2) W₁]

/-- The earlier center family discharges centrality in the refined full-parabolic consumer. -/
theorem original_bTwo_exceptional_parabolics_or_projective144_of_center_family
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (hc : IsCriticalPair F₀ α u) (hne : ⁅Z F₀ α,Z F₀ u⁆ ≠ ⊥)
    (hnot : ∀ y, (graph F₀).Adj y α →
      ¬ stabilizer F₀ α ≤ normalizer
        ((Q F₀ y ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (hcenters : ∀ y, (graph F₀).Adj y α → IsCriticalPair F₀ β y →
      ⁅Z F₀ β,Z F₀ y⁆ ≠ ⊥ → Nonempty (BTwoCenterActionData F₀ β α y k₁ W₁))
    (ht : (graph F₀).Adj α t) (htne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let Q₁ := (parabolic L S 1).pCoreIn 2
    let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype
    P₀ L S 0 ≤ normalizer (D₀ : Set G) ∧
      B₀ L S ≤ normalizer (D₀ : Set G) ∧
      ((ClassicalGroup.IsPSU (L 1 ⧸ pCore 2 (L 1)) 3 2 ∧
        Nat.card (enlargedEndpoint L S 1 ⧸ pCore 2 (enlargedEndpoint L S 1)) = 144) ∨
        ∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL (L 1 ⧸ pCore 2 (L 1)) 2 (2^n) ∧
          Nat.card k = 2 ∧
          ((2^n = 2 ∧ Nat.card Q₀ = 16 ∧ Nat.card Q₁ = 16 ∧
            (∀ i : Fin 2, enlargedEndpoint L S i = parabolic L S i) ∧
            commonBorel L S = (commonBorel L S).pCoreIn 2 ∧
            Nat.card (commonBorel L S) = 32 ∧
            Nonempty (RankTwoAmalgam.ParabolicEquiv
              (RankTwoAmalgam.ofSubgroups (parabolic L S 1) (commonBorel L S)
                (parabolic L S 0) (commonBorel_le_parabolic 1)
                (commonBorel_le_parabolic 0)) Atlas.G2.BinaryParabolicPair.derivedAmalgam)) ∨
            (2^n = 4 ∧ Nat.card Q₀ = 64 ∧ Nat.card Q₁ = 32))) := by
  have hcentral := original_bTwo_center_central_of_center_family h hb c E E₁ hc hne
    hnot hcenters
  have hnorm := original_bTwo_seed_layers_normalized h hb c ht htne
  exact ⟨hnorm.1.trans inf_le_right,hnorm.2.trans inf_le_right,
    original_bTwo_exceptional_parabolics_or_projective144 h hb c hactor hcentral
      ht htne hcomm (hnot β c.middle.symm) hD E⟩

private theorem original_projective_normal_nine
    (h : HypothesisF11 L S) (i : Fin 2)
    (hm : ClassicalGroup.IsPSU (L i ⧸ pCore 2 (L i)) 3 2) :
    ∃ N : Subgroup (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)),
      N.Normal ∧ IsElementaryAbelian 3 N ∧ Nat.card N = 9 := by
  obtain ⟨F,hF,hfin,J,hc,hconj,⟨e⟩⟩ := hm
  let := hF
  let := hfin
  let M := enlargedEndpoint L S i
  let D := M ⧸ pCore 2 M
  let C := (starredParabolic L S i).subgroupOf M
  let q := QuotientGroup.mk' (pCore 2 M)
  let I := C.map q
  have hM : M ≤ parabolic L S i :=
    sup_le (starredParabolic_le i) ((pCoreIn_le 2 _).trans (commonBorel_le_parabolic i))
  let : Finite (parabolic L S i) := h.finite_parabolic i
  let : Finite M := Finite.of_injective (inclusion hM) (inclusion_injective _)
  let : C.Normal := normal_subgroupOf_of_le_normalizer (hM.trans
    ((normal_subgroupOf_iff_le_normalizer (starredParabolic_le i)).mp
      (h.starredParabolic_normal i)))
  let : I.Normal := (inferInstance : C.Normal).map q (QuotientGroup.mk'_surjective _)
  let f : C ≃* starredParabolic L S i := subgroupOfEquivOfLe le_sup_left
  let g : I ≃* ProjectiveSpecialUnitaryMatrixGroup J := (coreQuotientEquivImage 2 C).symm.trans
    ((QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans
      ((h.starredQuotientEquiv i).symm.trans e))
  let N := (pCore 3 I).map I.subtype
  let a : pCore 3 I ≃* pCore 3 (ProjectiveSpecialUnitaryMatrixGroup J) :=
    ((pCore 3 I).equivMapOfInjective g.toMonoidHom g.injective).trans
      (MulEquiv.subgroupCongr (pCore_map_iso 3 g))
  let b : N ≃* pCore 3 (ProjectiveSpecialUnitaryMatrixGroup J) :=
    ((pCore 3 I).equivMapOfInjective I.subtype I.subtype_injective).symm.trans a
  obtain ⟨h9,hE,_⟩ := HermitianForm.SmallThreeCore.projective_core_structure J hc hconj
  let := hE
  exact ⟨N,inferInstance,IsElementaryAbelian.of_injective b.toMonoidHom b.injective,
    (Nat.card_congr b.toEquiv).trans h9⟩

/-- The original PSU₃(2) beta row is excluded, including its genuine order-144 enlargement. -/
theorem original_bTwo_not_small_projective_beta
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (hm : ClassicalGroup.IsPSU (L 1 ⧸ pCore 2 (L 1)) 3 2) : False := by
  let M := enlargedEndpoint L S 1
  let H := M ⧸ pCore 2 M
  have hM : M ≤ parabolic L S 1 := sup_le (starredParabolic_le 1)
    ((pCoreIn_le 2 _).trans (commonBorel_le_parabolic 1))
  let : Finite (parabolic L S 1) := h.finite_parabolic 1
  let : Finite M := Finite.of_injective (inclusion hM) (inclusion_injective _)
  have hcard : Nat.card H = 144 := original_bTwo_small_projective_enlarged_order h hb c
    hactor hcentral ht hne hcomm hnot hm
  let : Finite H := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  obtain ⟨N,hN,hE,h9⟩ := original_projective_normal_nine h 1 hm
  let := hN
  let := hE
  apply c.not_beta_normal_elementary_le_frattini (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb hactor hcentral
    ht hne hcomm hnot (H := H) (reduced_graphEnlargementQuotient h true)
  intro T E hET hnE hE
  let := hE
  let : (E.subgroupOf (T : Subgroup H)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hET).mpr hnE
  let : IsElementaryAbelian 2 (E.subgroupOf (T : Subgroup H)) :=
    IsElementaryAbelian.comap_of_injective (T : Subgroup H).subtype
      (T : Subgroup H).subtype_injective E
  have hh := normal_elementary_le_frattini_of_normal_nine hcard N h9
    (pCore_quotient_pCore_eq_bot (G := M) 2) T (E.subgroupOf (T : Subgroup H))
  have hh' := map_mono (f := (T : Subgroup H).subtype) hh
  rwa [map_subgroupOf_eq_of_le hET] at hh'

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
