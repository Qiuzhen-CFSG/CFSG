module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.PairCoprimeSplitting
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.RankOnePairSplitting

/-!
# Original-source applications of the center-pair actor and splitting

The actual quotient marking on the original local-group image pulls back
through the quotient isomorphism induced by the reduced-group inclusion.
The center-pair actor retains its literal quotient map. The linear, Suzuki,
D10 and both unitary splittings now transport through that same inclusion
for every source field, including the odd actor, both factors, and their
exact intersection. The general direct-product decomposition is constructed
on the literal original quotient Q_beta/(Q_alpha intersect Q_gamma), with
both quotient images and their multiplication marking retained.

The fixed-point-free-actor and coprime-splitting premises are discharged
throughout the earlier rank-one catalogue. The omega-containment argument
eliminating the complementary factor, the (11.4) core product, alpha row
selection, later profiles and original marked assembly remain obligations.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3)(h), printed pp.170--171; source reduction, pp.95--96.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open scoped Pointwise IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
open BenderSuzuki.MatrixGroups
section Original
variable {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀

/-- The exact omega-pair actor in the reduced source geometry, with the
beta marking supplied on its image in the original completion. -/
theorem original_reduced_pair_actor_equiv (h : HypothesisF11 L₀ S₀)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Mb : IsRankOneModel ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)))
    [hN : ((Q F₀ b).subgroupOf ((Z F₀ a ⊔ Z F₀ c) ⊔ Q F₀ b)).Normal] :
    let H := (Z F₀ a ⊔ Z F₀ c) ⊔ Q F₀ b
    let K := d.localGroup b
    ∃ R T : Sylow 2 (K ⧸ pCore 2 K), R ≠ T ∧
      ∃ hHK : H ≤ K,
        ∃ e : (H ⧸ (Q F₀ b).subgroupOf H) ≃*
            (omegaCenterIn (R : Subgroup (K ⧸ pCore 2 K)) ⊔
              omegaCenterIn (T : Subgroup (K ⧸ pCore 2 K)) : Subgroup (K ⧸ pCore 2 K)),
          ∀ x : H, (e (QuotientGroup.mk' ((Q F₀ b).subgroupOf H) x) : K ⧸ pCore 2 K) =
            QuotientGroup.mk' (pCore 2 K) (inclusion hHK x) := by
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  exact source_pair_actor_equiv (hN := hN) (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hbc hac (Mb.of_equiv eqb)

private theorem map_inf_centralizer {C D : Type*} [Group C] [Group D]
    (j : C →* D) (hj : Function.Injective j) (A K : Subgroup C) :
    (A ⊓ centralizer (K : Set C)).map j = A.map j ⊓ centralizer (K.map j : Set D) := by
  apply le_antisymm
  · rintro x ⟨a,ha,rfl⟩
    refine ⟨mem_map_of_mem j ha.1,?_⟩
    rintro z ⟨k,hk,rfl⟩
    simpa only [map_mul] using congrArg j (ha.2 k hk)
  · rintro x ⟨⟨a,ha,rfl⟩,hx⟩
    refine ⟨a,⟨ha,?_⟩,rfl⟩
    intro k hk
    apply hj
    simpa only [map_mul] using hx (j k) (mem_map_of_mem j hk)

private theorem map_pair_splitting {C D : Type*} [Group C] [Group D]
    (j : C →* D) (hj : Function.Injective j) (A Q V J : Subgroup C)
    (hs : ∃ y ∈ A, Odd (orderOf y) ∧ y ≠ 1 ∧
      Q = V ⊔ (Q ⊓ centralizer (zpowers y : Set C)) ∧
      V ⊓ centralizer (zpowers y : Set C) = J) :
    ∃ y ∈ A.map j, Odd (orderOf y) ∧ y ≠ 1 ∧
      Q.map j = V.map j ⊔ (Q.map j ⊓ centralizer (zpowers y : Set D)) ∧
      V.map j ⊓ centralizer (zpowers y : Set D) = J.map j := by
  obtain ⟨y,hy,ho,hy1,hgen,hint⟩ := hs
  refine ⟨j y,mem_map_of_mem j hy,(orderOf_injective j hj y).symm ▸ ho,
    fun he => hy1 (hj (he.trans j.map_one.symm)),?_,?_⟩
  · have hm := congrArg (map j) hgen
    rwa [Subgroup.map_sup,map_inf_centralizer j hj,MonoidHom.map_zpowers] at hm
  · have hm := congrArg (map j) hint
    rwa [map_inf_centralizer j hj,MonoidHom.map_zpowers] at hm

/-- The linear-beta coprime splitting on the literal original subgroup images.
The original completion may be infinite, and alpha is not preselected. -/
theorem original_reduced_linear_pair_coprime_splitting
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)))
    (e : ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)) ≃* SL(2,k)) :
    let j := (G₀).subtype
    let V := (pairSpan (Z F₀ a) (Z F₀ c) (Q F₀ b)).map j
    ∃ y ∈ (Z F₀ a).map j ⊔ (Z F₀ c).map j, Odd (orderOf y) ∧ y ≠ 1 ∧
      (Q F₀ b).map j = V ⊔ ((Q F₀ b).map j ⊓ centralizer (zpowers y : Set G)) ∧
      V ⊓ centralizer (zpowers y : Set G) = (Z F₀ a).map j ⊓ (Z F₀ c).map j := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  have hs := source_linear_pair_coprime_splitting (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hbc hac (Ma.of_equiv eqa) (Mb.of_equiv eqb)
      (eqb.trans e)
  dsimp only
  rw [←Subgroup.map_sup,←map_inf _ _ _ (G₀).subtype_injective]
  exact map_pair_splitting (G₀).subtype (G₀).subtype_injective _ _ _ _ hs

/-- The nondegenerate Suzuki-beta splitting through the same original inclusion,
with every earlier alpha alternative retained. -/
theorem original_reduced_suzuki_pair_coprime_splitting
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)))
    {m : ℕ} (hm : 0 < m)
    (e : ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)) ≃* SuzukiMatrixGroup m) :
    let j := (G₀).subtype
    let V := (pairSpan (Z F₀ a) (Z F₀ c) (Q F₀ b)).map j
    ∃ y ∈ (Z F₀ a).map j ⊔ (Z F₀ c).map j, Odd (orderOf y) ∧ y ≠ 1 ∧
      (Q F₀ b).map j = V ⊔ ((Q F₀ b).map j ⊓ centralizer (zpowers y : Set G)) ∧
      V ⊓ centralizer (zpowers y : Set G) = (Z F₀ a).map j ⊓ (Z F₀ c).map j := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  have hs := source_suzuki_pair_coprime_splitting (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hbc hac (Ma.of_equiv eqa) (Mb.of_equiv eqb)
      hm (eqb.trans e)
  dsimp only
  rw [←Subgroup.map_sup,←map_inf _ _ _ (G₀).subtype_injective]
  exact map_pair_splitting (G₀).subtype (G₀).subtype_injective _ _ _ _ hs
/-- The D10, Sz(2), SU3(2), and PSU3(2) splittings on the literal original
images, with arbitrary alpha and the complete original beta marking. -/
theorem original_reduced_small_models_pair_coprime_splitting
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)))
    (hsmall : Nonempty (((d.localGroup b).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup b).map (G₀).subtype)) ≃* DihedralGroup 5) ∨
      Nonempty (((d.localGroup b).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup b).map (G₀).subtype)) ≃* SuzukiMatrixGroup 0) ∨
      IsSU ((d.localGroup b).map (G₀).subtype ⧸ pCore 2 ((d.localGroup b).map (G₀).subtype)) 3 2 ∨
      ClassicalGroup.IsPSU ((d.localGroup b).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup b).map (G₀).subtype)) 3 2) :
    let j := (G₀).subtype
    let V := (pairSpan (Z F₀ a) (Z F₀ c) (Q F₀ b)).map j
    ∃ y ∈ (Z F₀ a).map j ⊔ (Z F₀ c).map j, Odd (orderOf y) ∧ y ≠ 1 ∧
      (Q F₀ b).map j = V ⊔ ((Q F₀ b).map j ⊓ centralizer (zpowers y : Set G)) ∧
      V ⊓ centralizer (zpowers y : Set G) = (Z F₀ a).map j ⊓ (Z F₀ c).map j := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  let : ∀ i, Finite (F₀ i) := finite_endpoints (Reduction.reduced_triple h)
  let : Finite (d.localGroup b) := Finite.of_injective (inclusion (d.local_le b)) (inclusion_injective _)
  let : Finite ((d.localGroup b).map (G₀).subtype) := Finite.of_surjective eb eb.surjective
  let : Finite ((d.localGroup b).map (G₀).subtype ⧸ pCore 2 ((d.localGroup b).map (G₀).subtype)) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  let : Finite (d.localGroup b ⧸ pCore 2 (d.localGroup b)) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  have hr := (primeRank_le_of_injective 2 eqb.toMonoidHom eqb.injective).trans
    (small_beta_models_two_rank hsmall)
  have hs := source_small_pair_coprime_splitting (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hbc hac (Ma.of_equiv eqa) (Mb.of_equiv eqb) hr
  dsimp only
  rw [←Subgroup.map_sup,←map_inf _ _ _ (G₀).subtype_injective]
  exact map_pair_splitting (G₀).subtype (G₀).subtype_injective _ _ _ _ hs

/-- The small-model decomposition on Q_beta/D inside the original completion.
Both factors are literal images under its quotient map, and the displayed
isomorphism multiplies those images. -/
theorem original_reduced_small_models_pair_core_direct_product
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)))
    (hsmall : Nonempty (((d.localGroup b).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup b).map (G₀).subtype)) ≃* DihedralGroup 5) ∨
      Nonempty (((d.localGroup b).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup b).map (G₀).subtype)) ≃* SuzukiMatrixGroup 0) ∨
      IsSU ((d.localGroup b).map (G₀).subtype ⧸ pCore 2 ((d.localGroup b).map (G₀).subtype)) 3 2 ∨
      ClassicalGroup.IsPSU ((d.localGroup b).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup b).map (G₀).subtype)) 3 2) :
    let j := (G₀).subtype
    let Q₁ := (Q F₀ b).map j
    let D₁ := (Q F₀ a).map j ⊓ (Q F₀ c).map j
    let V₁ := (pairSpan (Z F₀ a) (Z F₀ c) (Q F₀ b)).map j
    ∃ hD : (D₁.subgroupOf Q₁).Normal, letI := hD
      let π := QuotientGroup.mk' (D₁.subgroupOf Q₁)
      let A := (V₁.subgroupOf Q₁).map π
      ∃ y ∈ (Z F₀ a).map j ⊔ (Z F₀ c).map j, Odd (orderOf y) ∧ y ≠ 1 ∧
        let C := ((Q₁ ⊓ centralizer (zpowers y : Set G)).subgroupOf Q₁).map π
        IsElementaryAbelian 2 A ∧ Disjoint A C ∧
          ∃ e : A × C ≃* (Q₁ ⧸ D₁.subgroupOf Q₁),
            ∀ x z, e (x,z) = (x : Q₁ ⧸ D₁.subgroupOf Q₁) * (z : Q₁ ⧸ D₁.subgroupOf Q₁) := by
  let j := (G₀).subtype
  let Q₀ := Q F₀ b
  let D := Q F₀ a ⊓ Q F₀ c
  let V := pairSpan (Z F₀ a) (Z F₀ c) Q₀
  let Q₁ := Q₀.map j
  let D₁ := (Q F₀ a).map j ⊓ (Q F₀ c).map j
  have hDmap : D.map j = D₁ := map_inf _ _ _ (G₀).subtype_injective
  have hn : Q₀ ≤ normalizer (D : Set G₀) := le_sup_right.trans
    (source_pair_core_normalizers (Reduction.reduced_triple h)
      (source_critical_one_adjacent hc hb) hbc).2.1
  let hD : (D₁.subgroupOf Q₁).Normal := normal_subgroupOf_of_le_normalizer (by
    change Q₀.map j ≤ normalizer (D₁ : Set G)
    rw [←hDmap]
    exact (map_mono hn).trans (le_normalizer_map j))
  let π := QuotientGroup.mk' (D₁.subgroupOf Q₁)
  let eq := Q₀.equivMapOfInjective j (G₀).subtype_injective
  let f := π.comp eq.toMonoidHom
  have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp eq.surjective
  have hk : f.ker = D.subgroupOf Q₀ := by
    ext x
    change π (eq x) = 1 ↔ x.val ∈ D
    change eq x ∈ π.ker ↔ _
    have hkπ : π.ker = D₁.subgroupOf Q₁ := QuotientGroup.ker_mk' _
    rw [hkπ]
    change j x.val ∈ D₁ ↔ _
    rw [←hDmap]
    constructor
    · rintro ⟨z,hz,he⟩
      exact (G₀).subtype_injective he ▸ hz
    · exact mem_map_of_mem j
  have hm (A : Subgroup G₀) (hAQ : A ≤ Q₀) :
      (A.subgroupOf Q₀).map f = ((A.map j).subgroupOf Q₁).map π := by
    rw [show f = π.comp eq.toMonoidHom from rfl,←map_map]
    congr 1
    ext x
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact mem_map_of_mem j hv
    · rintro ⟨v,hv,he⟩
      refine ⟨⟨v,hAQ hv⟩,hv,?_⟩
      exact Subtype.ext he
  obtain ⟨y,hy,ho,hy1,hgen,hint⟩ :=
    original_reduced_small_models_pair_coprime_splitting h d hc hb hbc hac Ma Mb hsmall
  rw [←Subgroup.map_sup] at hy
  obtain ⟨y,hy,rfl⟩ := hy
  have hgen₀ : Q₀ = V ⊔ (Q₀ ⊓ centralizer (zpowers y : Set G₀)) := by
    apply map_injective (G₀).subtype_injective
    rw [Subgroup.map_sup,map_inf_centralizer j (G₀).subtype_injective,MonoidHom.map_zpowers]
    exact hgen
  have hint₀ : V ⊓ centralizer (zpowers y : Set G₀) = Z F₀ a ⊓ Z F₀ c := by
    apply map_injective (G₀).subtype_injective
    rw [map_inf_centralizer j (G₀).subtype_injective,MonoidHom.map_zpowers,
      map_inf _ _ _ (G₀).subtype_injective]
    exact hint
  let ea := (d.localGroup a).equivMapOfInjective j (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective j (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  have hs := source_pair_core_split_images (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hbc hac (Ma.of_equiv eqa) (Mb.of_equiv eqb)
      f hf hk y hy hgen₀ hint₀
  change IsElementaryAbelian 2 ((V.subgroupOf Q₀).map f) ∧
    Disjoint ((V.subgroupOf Q₀).map f)
      (((Q₀ ⊓ centralizer (zpowers y : Set G₀)).subgroupOf Q₀).map f) ∧
      (∃ e : ((V.subgroupOf Q₀).map f) ×
          (((Q₀ ⊓ centralizer (zpowers y : Set G₀)).subgroupOf Q₀).map f) ≃*
            (Q₁ ⧸ D₁.subgroupOf Q₁),
        ∀ x z, e (x,z) = (x : Q₁ ⧸ D₁.subgroupOf Q₁) *
          (z : Q₁ ⧸ D₁.subgroupOf Q₁)) at hs
  rw [hm V (pairSpan_le_core _ _ _),hm _ inf_le_left,
    map_inf_centralizer j (G₀).subtype_injective,MonoidHom.map_zpowers] at hs
  refine ⟨hD,j y,?_,ho,hy1,hs⟩
  rw [←Subgroup.map_sup]
  exact mem_map_of_mem j hy

/-- The coprime splitting in the original completion for the complete earlier
quotient catalogue, retaining both endpoint markings and the actual inclusion. -/
theorem original_reduced_rankOne_pair_coprime_splitting
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype))) :
    let j := (G₀).subtype
    let V := (pairSpan (Z F₀ a) (Z F₀ c) (Q F₀ b)).map j
    ∃ y ∈ (Z F₀ a).map j ⊔ (Z F₀ c).map j, Odd (orderOf y) ∧ y ≠ 1 ∧
      (Q F₀ b).map j = V ⊔ ((Q F₀ b).map j ⊓ centralizer (zpowers y : Set G)) ∧
      V ⊓ centralizer (zpowers y : Set G) = (Z F₀ a).map j ⊓ (Z F₀ c).map j := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  have hs := source_rankOne_pair_coprime_splitting (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hbc hac (Ma.of_equiv eqa) (Mb.of_equiv eqb)
  dsimp only
  rw [←Subgroup.map_sup,←map_inf _ _ _ (G₀).subtype_injective]
  exact map_pair_splitting (G₀).subtype (G₀).subtype_injective _ _ _ _ hs

/-- The direct decomposition of the literal original beta-core quotient,
for every rank-one row. Both quotient images and multiplication are retained. -/
theorem original_reduced_rankOne_pair_core_direct_product
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype))) :
    let j := (G₀).subtype
    let Q₁ := (Q F₀ b).map j
    let D₁ := (Q F₀ a).map j ⊓ (Q F₀ c).map j
    let V₁ := (pairSpan (Z F₀ a) (Z F₀ c) (Q F₀ b)).map j
    ∃ hD : (D₁.subgroupOf Q₁).Normal, letI := hD
      let π := QuotientGroup.mk' (D₁.subgroupOf Q₁)
      let A := (V₁.subgroupOf Q₁).map π
      ∃ y ∈ (Z F₀ a).map j ⊔ (Z F₀ c).map j, Odd (orderOf y) ∧ y ≠ 1 ∧
        let C := ((Q₁ ⊓ centralizer (zpowers y : Set G)).subgroupOf Q₁).map π
        IsElementaryAbelian 2 A ∧ Disjoint A C ∧
          ∃ e : A × C ≃* (Q₁ ⧸ D₁.subgroupOf Q₁),
            ∀ x z, e (x,z) = (x : Q₁ ⧸ D₁.subgroupOf Q₁) * (z : Q₁ ⧸ D₁.subgroupOf Q₁) := by
  let j := (G₀).subtype
  let Q₀ := Q F₀ b
  let D := Q F₀ a ⊓ Q F₀ c
  let V := pairSpan (Z F₀ a) (Z F₀ c) Q₀
  let Q₁ := Q₀.map j
  let D₁ := (Q F₀ a).map j ⊓ (Q F₀ c).map j
  have hDmap : D.map j = D₁ := map_inf _ _ _ (G₀).subtype_injective
  have hn : Q₀ ≤ normalizer (D : Set G₀) := le_sup_right.trans
    (source_pair_core_normalizers (Reduction.reduced_triple h)
      (source_critical_one_adjacent hc hb) hbc).2.1
  let hD : (D₁.subgroupOf Q₁).Normal := normal_subgroupOf_of_le_normalizer (by
    change Q₀.map j ≤ normalizer (D₁ : Set G)
    rw [←hDmap]
    exact (map_mono hn).trans (le_normalizer_map j))
  let π := QuotientGroup.mk' (D₁.subgroupOf Q₁)
  let eq := Q₀.equivMapOfInjective j (G₀).subtype_injective
  let f := π.comp eq.toMonoidHom
  have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp eq.surjective
  have hk : f.ker = D.subgroupOf Q₀ := by
    ext x
    change π (eq x) = 1 ↔ x.val ∈ D
    change eq x ∈ π.ker ↔ _
    have hkπ : π.ker = D₁.subgroupOf Q₁ := QuotientGroup.ker_mk' _
    rw [hkπ]
    change j x.val ∈ D₁ ↔ _
    rw [←hDmap]
    constructor
    · rintro ⟨z,hz,he⟩
      exact (G₀).subtype_injective he ▸ hz
    · exact mem_map_of_mem j
  have hm (A : Subgroup G₀) (hAQ : A ≤ Q₀) :
      (A.subgroupOf Q₀).map f = ((A.map j).subgroupOf Q₁).map π := by
    rw [show f = π.comp eq.toMonoidHom from rfl,←map_map]
    congr 1
    ext x
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact mem_map_of_mem j hv
    · rintro ⟨v,hv,he⟩
      refine ⟨⟨v,hAQ hv⟩,hv,?_⟩
      exact Subtype.ext he
  obtain ⟨y,hy,ho,hy1,hgen,hint⟩ :=
    original_reduced_rankOne_pair_coprime_splitting h d hc hb hbc hac Ma Mb
  rw [←Subgroup.map_sup] at hy
  obtain ⟨y,hy,rfl⟩ := hy
  have hgen₀ : Q₀ = V ⊔ (Q₀ ⊓ centralizer (zpowers y : Set G₀)) := by
    apply map_injective (G₀).subtype_injective
    rw [Subgroup.map_sup,map_inf_centralizer j (G₀).subtype_injective,MonoidHom.map_zpowers]
    exact hgen
  have hint₀ : V ⊓ centralizer (zpowers y : Set G₀) = Z F₀ a ⊓ Z F₀ c := by
    apply map_injective (G₀).subtype_injective
    rw [map_inf_centralizer j (G₀).subtype_injective,MonoidHom.map_zpowers,
      map_inf _ _ _ (G₀).subtype_injective]
    exact hint
  let ea := (d.localGroup a).equivMapOfInjective j (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective j (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  have hs := source_pair_core_split_images (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hbc hac (Ma.of_equiv eqa) (Mb.of_equiv eqb)
      f hf hk y hy hgen₀ hint₀
  change IsElementaryAbelian 2 ((V.subgroupOf Q₀).map f) ∧
    Disjoint ((V.subgroupOf Q₀).map f)
      (((Q₀ ⊓ centralizer (zpowers y : Set G₀)).subgroupOf Q₀).map f) ∧
      (∃ e : ((V.subgroupOf Q₀).map f) ×
          (((Q₀ ⊓ centralizer (zpowers y : Set G₀)).subgroupOf Q₀).map f) ≃*
            (Q₁ ⧸ D₁.subgroupOf Q₁),
        ∀ x z, e (x,z) = (x : Q₁ ⧸ D₁.subgroupOf Q₁) *
          (z : Q₁ ⧸ D₁.subgroupOf Q₁)) at hs
  rw [hm V (pairSpan_le_core _ _ _),hm _ inf_le_left,
    map_inf_centralizer j (G₀).subtype_injective,MonoidHom.map_zpowers] at hs
  refine ⟨hD,j y,?_,ho,hy1,hs⟩
  rw [←Subgroup.map_sup]
  exact mem_map_of_mem j hy

end Original

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
