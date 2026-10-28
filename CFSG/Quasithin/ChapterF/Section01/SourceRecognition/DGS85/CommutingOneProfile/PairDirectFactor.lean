module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SmallPairSplitting

/-!
# The direct factor in the Chapter 11 beta-core quotient

The odd-actor splitting Q_beta = V C_Q_beta(y) has intersection J with V.
The two-alpha-core intersection D centralizes the center pair, lies in the
second factor, and satisfies [Q_beta,V] <= D. Consequently modulo D the
two factors commute and are disjoint. Their multiplication is the explicit
direct-product isomorphism, and the image of V is elementary abelian.

The small beta models supply the splitting here with no extra actor premise.
The linear and positive Suzuki splittings can use the same quotient theorem.
The source omega-containment argument is still needed to eliminate the
second factor; this module does not assert (11.3)(h) or select alpha.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3)(h), printed pp.170--171.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open scoped Pointwise IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The actual coprime splitting becomes a direct product modulo the two
alpha cores. The equivalence multiplies the literal quotient images. -/
theorem source_pair_core_split_images {K : Type*} [Group K]
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (π : Q (family P) b →* K) (hπ : Function.Surjective π)
    (hker : π.ker = (Q (family P) a ⊓ Q (family P) c).subgroupOf (Q (family P) b))
    (y : G) (hy : y ∈ Z (family P) a ⊔ Z (family P) c)
    (hsplit : Q (family P) b =
      pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) ⊔
        (Q (family P) b ⊓ centralizer (zpowers y : Set G)))
    (hint : pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) ⊓
      centralizer (zpowers y : Set G) = Z (family P) a ⊓ Z (family P) c) :
    let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
    let A := (V.subgroupOf (Q (family P) b)).map π
    let C := ((Q (family P) b ⊓ centralizer (zpowers y : Set G)).subgroupOf (Q (family P) b)).map π
    IsElementaryAbelian 2 A ∧ Disjoint A C ∧
      ∃ e : A × C ≃* K, ∀ x z, e (x,z) = (x : K) * (z : K) := by
  let Q₀ := Q (family P) b
  let V := pairSpan (Z (family P) a) (Z (family P) c) Q₀
  let D := Q (family P) a ⊓ Q (family P) c
  let C₀ := Q₀ ⊓ centralizer (zpowers y : Set G)
  let A₀ := V.subgroupOf Q₀
  let B₀ := C₀.subgroupOf Q₀
  have hVQ : V ≤ Q₀ := pairSpan_le_core _ _ _
  have hDcent : D ≤ centralizer (zpowers y : Set G) :=
    (le_centralizer_iff.mp (source_pair_core_normalizers h (source_critical_one_adjacent hc hb) hbc).1).trans
      (centralizer_le (zpowers_le.mpr hy))
  have hkerB : π.ker ≤ B₀ := by
    intro x hx
    rw [hker] at hx
    exact ⟨x.property,hDcent hx⟩
  have hAB : A₀ ⊓ B₀ ≤ π.ker := by
    intro x hx
    rw [hker]
    have hxJ := hint.le ⟨hx.1,hx.2.2⟩
    exact ⟨((source_Z_Q_U h a).1.trans (map_subtype_le _)) hxJ.1,
      ((source_Z_Q_U h c).1.trans (map_subtype_le _)) hxJ.2⟩
  have hd : Disjoint (A₀.map π) (B₀.map π) := by
    apply disjoint_def.mpr
    rintro x ⟨v,hv,rfl⟩ ⟨z,hz,he⟩
    have hvz : v*z⁻¹ ∈ π.ker := by
      change π (v*z⁻¹) = 1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    have hvB : v ∈ B₀ := by
      have hh := B₀.mul_mem (hkerB hvz) hz
      simpa only [inv_mul_cancel_right] using hh
    exact hAB ⟨hv,hvB⟩
  have hcomm : A₀.map π ≤ centralizer (B₀.map π : Set K) := by
    rintro x ⟨v,hv,rfl⟩ z ⟨w,hw,rfl⟩
    have hcD : ⁅(w:G),(v:G)⁆ ∈ D :=
      source_rankOne_pair_core_action h hB d hc hb hbc Ma Mb
        (commutator_mem_commutator w.property hv)
    have hcπ : π ⁅w,v⁆ = 1 := by
      apply (show ⁅w,v⁆ ∈ π.ker from hker.symm ▸ hcD)
    have hc' : ⁅π w,π v⁆ = 1 := by
      rw [←map_commutatorElement]
      exact hcπ
    exact commutatorElement_eq_one_iff_mul_comm.mp hc'
  have hgen : A₀.map π ⊔ B₀.map π = ⊤ := by
    rw [←Subgroup.map_sup,←subgroupOf_sup hVQ (show C₀ ≤ Q₀ from inf_le_left),
      ←hsplit,subgroupOf_self,map_top_of_surjective π hπ]
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (A₀.map π) (B₀.map π) hd hcomm
  have hel : IsElementaryAbelian 2 (A₀.map π) := by
    let j := inclusion hVQ
    have hk : (π.comp j).ker = D.subgroupOf V := by
      ext x
      change π (j x) = 1 ↔ _
      change j x ∈ π.ker ↔ _
      rw [hker]
      rfl
    have hh := (source_rankOne_pair_image_direct_product h hB d hc hb hbc hac Mb
      (π.comp j) hk).1
    have hr : (π.comp j).range = A₀.map π := by
      rw [MonoidHom.range_comp]
      congr 1
      ext x
      constructor
      · rintro ⟨v,rfl⟩
        exact v.property
      · intro hx
        exact ⟨⟨x.val,hx⟩,Subtype.ext rfl⟩
    exact hr ▸ hh
  refine ⟨hel,hd,e.trans ((MulEquiv.subgroupCongr hgen).trans topEquiv),?_⟩
  exact he


/-- The source direct decomposition in the literal quotient Q_beta/D,
including relative normality and the multiplication marking. -/
theorem source_pair_core_direct_product_of_splitting
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (hs : ∃ y ∈ Z (family P) a ⊔ Z (family P) c, Odd (orderOf y) ∧ y ≠ 1 ∧
      Q (family P) b = pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) ⊔
        (Q (family P) b ⊓ centralizer (zpowers y : Set G)) ∧
      pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) ⊓
        centralizer (zpowers y : Set G) = Z (family P) a ⊓ Z (family P) c) :
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
  let hD : ((Q (family P) a ⊓ Q (family P) c).subgroupOf (Q (family P) b)).Normal :=
    normal_subgroupOf_of_le_normalizer (le_sup_right.trans
      (source_pair_core_normalizers h (source_critical_one_adjacent hc hb) hbc).2.1)
  obtain ⟨y,hy,ho,hy1,hgen,hint⟩ := hs
  refine ⟨hD,y,hy,ho,hy1,?_⟩
  exact source_pair_core_split_images h hB d hc hb hbc hac Ma Mb _
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) y hy hgen hint

/-- The four small beta models supply the actual direct decomposition without
an odd-actor, splitting, or alpha-selection premise. -/
theorem source_small_models_pair_core_direct_product
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (hsmall : Nonempty ((d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5) ∨
      Nonempty ((d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 2 ∨
      ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 2) :
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
    (source_small_models_pair_coprime_splitting h hB d hc hb hbc hac Ma Mb hsmall)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
