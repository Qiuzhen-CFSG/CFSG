module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.PairNonabelian
public import Theory.Representation.BinaryFourTransitive

/-!
# The small beta seed-square bound

If the opposite seed had index two, the literal pair section would have
order four. Its proved zero fixed space makes the pair action transitive
on the three nonzero vectors. Central elementary kernel and an elementary
seed lift then make the pair elementary. The alpha-center sharp-index
argument excludes this when the critical-center image also has order two.
The opposite seed index is a nontrivial power of two, so it is at least four.

Two-rank one identifies the critical-center image order for D10, Sz(2),
SU3(2), and PSU3(2), retaining their actual quotient maps. This discharges
all small cases of DGS85 (11.3)(g) at prime two, without selecting alpha.
Source: Groups and Graphs (1985), (11.3)(a,b,e,g), pp.168--170.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.BinaryConjugationSection
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- An opposite seed of index two makes the full pair elementary. -/
theorem source_pair_elementary_of_opposite_seed_index_two
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (hidx : (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b) = 2) :
    IsElementaryAbelian 2 (pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)) := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let := source_center_elementary h c
  let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
  let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
  let J := Z (family P) a ⊓ Z (family P) c
  let E := Z (family P) a ⊓ Q (family P) b
  let : Finite V := Finite.of_injective
    (inclusion ((pairSpan_le_core _ _ _).trans (Q_le_stabilizer _ b))) (inclusion_injective _)
  obtain ⟨hJ,hE,hQ,σ,s,_,_,_,_⟩ := source_rankOne_pair_section h hB d hc hb hbc hac Ma Mb
  let := hJ
  let := hE
  let := hQ
  let π := QuotientGroup.mk' ((Q (family P) b).subgroupOf H)
  let : Finite (V ⧸ J.subgroupOf V) := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  have hfixed := (source_rankOne_pair_fixed_spaces h hB d hc hb hbc Mb π
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) σ s).1
  have hfour : Nat.card (Additive (V ⧸ J.subgroupOf V)) = 4 := by
    change Nat.card (V ⧸ J.subgroupOf V) = 4
    rw [source_rankOne_pair_quotient_order h hB d hc hb hbc hac Mb,hidx]
    rfl
  have hcentral : J ≤ centralizer (V : Set G) := by
    apply le_centralizer_iff.mpr
    apply sup_le
    · exact inf_le_left.trans ((le_centralizer_iff_isMulCommutative.mpr
        (inferInstance : IsMulCommutative (Z (family P) a))).trans (centralizer_le inf_le_left))
    · exact inf_le_left.trans ((le_centralizer_iff_isMulCommutative.mpr
        (inferInstance : IsMulCommutative (Z (family P) c))).trans (centralizer_le inf_le_right))
  apply s.elementary_of_transitive hcentral
  · intro x hx
    exact elemPow_eq_one_of_isElementaryAbelian x hx.1
  · obtain ⟨x,hx,hesc⟩ := SetLike.not_le_iff_exists.mp (source_rankOne_seed_escape h hB d hc hb hbc hac Mb).1
    refine ⟨⟨x,(show E ≤ V from le_sup_left) hx⟩,
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian x hx.1),?_⟩
    intro he
    exact hesc (((source_Z_Q_U h c).1.trans (map_subtype_le _))
      ((s.coordinates_eq_one_iff _).mp he).2)
  · intro u v hu hv
    obtain ⟨x,hx⟩ := transitive_nonzero_of_card_four σ hfour hfixed u v hu hv
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective ((Q (family P) b).subgroupOf H) x
    exact ⟨y,hx⟩

/-- Source (11.3)(g) whenever the critical-center image has order two. -/
theorem source_small_beta_seed_square
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (hsmall : (Q (family P) b).relIndex (Z (family P) a) = 2) :
    ((Q (family P) b).relIndex (Z (family P) a))^2 ≤
      (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b) := by
  let := finite_endpoints h
  let := source_center_elementary h c
  let C := Z (family P) c ⊓ Q (family P) b
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le inf_le_left
  let : Finite C := Finite.of_injective
    (inclusion (inf_le_left.trans (Z_le_stabilizer _ c))) (inclusion_injective _)
  have hesc : ¬ C ≤ Q (family P) a := source_seed_not_le_opposite_core h hbc.symm
    (source_critical_one_adjacent hc hb).symm
    (by intro hp; apply source_rankOne_centers_not_isPGroup h hB d hc hb hbc hac Mb;
        rw [sup_comm]; exact hp)
  have hpow : ∃ n : ℕ, (Q (family P) a).relIndex C = 2^n := by
    exact (IsElementaryAbelian.isPGroup 2 C).index ((Q (family P) a).subgroupOf C)
  obtain ⟨n,hn⟩ := hpow
  have hnpos : 0 < n := by
    by_contra! he
    have hn0 : n = 0 := by omega
    rw [hn0,pow_zero] at hn
    exact hesc (relIndex_eq_one.mp hn)
  have hn1 : n ≠ 1 := by
    intro he
    have hi : (Q (family P) a).relIndex C = 2 := by simpa only [he,pow_one] using hn
    let := source_pair_elementary_of_opposite_seed_index_two h hB d hc hb hbc hac Ma Mb hi
    exact source_pair_nonabelian_of_seed_index_le h hB d hc hb hcomm hbc hac Ma Mb
      (by rw [hsmall,hi])
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff_isMulCommutative.mpr
        (inferInstance : IsMulCommutative (pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)))))
  rw [hsmall,hn]
  exact Nat.pow_le_pow_right (by decide) (by omega)

/-- In a beta quotient of two-rank one, the critical-center image has
order exactly two, using its actual quotient map. -/
theorem source_beta_seed_index_two_of_two_rank
    (h : LocallyRankOneTriple P B) (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hr : primeRank 2 (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≤ 1) :
    (Q (family P) b).relIndex (Z (family P) a) = 2 := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let L := d.localGroup b
  let : Finite L := Finite.of_injective (inclusion (d.local_le b)) (inclusion_injective _)
  let : Finite (L ⧸ pCore 2 L) := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  have hab := source_critical_one_adjacent hc hb
  have hZaL : Z (family P) a ≤ L := pGroup_le_localGroup (family P) d b (Z (family P) a)
    (IsElementaryAbelian.isPGroup 2 _) ((((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
      (source_Z_Q_U h a).2).trans ((ballKernel_one_le_edge _ hab).trans inf_le_right))
  let q := QuotientGroup.mk' (pCore 2 L)
  let A := ((Z (family P) a).subgroupOf L).map q
  let : IsElementaryAbelian 2 ((Z (family P) a).subgroupOf L) := IsElementaryAbelian.subgroupOf hZaL
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map q
  have hcard : Nat.card A = (Q (family P) b).relIndex (Z (family P) a) :=
    actor_image_card_eq_relIndex L (Q (family P) b) (Z (family P) a) q
      (local_quotient_kernel (family P) d b (MulEquiv.refl _)) hZaL
  have hu : Nat.card A ≤ 2 := by
    simpa using (primeRank_le_iff_elementary_card_le _).mp hr A inferInstance
  have hp := Nat.card_pos (α := A)
  have hn : Nat.card A ≠ 1 := by
    intro he
    exact hc.2 ((relIndex_eq_one.mp (hcard.symm.trans he)).trans (source_Z_Q_U h b).2)
  omega

/-- All four small nonlinear/dihedral beta models satisfy the literal
seed-square bound. The unitary special and projective carriers stay distinct. -/
theorem source_small_beta_model_seed_square
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (hsmall : Nonempty ((d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5) ∨
      Nonempty ((d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 2 ∨
      ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 2) :
    ((Q (family P) b).relIndex (Z (family P) a))^2 ≤
      (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b) := by
  let := Mb.finite
  exact source_small_beta_seed_square h hB d hc hb hcomm hbc hac Ma Mb
    (source_beta_seed_index_two_of_two_rank h d hc hb (small_beta_models_two_rank hsmall))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
