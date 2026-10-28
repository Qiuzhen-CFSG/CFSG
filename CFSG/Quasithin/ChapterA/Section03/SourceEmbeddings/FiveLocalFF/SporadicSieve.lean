module

public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowNormalElementary
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.NormalElementaryBound
public import Theory.Mathieu.M11.Properties.SylowTwo
public import Theory.GroupTheory.SemidihedralNormalElementary
public import Theory.Mathieu.SmallModuleRanks.M12
public import Theory.SpecificGroups.Janko1.Model.SylowTwo

/-!
# Sporadic carrier exclusions from the original elementary subgroup

An elementary two-subgroup normalized by a full Sylow lies in that Sylow.
The native normal-elementary bounds for HS and J₂, and the semidihedral
Sylow presentation for M₁₁, bound its order by eight, four, and two.
The two-rank bound for M₁₂ and Sylow order for J₁ bound every elementary
two-subgroup by eight. Thus an original subgroup of order at least sixteen
leaves only M₂₂, M₂₃, M₂₄, J₄, Held, and Rudvalis in the source C catalogue.

All transports preserve the supplied elementary subgroup and full Sylow.
No block structure, whole-core identification, or subgroup-placement premise
is required. The final catalogue theorem is the consumer for the original
point-module image in the quasisimple inspection of 10.2.9.

Source: Aschbacher–Smith A.2.4, A.3.12 and 10.2.9, printed pp.33,47–48,750–751;
the native HS and J₂ normal-elementary calculations cite GLS3 Tables 5.3m,g.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SporadicSieve
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem elementary_le_sylow (S : Sylow 2 G) (E : Subgroup G)
    (hE : IsElementaryAbelian 2 E) (hn : (S : Subgroup G) ≤ normalizer (E : Set G)) :
    E ≤ S := by
  let := hE
  exact sup_eq_left.mp (S.is_maximal'
    (S.isPGroup'.to_sup_of_normal_right' (IsElementaryAbelian.isPGroup 2 E) hn)
    le_sup_left)

private theorem normalized_bound_of_equiv {H : Type*} [Group H] [Finite H]
    (e : G ≃* H) {n : ℕ}
    (hb : ∀ (S : Sylow 2 H) (E : Subgroup H), IsElementaryAbelian 2 E →
      (S : Subgroup H) ≤ normalizer (E : Set H) → Nat.card E ≤ n)
    (S : Sylow 2 G) (E : Subgroup G) (hE : IsElementaryAbelian 2 E)
    (hn : (S : Subgroup G) ≤ normalizer (E : Set G)) : Nat.card E ≤ n := by
  let := hE
  have hh := hb (S.mapSurjective (f := e.toMonoidHom) e.surjective)
    (E.map e.toMonoidHom) (IsElementaryAbelian.map e.toMonoidHom)
    ((map_mono hn).trans (E.le_normalizer_map e.toMonoidHom))
  rwa [Nat.card_congr (E.equivMapOfInjective e.toMonoidHom e.injective).symm.toEquiv] at hh

private theorem j2_normalized_bound (S : Sylow 2 Sporadic.LeechRelated.J2.Carrier)
    (E : Subgroup Sporadic.LeechRelated.J2.Carrier) (hE : IsElementaryAbelian 2 E)
    (hn : (S : Subgroup Sporadic.LeechRelated.J2.Carrier) ≤
      normalizer (E : Set Sporadic.LeechRelated.J2.Carrier)) : Nat.card E ≤ 4 := by
  let := hE
  have hES := elementary_le_sylow S E hE hn
  have hh := Sporadic.LeechRelated.J2.sylow_normal_elementary_card_le_four S
    (E.subgroupOf S) ((normal_subgroupOf_iff_le_normalizer hES).mpr hn)
    (IsElementaryAbelian.subgroupOf hES)
  rwa [Nat.card_congr (subgroupOfEquivOfLe hES).toEquiv] at hh

private theorem m11_normalized_bound (S : Sylow 2 Sporadic.Mathieu.M11)
    (E : Subgroup Sporadic.Mathieu.M11) (hE : IsElementaryAbelian 2 E)
    (hn : (S : Subgroup Sporadic.Mathieu.M11) ≤
      normalizer (E : Set Sporadic.Mathieu.M11)) : Nat.card E ≤ 2 := by
  let := hE
  have hES := elementary_le_sylow S E hE hn
  obtain ⟨P,a,b,ha,hb,hc,hg⟩ := Sporadic.Mathieu.m11_exists_semidihedral_sylow
  let e := S.equiv P
  let R := (E.subgroupOf S).map e.toMonoidHom
  let : (E.subgroupOf S).Normal := (normal_subgroupOf_iff_le_normalizer hES).mpr hn
  let : IsElementaryAbelian 2 (E.subgroupOf S) := IsElementaryAbelian.subgroupOf hES
  let : R.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  let : IsElementaryAbelian 2 R := IsElementaryAbelian.map e.toMonoidHom
  have hcard : Nat.card R = Nat.card E :=
    (card_map_of_injective e.injective).trans
      (Nat.card_congr (subgroupOfEquivOfLe hES).toEquiv)
  rw [←hcard]
  by_cases hR : R = ⊥
  · rw [hR,card_bot]
    decide
  · rw [Semidihedral.normal_elementary_eq_of_order_sixteen a b ha hb hc hg R hR,
      Nat.card_zpowers,orderOf_pow,ha]
    decide

/-- The actual HS carrier cannot contain the normalized original sixteen. -/
theorem not_higmanSims (S : Sylow 2 G) (E : Subgroup G)
    (hE : IsElementaryAbelian 2 E) (hn : (S : Subgroup G) ≤ normalizer (E : Set G))
    (hc : 16 ≤ Nat.card E) (e : G ≃* Sporadic.LeechRelated.HS.Carrier) : False := by
  have hh := normalized_bound_of_equiv e
    Sporadic.LeechRelated.HS.normal_elementary_card_le_eight S E hE hn
  omega

/-- The actual J₂ carrier cannot contain the normalized original sixteen. -/
theorem not_jankoTwo (S : Sylow 2 G) (E : Subgroup G)
    (hE : IsElementaryAbelian 2 E) (hn : (S : Subgroup G) ≤ normalizer (E : Set G))
    (hc : 16 ≤ Nat.card E) (e : G ≃* Sporadic.LeechRelated.J2.Carrier) : False := by
  have hh := normalized_bound_of_equiv e j2_normalized_bound S E hE hn
  omega

/-- The actual M₁₁ carrier cannot contain the normalized original sixteen. -/
theorem not_mathieuEleven (S : Sylow 2 G) (E : Subgroup G)
    (hE : IsElementaryAbelian 2 E) (hn : (S : Subgroup G) ≤ normalizer (E : Set G))
    (hc : 16 ≤ Nat.card E) (e : G ≃* Sporadic.Mathieu.M11) : False := by
  have hh := normalized_bound_of_equiv e m11_normalized_bound S E hE hn
  omega

/-- M₁₂ has no elementary two-subgroup of order at least sixteen. -/
theorem not_mathieuTwelve (E : Subgroup G) (hE : IsElementaryAbelian 2 E)
    (hc : 16 ≤ Nat.card E) (e : G ≃* Sporadic.Mathieu.M12) : False := by
  have hr : primeRank 2 G ≤ 3 := by
    rw [primeRank_equiv 2 e]
    exact Sporadic.Mathieu.m12_twoRank_le_three
  have hh := (primeRank_le_iff_elementary_card_le G).mp hr E hE
  norm_num at hh
  omega

omit [Finite G] in
/-- J₁ has no elementary two-subgroup of order at least sixteen. -/
theorem not_jankoOne (E : Subgroup G) (hE : IsElementaryAbelian 2 E)
    (hc : 16 ≤ Nat.card E) (e : G ≃* Janko1.Model) : False := by
  let := hE
  let A := E.map e.toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map e.toMonoidHom
  obtain ⟨S,hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  have hh := card_le_of_le hAS
  rw [Janko1.SylowTwo.card S,card_map_of_injective e.injective] at hh
  omega

/-- The actual source C sporadic catalogue reduces to six carriers when its
full Sylow normalizes the original large elementary subgroup. -/
theorem six_carriers (S : Sylow 2 G) (E : Subgroup G)
    (hE : IsElementaryAbelian 2 E) (hn : (S : Subgroup G) ≤ normalizer (E : Set G))
    (hc : 16 ≤ Nat.card E) (hm : Section02.IsTheoremCSporadicModel G) :
    ∃ name : ClassificationModels.SporadicName,
      (name = .m22 ∨ name = .m23 ∨ name = .m24 ∨ name = .j4 ∨
        name = .he ∨ name = .ru) ∧ Nonempty (G ≃* name.Carrier) := by
  rcases hm with hm | hm
  · obtain ⟨name,hne,⟨e⟩⟩ := hm
    cases name with
    | m11 => exact (not_mathieuEleven S E hE hn hc e).elim
    | m12 => exact (not_mathieuTwelve E hE hc e).elim
    | j2 => exact (not_jankoTwo S E hE hn hc e).elim
    | j3 => exact (hne rfl).elim
    | hs => exact (not_higmanSims S E hE hn hc e).elim
    | m22 => exact ⟨.m22,by simp,⟨e⟩⟩
    | m23 => exact ⟨.m23,by simp,⟨e⟩⟩
    | m24 => exact ⟨.m24,by simp,⟨e⟩⟩
    | j4 => exact ⟨.j4,by simp,⟨e⟩⟩
    | he => exact ⟨.he,by simp,⟨e⟩⟩
    | ru => exact ⟨.ru,by simp,⟨e⟩⟩
  · obtain ⟨e⟩ := hm
    exact (not_jankoOne E hE hc e).elim

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SporadicSieve
