module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.ClassicalModels
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.Alternating.PrimeRank
public import Theory.Quasithin.CoprimeRank
public import Theory.PGroupCore

/-!
# The literal local A₈ quotient

Finite-field transport identifies the supplied PSL₄(2) quotient with A₈.
Its order and three-rank survive the original two-core extension. In a
simple ambient group, a local component with nontrivial two-core cannot
generate the whole group together with its marking subgroup.
Source: Aschbacher–Smith A.3.12 and 15.3.32(3), printed pp.47–48 and 1132.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem quotient_equiv {B : Subgroup G}
    (h : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2) :
    Nonempty (B ⧸ pCore 2 B ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let := Fintype.ofFinite F
  let a : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  exact ⟨e.trans ((Atlas.fieldEquivPSL 4 a).trans
    Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8)⟩

omit [Finite G] in
theorem quotient_card {B : Subgroup G}
    (h : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2) :
    Nat.card (B ⧸ pCore 2 B) = 20160 := by
  obtain ⟨e⟩ := quotient_equiv h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  norm_num

omit [Finite G] in
theorem quotient_card_dvd {B : Subgroup G}
    (h : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2) : 20160 ∣ Nat.card B := by
  rw [← quotient_card h]
  exact (pCore 2 B).index_dvd_card

omit [Finite G] in
theorem ambient_card_dvd {B : Subgroup G}
    (h : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2) : 20160 ∣ Nat.card G :=
  (quotient_card_dvd h).trans B.card_subgroup_dvd_card

theorem threeRank {B : Subgroup G}
    (h : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2) : primeRank 3 B = 2 := by
  obtain ⟨e⟩ := quotient_equiv h
  rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 B) pCore_isPGroup,
    primeRank_congr 3 e,
    GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 8 3 (by decide) (by decide)]

omit [Finite G] in
theorem local_perfect {T B : Subgroup G} (hB : B ∈ localCComponents T) :
    Group.IsPerfect B := by
  let := hB.perfect
  let e := subgroupOfEquivOfLe (show B ≤ B ⊔ T from le_sup_left)
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

omit [Finite G] in
theorem join_ne_top_of_core_ne_bot [IsSimpleGroup G] {T B : Subgroup G}
    (hB : B ∈ localCComponents T)
    (h : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (hcore : pCore 2 B ≠ ⊥) : B ⊔ T ≠ ⊤ := by
  intro hj
  change (B.subgroupOf (B ⊔ T)).IsCComponent at hB
  rw [hj] at hB
  have hs : B.IsSubnormal := by
    have hh := hB.subnormal.trans' IsSubnormal.top
    simpa only [map_subgroupOf_eq_of_le le_top] using hh
  have hne : B ≠ ⊥ := by
    intro hb
    have hh := quotient_card_dvd h
    rw [hb,card_bot] at hh
    norm_num at hh
  have ht : B = ⊤ :=
    (hs.eq_bot_or_top_of_isSimpleGroup inferInstance).resolve_left hne
  let : IsSimpleGroup B := ((MulEquiv.subgroupCongr ht).trans topEquiv).isSimpleGroup
  have hc : pCore 2 B = ⊤ :=
    (inferInstance : (pCore 2 B).Normal).eq_bot_or_eq_top.resolve_left hcore
  have hcard := quotient_card h
  rw [hc] at hcard
  simp at hcard

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
