module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Preparation
public import CFSG.Quasithin.ChapterA.Section02.OddModelTwoRank
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Bender
public import Theory.GroupTheory.PerfectMovedElementaryRank
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# Carrier reduction for the non-A₅ quasisimple point inspection

The literal image of the moved subgroup is nonzero and fully moved by the
perfect local component. Consequently the containing central quotient has
two-rank at least three. This excludes every odd-characteristic carrier and
all alternating degrees below eight. The actual A₈--PSL₄(2) equivalence
puts degree eight in the higher binary-linear branch. The Bender branch
is excluded by the full-Sylow local embedding and properness, without
assuming that the smaller subgroup is quasisimple.

The surviving binary-linear and sporadic rows still require their embedding
and module inspections. No irreducibility or module degree is assumed here.
Source: Aschbacher--Smith, A.3.12 and the quasisimple part of 10.2.9,
printed pp.47--48,750--751.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
open Chapter3.Section02 ChapterA.Section03
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c

/-- Full movement of the actual elementary image forces two-rank at least three. -/
theorem center_quotient_rank [Group.IsPerfect I] :
    3 ≤ primeRank 2 (I ⧸ center I) := by
  obtain ⟨S,_,hB,_,_,_,_,hE,hEB,hne,hm⟩ := center_quotient_data D c
  let q := QuotientGroup.mk' (center I)
  let B := (L.subgroupOf I).map q
  let E := ((⁅D.fullModule,L⁆).subgroupOf I).map q
  let := hB.perfect
  let e := subgroupOfEquivOfLe
    (show B ≤ B ⊔ (S.mapSurjective (QuotientGroup.mk'_surjective (center I)) :
      Subgroup (I ⧸ center I)) from le_sup_left)
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  let : IsElementaryAbelian 2 E := hE
  exact three_le_primeRank_of_perfect_moved_elementary B E hEB hne hm.symm

/-- No odd-characteristic row of the full Theorem C catalogue can occur. -/
theorem not_odd [Group.IsPerfect I] :
    ¬ ChapterA.Section02.IsTheoremCOddModel (I ⧸ center I) := by
  intro hm
  have hl := center_quotient_rank D c
  have hu := hm.twoRank_le_two
  omega

/-- The actual proper local component excludes every Bender carrier. -/
theorem not_bender [IsQuasisimple I] :
    ¬ ClassificationModels.IsBenderModel (I ⧸ center I) := by
  intro hm
  let : IsSimpleGroup (I ⧸ center I) := IsQuasisimple.simple
  let : IsQuasisimple (I ⧸ center I) := IsQuasisimple.of_surjective
    (QuotientGroup.mk' (center I)) (QuotientGroup.mk'_surjective (center I))
  obtain ⟨S,_,hB,_,_,hproper,_⟩ := center_quotient_data D c
  have ht : (⊤ : Subgroup (I ⧸ center I)).IsCComponent :=
    (show IsComponent (I ⧸ center I) ⊤ from
      ⟨.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  exact hproper (SourceEmbeddings.eq_of_bender_containing_component
    (S.mapSurjective (QuotientGroup.mk'_surjective (center I))) hB ht le_top
    (hm.of_mulEquiv topEquiv))

omit D c in
private theorem small_alternating_rank {n : ℕ} (hn : n ≤ 7) :
    primeRank 2 (alternatingGroup (Fin n)) ≤ 2 := by
  classical
  let j : Fin n ↪ Fin 7 := Fin.castLEEmb hn
  let f : alternatingGroup (Fin n) →* alternatingGroup (Fin 7) :=
    ((Equiv.Perm.viaEmbeddingHom j).comp (alternatingGroup (Fin n)).subtype).codRestrict _
      (fun a => by
        change Equiv.Perm.sign ((a : Equiv.Perm (Fin n)).viaEmbedding j) = 1
        rw [Equiv.Perm.viaEmbedding, Equiv.Perm.sign_extendDomain]
        exact a.property)
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (Equiv.Perm.viaEmbeddingHom_injective j (congrArg Subtype.val hab))
  exact (Theory.GroupTheory.primeRank_le_of_injective 2 f hf).trans
    Representation.AlternatingSevenConjugatePair.ElementaryGeometry.primeRank_alternating.le

/-- The alternating catalogue retains only A₈, without using an A₅ degree bound. -/
theorem alternating_degree [Group.IsPerfect I] {n : ℕ} (hn : n ≤ 8)
    (e : (I ⧸ center I) ≃* alternatingGroup (Fin n)) : n = 8 := by
  have hl := center_quotient_rank D c
  by_contra hne
  have hu := small_alternating_rank (show n ≤ 7 by omega)
  rw [← primeRank_equiv 2 e] at hu
  omega

/-- Every complementary carrier is genuinely higher binary-linear or sporadic.
The alternating-eight alternative is transported through its actual isomorphism. -/
theorem binary_or_sporadic [IsQuasisimple I]
    (hm : ChapterA.Section02.IsTheoremCModel (I ⧸ center I))
    (hr : ¬ ∃ n, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) n) :
    (∃ n, (n = 4 ∨ n = 5) ∧ ClassicalGroup.IsPSL (I ⧸ center I) n 2) ∨
      ChapterA.Section02.IsTheoremCSporadicModel (I ⧸ center I) := by
  cases hm with
  | alternating n hn he =>
    obtain ⟨e⟩ := he
    have hn8 := alternating_degree D c hn e
    subst n
    exact .inl ⟨4, Or.inl rfl, ZMod 2, inferInstance, inferInstance, by simp,
      ⟨e.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two⟩⟩
  | odd hm => exact (not_odd D c hm).elim
  | bender hm => exact (not_bender D c hm).elim
  | rank_two n hm => exact (hr ⟨n,hm⟩).elim
  | linear_binary n hn hm => exact .inl ⟨n,hn,hm⟩
  | sporadic hm => exact .inr hm

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
