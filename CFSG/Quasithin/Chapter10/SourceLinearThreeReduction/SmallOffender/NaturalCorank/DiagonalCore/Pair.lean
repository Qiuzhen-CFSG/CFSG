module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Contracts
public import CFSG.Quasithin.Chapter10.SourceNonnormalPairAction
public import Theory.GroupTheory.TwoFixedLinesIrreducible
public import Theory.GroupTheory.DisjointCommutingProduct
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Inputs

/-!
# The natural pair before the weak-closure bound

The natural geometry and a specified Sylow exchanger give the two moved
factors and their product. Their intersection lies in the full fixed part.
Point-centralizer control also bounds the kernel on the diagonal conjugate
span. The pair record omits both later numerical conclusions, w=2 and n(H)=2.
It is constructed from the earlier geometry in `Source.diagonalCoreAt`.

These proofs adapt `SourceLinearThreeReplacement/Geometry/Pair.lean` to
its actual earlier hypotheses without changing the natural pair API.
Source: Aschbacher--Smith 10.2.10--11, printed pp.753--754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)
/-- The original natural pair before the numerical conclusions of 10.2.12--13.
Every field is supplied by the earlier natural geometry and point control. -/
structure SourceLinearThreePair {L : Subgroup G}
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) where
  exchange : G
  exchange_mem : exchange ∈ T
  exchange_moves : exchange ∉ normalizer (L : Set G)
  full_eq_local : D.fullModule = D.moduleSubgroup
  generated : D.fullModule = ⁅D.fullModule,L⁆ ⊔
    (⁅D.fullModule,L⁆).map (MulAut.conj exchange).toMonoidHom
  crossed : (⁅D.fullModule,L⁆).map (MulAut.conj exchange).toMonoidHom ≤
    centralizer (L : Set G)
  quotient : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
  natural : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
    (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
    ((Representation.specialLinearNatural 3).comp
      (quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))
  pointCentralizers : ∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 →
    centralizer ({v} : Set G) ≤ D.maximalLocal


end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier
-- Adapted from Geometry/Pair.lean.
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier
open Chapter3.Section02
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  (s : SourceLinearThreePair T D)

include s

/-- The specified exchange witnesses the original nonnormal case. -/
theorem pair_nonnormal : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) :=
  fun h => s.exchange_moves (h s.exchange_mem)

/-- The first moved factor lies in the original full module. -/
theorem pair_moved_le : ⁅D.fullModule,L⁆ ≤ D.fullModule := by
  exact le_sup_left.trans_eq s.generated.symm

/-- The exchanged moved factor lies in the same full module. -/
theorem pair_partner_le :
    (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom ≤ D.fullModule := by
  exact le_sup_right.trans_eq s.generated.symm

/-- The whole original maximal local group permutes the two moved factors. -/
theorem pair_moved_pair (g : G) (hg : g ∈ D.maximalLocal) :
    (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⁅D.fullModule,L⁆ ∨
    (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom =
      (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom := by
  have hV (m : G) (hm : m ∈ D.maximalLocal) :
      D.fullModule.map (MulAut.conj m).toMonoidHom = D.fullModule :=
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hm)
  rw [map_commutator, hV g hg, map_commutator,
    hV s.exchange (le_normalizer_componentOrbit L T s.exchange_mem)]
  rcases source_nonnormal_maximal_pair D (pair_nonnormal s)
      s.exchange_mem s.exchange_moves g hg with h | h
  · exact Or.inl (congrArg (fun A : Subgroup G => ⁅D.fullModule,A⁆) h)
  · exact Or.inr (congrArg (fun A : Subgroup G => ⁅D.fullModule,A⁆) h)

private theorem partner_pair (g : G) (hg : g ∈ D.maximalLocal) :
    ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom).map
        (MulAut.conj g).toMonoidHom = ⁅D.fullModule,L⁆ ∨
    ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom).map
        (MulAut.conj g).toMonoidHom =
      (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom := by
  have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj s.exchange).toMonoidHom =
      (MulAut.conj (g * s.exchange)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [map_map, he]
  exact pair_moved_pair s _
    (D.maximalLocal.mul_mem hg (le_normalizer_componentOrbit L T s.exchange_mem))

/-- The intersection of the exchanged factors belongs to the full fixed part. -/
theorem pair_pair_intersection_fixed :
    ⁅D.fullModule,L⁆ ⊓ (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom ≤
      D.fullModule ⊓ centralizer (localOrbit T L : Set G) := by
  let A := ⁅D.fullModule,L⁆
  let B := A.map (MulAut.conj s.exchange).toMonoidHom
  let I := A ⊓ B
  have hn : D.maximalLocal ≤ normalizer (I : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (A ⊓ B).map (MulAut.conj g).toMonoidHom = A ⊓ B
    rw [map_inf _ _ _ (MulAut.conj g).injective]
    rcases pair_moved_pair s g hg with ha | ha <;>
      rcases partner_pair s g hg with hb | hb
    · have he : A = B := map_injective (MulAut.conj g).injective (ha.trans hb.symm)
      change A.map _ = A at ha
      change B.map _ = A at hb
      simp only [hb, he]
    · rw [ha, hb]
    · rw [ha, hb, inf_comm]
    · have he : A = B := map_injective (MulAut.conj g).injective (ha.trans hb.symm)
      change A.map _ = B at ha
      change B.map _ = B at hb
      simp only [hb, he]
  have hLC : L ≤ centralizer (I : Set G) :=
    le_centralizer_iff.mp (inf_le_right.trans s.crossed)
  have hTC : (T : Subgroup G) ≤ normalizer (centralizer (I : Set G) : Set G) :=
    ((le_normalizer_componentOrbit L T).trans hn).trans
      (normalizer_le_normalizer_centralizer _)
  exact le_inf (inf_le_left.trans (pair_moved_le s))
    (le_centralizer_iff.mpr (iSup_conjugates_le_of_le_normalizer _ _ _ hLC hTC))

/-- Vanishing of the full fixed part gives an internal direct product. -/
theorem pair_pair_disjoint
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    Disjoint ⁅D.fullModule,L⁆
      ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom) :=
  disjoint_iff.mpr (bot_unique ((pair_pair_intersection_fixed s).trans_eq hz))

/-- The literal stabilizer N_T(L) preserves the first moved factor. -/
theorem pair_stabilizer_normalizes_moved :
    (T : Subgroup G) ⊓ normalizer (L : Set G) ≤
      normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator, s.full_eq_local,
    mem_normalizer_iff_map_conj_eq.mp (D.sylow_normalizes_module hg.1),
    mem_normalizer_iff_map_conj_eq.mp hg.2]

/-- The same stabilizer preserves the exchanged factor. -/
theorem pair_stabilizer_normalizes_partner :
    (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer
      (((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom) : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  rcases partner_pair s g (le_normalizer_componentOrbit L T hg.1) with h | h
  · have ha := mem_normalizer_iff_map_conj_eq.mp (pair_stabilizer_normalizes_moved s hg)
    have he := map_injective (MulAut.conj g).injective (h.trans ha.symm)
    exact h.trans he.symm
  · exact h

/-- The required V_z-centralizer bound follows from the first fixed vector
and the pair's original point-centralizer control. -/
theorem centralizerModule_centralizer_le {a b : G}
    (ha : a ∈ ⁅D.fullModule,L⁆) (hne : a ≠ 1) :
    centralizer ({a*b} : Set G) ⊓ centralizer (centralizerModule a b : Set G) ≤ D.maximalLocal := by
  apply inf_le_right.trans
  apply le_trans (centralizer_le ?_) (s.pointCentralizers a ha hne)
  exact Set.singleton_subset_iff.mpr (le_conjugateSpanBy (zpowers a ⊔ zpowers b)
    (centralizer ({a*b} : Set G)) (mem_sup_left (mem_zpowers a)))

/-- The whole full module lies in the centralizer of each such product. -/
theorem pair_full_le_diagonal_centralizer {a b : G}
    (ha : a ∈ ⁅D.fullModule,L⁆)
    (hb : b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom) :
    D.fullModule ≤ centralizer ({a*b} : Set G) := by
  let : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
  have hz : a*b ∈ D.fullModule :=
    D.fullModule.mul_mem (pair_moved_le s ha) (pair_partner_le s hb)
  intro x hx
  apply mem_centralizer_singleton_iff.mpr
  exact congrArg Subtype.val (mul_comm (⟨x,hx⟩ : D.fullModule) ⟨a*b,hz⟩)

/-- The actual E-conjugate span lies in its acting centralizer. -/
theorem pair_centralizerModule_le {a b : G}
    (ha : a ∈ ⁅D.fullModule,L⁆)
    (hb : b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom) :
    centralizerModule a b ≤ centralizer ({a*b} : Set G) := by
  apply conjugateSpanBy_le_self
  have hv := pair_full_le_diagonal_centralizer s ha hb
  exact sup_le (zpowers_le.mpr (hv (pair_moved_le s ha)))
    (zpowers_le.mpr (hv (pair_partner_le s hb)))

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier
