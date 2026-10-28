module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Comparison.Action
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalModels.ChosenGeometry
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.QuadraticBound
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.FinalAssembly
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ExternalComponentAction.CoreImage

/-!
# The original edge and component at the critical endpoint

Conjugation carries the actual component, its relative normality, two-perfectness
and quasisimple star image to the terminal vertex. The Sylow supplement identifies
the original edge with L1 T. The natural module has order sixteen, giving the
index-two seed. H outside M makes that edge proper. Its core containment and
seed commutator use the original F.9 data and the unchanged flag.

Source: Aschbacher--Smith, Notation 13.2.1 and 13.8.4,18, printed pp.877,947,953.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Comparison
open ComponentSieve.FieldComponents.LinearThree.Geometry.ExternalComponentAction
variable {G : Type*} [Group G] [Finite G]

theorem component_conjugate (H K : Subgroup G) (hKH : K ≤ H)
    (hN : (K.subgroupOf H).Normal) [Group.IsPerfect (K.subgroupOf H)]
    (hqs : IsQuasisimple (Source.starImage H K)) (e : G ≃* G) :
    ((K.map e.toMonoidHom).subgroupOf (H.map e.toMonoidHom)).Normal ∧
    pResidual 2 ((K.map e.toMonoidHom).subgroupOf (H.map e.toMonoidHom)) = ⊤ ∧
    IsQuasisimple (Source.starImage (H.map e.toMonoidHom) (K.map e.toMonoidHom)) := by
  have hN' : ((K.map e.toMonoidHom).subgroupOf (H.map e.toMonoidHom)).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer (map_mono hKH)).mpr
    rw [←map_equiv_normalizer_eq]
    exact map_mono ((normal_subgroupOf_iff_le_normalizer hKH).mp hN)
  let ec := (subgroupOfEquivOfLe hKH).trans ((e.subgroupMap K).trans
    (subgroupOfEquivOfLe (map_mono (f:=e.toMonoidHom) hKH)).symm)
  let : Group.IsPerfect ((K.map e.toMonoidHom).subgroupOf (H.map e.toMonoidHom)) :=
    Group.IsPerfect.ofSurjective (f:=ec.toMonoidHom) ec.surjective
  have hr : pResidual 2 ((K.map e.toMonoidHom).subgroupOf (H.map e.toMonoidHom)) = ⊤ := by
    apply (pResidual_eq_top_iff 2 _).mpr
    intro N hN hp
    let := hN
    by_contra hn
    let : Nontrivial (((K.map e.toMonoidHom).subgroupOf (H.map e.toMonoidHom)) ⧸ N) :=
      QuotientGroup.nontrivial_iff.mpr hn
    let : Group.IsPerfect (((K.map e.toMonoidHom).subgroupOf (H.map e.toMonoidHom)) ⧸ N) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    exact Group.IsPerfect.not_isNilpotent _ hp.isNilpotent
  let eq := QuotientGroup.congr (pCore 2 K) (pCore 2 (K.map e.toMonoidHom))
    (e.subgroupMap K) (pCore_map_iso 2 (e.subgroupMap K))
  let es := (quotientStarEquiv H K hKH hN.isSubnormal).symm.trans
    (eq.trans (quotientStarEquiv _ _ (map_mono hKH) hN'.isSubnormal))
  exact ⟨hN',hr,IsQuasisimple.of_mulEquiv es (hG:=hqs)⟩
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Comparison
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Comparison
open CriticalGeometry CriticalGeometry.SectionActions
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)

include d hF9

theorem local_edge : (L ⊔ (T:Subgroup G)) ⊓ H = one L T V₁ ⊔ (T:Subgroup G) := by
  let P := parabolic L (T:Subgroup G) V₁
  have hTP : (T:Subgroup G) ≤ P := le_inf le_sup_right d.line_stable
  have he : (L ⊔ (T:Subgroup G)) ⊓ H = P := by
    calc
      _ = (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T:Subgroup G) := hF9.LT_inf_H_eq
      _ = P := hF9.normalizer_point_LT_eq.symm
  have hs := congrArg (fun A : Subgroup P => A.map P.subtype)
    (pResidual_sup_sylow_eq_top (T.subtype hTP))
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype,
    Sylow.coe_subtype,map_subgroupOf_eq_of_le hTP] at hs
  exact he.trans hs.symm

omit hF9 in
theorem local_seed_index : V₃.relIndex V = 2 := by
  have hc := Nat.card_congr d.coordinate.toEquiv
  change Nat.card V = Nat.card (BinaryPermutation.natural (Fin 6)) at hc
  rw [Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=BinaryPermutation.natural (Fin 6)),show Nat.card (ZMod 2) = 2 from by simp,
    BinaryPermutation.finrank_natural_even (Fin 6) (by decide),Fintype.card_fin] at hc
  have hi := Subgroup.card_mul_index (V₃.subgroupOf V)
  rw [Nat.card_congr (subgroupOfEquivOfLe d.seed_le).toEquiv,d.seed_card] at hi
  change 8 * V₃.relIndex V = Nat.card V at hi
  norm_num at hc
  omega

theorem local_proper_edge (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (c : CriticalPair L (T:Subgroup G) H V) :
    edgeGroup L (T:Subgroup G) H c.gamma c.previous < vertexGroup L (T:Subgroup G) H c.gamma := by
  have he : (L ⊔ (T:Subgroup G)) ⊓ H < H := by
    refine lt_of_le_of_ne inf_le_right ?_
    intro heq
    apply hH.2.2
    have hm : L ⊔ (T:Subgroup G) ≤ M := by
      rw [d.local_normalizer]
      exact sup_le L.le_normalizer d.normalizes_L
    exact (heq.symm.le.trans inf_le_left).trans hm
  rw [c.edgeGroup_eq (one L T V₁) (local_edge d hF9),c.vertexGroup_gamma]
  apply (map_lt_map_iff_of_injective (MulAut.conj (c.gb:G)).injective).mpr
  rwa [local_edge d hF9] at he

theorem local_core_le_edge (c : CriticalPair L (T:Subgroup G) H V) :
    c.Qgamma ≤ edgeGroup L (T:Subgroup G) H c.gamma c.previous := by
  rw [c.edgeGroup_eq (one L T V₁) (local_edge d hF9)]
  exact map_mono (hF9.QH_le_T.trans le_sup_right)

theorem local_seed_commutator
    (hnoncentral : ¬ ⁅Source.VH H V,H⁆ ≤ Source.UH H V₃)
    (c : CriticalPair L (T:Subgroup G) H V) :
    ⁅one L T V₁ ⊔ (T:Subgroup G),V⁆ ≤ Source.UH H V₃ := by
  let : IsElementaryAbelian 2 V := hF9.elementary
  have hh := c.edge_commutator_le_of_flag V₃ d.seed_le (local_seed_index d)
    hnoncentral (inf_le_left.trans d.normalizes_V)
  rw [c.edgeGroup_eq _ (local_edge d hF9),←map_commutator] at hh
  exact (map_le_map_iff_of_injective (MulAut.conj (c.gb:G)).injective).mp hh

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Comparison
