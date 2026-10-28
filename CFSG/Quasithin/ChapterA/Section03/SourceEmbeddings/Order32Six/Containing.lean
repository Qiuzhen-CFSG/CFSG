module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.NoncentralOddCore
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuasisimpleContaining
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.EvenCharacteristic

/-!
# Actual containing models of an order-32 alternating-six local section

The proved noncentral-Fitting branch of A.3.12 supplies one of its last
two embeddings. The order-32 A₆ sieve excludes both, so the original
containing C-component is quasisimple. The genuine A.3.6 theorem then
supplies its simple carrier or central three-cover. Restriction preserves
the literal intersection with the original Sylow and its normalization.

This reduces the original source problem to its actual containing models;
it does not assert their proper local-embedding classification.
Source: Aschbacher–Smith A.3.6 and A.3.12, pp.43–48, and 8.2.13,
pp.722–723, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six
open Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original source hypotheses rule out the noncentral-Fitting branch
using its proved embedding producer, with no catalogue callback. -/
theorem fitting_le_center {𝒦 : GroupClass.{u}}
    (hG : IsSQTK 𝒦 G) (hO : pCore 2 G = ⊥)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B < K)
    (hcore : Nat.card (pCore 2 B) = 32)
    (hA6 : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))) :
    fittingSubgroup K ≤ center K := by
  by_contra hn
  exact not_a312_embedding hBK hcore hA6
    (embedding_of_noncentral_fitting hG hO T hB hK hBK.le hn)

/-- The supplied containing C-component is quasisimple. -/
theorem containing_quasisimple {𝒦 : GroupClass.{u}}
    (hG : IsSQTK 𝒦 G) (hO : pCore 2 G = ⊥)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B < K)
    (hcore : Nat.card (pCore 2 B) = 32)
    (hA6 : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))) :
    IsQuasisimple K := by
  have hf := fitting_le_center hG hO T hB hK hBK hcore hA6
  have hs : solvableRadical K = center K := by
    apply le_antisymm (solvableRadical_le_center_of_fitting_le_center hf)
    exact le_solvableRadical (center K) inferInstance
      (Group.isSolvable_of_comm (fun a b => Subtype.ext
        (mem_center_iff.mp a.property b).symm))
  let := hK.perfect
  let := hK.isSimpleGroup_quotient_solvableRadical
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hs).symm.isSimpleGroup⟩

/-- The genuine A.3.6 carrier catalogue on the original containing component. -/
theorem containing_models_knownSimple
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B < K)
    (hcore : Nat.card (pCore 2 B) = 32)
    (hA6 : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))) :
    IsQuasisimple K ∧ ((IsSimpleGroup K ∧ TheoremCModel K) ∨
      (Nonempty (center K ≃* Multiplicative (ZMod 3)) ∧ ThreeCoverModel K)) := by
  let hq := containing_quasisimple hG hO T hB hK hBK hcore hA6
  let := hq
  exact ⟨hq, quasisimple_containing_component_models_knownSimple hG hO hK⟩

/-- The exact original Sylow intersection acts on the same local subgroup;
the order and full A₆ quotient survive this restriction without any source
classification premise. -/
theorem source_sylow_restriction
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B < K)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hcore : Nat.card (pCore 2 B) = 32)
    (hA6 : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))) :
    ∃ S : Sylow 2 K, (S : Subgroup K) = (T : Subgroup G).subgroupOf K ∧
      B.subgroupOf K ∈ localCComponents S ∧
      (S : Subgroup K) ≤ normalizer (B.subgroupOf K : Set K) ∧
      B.subgroupOf K ≠ ⊤ ∧ Nat.card (pCore 2 (B.subgroupOf K)) = 32 ∧
      Nonempty (((B.subgroupOf K) ⧸ pCore 2 (B.subgroupOf K)) ≃*
        alternatingGroup (Fin 6)) := by
  obtain ⟨S, hS, hl, hn⟩ := exists_local_sylow_normalizing T hB hK.subnormal hBK.le hTB
  let e := subgroupOfEquivOfLe hBK.le
  refine ⟨S, hS, hl, hn, ?_, ?_, ?_⟩
  · intro he
    exact hBK.not_ge (subgroupOf_eq_top.mp he)
  · calc
      Nat.card (pCore 2 (B.subgroupOf K)) =
          Nat.card ((pCore 2 (B.subgroupOf K)).map e.toMonoidHom) :=
        (card_map_of_injective (f := e.toMonoidHom) e.injective).symm
      _ = 32 := by rw [pCore_map_iso 2 e, hcore]
  · obtain ⟨a⟩ := hA6
    exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans a⟩

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six
