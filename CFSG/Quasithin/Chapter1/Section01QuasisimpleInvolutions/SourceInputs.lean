module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Ambient
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.ComponentMarking
public import CFSG.Quasithin.ChapterA.Section02.Statements

/-!
# Source inputs for the quasisimple involution lemma

The original ambient 1.1.5 hypotheses supply the marked involution on each
ordinary component: it fixes a Sylow two-subgroup, its centralizer has
characteristic two, and it inverts the odd core. The component is outside the
specified overgroup and equals its commutator with the original involution.

Theorem A supplies the strongly quasithin central quotient and the full
Theorem C implication supplies its actual model. Applying the full local
quasisimple classifier then proves the component clause of 1.1.5. These
universal earlier implications remain explicit: their producers are
`qt-a02-abc-assembly` and `qt-1-01-quasisimple-involutions`.

Source: Aschbacher–Smith, Lemma 1.1.5, pp.501–503.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1
open QuasisimpleInvolutions
open Chapter15.Section03.Candidates.ComponentStructure
universe u
variable {G : Type u} [Group G] [Finite G] {H M : Subgroup G} {S : Sylow 2 H} {z : G}

theorem Lemma115Hypotheses.component_inputs (h : Lemma115Hypotheses H S M z)
    (D : Subgroup H) (hD : IsComponent H D) :
    ¬ D.map H.subtype ≤ M ∧
      ∃ (α : MulAut D) (P : Sylow 2 D),
        (∀ x : D, ((α x : H) : G) = z * (x : G) * z⁻¹) ∧
        MarkedInvolution α P ∧ D.map H.subtype = ⁅D.map H.subtype, zpowers z⁆ := by
  have hout : ¬ D.map H.subtype ≤ M := by
    intro hd
    have hDM : D ≤ M.subgroupOf H := map_le_iff_le_comap.mp hd
    exact not_isComponent_of_twoCore h.intersection_characteristicTwo _ (hD.subgroupOf hDM)
  let zH : H := ⟨z, h.mem_intersection.1⟩
  have hzH : orderOf zH = 2 := (Subgroup.orderOf_coe zH).symm.trans h.involution
  have hfix : ∀ s ∈ S, s * zH = zH * s := by
    intro s hs
    exact Subtype.ext (h.central s (mem_map_of_mem H.subtype hs))
  have hinv : ∀ x ∈ pPrimeCore 2 H, zH * x * zH⁻¹ = x⁻¹ := by
    intro x hx
    exact Subtype.ext (h.inverts_oddCore x hx)
  obtain ⟨α, P, ha, d, hcomm⟩ := component_marked S zH hzH hfix
    h.intrinsic_centralizer_characteristicTwo hinv D hD
  refine ⟨hout, α, P, fun x => congrArg Subtype.val (ha x), d, ?_⟩
  have hm := congrArg (Subgroup.map H.subtype) hcomm
  rw [map_commutator, MonoidHom.map_zpowers] at hm
  exact hm.symm
end CFSG.Quasithin.Chapter1

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
universe u
variable {L : Type u} [Group L] [Finite L] [IsQuasisimple L] {κ : GroupClass.{u}}

theorem quotient_model (hL : IsSQTK κ L)
    (hA : ChapterA.Section02.TheoremA κ L)
    (hC : ChapterA.Section02.TheoremC κ (L ⧸ center L)) :
    ChapterA.Section02.IsTheoremCModel (L ⧸ center L) := by
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Group.IsPerfect (L ⧸ center L) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple (L ⧸ center L) :=
    IsQuasisimple.of_surjective (QuotientGroup.mk' (center L)) (QuotientGroup.mk'_surjective _)
  have hsemi : ChapterA.Section02.IsSemisimple (L ⧸ center L) := by
    apply top_unique
    apply le_sSup
    exact ⟨IsSubnormal.top, IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm⟩
  exact hC inferInstance (Group.IsPerfect.not_isMulCommutative _)
    (hA.stronglyQuasithin_section hL.stronglyQuasithin hL.isKGroup
      (ChapterA.Section02.IsSectionOf.of_surjective (QuotientGroup.mk' (center L))
        (QuotientGroup.mk'_surjective _)) hsemi)
    (hL.isKGroup.quotient (center L))

variable {G : Type u} [Group G] [Finite G]

private theorem local_sqtk (hG : IsSimpleQTKE κ G) {H : Subgroup G}
    (hH : H ∈ Chapter1.H G) : IsSQTK κ H := by
  have hnorm : H ≤ normalizer (H.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map,
      range_subtype] using (pCore 2 H).le_normalizer_map H.subtype
  have hs := hG.twoLocal_sqtk
    (show IsTwoLocal (normalizer (H.pCoreIn 2 : Set G)) from
      ⟨H.pCoreIn 2, hH, isPGroup_pCoreIn 2 H, rfl⟩)
  exact ⟨hs.stronglyQuasithin.of_injective (inclusion hnorm) (inclusion_injective hnorm),
    hs.isKGroup.of_injective (inclusion hnorm) (inclusion_injective hnorm)⟩
end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions


namespace CFSG.Quasithin.Chapter1
open Subgroup Theory.GroupTheory QuasisimpleInvolutions ChapterA.Section02
open Chapter15.Section03.Candidates.ComponentStructure
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

theorem lemma_1_1_5_three_of_local_classification
    (hG : IsSimpleQTKE κ G)
    (hABC : ∀ (X : Type u) [Group X] [Finite X], TheoremsABC κ X)
    (hclass : ∀ (L : Type u) [Group L] [Finite L] [IsQuasisimple L]
      (α : MulAut L) (P : Sylow 2 L), MarkedInvolution α P →
        IsTheoremCModel (L ⧸ center L) → ModelAction115 L α)
    (H : Subgroup G) (S : Sylow 2 H) (M : Subgroup G) (z : G)
    (h : Lemma115Hypotheses H S M z) (D : Subgroup H) (hD : IsComponent H D) :
    D.map H.subtype = ⁅D.map H.subtype, zpowers z⁆ ∧
      ¬ D.map H.subtype ≤ M ∧ HasModelAction115 D z := by
  let : IsQuasisimple D := hD.2
  obtain ⟨hout, α, P, ha, d, hc⟩ := h.component_inputs D hD
  have hsqtk : IsSQTK κ D := (local_sqtk hG h.mem_H).subgroup D
  have hm : IsTheoremCModel (D ⧸ center D) :=
    quotient_model hsqtk (hABC D).1 (hABC (D ⧸ center D)).2.2
  exact ⟨hc, hout, α, ha, hclass D α P d hm⟩
end CFSG.Quasithin.Chapter1
