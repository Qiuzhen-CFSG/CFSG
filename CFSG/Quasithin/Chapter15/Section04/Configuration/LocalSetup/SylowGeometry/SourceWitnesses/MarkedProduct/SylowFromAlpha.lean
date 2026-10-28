module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.MarkedProduct.QuotientCoordinates
public import CFSG.Quasithin.ChapterB.Section02.Baumann.Sylow
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.SylowNormalizedSupIndex

/-!
# The source Sylow supplement from Baumann's alpha decomposition

The actual X-action has kernel O₂(X), which lies in T and centralizes W.
B.2.18's original alpha decomposition therefore puts this core in S=Baum(T).
The odd core index nine then gives the original Sylow witness in XS and puts
O₂(XS) in S. This uses only the actual alpha output of the earlier Baumann
argument; no stronger fixed-summand or omega placement is required.

Source: Aschbacher–Smith, B.2.18 and 15.4.12(4), pp.81 and1160.
-/

@[expose] public section
open Subgroup Stellmacher
open OrthogonalFourBinary.TerminalLines
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct
open FamilySource FamilySource.ModuleStructure
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M X : Subgroup G}

theorem source_member_core_in_sylow_centralizer (h : Input K T M X 2) :
    X.pCoreIn 2 ≤ (T : Subgroup G) ⊓ centralizer (movedModule (T : Subgroup G) M X : Set G) := by
  have hn : M ≤ normalizer (X : Set G) := (normal_subgroupOf_iff_le_normalizer h.member_le).mp h.normal
  have hcoreM : X.pCoreIn 2 ≤ M.pCoreIn 2 := pCoreIn_mono_of_normalizes h.member_le hn
  have hcoreT : M.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le h.sylow_le] using
      pCoreIn_le_sylow M (T.subtype h.sylow_le)
  refine le_inf (hcoreM.trans hcoreT) ?_
  obtain ⟨d⟩ := exists_sourceAction h
  rintro c ⟨x,hx,rfl⟩ w hw
  have he := d.intertwines (inclusion d.member_le x) ⟨w,hw⟩
  have hk : d.actor (inclusion d.member_le x) = 1 := (d.member_kernel h).ge hx
  rw [hk, map_one] at he
  change (d.coordinates.symm (d.coordinates ⟨w,hw⟩) : G) = (x : G)*w*(x : G)⁻¹ at he
  rw [d.coordinates.symm_apply_apply] at he
  exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm

/-- The exact alpha output of B.2.18 gives the original XS Sylow witness.
No fixed-summand or omega placement for alpha is required. -/
theorem source_sylow_of_alpha_decomposition (h : Input K T M X 2)
    (ha : ChapterB.thompsonAlpha (T : Subgroup G) =
      (ChapterB.thompsonAlpha (T : Subgroup G) ⊓ centralizer (X : Set G)) ⊔
        (movedModule (T : Subgroup G) M X ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G))) :
    X.pCoreIn 2 ≤ ChapterB.baumann (T : Subgroup G) ∧
      (∃ P : Sylow 2 (X ⊔ ChapterB.baumann (T : Subgroup G) : Subgroup G),
        (P : Subgroup (X ⊔ ChapterB.baumann (T : Subgroup G) : Subgroup G)).map
          (X ⊔ ChapterB.baumann (T : Subgroup G) : Subgroup G).subtype = ChapterB.baumann (T : Subgroup G)) ∧
      (X ⊔ ChapterB.baumann (T : Subgroup G)).pCoreIn 2 ≤ ChapterB.baumann (T : Subgroup G) := by
  have hc := ChapterB.BaumannArgument.core_le_baumann_of_decomposition
    (movedModule (T : Subgroup G) M X) (T : Subgroup G) X (source_member_core_in_sylow_centralizer h) ha
  have hodd : ¬ 2 ∣ (pCore 2 X).index := by
    change ¬ 2 ∣ Nat.card (X ⧸ pCore 2 X)
    rw [source_member_quotient_card h]
    decide
  obtain ⟨P,hP⟩ := IsPGroup.exists_sylow_sup_of_coprime_index X
    (ChapterB.baumann (T : Subgroup G)) (T.isPGroup'.to_le inf_le_left)
    (inf_le_left.trans (YFamily.invariant h.member)) (pCore 2 X) hodd hc
  exact ⟨hc,⟨P,hP⟩,(pCoreIn_le_sylow _ P).trans_eq hP⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct
