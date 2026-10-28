module
public import Theory.Mathieu.M22.Properties.LocalA5Placement
public import Theory.Mathieu.M22.Properties.LocalA5Shape

/-!
# Uniqueness of the full-Sylow-normalized A₅ section in M₂₂

Conjugate the full Sylow once for both subgroups. Their intrinsic elementary
cores have order sixteen; the hexad case is excluded, and the same quintet
core determines the same literal natural actor. Injectivity of the native
embedding recovers equality of the original subgroups.

Source: Aschbacher--Smith A.3.14(6) and 5.1.13, printed pp.49,637.
-/

public section
open Subgroup Theory.GroupTheory Sporadic.Mathieu MathieuCode
namespace Sporadic.Mathieu.M22LocalA5Placement

private theorem marked_image (B : Subgroup M22) [Group.IsPerfect B]
    (hn : (M22ChapterH.CompatibleSylow.inner : Subgroup M22) ≤ normalizer (B : Set M22))
    (e : B ⧸ pCore 2 B ≃* alternatingGroup (Fin 5)) :
    B.map m22ToPairStabilizer = M22ChapterH.Quintet.naturalActor.map M22Quintet.Q.subtype := by
  obtain ⟨he,hcard⟩ := M22LocalA5Shape.core_shape_of_normalized _ B hn e
  let := he
  have hs : (B.subgroupOf (B ⊔ (M22ChapterH.CompatibleSylow.inner : Subgroup M22))).IsSubnormal :=
    (normal_subgroupOf_of_le_normalizer (sup_le B.le_normalizer hn)).isSubnormal
  have hc : Nat.card (B.pCoreIn 2) = 16 := by
    rw [pCoreIn,card_map_of_injective B.subtype_injective,hcard]
  have hcore := (marked_core_cases B hs (IsElementaryAbelian.map B.subtype) hc).resolve_left
    (core_ne_hexad_kernel B hs e)
  apply quintet_core_placement B hcore
  have hq : (pCore 2 B).index = 60 := by
    change Nat.card (B ⧸ pCore 2 B) = 60
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num
  rw [← (pCore 2 B).card_mul_index,hcard,hq]

/-- A full Sylow normalizes at most one perfect subgroup with two-core quotient A₅. -/
theorem eq_of_normalized (S : Sylow 2 M22) (B C : Subgroup M22)
    [Group.IsPerfect B] [Group.IsPerfect C]
    (hB : (S : Subgroup M22) ≤ normalizer (B : Set M22))
    (hC : (S : Subgroup M22) ≤ normalizer (C : Set M22))
    (eB : B ⧸ pCore 2 B ≃* alternatingGroup (Fin 5))
    (eC : C ⧸ pCore 2 C ≃* alternatingGroup (Fin 5)) : B = C := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M22 S M22ChapterH.CompatibleSylow.inner
  let a := MulAut.conj g
  have hS : (S : Subgroup M22).map a.toMonoidHom =
      (M22ChapterH.CompatibleSylow.inner : Subgroup M22) := congrArg Sylow.toSubgroup hg
  have step (R : Subgroup M22) [Group.IsPerfect R]
      (hn : (S : Subgroup M22) ≤ normalizer (R : Set M22))
      (e : R ⧸ pCore 2 R ≃* alternatingGroup (Fin 5)) :
      (R.map a.toMonoidHom).map m22ToPairStabilizer =
        M22ChapterH.Quintet.naturalActor.map M22Quintet.Q.subtype := by
    let := Group.IsPerfect.map (H := R) a.toMonoidHom
    let d := a.subgroupMap R
    apply marked_image
    · rw [← hS]
      exact (map_mono hn).trans (R.le_normalizer_map a.toMonoidHom)
    · exact (QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).symm.trans e
  apply map_injective (f := a.toMonoidHom) a.injective
  apply map_injective (f := m22ToPairStabilizer)
    (fun _ _ hh => m22Embedding_injective (congrArg Subtype.val hh))
  exact (step B hB eB).trans (step C hC eC).symm
end Sporadic.Mathieu.M22LocalA5Placement
