module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.Statement
public import CFSG.Quasithin.ChapterB.Section01.Restriction
public import Theory.Representation.BinaryOffender.IrreducibleMovedGeneration
public import Theory.Representation.Quotient

/-!
# The literal local seed and its equality with the moved space

Normality of O₂(LA) inside LA and the relation L=[L,A] construct the
LA-action on U=[C_V(O₂(LA)),L]. If U supplements C_V(A), the action on V/U
kills A and therefore kills [L,A]=L. This proves U=[V,L]. The proved
B.1.5(2)/B.7.1(2) restriction theorem supplies that supplement and a trivial
offender kernel when the actual image rank equals its fixed codimension.

No ambient G-action on U, representation classification or U=W equality is
assumed in this construction. The final equality theorem is used after the
local representation comparison in each non-IV branch.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.9, printed p.107, first paragraph of the proof.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
open QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem seedSpace_stable {A L : Subgroup G} (hLA : ⁅L,A⁆ = L) :
    L ⊔ A ≤ subspaceStabilizer ρ (naturalSeedSpace ρ L A) := by
  have hN : L ⊔ A ≤ normalizer (L : Set G) :=
    sup_le L.le_normalizer (le_normalizer_iff_commutator_le_left.mpr hLA.le)
  have hQ : L ⊔ A ≤ normalizer (localTwoCore L A : Set G) := by
    simpa only [localTwoCore, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (pCore 2 ↥(L ⊔ A)).le_normalizer_map (L ⊔ A).subtype
  exact subspaceCommutator_invariant_normalizer ρ (fixedSpace_invariant_normalizer ρ hQ) hN

/-- The seed has the LA-action justified before U=W. -/
noncomputable def seedSubrepresentation {A L : Subgroup G} (hLA : ⁅L,A⁆ = L) :
    Subrepresentation (ρ.comp (L ⊔ A).subtype) :=
  ⟨naturalSeedSpace ρ L A, fun g _ hv => (seedSpace_stable ρ hLA g.property _).2 hv⟩

theorem seedSpace_le_moved (A L : Subgroup G) : naturalSeedSpace ρ L A ≤ moved ρ L :=
  subspaceCommutator_mono_left ρ le_top L

/-- If an LA-invariant subspace supplements C_V(A), the quotient action
kills A and hence [L,A]=L, so it contains all of [V,L]. -/
theorem moved_le_of_supplement {A L : Subgroup G} (hLA : ⁅L,A⁆ = L)
    (U : Subrepresentation (ρ.comp (L ⊔ A).subtype))
    (hs : U.toSubmodule ⊔ fixedSpace ρ A = ⊤) : moved ρ L ≤ U.toSubmodule := by
  let H := L ⊔ A
  let L₀ := L.subgroupOf H
  let A₀ := A.subgroupOf H
  have hcomm : ⁅L₀,A₀⁆ = L₀ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right, hLA]
  have hAk : A₀ ≤ U.quotientRepresentation.ker := by
    intro a ha
    apply MonoidHom.mem_ker.mpr
    apply LinearMap.ext
    intro q
    obtain ⟨v,rfl⟩ := U.toSubmodule.mkQ_surjective q
    obtain ⟨w,hw,c,hc,rfl⟩ := Submodule.mem_sup.mp (hs ▸ (Submodule.mem_top : v ∈ ⊤))
    change U.toSubmodule.mkQ (ρ a (w+c)) = U.toSubmodule.mkQ (w+c)
    have hca : ρ a c = c := hc ⟨a,ha⟩
    rw [map_add, hca, map_add, map_add]
    have hz : U.toSubmodule.mkQ w = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hw
    have haz : U.toSubmodule.mkQ (ρ a w) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (U.apply_mem_toSubmodule a hw)
    rw [hz,haz]
  have hLk : L₀ ≤ U.quotientRepresentation.ker := by
    rw [← hcomm]
    exact (commutator_mono le_rfl hAk).trans (commutator_le_right _ _)
  apply Submodule.span_le.mpr
  rintro _ ⟨l,hl,v,_,rfl⟩
  let l₀ : H := ⟨l, (le_sup_left : L ≤ H) hl⟩
  have he := LinearMap.congr_fun (MonoidHom.mem_ker.mp (hLk (show l₀ ∈ L₀ from hl)))
    (U.toSubmodule.mkQ v)
  change U.toSubmodule.mkQ (ρ l v) = U.toSubmodule.mkQ v at he
  apply (Submodule.Quotient.mk_eq_zero _).mp
  change U.toSubmodule.mkQ (ρ l v - v) = 0
  rw [map_sub,he,sub_self]

/-- This is the U=W inference in each non-IV branch of B.5.9. -/
theorem seedSpace_eq_moved_of_supplement {A L : Subgroup G} (hLA : ⁅L,A⁆ = L)
    (hs : naturalSeedSpace ρ L A ⊔ fixedSpace ρ A = ⊤) :
    naturalSeedSpace ρ L A = moved ρ L :=
  le_antisymm (seedSpace_le_moved ρ A L)
    (moved_le_of_supplement ρ hLA (seedSubrepresentation ρ hLA) hs)

/-- B.1.5(2) supplies both the supplement and U=W at equality of the
actual offender-image rank and its fixed codimension. -/
theorem seed_equality_of_image_rank [Finite G] [Module.Finite (ZMod 2) V]
    (hf : Function.Injective ρ) {A L : Subgroup G}
    (hA : IsMinimalBestOffender ρ A) (hLA : ⁅L,A⁆ = L)
    (hm : subspaceCommutator ρ (naturalSeedSpace ρ L A) A ≠ ⊥)
    (he : rank (restrictedSubgroup ρ (naturalSeedSpace ρ L A) A) =
      fixedCodim (subspaceImageRepresentation ρ (naturalSeedSpace ρ L A))
        (restrictedSubgroup ρ (naturalSeedSpace ρ L A) A)) :
    subspaceKernel ρ (naturalSeedSpace ρ L A) A = ⊥ ∧
      naturalSeedSpace ρ L A = moved ρ L ∧ moved ρ L ⊔ fixedSpace ρ A = ⊤ := by
  have hstab : A ≤ subspaceStabilizer ρ (naturalSeedSpace ρ L A) :=
    le_sup_right.trans (seedSpace_stable ρ hLA)
  obtain ⟨hk,hs⟩ := (ChapterB.source_lemma_B_7_1_2 ρ (naturalSeedSpace ρ L A)
    hf hA (fun a ha v hv => (hstab ha v).2 hv) hm).2 he
  have heq := seedSpace_eq_moved_of_supplement ρ hLA hs
  exact ⟨(subspaceKernel_eq_bot_iff ρ _ A).mpr hk, heq, heq ▸ hs⟩

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
