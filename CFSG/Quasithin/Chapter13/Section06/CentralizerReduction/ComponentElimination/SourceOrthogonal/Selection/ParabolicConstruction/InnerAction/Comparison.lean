module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.Marking
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# Comparing the old and replacement plus actions

For D≤K the source module W_D is contained in W_K. Restricting the action
therefore induces an explicit surjection from the original plus image of D
on W_K to its own plus image on W_D, agreeing on every representative.
If the original image modulo its two-core is L₃(2), and the replacement
image has trivial two-core and moves z, this surjection induces an actual
isomorphism of the replacement image with L₃(2).

The consumer in InnerAction uses the source R₂ condition after proving Y_z
membership, so no equality between the two faithful images is assumed.
Source: Aschbacher–Smith, proof of 13.6.23, printed p.933/PDF p.950.
-/

@[expose] public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.InnerAction
open ComponentSelection
variable {G : Type*} [Group G]

/-- The source-generated module shrinks with the acting component. -/
theorem WK_mono (K D L T : Subgroup G) (z v : G) (hDK : D ≤ K) :
    WK D L T z v ≤ WK K L T z v :=
  conjugateSpanBy_mono le_rfl
    (sup_le_sup (conjugateSpanBy_mono hDK le_rfl) le_rfl)

/-- The restricted plus kernel is the centralizer of the original module. -/
theorem plusImageMap_ker (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (H : Subgroup G) (hH : H ≤ plusActor K L T v) :
    (plusImageMap K L T z v hL hz H hH).ker =
      (centralizer (WK K L T z v : Set G)).subgroupOf H := by
  ext x
  change plusImageMap K L T z v hL hz H hH x = 1 ↔ _
  rw [Subtype.ext_iff]
  change inclusion hH x ∈ (plusMk K L T z v hL hz).ker ↔ _
  rw [plusMk_ker]
  rfl

variable (K D L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hDK : D ≤ K)

/-- Restriction from W_K to W_D gives a map between the two actual plus images. -/
noncomputable def plusComparison :
    plusImage K L T z v hL hz D →* plusImage D L T z v hL hz D :=
  (plusImageMap K L T z v hL hz D (hDK.trans (K_le_plusActor K L T v))).liftOfSurjective
    (plusImageMap_surjective K L T z v hL hz D _) ⟨
      plusImageMap D L T z v hL hz D (K_le_plusActor D L T v), by
        rw [plusImageMap_ker, plusImageMap_ker]
        exact comap_mono (centralizer_le (WK_mono K D L T z v hDK))⟩

/-- Both actions are induced by the same representative d. -/
theorem plusComparison_mk (d : D) :
    plusComparison K D L T z v hL hz hDK
      (plusImageMap K L T z v hL hz D (hDK.trans (K_le_plusActor K L T v)) d) =
        plusImageMap D L T z v hL hz D (K_le_plusActor D L T v) d := by
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem plusComparison_surjective :
    Function.Surjective (plusComparison K D L T z v hL hz hDK) := by
  intro y
  obtain ⟨d, hd⟩ := plusImageMap_surjective D L T z v hL hz D (K_le_plusActor D L T v) y
  exact ⟨plusImageMap K L T z v hL hz D (hDK.trans (K_le_plusActor K L T v)) d,
    (plusComparison_mk K D L T z v hL hz hDK d).trans hd⟩

private theorem image_twoCore_le_ker {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Surjective f) (hB : pCore 2 B = ⊥) :
    pCore 2 A ≤ f.ker := by
  have hm : (pCore 2 A).map f ≤ pCore 2 B :=
    le_sSup ⟨(inferInstance : (pCore 2 A).Normal).map f hf, pCore_isPGroup.map f⟩
  exact (Subgroup.map_eq_bot_iff _).mp (bot_unique (hm.trans hB.le))

include hDK in
/-- The geometric L₃(2) quotient identifies the replacement's own faithful image.
The restriction map is used explicitly; the two plus images are not identified. -/
theorem ownPlus_model_of_old_quotient
    (hcore : pCore 2 (plusImage D L T z v hL hz D) = ⊥)
    (hmove : ¬ D ≤ centralizer ({z} : Set G))
    (e : (plusImage K L T z v hL hz D ⧸ pCore 2 (plusImage K L T z v hL hz D)) ≃*
      SL(3, ZMod 2)) :
    Nonempty (plusImage D L T z v hL hz D ≃* SL(3, ZMod 2)) := by
  let A := plusImage K L T z v hL hz D
  let B := plusImage D L T z v hL hz D
  let f := plusComparison K D L T z v hL hz hDK
  have hf := plusComparison_surjective K D L T z v hL hz hDK
  let q : (A ⧸ pCore 2 A) →* B := QuotientGroup.lift _ f (image_twoCore_le_ker f hf hcore)
  have hq : Function.Surjective q := QuotientGroup.lift_surjective_of_surjective _ _ hf _
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  let : IsSimpleGroup SL(3, ZMod 2) :=
    ((BinaryLinear.OuterCyclic.slEquivLinear 3).trans
      BinaryLinear.SmallParabolicLevi.linearThreeEquivProjective).isSimpleGroup
  let : IsSimpleGroup (A ⧸ pCore 2 A) := e.isSimpleGroup
  have hB : B ≠ ⊥ := by
    intro he
    apply hmove
    exact ((plusImage_eq_bot_iff D L T z v hL hz D (K_le_plusActor D L T v)).mp he).trans
      (centralizer_le (Set.singleton_subset_iff.mpr
        (le_conjugateSpanBy (zpowers z) (Kminus D T v ⊔ Lv L v) (mem_zpowers z))))
  have hi : Function.Injective q := by
    apply (MonoidHom.ker_eq_bot_iff q).mp
    rcases (inferInstance : q.ker.Normal).eq_bot_or_eq_top with hh | hh
    · exact hh
    · have htriv : ∀ y : B, y = 1 := by
        intro y
        obtain ⟨x, rfl⟩ := hq y
        exact show x ∈ q.ker from hh.symm ▸ mem_top x
      exact (hB (eq_bot_iff.mpr (fun x hx => congrArg Subtype.val (htriv ⟨x, hx⟩)))).elim
  exact ⟨(MulEquiv.ofBijective q ⟨hi, hq⟩).symm.trans e⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.InnerAction
