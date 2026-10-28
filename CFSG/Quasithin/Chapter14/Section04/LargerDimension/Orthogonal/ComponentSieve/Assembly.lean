module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve.Placement
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.Assembly

/-!
# Constructing the smaller local component from the actual orthogonal lift

The source's literal K₀ is unsuitable as a local C-component. Its corrected
replacement is the embedded solvable residual of K₀UD. The moved A₅ map
constructs its C-component structure, the selected normal-square fixed
subgroup proves normalization by the original T_D, and the order-64 lift
supplies the nontrivial two-core clause. The existing global Sylow witness
is retained unchanged.

This discharges local-family placement. Identification of this subgroup's
image core and binary action, followed by all fourteen A.3.14 alternatives,
is still required for the source contradiction. The universal embedding
classification remains owned by qt-a03-embeddings.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve
variable {G : Type*} [Group G] [Finite G]

/-- The constructed smaller subgroup lies in the genuine local family of
N_G(D) relative to the original N_T(D). Every placement premise follows from
the earlier selected configuration and its proved LiftResult. -/
theorem source_residual_mem_localFamily
    (U : Subgroup G) [IsExtraspecial 2 U] (T : Sylow 2 G) (z x : G)
    (hz : orderOf z = 2)
    (hZ : (center U).map U.subtype = zpowers z)
    (hUcore : (centralizer ({z} : Set G)).pCoreIn 2 = U)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hiT : conjugateElement z x ∈ T) (hout : conjugateElement z x ∉ U)
    (hKU : diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x) ≤
      normalizer (U : Set G))
    (m : MovedCoreModel U
      (diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x))
      (conjugateElement z x) hKU)
    (d : QuotientModel.SelectedComponentData
      ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G)))
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))
        ⟨conjugateElement z x,hTz hiT⟩)
      (((diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x)).subgroupOf
        (centralizer ({z} : Set G))).map
          (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))))
    (r : LiftResult U T z x hKU m) :
    let D := centralizerLift U z (conjugateElement z x)
    let N := normalizer (D : Set G)
    let S := localSylow (T : Subgroup G) D
    let J := diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x) ⊔ U ⊔ D
    (solvableResidual J).map J.subtype ∈ Chapter1.LIn N S := by
  let i := conjugateElement z x
  let D := centralizerLift U z i
  let N := normalizer (D : Set G)
  let S := localSylow (T : Subgroup G) D
  let A := diagonalResidual (centralizer ({z} : Set G)) i ⊔ U
  have hi : orderOf i = 2 := by
    simpa only [i, conjugateElement, MulEquiv.orderOf_eq] using hz
  have hzU : zpowers z ≤ U := by rw [← hZ]; exact map_subtype_le _
  have hU := IsExtraspecial.isPGroup 2 U
  let : IsElementaryAbelian 2 D := r.actions.chief.elementary_D
  have hD : IsPGroup 2 D := IsElementaryAbelian.isPGroup 2 D
  have hAN : A ≤ N := le_sup_left.trans r.symmetric_normalizes
  obtain ⟨P,hP⟩ := r.global_sylow
  have hSP : (P : Subgroup N).map N.subtype = S := by
    rw [hP, map_subgroupOf_eq_of_le (show S ≤ N from inf_le_right)]
  have hS : Chapter1.IsSylowIn 2 S N := ⟨P,hSP⟩
  have hDS : D ≤ S := r.normalizer_core.1.trans (by
    rw [← hSP]
    exact pCoreIn_le_sylow N P)
  have hne : D ≠ ⊥ := by
    intro he
    have hc := r.actions.chief.card_D
    change Nat.card D = 64 at hc
    rw [he, Nat.card_eq_fintype_card] at hc
    norm_num at hc
  have hSA : S ≤ normalizer (A : Set G) :=
    source_normalizes_actor U S z i hi hUcore hzU (hTz hiT) hout
      (inf_le_left.trans hTz) inf_le_right d
  have hB := residual_mem_localFamily A D S N hAN hS hSA
    (moved_residual_isCComponent m hU) hD hne hDS hAN inf_le_right
  have hiU : i ∈ normalizer (U : Set G) := by
    have hHU := (centralizer ({z} : Set G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image
        (centralizer ({z} : Set G)) (pCore 2 (centralizer ({z} : Set G))))
    change centralizer ({z} : Set G) ≤
      normalizer ((centralizer ({z} : Set G)).pCoreIn 2 : Set G) at hHU
    rw [hUcore] at hHU
    exact hHU (hTz hiT)
  change (solvableResidual (A ⊔ D : Subgroup G)).map (A ⊔ D).subtype ∈ Chapter1.LIn N S
  rw [corrected_residual_eq U z i hzU hiU hD]
  exact ⟨(map_subtype_le _).trans hAN,hB⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve
