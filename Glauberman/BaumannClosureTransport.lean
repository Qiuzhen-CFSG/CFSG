module
public import Glauberman.SmallMoverBaumann
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.NormalClosureSupplement
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.PResidual.NormalPGroupSupplement
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.SylowFixedNormalClosureSplitting

/-!
# Native all-abelian data in the Baumann normal closure

An intermediate subgroup containing the original all-abelian Thompson
subgroup has the same entire maximum-abelian family. This identifies the
Thompson subgroup, its central omega, and Baumann subgroup on the Sylow
intersection with the Baumann normal closure. A normal two-group supplement
preserves the whole residual and internal generation by Baumann conjugates.

An ambient normal elementary layer containing the original Thompson omega
makes its native normal closure elementary. A moving Sylow-fixed seed then
survives in the ordinary omega-center of the new Sylow, producing the actual
noncentral elementary core module and its fixed/moved splitting.

Source: the preparation for F₀ in MS93 (5.1), printed p.913; actual application
in NonbinarySymplectic.CriticalReduction.RootProductClosureLayer. These
transport results do not identify the new Sylow with its Baumann subgroup.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Glauberman
variable {G : Type*} [Group G] [Finite G]

/-- An intermediate subgroup containing J(T) has the full original maximum
abelian family, not just the same generated Thompson subgroup. -/
theorem maximum_abelian_family_of_thompson_le (T D : Subgroup G)
    (hDT : D ≤ T) (hJD : thompsonSubgroup T ≤ D) :
    thompsonAbelianSubgroups D = thompsonAbelianSubgroups T := by
  obtain ⟨A,hA⟩ := thompsonAbelianSubgroups_nonempty T
  have hAD : A ≤ D := (le_sSup hA).trans hJD
  apply Set.Subset.antisymm
  · intro B hB
    exact ⟨hB.1.trans hDT,hB.2.1,fun C hCT hCc =>
      (hA.2.2 C hCT hCc).trans (hB.2.2 A hAD hA.2.1)⟩
  · intro B hB
    exact thompsonAbelianSubgroups_mem_of_le hDT hB ((le_sSup hB).trans hJD)

/-- Baumann and Thompson heredity on the full all-abelian interval. -/
theorem baumann_intermediate (T D : Subgroup G)
    (hBD : baumannSubgroup T ≤ D) (hDT : D ≤ T) :
    thompsonAbelianSubgroups D = thompsonAbelianSubgroups T ∧
    thompsonSubgroup D = thompsonSubgroup T ∧
    omegaCenterIn (thompsonSubgroup D) = omegaCenterIn (thompsonSubgroup T) ∧
    baumannSubgroup D = baumannSubgroup T := by
  have hj := (thompson_le_baumann T).trans hBD
  have he := thompsonSubgroup_eq_of_le hDT hj
  refine ⟨maximum_abelian_family_of_thompson_le T D hDT hj,he,congrArg omegaCenterIn he,?_⟩
  unfold baumannSubgroup
  rw [he]
  exact le_antisymm (inf_le_inf_right _ hDT) (le_inf hBD inf_le_right)

omit [Finite G] in
/-- An elementary layer inside T containing its Thompson central omega
lies in the literal all-abelian Baumann subgroup. -/
theorem elementary_layer_le_baumann (T W : Subgroup G)
    [IsElementaryAbelian 2 W] (hWT : W ≤ T)
    (hZW : omegaCenterIn (thompsonSubgroup T) ≤ W) : W ≤ baumannSubgroup T := by
  apply le_inf hWT
  intro w hw z hz
  exact setLike_mul_comm (hZW hz) hw

/-- The actual Sylow of the Baumann normal closure retains the original
Thompson and Baumann data. Its Baumann subgroup normally generates the
closure, and its central-omega closure is elementary and still moved by
its own two-residual. No equality between the Sylow and Baumann is assumed. -/
theorem baumann_normalClosure_native_layer
    (S : Sylow 2 G) (N W : Subgroup G) [N.Normal] [W.Normal]
    [IsElementaryAbelian 2 W]
    (hN : N = normalClosure (baumannSubgroup (S : Subgroup G) : Set G))
    (hgen : N ⊔ (S : Subgroup G) = ⊤)
    (hZW : omegaCenterIn (thompsonSubgroup (S : Subgroup G)) ≤ W)
    (hmoving : ⁅omegaCenterIn (thompsonSubgroup (S : Subgroup G)),pResidual 2 G⁆ ≠ ⊥)
    (P : Sylow 2 N) (hP : (P : Subgroup N).map N.subtype = (S : Subgroup G) ⊓ N) :
    (thompsonSubgroup (P : Subgroup N)).map N.subtype = thompsonSubgroup (S : Subgroup G) ∧
    (omegaCenterIn (thompsonSubgroup (P : Subgroup N))).map N.subtype =
      omegaCenterIn (thompsonSubgroup (S : Subgroup G)) ∧
    (baumannSubgroup (P : Subgroup N)).map N.subtype = baumannSubgroup (S : Subgroup G) ∧
    normalClosure (baumannSubgroup (P : Subgroup N) : Set N) = ⊤ ∧
    (normalClosure (omegaCenterIn (thompsonSubgroup (P : Subgroup N)) : Set N)).map N.subtype =
      normalClosure (omegaCenterIn (thompsonSubgroup (S : Subgroup G)) : Set G) ∧
    IsElementaryAbelian 2 (normalClosure (omegaCenterIn (thompsonSubgroup (P : Subgroup N)) : Set N)) ∧
    normalClosure (omegaCenterIn (thompsonSubgroup (P : Subgroup N)) : Set N) ≤ pCore 2 N ∧
    ⁅omegaCenterIn (thompsonSubgroup (P : Subgroup N)),pResidual 2 N⁆ ≠ ⊥ := by
  let B := baumannSubgroup (S : Subgroup G)
  let Z := omegaCenterIn (thompsonSubgroup (S : Subgroup G))
  have hBN : B ≤ N := hN ▸ le_normalClosure
  have hBS : B ≤ (S : Subgroup G) := inf_le_left
  have hh := baumann_intermediate (S : Subgroup G) ((S : Subgroup G) ⊓ N)
    (le_inf hBS hBN) inf_le_left
  have hJ : (thompsonSubgroup (P : Subgroup N)).map N.subtype = thompsonSubgroup (S : Subgroup G) := by
    rw [thompson_map_injective _ _ N.subtype_injective,hP,hh.2.1]
  have hZ : (omegaCenterIn (thompsonSubgroup (P : Subgroup N))).map N.subtype = Z := by
    rw [omegaCenterIn_map_injective _ _ N.subtype_injective,hJ]
  have hB : (baumannSubgroup (P : Subgroup N)).map N.subtype = B := by
    rw [baumann_map_injective _ _ N.subtype_injective,hP,hh.2.2.2]
  have hBsub : B.subgroupOf N = baumannSubgroup (P : Subgroup N) := by
    rw [←hB]
    exact comap_map_eq_self_of_injective N.subtype_injective _
  have hSB : (S : Subgroup G) ≤ normalizer (B : Set G) :=
    (S : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumannSubgroup _)
  have hBgen : normalClosure (baumannSubgroup (P : Subgroup N) : Set N) = ⊤ := by
    apply map_injective N.subtype_injective
    rw [←hBsub,←normalClosure_eq_map_of_normal_supplement N (S : Subgroup G) B hgen hBN hSB,
      ←hN,←MonoidHom.range_eq_map,range_subtype]
  have hZN : Z ≤ N := by
    intro z hz
    exact hBN ((thompson_le_baumann (S : Subgroup G)) ((mem_omegaCenterIn_iff _ _).mp hz).1)
  have hSZ : (S : Subgroup G) ≤ normalizer (Z : Set G) :=
    (S : Subgroup G).le_normalizer.trans ((normalizer_le_normalizer_of_thompsonSubgroup _).trans
      (normalizer_le_normalizer_omegaCenterIn _))
  have hZsub : Z.subgroupOf N = omegaCenterIn (thompsonSubgroup (P : Subgroup N)) := by
    rw [←hZ]
    exact comap_map_eq_self_of_injective N.subtype_injective _
  let Y := normalClosure (omegaCenterIn (thompsonSubgroup (P : Subgroup N)) : Set N)
  have hYm : Y.map N.subtype = normalClosure (Z : Set G) := by
    rw [normalClosure_eq_map_of_normal_supplement N (S : Subgroup G) Z hgen hZN hSZ,hZsub]
  have hYW : Y.map N.subtype ≤ W := hYm ▸ normalClosure_le_normal hZW
  let : IsElementaryAbelian 2 (Y.map N.subtype) := IsElementaryAbelian.of_le hYW
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.of_injective
    (Y.equivMapOfInjective N.subtype N.subtype_injective).toMonoidHom
    (Y.equivMapOfInjective N.subtype N.subtype_injective).injective
  have hYcore : Y ≤ pCore 2 N := le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 Y⟩
  refine ⟨hJ,hZ,hB,hBgen,hYm,inferInstance,hYcore,?_⟩
  intro hz
  have hm := congrArg (Subgroup.map N.subtype) hz
  rw [map_commutator,hZ,pResidual_of_normal_pGroup_supplement 2 N (S : Subgroup G) S.isPGroup' hgen,
    Subgroup.map_bot] at hm
  exact hmoving hm

/-- The source Sylow-fixed seed survives in the ordinary central omega
of the closure's Sylow. Its native normal closure is an elementary,
noncentral two-core module with the exact fixed/moved splitting. -/
theorem baumann_closure_sylow_omega_layer
    (S : Sylow 2 G) (N U : Subgroup G) [N.Normal] [IsElementaryAbelian 2 U]
    (hgen : N ⊔ (S : Subgroup G) = ⊤)
    (hUN : U ≤ N) (hUS : U ≤ (S : Subgroup G))
    (hmoving : ⁅U ⊓ centralizer (S : Set G),pResidual 2 G⁆ ≠ ⊥)
    (P : Sylow 2 N) (hP : (P : Subgroup N).map N.subtype = (S : Subgroup G) ⊓ N)
    (helem : IsElementaryAbelian 2
      (normalClosure (omegaCenterIn (thompsonSubgroup (P : Subgroup N)) : Set N))) :
    U ⊓ centralizer (S : Set G) ≤ (omegaCenterIn (P : Subgroup N)).map N.subtype ∧
    IsElementaryAbelian 2 (normalClosure (omegaCenterIn (P : Subgroup N) : Set N)) ∧
    normalClosure (omegaCenterIn (P : Subgroup N) : Set N) ≤ pCore 2 N ∧
    ⁅normalClosure (omegaCenterIn (P : Subgroup N) : Set N),pResidual 2 N⁆ ≠ ⊥ ∧
    normalClosure (omegaCenterIn (P : Subgroup N) : Set N) =
      ⁅normalClosure (omegaCenterIn (P : Subgroup N) : Set N),(⊤ : Subgroup N)⁆ ⊔
        (normalClosure (omegaCenterIn (P : Subgroup N) : Set N) ⊓ center N) := by
  have hPsub : (P : Subgroup N) = (S : Subgroup G).subgroupOf N := by
    apply map_injective N.subtype_injective
    rw [hP,subgroupOf_map_subtype]
  have hfixed : U ⊓ centralizer (S : Set G) ≤ (omegaCenterIn (P : Subgroup N)).map N.subtype := by
    intro u hu
    refine ⟨⟨u,hUN hu.1⟩,(mem_omegaCenterIn_iff _ _).mpr ⟨?_,?_,?_⟩,rfl⟩
    · rw [hPsub]
      exact hUS hu.1
    · intro x hx
      apply Subtype.ext
      exact hu.2 x.val (by rw [hPsub] at hx; exact hx)
    · apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian u hu.1
  have hZc : omegaCenterIn (P : Subgroup N) ≤ centralizer (P : Set N) :=
    fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1
  have hZJ := smallMover_fixed_le_thompson_omega (omegaCenterIn (P : Subgroup N))
    (P : Subgroup N) (P : Subgroup N) (map_subtype_le _) (thompsonSubgroup_le _)
  have hZJ' : omegaCenterIn (P : Subgroup N) ≤ omegaCenterIn (thompsonSubgroup (P : Subgroup N)) :=
    (le_inf le_rfl hZc).trans hZJ
  let V := normalClosure (omegaCenterIn (P : Subgroup N) : Set N)
  let : IsElementaryAbelian 2
    (normalClosure (omegaCenterIn (thompsonSubgroup (P : Subgroup N)) : Set N)) := helem
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le (normalClosure_mono hZJ')
  refine ⟨hfixed,inferInstance,le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 V⟩,?_,
    Theory.GroupTheory.normalClosure_split_of_sylow_fixed P (omegaCenterIn (P : Subgroup N)) hZc⟩
  intro hz
  have hm := congrArg (Subgroup.map N.subtype) hz
  rw [map_commutator,pResidual_of_normal_pGroup_supplement 2 N (S : Subgroup G) S.isPGroup' hgen,
    Subgroup.map_bot] at hm
  exact hmoving (bot_unique ((commutator_mono
    (hfixed.trans (map_mono le_normalClosure)) le_rfl).trans_eq hm))

end Glauberman
