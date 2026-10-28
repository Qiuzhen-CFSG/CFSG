module
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.Residuals.GeometricFlags
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.MaximalLevi
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoImages
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# Rank-one normal sections in binary five-space parabolics

A proper Sylow overgroup containing a factor of five is an endpoint flag
stabilizer, with two-core quotient A₈. A normal perfect subgroup with simple
two-core quotient of order sixty has nontrivial normal image in A₈: a solvable
kernel cannot remove the factor five. Simplicity would make that image all
of A₈, contradicting the absent factor seven.

This supplies the literal SL₅(2) exclusion in Aschbacher–Smith C.4.1(4) and
4.3.7, printed pp.151–153,615–616. The representation-degree bound and source
markings are supplied by its Chapter 4 consumer.
-/

public section
open Subgroup Theory.GroupTheory
namespace BinaryLinear.RankOneNormalSections
open OuterCyclic
private instance : Finite (LinearGroup 5) :=
  Finite.of_equiv (Matrix.GeneralLinearGroup (Fin 5) (ZMod 2)) (matrixEquivLinear 5).toEquiv

/-- A normal perfect subgroup with simple two-core quotient of order sixty
cannot map with solvable kernel into a group with A₈ two-core quotient. -/
theorem no_normal_sixty_image {B D : Type*} [Group B] [Finite B] [Group D] [Finite D]
    [Group.IsPerfect B] [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hc : Nat.card (B ⧸ pCore 2 B) = 60)
    (f : B →* D) [f.range.Normal] [Group.IsSolvable f.ker]
    (e8 : (D ⧸ pCore 2 D) ≃* alternatingGroup (Fin 8)) : False := by
  let q := e8.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D))
  have hq : Function.Surjective q := e8.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqk : q.ker = pCore 2 D := by
    dsimp only [q]
    rw [MonoidHom.ker_comp_of_injective _ _ e8.injective,QuotientGroup.ker_mk']
  let : Group.IsNilpotent (pCore 2 D) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable q.ker := hqk.symm ▸ inferInstanceAs (Group.IsSolvable (pCore 2 D))
  let g := q.comp f
  let : Group.IsSolvable g.ker := isSolvable_comap_of_solvable_ker f q.ker
  let : g.range.Normal := by
    dsimp only [g]
    rw [MonoidHom.range_comp]
    exact Subgroup.Normal.map inferInstance q hq
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  have h7 : ¬ 7 ∣ Nat.card B := by
    obtain ⟨r,hr⟩ := (pCore_isPGroup (p := 2) (G := B)).exists_card_eq
    rw [←(pCore 2 B).card_mul_index,hr,index_eq_card,hc]
    intro hd
    have hh := ((by decide : Nat.Coprime 7 2).pow_right r).dvd_of_dvd_mul_left hd
    norm_num at hh
  have h5 : 5 ∣ Nat.card g.range := by
    have hB : 5 ∣ Nat.card B := by
      have hd := card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 B))
        (QuotientGroup.mk'_surjective _)
      rw [hc] at hd
      exact (by decide : 5 ∣ 60).trans hd
    have hker := pCore_isPGroup.to_le (PerfectCoreTwoExtension.solvable_ker_le_core g)
    obtain ⟨r,hr⟩ := hker.exists_card_eq
    rw [←g.ker.card_mul_index,hr,index_ker] at hB
    exact ((by decide : Nat.Coprime 5 2).pow_right r).dvd_of_dvd_mul_left hB
  rcases (inferInstance : g.range.Normal).eq_bot_or_eq_top with hg | hg
  · rw [hg,card_bot] at h5
    norm_num at h5
  · have hd := card_dvd_of_surjective g (MonoidHom.range_eq_top.mp hg)
    have h7A : 7 ∣ Nat.card (alternatingGroup (Fin 8)) := by
      rw [nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    exact h7 (h7A.trans hd)

/-- A proper full-Sylow overgroup in GL₅(2) has no normal perfect subgroup
whose simple two-core quotient has order sixty. -/
theorem no_normal_sixty_in_five_sylow_overgroup
    (S : Sylow 2 (LinearGroup 5)) (P : Subgroup (LinearGroup 5))
    (hSP : (S : Subgroup _) ≤ P) (hP : P ≠ ⊤)
    {B : Type*} [Group B] [Finite B] [Group.IsPerfect B]
    [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hc : Nat.card (B ⧸ pCore 2 B) = 60)
    (f : B →* P) (hf : Function.Injective f) [f.range.Normal] : False := by
  obtain ⟨b,cuts,hflag⟩ := FiveFlagGeometry.isFlagParabolic_of_sylow_le S P hSP
  have h5B : 5 ∣ Nat.card B := by
    rw [←(pCore 2 B).card_mul_index,index_eq_card,hc]
    exact dvd_mul_of_dvd_right (by decide : 5 ∣ 60) _
  have h5 : 5 ∣ Nat.card (FiveFlagGeometry.flagStabilizer b cuts) := by
    rw [←hflag]
    exact h5B.trans (card_dvd_of_injective f hf)
  have hp' : FiveFlagGeometry.flagStabilizer b cuts ≠ ⊤ := hflag ▸ hP
  rcases FiveFlagGeometry.cuts_eq_singleton_end_of_five_dvd b cuts hp' h5 with he | he
  all_goals
    rw [he] at hflag
    let a := MulEquiv.subgroupCongr hflag
    let q := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
    let : Group.IsSolvable f.ker := by
      rw [show f.ker = ⊥ from (MonoidHom.ker_eq_bot_iff f).mpr hf]
      infer_instance
    apply no_normal_sixty_image hc f
  · exact q.trans ((FiveFlagGeometry.MaximalOvergroups.lineQuotientEquiv b).trans
      Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm)
  · exact q.trans ((FiveFlagGeometry.MaximalOvergroups.hyperplaneQuotientEquiv b).trans
      Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm)
end BinaryLinear.RankOneNormalSections
