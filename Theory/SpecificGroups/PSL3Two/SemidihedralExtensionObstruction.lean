module

public import Theory.SpecificGroups.PSL3Two.Automorphisms
public import Theory.GroupTheory.SemidihedralSixteenInvolutions
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import GorensteinWalter.PGL2DihedralSylow
public import Mathlib.GroupTheory.IndexNormal

/-!
# No semidihedral Sylow subgroup in an index-two extension of PSL₃(2)

The conjugation action of an SD16 Sylow subgroup on a centerless normal
index-two subgroup is faithful. Indeed, a nontrivial kernel would meet the
Sylow center, whose generator is a square and hence belongs to the normal
subgroup. This contradicts centerlessness of that subgroup.

For PSL₃(2), the checked automorphism equivalence puts this faithful two-group
image inside PGL₂(7), whose Sylow two-subgroups are dihedral. A dihedral group
cannot realize SD16's order-eight generator with conjugation exponent three:
conjugation of a rotation either fixes it or inverts it.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, J.2.7,
printed p.435 (PDF p.446), the exclusion of L₃(2) after I.4.1(2).
-/

public section
open Subgroup
namespace Matrix.PSL3Two.SemidihedralExtensionObstruction
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem dihedral_no_twist {n : ℕ} (a b : DihedralGroup n)
    (ha : orderOf a = 8) (hab : b * a * b⁻¹ = a ^ 3) : False := by
  cases a with
  | sr i => simp only [DihedralGroup.orderOf_sr] at ha; omega
  | r i =>
    have hc : b * DihedralGroup.r i * b⁻¹ = DihedralGroup.r i ∨
        b * DihedralGroup.r i * b⁻¹ = (DihedralGroup.r i)⁻¹ := by
      cases b with
      | r j => left; simp
      | sr j => right; simp
    rcases hc with hc | hc
    · have hp : (DihedralGroup.r i : DihedralGroup n) ^ 1 = (DihedralGroup.r i) ^ 3 := by
        simpa only [pow_one, hc] using hab
      have h := pow_inj_mod.mp hp
      norm_num [ha] at h
    · have hp : (DihedralGroup.r i : DihedralGroup n) ^ 4 = 1 := by
        calc
          _ = (DihedralGroup.r i) ^ 3 * DihedralGroup.r i := pow_succ _ _
          _ = (DihedralGroup.r i)⁻¹ * DihedralGroup.r i := by rw [← hab, hc]
          _ = 1 := inv_mul_cancel _
      have hd := orderOf_dvd_of_pow_eq_one hp
      norm_num [ha] at hd

private theorem no_embedding_of_dihedral_sylow {H : Type*} [Group H]
    (hD : GorensteinWalter.HasDihedralSylowTwo H)
    (f : Semidihedral.StandardModel 4 (Nat.le_refl 4) →* H)
    (hf : Function.Injective f) : False := by
  have hp : IsPGroup 2 (Semidihedral.StandardModel 4 (Nat.le_refl 4)) :=
    IsPGroup.of_card (Semidihedral.standardModel_card 4 (Nat.le_refl 4))
  obtain ⟨T, hT⟩ := (hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  obtain ⟨m, _, ⟨eD⟩⟩ := hD T
  let g : Semidihedral.StandardModel 4 (Nat.le_refl 4) →* DihedralGroup (2 ^ m) :=
    eD.toMonoidHom.comp ((inclusion hT).comp f.rangeRestrict)
  have hg : Function.Injective g := by
    intro x y hxy
    apply hf
    exact congrArg Subtype.val (eD.injective hxy)
  apply dihedral_no_twist (g (Semidihedral.standardRotation 4 (Nat.le_refl 4)))
    (g (Semidihedral.standardReflection 4 (Nat.le_refl 4)))
  · rw [orderOf_injective g hg, Semidihedral.standardRotation_order]
    decide
  · simpa only [map_mul, map_inv, map_pow, show 2 ^ (4 - 2) - 1 = 3 from rfl] using
      congrArg g (Semidihedral.standard_conjugation 4 (Nat.le_refl 4))

private theorem sylow_action_injective {W : Type*} [Group W] [Finite W]
    (N : Subgroup W) [N.Normal] (hi : N.index = 2) (hc : center N = ⊥)
    (S : Sylow 2 W) (e : S ≃* Semidihedral.StandardModel 4 (Nat.le_refl 4)) :
    Function.Injective ((MulAut.conjNormal : W →* MulAut N).comp (S : Subgroup W).subtype) := by
  let f : S →* MulAut N := (MulAut.conjNormal : W →* MulAut N).comp (S : Subgroup W).subtype
  apply (MonoidHom.ker_eq_bot_iff _).mp
  change f.ker = ⊥
  by_contra hk
  let : Nontrivial f.ker := (nontrivial_iff_ne_bot _).mpr hk
  let : Fact (IsPGroup 2 S) := ⟨S.isPGroup'⟩
  obtain ⟨x, hxne, hxc⟩ := exists_nontrivial_center_mem_normal (p := 2) f.ker
  have hxe : e (x : S) ∈ center (Semidihedral.StandardModel 4 (Nat.le_refl 4)) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨y, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hxc y)
  rw [Semidihedral.center_standard_sixteen] at hxe
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hxe
  have hxN : ((x : S) : W) ∈ N := by
    have hs := N.sq_mem_of_index_two hi
      (((e.symm (Semidihedral.standardRotation 4 (Nat.le_refl 4))) ^ 2 : S) : W)
    have hs4 : ((e.symm (Semidihedral.standardRotation 4 (Nat.le_refl 4) ^ 4) : S) : W) ∈ N := by
      simpa only [map_pow, ← Subgroup.coe_pow, ← pow_mul] using hs
    have he : (x : S) = e.symm (Semidihedral.standardRotation 4 (Nat.le_refl 4) ^ 4) ^ k := by
      apply e.injective
      simp only [map_zpow, e.apply_symm_apply]
      exact hk.symm
    rw [he, Subgroup.coe_zpow]
    exact N.zpow_mem hs4 k
  have hfx : MulAut.conj (⟨((x : S) : W), hxN⟩ : N) = 1 := by
    rw [← MulAut.conjNormal_val]
    exact x.property
  have hx1 : (⟨((x : S) : W), hxN⟩ : N) = 1 :=
    (MulAut.conj_injective_of_center_eq_bot hc) (hfx.trans (map_one _).symm)
  exact hxne (Subtype.ext (Subtype.ext (congrArg (fun n : N => (n : W)) hx1)))

/-- An index-two extension of the actual PSL₃(2) group cannot have an SD16 Sylow subgroup. -/
theorem no_index_two_extension {W : Type*} [Group W] [Finite W]
    (N : Subgroup W) [N.Normal] (hi : N.index = 2)
    (eN : N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
    (S : Sylow 2 W) (eS : S ≃* Semidihedral.StandardModel 4 (Nat.le_refl 4)) : False := by
  have hc : center N = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have he := ((centerCongr eN) ⟨x, hx⟩).property
    change eN x ∈ center PSL at he
    rw [Automorphisms.center_psl_eq_bot, mem_bot] at he
    exact mem_bot.mpr (eN.map_eq_one_iff.mp he)
  let action : S →* MulAut N := (MulAut.conjNormal : W →* MulAut N).comp (S : Subgroup W).subtype
  have haction : Function.Injective action := sylow_action_injective N hi hc S eS
  let f : S →* GorensteinWalter.PGL2 (ZMod 7) :=
    Automorphisms.pgl2SevenEquivAut.symm.toMonoidHom.comp
      ((MulAut.congr eN).toMonoidHom.comp action)
  have hf : Function.Injective f :=
    Automorphisms.pgl2SevenEquivAut.symm.injective.comp
      ((MulAut.congr eN).injective.comp haction)
  have hseven : GorensteinWalter.IsOddPrimePower (Nat.card (ZMod 7)) := by
    refine ⟨7, 1, by decide, by decide, by decide, ?_⟩
    norm_num
  exact no_embedding_of_dihedral_sylow
    (GorensteinWalter.pgl2_odd_hasDihedralSylowTwo_model (ZMod 7) hseven)
    (f.comp eS.symm.toMonoidHom) (hf.comp eS.symm.injective)

end Matrix.PSL3Two.SemidihedralExtensionObstruction
