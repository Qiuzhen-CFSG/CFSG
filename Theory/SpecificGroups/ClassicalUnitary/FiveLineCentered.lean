module
public import Theory.GroupTheory.CentralCoverCenteredModules
public import Theory.GroupTheory.Commutator.PerfectSolvableSupplement
public import Theory.SpecificGroups.ClassicalUnitary.FivePerfectLocals
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.Flag.Center.LineRadical
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineCore.Parabolic.Perfect

/-!
# Centered perfect normal subgroups of the PSU₅(4) line parabolic

In the full radical--SU₃--cubic decomposition, perfectness kills the cubic
character. A nonsolvable normal subgroup surjects onto the simple SU₃(4)
factor. The solvable radical supplement and perfectness of the radical--SU₃
subgroup then identify the actual normal subgroup with that subgroup.
Its radical centralizer is central, so a central cover cannot contain a
nonzero centered commutator module.

Source: Aschbacher--Smith 4.4.12 and F.1.12(I)(7), printed pp.621--622,
263--264. The literal full parabolic, central kernel and module are retained.
-/

public noncomputable section

open Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic.Blocks
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
  (J : HermitianForm 5 F) (hconj : ∀ x, J.conj x = x ^ 4)

private theorem perfect_le_subnormal_of_le_sup_solvable {G : Type*} [Group G] [Finite G]
    (K B R : Subgroup G) [Group.IsPerfect K] [R.Normal] [Group.IsSolvable R]
    (hs : B.IsSubnormal) (hK : K ≤ B ⊔ R) : K ≤ B := by
  let M := B ⊔ R
  let : Group.IsPerfect (K.subgroupOf M) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hK).symm.toMonoidHom)
      (subgroupOfEquivOfLe hK).symm.surjective
  let eR := subgroupOfEquivOfLe (show R ≤ M from le_sup_right)
  let : Group.IsSolvable (R.subgroupOf M) :=
    Group.isSolvable_of_isSolvable_injective (f := eR.toMonoidHom) eR.injective
  have hle : K.subgroupOf M ≤ B.subgroupOf M :=
    (le_solvableResidual_of_isPerfect _).trans
      (hs.subgroupOf.solvableResidual_le_of_sup_eq_top (R.subgroupOf M)
        (codisjoint_subgroupOf_sup B R).eq_top)
  intro k hk
  exact hle (show (⟨k,hK hk⟩ : M) ∈ K.subgroupOf M from hk)

theorem perfect_normal_eq_radicalLevi_range
    (hcard : Nat.card F = 16) (c : F) (hc : c + J.conj c = 1)
    (B : Subgroup (FullProduct J hconj)) [B.Normal] [Group.IsPerfect B]
    (hB : ¬ Group.IsSolvable B) : B = (radicalLeviInclusion J hconj).range := by
  let : Finite (GL (Fin 3) F) := Finite.of_injective Units.val Units.val_injective
  let : Finite (FullProduct J hconj) := Finite.of_injective
    (fun x : FullProduct J hconj => (x.left,x.right)) (by
      intro x y hxy
      exact SemidirectProduct.ext (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
  let := Levi.simple (middleForm J) rfl hconj hcard (fixed_card_four _ hcard hconj)
  let := Levi.perfect (middleForm J) rfl hconj hcard (fixed_card_four _ hcard hconj)
  let := radicalLevi_isPerfect_of_card_sixteen J hcard hconj c hc
  let K := (radicalLeviInclusion J hconj).range
  let R := (SemidirectProduct.inl : Coord J →* FullProduct J hconj).range
  let f := productProjection J hconj
  let d := productCharacter J hconj
  have hd (b : B) : d b.val = 1 :=
    Abelianization.commutator_subset_ker (d.comp B.subtype) Group.IsPerfect.mem_commutator
  have hBK : B ≤ K := by
    dsimp only [K]
    rw [← productCharacter_ker]
    exact fun b hb => hd ⟨b,hb⟩
  have hf : Function.Surjective f := fun s => ⟨SemidirectProduct.inr (s,1),rfl⟩
  let : (B.map f).Normal := Normal.map inferInstance f hf
  have hfull : B.map f = ⊤ := by
    rcases (inferInstance : (B.map f).Normal).eq_bot_or_eq_top with hz | ht
    · exfalso
      have hBR : B ≤ R := by
        dsimp only [R]
        rw [← product_common_kernel]
        intro b hb
        exact ⟨mem_bot.mp (hz ▸ mem_map_of_mem f hb),hd ⟨b,hb⟩⟩
      let : Group.IsNilpotent R := ((Coord.isPGroup (J := J)).of_surjective
        (SemidirectProduct.inl : Coord J →* FullProduct J hconj).rangeRestrict
        (MonoidHom.rangeRestrict_surjective _)).isNilpotent
      exact hB (Group.isSolvable_of_isSolvable_injective (inclusion_injective hBR))
    · exact ht
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (radicalLeviInclusion J hconj).rangeRestrict)
    (MonoidHom.rangeRestrict_surjective _)
  let : R.Normal := by
    change (SemidirectProduct.inl : Coord J →* FullProduct J hconj).range.Normal
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  let : Group.IsNilpotent R := ((Coord.isPGroup (J := J)).of_surjective
    (SemidirectProduct.inl : Coord J →* FullProduct J hconj).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)).isNilpotent
  have hKR : K ≤ B ⊔ R := by
    intro k hk
    obtain ⟨b,hb,hbf⟩ := mem_map.mp (hfull.symm ▸ mem_top (f k))
    have hkchar : d k = 1 := by
      change k ∈ (radicalLeviInclusion J hconj).range at hk
      rwa [← productCharacter_ker] at hk
    have hbr : b⁻¹ * k ∈ R := by
      dsimp only [R]
      rw [← product_common_kernel]
      exact ⟨by change f (b⁻¹ * k) = 1; rw [map_mul,map_inv,hbf,inv_mul_cancel],
        by change d (b⁻¹ * k) = 1; rw [map_mul,map_inv,hd ⟨b,hb⟩,hkchar,inv_one,mul_one]⟩
    have hh := (B ⊔ R).mul_mem ((le_sup_left : B ≤ B ⊔ R) hb) ((le_sup_right : R ≤ B ⊔ R) hbr)
    simpa only [mul_inv_cancel_left] using hh
  exact le_antisymm hBK
    (perfect_le_subnormal_of_le_sup_solvable K B R (Normal.isSubnormal inferInstance) hKR)

end Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic.Blocks

namespace Theory.SpecificGroups.UnitaryFive
open LineCore LineCore.Parabolic LineCore.Parabolic.Blocks
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
  (J : HermitianForm 5 F) (hconj : ∀ x, J.conj x = x ^ 4)

include hconj in
theorem line_no_centered_commutator
    (hcard : Nat.card F = 16) (hJ : J.form = 1)
    {A : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    (hA : ¬ Group.IsSolvable A)
    (f : A →* lineParabolic J) (hker : f.ker ≤ center A) [f.range.Normal]
    (W : Subgroup A) (hW : W ≤ centralizer (pCore 2 A : Set A))
    (hcomm : W = ⁅W,⊤⁆) : W = ⊥ := by
  obtain ⟨c,hc⟩ := BenderSuzuki.External.huppert_II_10_4_trace_surjective J 4
    hcard (fixed_card_four J hcard hconj) 1 (map_one _)
  let e := MulEquiv.ofBijective (fullMap J hconj c hc hJ)
    ⟨fullMap_injective J hconj c hc hJ,
      Exhaustion.fullMap_surjective J hconj hcard c hc hJ⟩
  let j := e.symm.toMonoidHom.comp f
  have hjker : j.ker ≤ center A := by
    intro x hx
    apply hker
    exact e.symm.injective (hx.trans e.symm.map_one.symm)
  let : j.range.Normal := by
    rw [MonoidHom.range_comp]
    exact Normal.map inferInstance _ e.symm.surjective
  let : Group.IsPerfect j.range := Group.IsPerfect.ofSurjective j.rangeRestrict_surjective
  have hnsol : ¬ Group.IsSolvable j.range := by
    intro hh
    let := hh
    let : CommGroup (center A) := IsMulCommutative.instCommGroup
    let : Group.IsSolvable j.ker :=
      Group.isSolvable_of_isSolvable_injective (inclusion_injective hjker)
    exact hA (Group.isSolvable_of_ker_le_range j.ker.subtype j.rangeRestrict (by
      rw [MonoidHom.ker_rangeRestrict,range_subtype]))
  have hR := perfect_normal_eq_radicalLevi_range J hconj hcard c hc j.range hnsol
  have hinj : Function.Injective (radicalLeviInclusion J hconj) := by
    intro x y hh
    exact SemidirectProduct.ext (congrArg (fun z : FullProduct J hconj => z.left) hh)
      (congrArg (fun z : FullProduct J hconj => z.right.1) hh)
  let a := MonoidHom.ofInjective hinj
  let k := j.codRestrict (radicalLeviInclusion J hconj).range
    (fun x => hR ▸ (show j x ∈ j.range from ⟨x,rfl⟩))
  let q := a.symm.toMonoidHom.comp k
  have hk : Function.Surjective k := by
    rintro ⟨x,hx⟩
    obtain ⟨y,hy⟩ := (show x ∈ j.range from hR.symm ▸ hx)
    exact ⟨y,Subtype.ext hy⟩
  have hq : Function.Surjective q := a.symm.surjective.comp hk
  have hqker : q.ker ≤ center A := by
    intro x hx
    apply hjker
    have he : k x = 1 := a.symm.injective (hx.trans a.symm.map_one.symm)
    exact congrArg Subtype.val he
  have hcore : (SemidirectProduct.inl : Coord J →* RadicalLevi J).range ≤
      pCore 2 (RadicalLevi J) := by
    have hn : (SemidirectProduct.inl : Coord J →* RadicalLevi J).range.Normal := by
      rw [SemidirectProduct.range_inl_eq_ker_rightHom]
      infer_instance
    exact le_sSup ⟨hn,(Coord.isPGroup (J := J)).of_surjective
      (SemidirectProduct.inl : Coord J →* RadicalLevi J).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)⟩
  have hz : centralizer (pCore 2 (RadicalLevi J) : Set (RadicalLevi J)) ≤
      center (RadicalLevi J) := by
    rw [← Flag.Center.centralizer_inl_eq_center J c hc]
    exact centralizer_le hcore
  exact centered_commutator_eq_bot_of_central_cover q hq hqker hz W hW hcomm
end Theory.SpecificGroups.UnitaryFive
