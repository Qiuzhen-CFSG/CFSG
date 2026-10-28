module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedFactorOrbit.SourceGeometry
public import Theory.Representation.SL2NaturalOffenders.CoordinateSwap
public import Theory.SpecificGroups.SL2.OddFixedVectors
/-!
# Odd-order fixed points from the actual paired natural source

The same marked quotient map and actual Sylow exchanger kill both coordinates
of a central Sylow element fixed by a noncentral odd-order element. The kernel is the
original residual-fixed subgroup, including every retained central cover.
No field-size assumption or compatibility with an independent marking is used.

Source: Aschbacher--Smith E.2.3 and 10.2.3(4), pp.216--217 and746.
-/
public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterB.RankOneBaumann.PairedFactorOrbit
open QuasisimpleSource SourceInduction CFSG.Quasithin.ChapterB
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
set_option backward.isDefEq.respectTransparency false in
theorem paired_source_odd_fixed_center
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hker)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first)
    (hZU : omegaOneCenterAmbient (T : Subgroup G) ≤ U)
    (b : pResidual 2 G) (m : ℕ) (hm : Odd m) (hb : b^m=1)
    (hmove : (b:G) ∉ centralizer (U : Set G)) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer ({(b:G)} : Set G) =
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G) := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  have hcore : pCore 2 H = ⊥ := by
    let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [←pCore_map_iso 2 e,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hn : q.ker ≠ ⊤ := by
    intro he
    exact hJ (hker ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T:Subgroup G) ≤ ⊤)))
  have hp := (minimalParabolic_reduced_image T hP q hq hcore hn).2
  have hff : IsFFModule α := by
    obtain hf | ⟨_,hf,_,_,_⟩ := lemma_B_2_7 U q hq hker T
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hf.1)).elim
    · exact hf
  have hc : c.quotientMap.ker = fixedSpace α ((pResidual 2 G).map q) := by
    rw [map_pResidual_of_surjective 2 q hq]
    exact source_offender_pair_linear_kernel α (T.mapSurjective hq) hp hff hcore F c
  have hJY : (elementaryAbelianMaxJ (T : Subgroup G)).map q ≤ Y :=
    thompson_image_le_offender_layer T U q hq hker
      (hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)) Y le_rfl
  have hRY := residual_image_le_normal_thompson_layer T hP U hU hJ q hq hker Y hJY
  let bY : Y := ⟨q b,hRY (mem_map_of_mem q b.property)⟩
  have hbY : bY^m=1 := by
    apply Subtype.ext
    change (q (b:G))^m=1
    rw [←map_pow,show (b:G)^m=1 from congrArg (pResidual 2 G).subtype hb,map_one]
  have hbYne : bY ≠ 1 := by
    intro he
    apply hmove
    rw [←hker]
    exact congrArg Y.subtype he
  let p := c.action.groupEquiv bY
  have hpm : p^m=1 := by dsimp [p]; rw [←map_pow,hbY,map_one]
  have hpne : p≠1 := by
    intro he
    exact hbYne (c.action.groupEquiv.injective (he.trans c.action.groupEquiv.map_one.symm))
  have hne : p.1 ≠ 1 ∨ p.2 ≠ 1 := by
    by_cases h₁ : p.1 = 1
    · exact Or.inr (fun h₂ => hpne (Prod.ext h₁ h₂))
    · exact Or.inl h₁
  obtain ⟨ρ,_,hnat,he,_,_⟩ := source_images_and_fixedSpace T hP U hU hJ q hq hker d F c hexchange
  obtain ⟨t,ht₁,ht₂⟩ := hexchange
  obtain ⟨g,hg,hgt⟩ := t.property
  obtain ⟨f,hf⟩ := SL2NaturalOffenders.exchanged_pair_coordinate_equiv Y c.action.groupEquiv ρ
    (fun a v => hnat a v) (t:H)
    (by rw [c.first_eq,c.second_eq]; exact ht₁)
    (by rw [c.second_eq,c.first_eq]; exact ht₂)
  apply le_antisymm
  · intro z hz
    let v : Additive U := Additive.ofMul ⟨z,hZU hz.1⟩
    have htfix : α (q g) v = v := by
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [NormalElementaryQuotient.representation_apply]
      change g*z*g⁻¹=z
      rw [((mem_omegaOneCenterAmbient_iff _ _).mp hz.1).2.2 g hg,mul_inv_cancel_right]
    have hbfix : α (q b) v = v := by
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [NormalElementaryQuotient.representation_apply]
      change (b:G)*z*(b:G)⁻¹=z
      rw [hz.2 b (Set.mem_singleton _),mul_inv_cancel_right]
    have hrel : (c.quotientMap v).1 = f (c.quotientMap v).2 := by
      have hh := he (q g) v
      rw [htfix,hgt] at hh
      exact (congrArg Prod.fst hh).trans (hf _)
    have hfixed := c.quotientMap_action bY v
    change c.quotientMap (α (q b) v) = _ at hfixed
    rw [hbfix] at hfixed
    have hzv : c.quotientMap v=0 := by
      rcases hne with h₁ | h₂
      · have h1 := Matrix.SL2.odd_power_fixed_eq_zero p.1 m hm
          (congrArg Prod.fst hpm) h₁ (c.quotientMap v).1
          (congrArg Prod.fst hfixed.symm)
        have h2 : (c.quotientMap v).2=0 := by
          apply f.injective
          rw [←hrel,h1,map_zero]
        exact Prod.ext h1 h2
      · have h2 := Matrix.SL2.odd_power_fixed_eq_zero p.2 m hm
          (congrArg Prod.snd hpm) h₂ (c.quotientMap v).2
          (congrArg Prod.snd hfixed.symm)
        have h1 : (c.quotientMap v).1=0 := by rw [hrel,h2,map_zero]
        exact Prod.ext h1 h2
    have hv : v ∈ fixedSpace α ((pResidual 2 G).map q) := by rw [←hc]; exact hzv
    exact ⟨hz.1,(NormalElementaryQuotient.mem_fixedSpace_image U q hq hker _ v).mp hv⟩
  · intro z hz
    exact ⟨hz.1,fun x hx => Set.mem_singleton_iff.mp hx ▸ hz.2 b b.property⟩
end CFSG.Quasithin.ChapterB.RankOneBaumann.PairedFactorOrbit
