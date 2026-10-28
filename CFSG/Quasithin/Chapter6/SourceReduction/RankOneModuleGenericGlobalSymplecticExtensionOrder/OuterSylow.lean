module
public import Theory.SpecificGroups.SymplecticFour.SourceFusionOrder.OuterSylow
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.InvolutionTransfer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.NativeLift

/-!
# Outer involutions and centralizer growth in the original symplectic pair

The common-normalizer lift restricts to a faithful native action of the
original T with exact inner preimage S. Consequently an outer involution f
has |C_S(f)| ≤ q² and |C_T(f)| ≤ q²[T:S] ≤ q²n < q⁴. Every full ambient
involution centralizer already has Sylow order at least q⁴, so C_T(f) cannot
be Sylow there.

If S<T, the native image of the whole middle contains the full pure Borel.
Removing a Borel-inner factor gives an actual field involution in that image.
Sylow conjugacy inside the original middle then puts its lift in T outside S.
The final theorem constructs the strictly larger Sylow subgroup of C_G(f)
used in the contrary argument of F.4.37, rather than assuming a split of T.

Both orientations and n=2 are retained, as are the whole residual and all
original source hypotheses. The normalizer argument excluding this growth,
including the Sp₄(4) binary-fixed-group exception, is still required. Neither
S=T nor the full-extension order comparison is asserted here.

Source: Aschbacher–Smith F.4.37–38, printed pp.293–294, applied to 5.3.1–3,
pp.658–659 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
include d h hH hp hm hF he

omit hp [Field F] [Finite F] [CharP F 2] hm hF he in
private theorem sylow_mem_pure_iff (g : T) :
    g.val ∈ (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
      ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G) ↔
        g.val ∈ sourceS L H := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  let C := P 0 ⊓ P 1
  have hf := d.hypothesisF11 h hH.1.1.2
  have hs : Chapter1.IsSylowIn 2 (sourceS L H) C := by
    change Chapter1.IsSylowIn 2 (sourceS L H) (P 0 ⊓ P 1)
    rw [show P 0 ⊓ P 1 = ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) from
      ChapterF.Source.lemma_F_1_3_6 hf]
    exact hf.sylow_commonBorel
  obtain ⟨R,hR⟩ := hs
  have hRT : (R : Subgroup C) ≤ (T : Subgroup G).subgroupOf C := by
    intro x hx
    exact sourceS_le_sylow h.sylow_normalizes hH.1.1.2
      (hR ▸ mem_map_of_mem C.subtype hx)
  have hTR : (T : Subgroup G).subgroupOf C = R :=
    R.is_maximal' (T.isPGroup'.comap_subtype (K := C)) hRT
  constructor
  · intro hgC
    have hgR : (⟨g.val,hgC⟩ : C) ∈ (R : Subgroup C) := by
      rw [←hTR]
      exact g.property
    exact hR ▸ mem_map_of_mem C.subtype hgR
  · intro hg
    exact ⟨(show sourceS L H ≤ P 0 from le_sup_right.trans le_sup_left) hg,
      (show sourceS L H ≤ P 1 from le_sup_right.trans le_sup_left) hg⟩

/-- The original Sylow acts faithfully on the native group, with exactly S as its inner preimage. -/
theorem Preparation.symplectic_sylow_native_action :
    ∃ ρ : T →* MulAut (Sp F), Function.Injective ρ ∧
      (∀ g, DiagramAutomorphisms.PreservesDiagram (ρ g)) ∧
      ∀ g, ρ g ∈ MulAut.innerSubgroup (Sp F) ↔ g.val ∈ sourceS L H := by
  let D := normalizer (L : Set G) ⊓ normalizer (residual H : Set G)
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  let C := P 0 ⊓ P 1
  have hTD : (T : Subgroup G) ≤ D :=
    le_inf h.sylow_normalizes (hH.1.1.2.trans (le_normalizer_residual H))
  obtain ⟨_,hlift⟩ := d.symplectic_native_middle_lift h hH hp F hm hF he
  have hact : ∃ σ : D →* SourceNormalizerExtension.flagAutomorphisms F,
      Function.Injective σ ∧
      ∀ g, (σ g).val ∈ MulAut.innerSubgroup (Sp F) ↔ g.val ∈ C := by
    rcases hlift with ⟨_,σ,hσ,_,_,hi⟩ | ⟨_,σ,hσ,_,_,hi⟩
    · exact ⟨σ,hσ,hi⟩
    · exact ⟨σ,hσ,hi⟩
  obtain ⟨σ,hσ,hi⟩ := hact
  let ρ : T →* MulAut (Sp F) :=
    (SourceNormalizerExtension.flagAutomorphisms F).subtype.comp (σ.comp (inclusion hTD))
  refine ⟨ρ,Subtype.val_injective.comp (hσ.comp (inclusion_injective hTD)),
    fun g => SourceNormalizerExtension.flag_preservesDiagram _,?_⟩
  intro g
  change (σ (inclusion hTD g)).val ∈ MulAut.innerSubgroup (Sp F) ↔ _
  rw [hi]
  exact sylow_mem_pure_iff d h hH g

/-- The centralizer in S of an outer involution has order at most q². -/
theorem Preparation.symplectic_outer_inner_centralizer_bound
    (f : T) (hf : orderOf f=2) (hfo : f.val ∉ sourceS L H) :
    Nat.card (sourceS L H ⊓ centralizer ({f.val} : Set G) : Subgroup G) ≤ Nat.card F^2 := by
  obtain ⟨ρ,hρ,hpres,hi⟩ := d.symplectic_sylow_native_action h hH hp F hm hF he
  let V := sourceS L H ⊓ centralizer ({f.val} : Set G)
  have hVT : V ≤ (T : Subgroup G) :=
    inf_le_left.trans (sourceS_le_sylow h.sylow_normalizes hH.1.1.2)
  let j : V →* MulAut (Sp F) := ρ.comp (inclusion hVT)
  have hj : Function.Injective j := hρ.comp (inclusion_injective hVT)
  have hVi : j.range ≤ MulAut.innerSubgroup (Sp F) := by
    rintro _ ⟨v,rfl⟩
    exact (hi (inclusion hVT v)).mpr v.property.1
  have hVc : j.range ≤ centralizer ({ρ f} : Set (MulAut (Sp F))) := by
    rintro _ ⟨v,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change ρ (inclusion hVT v) * ρ f = ρ f * ρ (inclusion hVT v)
    rw [←map_mul,←map_mul]
    apply congrArg ρ
    exact Subtype.ext (mem_centralizer_singleton_iff.mp v.property.2)
  have hm' : 1 < m := (d.symplectic_amalgam_blocks h hH.1.1.2 hp F hm hF he).1.symm ▸ h.exponent
  have hb := SourceFusionOrder.inner_outer_centralizer_card hm' hF (ρ f)
    ((orderOf_injective ρ hρ f).trans hf) (hpres f) (fun hh => hfo ((hi f).mp hh))
    j.range ((T.isPGroup'.to_le hVT).of_surjective j.rangeRestrict j.rangeRestrict_surjective) hVi hVc
  rwa [←Nat.card_congr (MonoidHom.ofInjective hj).toEquiv] at hb

/-- The entire centralizer in T retains the actual outer index [T:S]. -/
theorem Preparation.symplectic_outer_sylow_centralizer_bound
    (f : T) (hf : orderOf f=2) (hfo : f.val ∉ sourceS L H) :
    Nat.card ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G) : Subgroup G) ≤
      Nat.card F^2 * (sourceS L H).relIndex (T : Subgroup G) := by
  let V := (T : Subgroup G) ⊓ centralizer ({f.val} : Set G)
  have hST := sourceS_le_sylow h.sylow_normalizes hH.1.1.2
  have heq : sourceS L H ⊓ V = sourceS L H ⊓ centralizer ({f.val} : Set G) := by
    rw [←inf_assoc,inf_eq_left.mpr hST]
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) (sourceS L H ⊓ V) V bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_right] at hc
  calc
    Nat.card V = Nat.card (sourceS L H ⊓ V : Subgroup G) * (sourceS L H).relIndex V := hc.symm
    _ ≤ Nat.card F^2 * (sourceS L H).relIndex (T : Subgroup G) := by
      apply Nat.mul_le_mul
      · rw [heq]
        exact d.symplectic_outer_inner_centralizer_bound h hH hp F hm hF he f hf hfo
      · exact relIndex_le_of_le_right inf_le_left index_ne_zero_of_finite

/-- The outer-involution centralizer in T is strictly smaller than the inner Sylow. -/
theorem Preparation.symplectic_outer_sylow_centralizer_lt
    (f : T) (hf : orderOf f=2) (hfo : f.val ∉ sourceS L H) :
    Nat.card ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G) : Subgroup G) < Nat.card F^4 := by
  have hb := d.symplectic_outer_sylow_centralizer_bound h hH hp F hm hF he f hf hfo
  have hn : (sourceS L H).relIndex (T : Subgroup G) ≤ n :=
    Nat.le_of_dvd (by have := h.exponent; omega) (d.symplectic_source_sylow_index_dvd h hH hp F hm hF he)
  have hmn := (d.symplectic_amalgam_blocks h hH.1.1.2 hp F hm hF he).1
  have hnF : n < Nat.card F^2 := by
    rw [hF,hmn,←pow_mul]
    exact lt_of_lt_of_le (Nat.lt_two_pow_self (n := n))
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : n ≤ n*2))
  calc
    _ ≤ Nat.card F^2 * n := hb.trans (Nat.mul_le_mul_left _ hn)
    _ < Nat.card F^2 * Nat.card F^2 := Nat.mul_lt_mul_of_pos_left hnF (pow_pos Nat.card_pos _)
    _ = Nat.card F^4 := by ring

/-- The full ambient centralizer has larger Sylow order than C_T(f). -/
theorem Preparation.symplectic_outer_centralizer_not_sylow
    (f : T) (hf : orderOf f=2) (hfo : f.val ∉ sourceS L H) :
    ¬ Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G))
      (centralizer ({f.val} : Set G)) := by
  rintro ⟨P,hP⟩
  have hb := d.symplectic_involution_centralizer_sylow_lower_bound h hH hp F hm hF he
    f.val ((Subgroup.orderOf_coe f).trans hf) P
  have hc : Nat.card ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G) : Subgroup G) = Nat.card P := by
    rw [←hP,card_map_of_injective Subtype.val_injective]
  rw [←hc] at hb
  exact (not_lt_of_ge hb) (d.symplectic_outer_sylow_centralizer_lt h hH hp F hm hF he f hf hfo)

private theorem middle_native_range :
    ∃ ρ : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G) →*
        MulAut (Sp F),
      Function.Injective ρ ∧
      (∀ g, ρ g ∈ SourceNormalizerExtension.flagAutomorphisms F) ∧
      (borel (F := F)).map (MulAut.conj : Sp F →* MulAut (Sp F)) ≤ ρ.range ∧
      ∀ g, ρ g ∈ MulAut.innerSubgroup (Sp F) ↔
        g.val ∈ (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
          ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G) := by
  obtain ⟨_,hlift⟩ := d.symplectic_native_middle_lift h hH hp F hm hF he
  rcases hlift with ⟨a,σ,hσ,hs,_,hi⟩ | ⟨a,σ,hσ,hs,_,hi⟩
  · let ρ := (SourceNormalizerExtension.flagAutomorphisms F).subtype.comp σ
    refine ⟨ρ,Subtype.val_injective.comp hσ,fun g => (σ g).property,?_,hi⟩
    rintro _ ⟨b,hb,rfl⟩
    let c := a.comparison.middle.symm ⟨b,hb⟩
    refine ⟨inclusion a.middle_le c,?_⟩
    have hh : σ (inclusion a.middle_le c) =
        SourceNormalizerExtension.innerBorel (a.comparison.middle c) :=
      SourceNormalizerExtension.restriction_injective
        ((DFunLike.congr_fun hs _).trans (a.native_inner_action c))
    change (σ (inclusion a.middle_le c)).val = _
    rw [hh]
    simp only [SourceNormalizerExtension.innerBorel_apply,c,a.comparison.middle.apply_symm_apply]
  · let ρ := (SourceNormalizerExtension.flagAutomorphisms F).subtype.comp σ
    refine ⟨ρ,Subtype.val_injective.comp hσ,fun g => (σ g).property,?_,hi⟩
    rintro _ ⟨b,hb,rfl⟩
    let c := a.comparison.middle.symm ⟨b,hb⟩
    refine ⟨inclusion a.middle_le c,?_⟩
    have hh : σ (inclusion a.middle_le c) =
        SourceNormalizerExtension.innerBorel (a.comparison.middle c) :=
      SourceNormalizerExtension.reverseRestriction_injective
        ((DFunLike.congr_fun hs _).trans (a.native_inner_action_reverse c))
    change (σ (inclusion a.middle_le c)).val = _
    rw [hh]
    simp only [SourceNormalizerExtension.innerBorel_apply,c,a.comparison.middle.apply_symm_apply]

/-- Properness of S constructs an actual outer involution in T, with no splitting premise. -/
theorem Preparation.symplectic_outer_involution_exists
    (hst : sourceS L H ≠ (T : Subgroup G)) :
    ∃ f : T, orderOf f=2 ∧ f.val ∉ sourceS L H := by
  let D := normalizer (L : Set G) ⊓ normalizer (residual H : Set G)
  have hTD : (T : Subgroup G) ≤ D :=
    le_inf h.sylow_normalizes (hH.1.1.2.trans (le_normalizer_residual H))
  obtain ⟨ρ,hρ,hflag,hB,hi⟩ := middle_native_range d h hH hp F hm hF he
  have hm' : 1 < m := (d.symplectic_amalgam_blocks h hH.1.1.2 hp F hm hF he).1.symm ▸ h.exponent
  have hnle : ¬ (T : Subgroup G) ≤ sourceS L H := fun hh =>
    hst (le_antisymm (sourceS_le_sylow h.sylow_normalizes hH.1.1.2) hh)
  obtain ⟨t,ht,htS⟩ := SetLike.not_le_iff_exists.mp hnle
  let tD : D := ⟨t,hTD ht⟩
  have hto : ρ tD ∉ MulAut.innerSubgroup (Sp F) := by
    intro hh
    exact htS ((sylow_mem_pure_iff d h hH ⟨t,ht⟩).mp ((hi tD).mp hh))
  have htp : ∃ k, orderOf (ρ tD)=2^k := by
    obtain ⟨k,hk⟩ := T.isPGroup'.exists_orderOf_eq_pow (⟨t,ht⟩ : T)
    refine ⟨k,?_⟩
    exact (orderOf_injective ρ hρ tD).trans ((Subgroup.orderOf_coe tD).symm.trans
      ((Subgroup.orderOf_coe (⟨t,ht⟩ : T)).trans hk))
  obtain ⟨τ,hτ,hτV⟩ := SourceFusionOrder.flag_overgroup_field_involution hF hm'
    ρ.range hB (ρ tD) ⟨tD,rfl⟩ (hflag tD) hto htp
  obtain ⟨x,hx⟩ := hτV
  have hfieldinj : Function.Injective (DiagramAutomorphisms.fieldAutomorphismHom (F := F)) := by
    intro a b hh
    apply DiagramAutomorphisms.InvolutionNormalForms.outerFieldHom_injective
    exact congrArg (QuotientGroup.mk' (MulAut.innerSubgroup (Sp F))) hh
  have hxo : orderOf x=2 := by
    rw [←orderOf_injective ρ hρ,hx]
    exact (orderOf_injective DiagramAutomorphisms.fieldAutomorphismHom hfieldinj τ).trans hτ
  have hxi : ρ x ∉ MulAut.innerSubgroup (Sp F) := by
    rw [hx]
    intro hh
    have hh' := DiagramAutomorphisms.InvolutionNormalForms.field_eq_one_of_inner τ hh
    rw [hh',orderOf_one] at hτ
    omega
  obtain ⟨y,hy⟩ := (T.subtype hTD).exists_isConj_of_orderOf_eq_prime_pow (x := x) (n := 1)
    (by change orderOf x = 2; exact hxo)
  let f : T := ⟨y.val.val,y.property⟩
  have hyo : orderOf y.val=2 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hy
    rw [←hg]
    exact ((MulAut.conj g).orderOf_eq x).trans hxo
  refine ⟨f,?_,?_⟩
  · rw [←Subgroup.orderOf_coe]
    exact (Subgroup.orderOf_coe y.val).trans hyo
  · intro hfS
    have hfi : ρ y.val ∈ MulAut.innerSubgroup (Sp F) :=
      (hi y.val).mpr ((sylow_mem_pure_iff d h hH f).mpr hfS)
    obtain ⟨g,hg⟩ := isConj_iff.mp hy.symm
    apply hxi
    have hh := (inferInstance : (MulAut.innerSubgroup (Sp F)).Normal).conj_mem
      (ρ y.val) hfi (ρ g)
    have heq : ρ g * ρ y.val * (ρ g)⁻¹ = ρ x := by
      simpa only [map_mul,map_inv] using congrArg ρ hg
    exact heq ▸ hh

/-- If the inner Sylow were proper, there would be an actual outer
involution whose ambient centralizer contains a strictly larger two-group
than its centralizer in T. This is the contrary setup of F.4.37. -/
theorem Preparation.symplectic_outer_involution_centralizer_growth
    (hst : sourceS L H ≠ (T : Subgroup G)) :
    ∃ f : T, orderOf f=2 ∧ f.val ∉ sourceS L H ∧
      ∃ R : Sylow 2 (centralizer ({f.val} : Set G)),
        (T : Subgroup G) ⊓ centralizer ({f.val} : Set G) <
          (R : Subgroup (centralizer ({f.val} : Set G))).map
            (centralizer ({f.val} : Set G)).subtype := by
  obtain ⟨f,hf,hfo⟩ := d.symplectic_outer_involution_exists h hH hp F hm hF he hst
  let C := centralizer ({f.val} : Set G)
  obtain ⟨R,hR⟩ := (T.isPGroup'.comap_subtype (K := C)).exists_le_sylow
  refine ⟨f,hf,hfo,R,lt_of_le_of_ne ?_ ?_⟩
  · intro x hx
    exact mem_map_of_mem C.subtype (hR (show (⟨x,hx.2⟩ : C) ∈
      (T : Subgroup G).subgroupOf C from hx.1))
  · intro heq
    have hlt := d.symplectic_outer_sylow_centralizer_lt h hH hp F hm hF he f hf hfo
    have hlo := d.symplectic_involution_centralizer_sylow_lower_bound h hH hp F hm hF he
      f.val ((Subgroup.orderOf_coe f).trans hf) R
    rw [heq,card_map_of_injective Subtype.val_injective] at hlt
    exact (not_lt_of_ge hlo) hlt
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
