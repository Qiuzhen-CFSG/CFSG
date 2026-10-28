module

public import Theory.Representation.G2BinaryDerivedRatios
public import Theory.Representation.G2OrthogonalCover
public import Theory.AtlasPort.LinearGroups.G2.BinaryCore

/-!
# Offenders on the binary natural and Weyl G₂ modules

The octonion norm forces a trace-zero representative fixed modulo the scalar
line to be fixed itself. The third isomorphism theorem therefore identifies
the quotients by fixed spaces in the Weyl and natural modules, for every
actor subgroup. Their fixed-space dimensions differ by one, so they have
exactly the same best offenders.

The existing natural offender classification identifies these with conjugates
of the A–B–C elementary eight. We identify that subgroup with the literal
BinaryCore coordinates and transport the derived rank bound. This supplies
the model premises used in the original marked geometry of 14.7.55.

Source: Aschbacher–Smith B.4.6 and 14.7.54–55, printed pp.88–90,1065–1066.
Root coordinates retain the ATLAS attribution in LICENSES/ATLAS.txt.
-/

public noncomputable section

open Subgroup Representation Representation.BinaryOffender
open Atlas.SplitOctonion
namespace Atlas.G2.Natural.BinaryModelOffenders
open NaturalOffenders
local notation "𝔽" => ZMod 2
local notation "τ" => Natural.action 𝔽
local notation "σ" => traceZeroAction 𝔽

/-- The two concrete definitions of the A–B–C elementary eight agree. -/
theorem elementary_eq : BinaryCore.elementary = EvenTwoRank.elementary 𝔽 := by
  ext g
  constructor
  · rintro ⟨x,⟨hd,he⟩,rfl⟩
    refine ⟨Multiplicative.ofAdd ![x.a,x.b,x.c],?_⟩
    change unipotentProduct (EvenTwoRank.elementaryParameters 𝔽 _) =
      unipotentProduct (BinaryCore.parameters x)
    congr 1
    simp [EvenTwoRank.elementaryParameters,BinaryCore.parameters,hd,he]
  · rintro ⟨x,rfl⟩
    refine ⟨⟨x.toAdd 0,x.toAdd 1,x.toAdd 2,0,0⟩,⟨rfl,rfl⟩,?_⟩
    rfl

private theorem norm_scalar_add {F : Type*} [Field F] (r : F) (x : Carrier F) :
    Atlas.SplitOctonion.norm (r • unit + x) =
      r^2 + r * trace x + Atlas.SplitOctonion.norm x := by
  simp only [Atlas.SplitOctonion.norm,unit,Pi.add_apply,Pi.smul_apply,smul_eq_mul,trace]
  simp
  ring

/-- Norm preservation reflects fixedness through the actual scalar quotient. -/
theorem natural_fix_iff_weyl_fix (g : Model 𝔽) (x : TraceZero 𝔽) :
    τ g (mk 𝔽 x) = mk 𝔽 x ↔ σ g x = x := by
  rw [action_mk]
  constructor
  · intro h
    obtain ⟨r,hr⟩ := (mk_eq_mk_iff 𝔽 _ _).mp h
    have he : (σ g x).val = r • unit + x.val := eq_add_of_sub_eq hr.symm
    have hn : Atlas.SplitOctonion.norm (σ g x).val = Atlas.SplitOctonion.norm x.val :=
      automorphism_norm g x.val
    rw [he,norm_scalar_add,show trace x.val=0 from x.property,mul_zero,add_zero] at hn
    have hr2 : r^2 = 0 := add_right_cancel (show r^2 + Atlas.SplitOctonion.norm x.val =
      0 + Atlas.SplitOctonion.norm x.val by simpa only [zero_add] using hn)
    have hr0 : r=0 := eq_zero_of_pow_eq_zero hr2
    apply Subtype.ext
    simpa only [hr0,zero_smul,zero_add] using he
  · exact congrArg (mk 𝔽)

/-- Every natural fixed vector has a fixed Weyl lift, for the same actor. -/
theorem weyl_fixedSpace_map (A : Subgroup (Model 𝔽)) :
    (fixedSpace σ A).map (mk 𝔽) = fixedSpace τ A := by
  ext v
  constructor
  · rintro ⟨x,hx,rfl⟩ g
    exact (natural_fix_iff_weyl_fix g.val x).mpr (hx g)
  · intro hv
    obtain ⟨x,rfl⟩ := mk_surjective 𝔽 v
    exact ⟨x,fun g => (natural_fix_iff_weyl_fix g.val x).mp (hv g),rfl⟩

/-- The actual Weyl and natural fixed codimensions agree for every subgroup. -/
theorem weyl_fixedCodim (A : Subgroup (Model 𝔽)) :
    fixedCodim σ A = fixedCodim τ A := by
  have hs : scalarLine 𝔽 ≤ fixedSpace σ A := by
    rw [scalarLine,Submodule.span_singleton_le_iff_mem]
    intro g
    exact traceZeroAction_identity 𝔽 g.val
  have hd := (Submodule.quotientQuotientEquivQuotient (scalarLine 𝔽)
    (fixedSpace σ A) hs).finrank_eq
  change Module.finrank 𝔽 (Space 𝔽 ⧸ (fixedSpace σ A).map (mk 𝔽)) = _ at hd
  rw [weyl_fixedSpace_map] at hd
  exact hd.symm

/-- The scalar line accounts for the one additional Weyl fixed dimension. -/
theorem weyl_fixed_finrank (A : Subgroup (Model 𝔽)) :
    Module.finrank 𝔽 (fixedSpace σ A) = Module.finrank 𝔽 (fixedSpace τ A) + 1 := by
  have hw := fixedCodim_add_finrank σ A
  have hn := fixedCodim_add_finrank τ A
  rw [weyl_fixedCodim,OrthogonalCover.finrank_traceZero] at hw
  rw [finrank_space] at hn
  omega

/-- Every subgroup weight comparison is preserved by the scalar quotient. -/
theorem weyl_bestOffender_iff_natural (A : Subgroup (Model 𝔽)) :
    IsBestOffender σ A ↔ IsBestOffender τ A := by
  have hw (B : Subgroup (Model 𝔽)) : weight σ B = weight τ B + 1 := by
    simp only [weight,weyl_fixed_finrank,Nat.add_assoc]
  constructor
  · rintro ⟨hA,hbest⟩
    refine ⟨hA,fun B hB => ?_⟩
    have h := hbest B hB
    rw [hw,hw] at h
    omega
  · rintro ⟨hA,hbest⟩
    refine ⟨hA,fun B hB => ?_⟩
    rw [hw,hw]
    exact Nat.add_le_add_right (hbest B hB) 1

/-- The natural best offenders are precisely conjugates of the marked root eight. -/
theorem natural_bestOffender (A : Subgroup (Model 𝔽)) :
    IsBestOffender τ A ↔ ∃ g : Model 𝔽,
      BinaryCore.elementary.map (MulAut.conj g).toMonoidHom = A := by
  have hh := natural_bestOffender_iff_conjugate (F := 𝔽) (n := 1)
    (by norm_num) (by decide) A
  change IsBestOffender τ A ↔ _ at hh
  rw [elementary_eq]
  exact hh.trans (exists_congr fun _ => eq_comm)

/-- The Weyl best offenders are precisely the same marked conjugacy class. -/
theorem weyl_bestOffender (A : Subgroup (Model 𝔽)) :
    IsBestOffender σ A ↔ ∃ g : Model 𝔽,
      BinaryCore.elementary.map (MulAut.conj g).toMonoidHom = A :=
  (weyl_bestOffender_iff_natural A).trans (natural_bestOffender A)

/-- Elementary subgroups of the actual binary derived group have rank at most two. -/
theorem rank_le_two (A : Subgroup (Model 𝔽))
    (hAD : A ≤ commutator (Model 𝔽)) (hA : IsElementaryTwo A) : rank A ≤ 2 := by
  let D := commutator (Model 𝔽)
  have he : (A.subgroupOf D).map D.subtype = A := map_subgroupOf_eq_of_le hAD
  let : IsElementaryAbelian 2 A := hA.2
  have hAs : IsElementaryTwo (A.subgroupOf D) := by
    refine ⟨?_,IsElementaryAbelian.subgroupOf (p := 2) hAD⟩
    intro hh
    rw [hh,Subgroup.map_bot] at he
    exact hA.1 he.symm
  have hh := BinaryNormalizer.derived_rank_le_two (A.subgroupOf D) hAs
  have hr := rank_map_injective D.subtype D.subtype_injective (A.subgroupOf D)
  rw [he] at hr
  omega

/-- An elementary subgroup of rank below three cannot offend on the natural module. -/
theorem natural_small_rank_bound (A : Subgroup (Model 𝔽)) (hA : IsElementaryTwo A)
    (hr : rank A < 3) : rank A < fixedCodim τ A := by
  by_contra! hc
  have hh := natural_offender_rank (F := 𝔽) (n := 1) (by norm_num) (by decide)
    A ⟨hA,hc⟩
  omega

/-- The same strict bound holds on the Weyl module. -/
theorem weyl_small_rank_bound (A : Subgroup (Model 𝔽)) (hA : IsElementaryTwo A)
    (hr : rank A < 3) : rank A < fixedCodim σ A := by
  rw [weyl_fixedCodim]
  exact natural_small_rank_bound A hA hr

end Atlas.G2.Natural.BinaryModelOffenders
