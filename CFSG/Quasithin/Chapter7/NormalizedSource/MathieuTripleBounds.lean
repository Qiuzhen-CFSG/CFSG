module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTripleFixer
public import Theory.Representation.FiniteFieldSemilinearDisplacement.Saturation
public import CFSG.Quasithin.ChapterH.Section10To12.TripleDisplacement.Odd
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer
/-!
# The full triple Mathieu near-offender and odd-displacement bounds

Inner common fixed spaces have even codimension. The native involution
minimum and the four-element pointwise-fixer bound exclude an inner
(F-1)-offender. A semilinear outer actor attaining half-space fixed dimension
would inject the whole elementary actor into the field automorphism group;
its rank would then be one, contradicting displacement six.

Odd-prime actors lie in the cover and move at least eight dimensions.
These unconditional model estimates feed NonFFSourceMathieuTriple on the
literal chosen-orbit automizer, proving the triple-cover branch impossible.
Source: Aschbacher--Smith H.12.1(7),(11),(12), Table 7.2.1,7.4.1 and7.5.2,
printed pp.393--395,698--700.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTriple
open Representation.SL2FourNatural
open Sporadic.Mathieu.M22TripleCover.Unitary Sporadic.Mathieu.M22TripleCover.NoFF
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
open Sporadic.Mathieu Representation Representation.BinaryOffender Subgroup Theory.GroupTheory
open scoped Matrix
noncomputable section

private theorem elementary_rank_le {G : Type*} [Group G] [Finite G]
    {A : Subgroup G} (hA : IsElementaryTwo A) {r : ℕ} (hr : primeRank 2 G ≤ r) :
    rank A ≤ r := by
  have hc := (primeRank_le_iff_elementary_card_le G).mp hr A hA.2
  have hh := Nat.log_mono_right (b := 2) hc
  simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hh

private theorem fixedCodim_mono {G W : Type*} [Group G]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) {A B : Subgroup G} (h : A ≤ B) :
    fixedCodim ρ A ≤ fixedCodim ρ B := by
  have hm := Submodule.finrank_mono (fixedSpace_antitone ρ h)
  have hA := fixedCodim_add_finrank ρ A
  have hB := fixedCodim_add_finrank ρ B
  omega

private theorem field_intertwines (a : M22TripleCover) (v : M22TripleCover.BinarySpace) :
    binaryCoordinates (M22TripleCover.binaryRepresentation a v) =
      fieldAction a (binaryCoordinates v) := by
  change binaryCoordinates (M22TripleCover.binaryRepresentation a v) =
    binaryCoordinates (M22TripleCover.binaryRepresentation a
      (binaryCoordinates.symm (binaryCoordinates v)))
  rw [binaryCoordinates.symm_apply_apply]

/-- The common fixed codimension of an inner actor is even, using its actual F4 action. -/
theorem inner_fixedCodim_even (A : Subgroup M22TripleCover) :
    Even (fixedCodim M22TripleCover.binaryRepresentation A) := by
  let P := Representation.invariants (fieldAction.comp A.subtype)
  have hm : (fixedSpace M22TripleCover.binaryRepresentation A).map binaryCoordinates.toLinearMap =
      P.restrictScalars (ZMod 2) := by
    ext v
    constructor
    · rintro ⟨w,hw,rfl⟩ a
      exact (field_intertwines a w).symm.trans (congrArg binaryCoordinates (hw a))
    · intro hv
      refine ⟨binaryCoordinates.symm v,?_,binaryCoordinates.apply_symm_apply v⟩
      intro a
      apply binaryCoordinates.injective
      change binaryCoordinates (M22TripleCover.binaryRepresentation a (binaryCoordinates.symm v)) = binaryCoordinates (binaryCoordinates.symm v)
      rw [field_intertwines,binaryCoordinates.apply_symm_apply]
      exact hv a
  have he := (binaryCoordinates.ofSubmodules _ _ hm).finrank_eq
  have hp := Module.finrank_mul_finrank (ZMod 2) F P
  rw [QuadraticAlgebra.finrank_eq_two] at hp
  have hpr := ((Submodule.restrictScalarsEquiv (ZMod 2) F Vector P).restrictScalars (ZMod 2)).finrank_eq
  have hd := fixedCodim_add_finrank M22TripleCover.binaryRepresentation A
  rw [M22TripleCover.binarySpace_finrank] at hd
  have hc : fixedCodim M22TripleCover.binaryRepresentation A % 2 = 0 := by omega
  exact Nat.even_iff.mpr hc

/-- An elementary inner actor moving at most four dimensions has order at most four. -/
theorem inner_small_displacement_card (A : Subgroup M22TripleCover) (hA : IsElementaryTwo A)
    (hd : fixedCodim M22TripleCover.binaryRepresentation A ≤ 4) : Nat.card A ≤ 4 := by
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨t,ht,ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have hto : orderOf t = 2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian t ht) ht1
  obtain ⟨c,hc⟩ := isConj_iff.mp (involutions_isConj t coreGeneratorB hto coreGeneratorB_order)
  let B := A.map (MulAut.conj c).toMonoidHom
  have hB : IsElementaryTwo B := hA.map_conj c
  let : IsElementaryAbelian 2 B := hB.2
  have hBt : coreGeneratorB ∈ B := ⟨t,ht,hc⟩
  have hdimB : fixedCodim M22TripleCover.binaryRepresentation B = 4 := by
    have hle := fixedCodim_mono M22TripleCover.binaryRepresentation (Subgroup.zpowers_le.mpr hBt)
    rw [binaryCodim_involution coreGeneratorB coreGeneratorB_order] at hle
    have hh : fixedCodim M22TripleCover.binaryRepresentation B ≤ 4 := by
      simpa only [B,fixedCodim_map_conj] using hd
    omega
  have hfix : fixedSpace M22TripleCover.binaryRepresentation B =
      fixedSpace M22TripleCover.binaryRepresentation (Subgroup.zpowers coreGeneratorB) := by
    apply Submodule.eq_of_le_of_finrank_eq
      (fixedSpace_antitone M22TripleCover.binaryRepresentation (Subgroup.zpowers_le.mpr hBt))
    have h₁ := fixedCodim_add_finrank M22TripleCover.binaryRepresentation B
    have h₂ := fixedCodim_add_finrank M22TripleCover.binaryRepresentation (Subgroup.zpowers coreGeneratorB)
    rw [hdimB] at h₁
    rw [binaryCodim_involution coreGeneratorB coreGeneratorB_order] at h₂
    omega
  have hcard := commonFixer_card_le_four B
    (fun a => elemPow_eq_one_of_isElementaryAbelian a.val a.property) (by
      intro a v hv
      have hbv : binaryCoordinates.symm v ∈ fixedSpace M22TripleCover.binaryRepresentation B := by
        rw [hfix,mem_fixedSpace_zpowers_iff]
        apply binaryCoordinates.injective
        rw [field_intertwines,binaryCoordinates.apply_symm_apply]
        exact hv
      have hh := congrArg binaryCoordinates (hbv a)
      change binaryCoordinates (M22TripleCover.binaryRepresentation a (binaryCoordinates.symm v)) = binaryCoordinates (binaryCoordinates.symm v) at hh
      rw [field_intertwines,binaryCoordinates.apply_symm_apply] at hh
      exact hh)
  have he : Nat.card B = Nat.card A := Subgroup.card_map_of_injective (MulAut.conj c).injective
  omega

/-- There is no inner (F-1)-offender on the genuine triple-cover module. -/
theorem inner_fixedCodim_gap (A : Subgroup M22TripleCover) (hA : IsElementaryTwo A) :
    rank A+1 < fixedCodim M22TripleCover.binaryRepresentation A := by
  have hr := elementary_rank_le hA twoRank_le_four
  have he := inner_fixedCodim_even A
  have hnf : rank A < fixedCodim M22TripleCover.binaryRepresentation A := by
    by_contra! hh
    exact binaryRepresentation_not_isFFModule ⟨A,hA,hh⟩
  by_contra! hh
  have hd : fixedCodim M22TripleCover.binaryRepresentation A ≤ 4 := by
    obtain ⟨n,hn⟩ := he
    omega
  have hc := inner_small_displacement_card A hA hd
  have hr2 : rank A ≤ 2 := (Nat.log_mono_right (b := 2) hc).trans_eq (by decide)
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨t,ht,ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have hto : orderOf t = 2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian t ht) ht1
  have hmin := fixedCodim_mono M22TripleCover.binaryRepresentation (Subgroup.zpowers_le.mpr ht)
  rw [binaryCodim_involution t hto] at hmin
  omega

private theorem frobenius_ne_one : fieldFrobenius ≠ 1 := by
  intro he
  have h := congrArg (fun f : F ≃+* F => f QuadraticAlgebra.omega) he
  revert h
  decide +kernel

private def coefficient : actionGroup →* (F ≃+* F) := by
  classical
  exact {
    toFun g := if g ∈ coverSubgroup then 1 else fieldFrobenius
    map_one' := by simp
    map_mul' g h := by
      have hm := Subgroup.mul_mem_iff_of_index_two (a := g) (b := h) coverSubgroup_index
      have hff : fieldFrobenius * fieldFrobenius = 1 := RingEquiv.ext fieldFrobenius_involutive
      by_cases hg : g ∈ coverSubgroup <;> by_cases hh : h ∈ coverSubgroup
      · simp [hg,hh,coverSubgroup.mul_mem hg hh]
      · have hgh : g*h ∉ coverSubgroup := fun hgh => hh ((hm.mp hgh).mp hg)
        simp [hg,hh,hgh]
      · have hgh : g*h ∉ coverSubgroup := fun hgh => hg ((hm.mp hgh).mpr hh)
        simp [hg,hh,hgh]
      · have hgh : g*h ∈ coverSubgroup := hm.mpr (iff_of_false hg hh)
        simp [hg,hh,hgh,hff]
  }

private theorem coefficient_semilinear (g : actionGroup) (c : F) (v : Vector) :
    M22TripleCover.Ambient.tripleFieldAction g (c • v) =
      coefficient g c • M22TripleCover.Ambient.tripleFieldAction g v := by
  classical
  by_cases hg : g ∈ coverSubgroup
  · have he : coefficient g = 1 := if_pos hg
    rw [he]
    exact M22TripleCover.Ambient.tripleFieldAction_inner_linear g hg c v
  · have he : coefficient g = fieldFrobenius := if_neg hg
    rw [he]
    exact M22TripleCover.Ambient.tripleFieldAction_outer_semilinear g hg c v

/-- Faithfulness of the full native matrix extension. -/
theorem binaryAction_faithful : Function.Injective M22TripleCover.Ambient.binaryAction := by
  intro a b he
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  exact LinearMap.congr_fun he v

private theorem fieldAction_faithful : Function.Injective M22TripleCover.Ambient.tripleFieldAction := by
  intro a b he
  apply binaryAction_faithful
  apply LinearMap.ext
  intro v
  apply binaryCoordinates.injective
  have hh := LinearMap.congr_fun he (binaryCoordinates v)
  change binaryCoordinates (M22TripleCover.Ambient.binaryAction a
    (binaryCoordinates.symm (binaryCoordinates v))) =
    binaryCoordinates (M22TripleCover.Ambient.binaryAction b
      (binaryCoordinates.symm (binaryCoordinates v))) at hh
  simpa only [binaryCoordinates.symm_apply_apply] using hh

private theorem field_fixedCodim (A : Subgroup actionGroup) :
    fixedCodim M22TripleCover.Ambient.binaryAction A =
      fixedCodim M22TripleCover.Ambient.tripleFieldAction A := by
  simpa only [Subgroup.map_id] using fixedCodim_map_equivariant
    M22TripleCover.Ambient.binaryAction M22TripleCover.Ambient.tripleFieldAction
    (MonoidHom.id _) binaryCoordinates (fun a v => by
      change binaryCoordinates (M22TripleCover.Ambient.binaryAction a v) =
        binaryCoordinates (M22TripleCover.Ambient.binaryAction a
          (binaryCoordinates.symm (binaryCoordinates v)))
      rw [binaryCoordinates.symm_apply_apply]) A

/-- The complete near-offender gap, retaining every semilinear outer actor. -/
theorem ambient_fixedCodim_gap (A : Subgroup actionGroup) (hA : IsElementaryTwo A) :
    rank A+1 < fixedCodim M22TripleCover.Ambient.binaryAction A := by
  let : IsElementaryAbelian 2 A := hA.2
  by_cases hcover : A ≤ coverSubgroup
  · have hi : Function.Injective coverInclusion := Subgroup.inclusion_injective _
    let B := A.comap coverInclusion
    have hm : B.map coverInclusion = A := by
      apply Subgroup.map_comap_eq_self
      simpa only [coverInclusion_range] using hcover
    let : IsElementaryAbelian 2 B := IsElementaryAbelian.comap_of_injective _ hi A
    have hB : IsElementaryTwo B := ⟨fun hb => hA.1 (by simpa only [hb,Subgroup.map_bot] using hm.symm),inferInstance⟩
    have he := fixedCodim_map_equivariant M22TripleCover.binaryRepresentation
      M22TripleCover.Ambient.binaryAction coverInclusion
      (LinearEquiv.refl _ _) (fun _ _ => rfl) B
    rw [hm] at he
    have hr := rank_map_injective coverInclusion hi B
    rw [hm] at hr
    simpa only [he,←hr] using inner_fixedCodim_gap B hB
  · obtain ⟨a,ha,hao⟩ := SetLike.not_le_iff_exists.mp hcover
    have ha1 : a ≠ 1 := fun he => hao (he ▸ coverSubgroup.one_mem)
    have ha2 : orderOf a = 2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a ha) ha1
    have hmin := fixedCodim_mono M22TripleCover.Ambient.binaryAction (Subgroup.zpowers_le.mpr ha)
    rw [outer_binaryCodim a ha2 hao] at hmin
    have hr := elementary_rank_le hA ambient_twoRank_le_five
    by_contra! hh
    have hd : 2 * fixedCodim M22TripleCover.Ambient.tripleFieldAction A ≤ Module.finrank (ZMod 2) Vector := by
      rw [←field_fixedCodim,←binaryCoordinates.finrank_eq,M22TripleCover.binarySpace_finrank]
      omega
    have hs := Representation.FiniteFieldSemilinearDisplacement.rank_le_one_of_half_fixed
      M22TripleCover.Ambient.tripleFieldAction fieldAction_faithful coefficient
      coefficient_semilinear A ha (by rw [show coefficient a = fieldFrobenius from if_neg hao]; exact frobenius_ne_one) hd
    omega

private def quotientCenterEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) : G ⧸ center G ≃* H ⧸ center H :=
  QuotientGroup.congr _ _ e (by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (centerCongr e ⟨y,hy⟩).property
    · intro hx
      exact ⟨e.symm x,(centerCongr e.symm ⟨x,hx⟩).property,e.apply_symm_apply x⟩)

/-- Odd-prime actors move at least eight dimensions on the full native extension. -/
theorem ambient_odd_fixedCodim {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (a : actionGroup) (ha : orderOf a = p) :
    8 ≤ fixedCodim M22TripleCover.Ambient.binaryAction (zpowers a) := by
  have hmem : a ∈ coverSubgroup := by
    obtain ⟨n,hn⟩ := ho
    have hs := coverSubgroup.sq_mem_of_index_two coverSubgroup_index a
    have hpow := coverSubgroup.pow_mem hs n
    have hh : (a^2)^n*a ∈ coverSubgroup := by
      rw [←pow_mul,←pow_succ,←hn,←ha,pow_orderOf_eq_one]
      exact coverSubgroup.one_mem
    exact (coverSubgroup.mul_mem_cancel_left hpow).mp hh
  rw [←coverInclusion_range] at hmem
  obtain ⟨b,rfl⟩ := hmem
  have hi : Function.Injective coverInclusion := Subgroup.inclusion_injective _
  have hb : orderOf b = p := (orderOf_injective _ hi b).symm.trans ha
  have ht : ChapterH.Section10To12.IsTripleM22 (⊤ : Subgroup M22TripleCover) := {
    quasisimple := IsQuasisimple.of_mulEquiv topEquiv.symm
    center_card := (Nat.card_congr (centerCongr (topEquiv : (⊤ : Subgroup M22TripleCover) ≃* M22TripleCover)).toEquiv).trans M22TripleCover.center_card
    centralQuotient := ⟨(quotientCenterEquiv topEquiv).trans M22TripleCover.centralQuotientEquiv⟩ }
  have hp2 : p ≠ 2 := by obtain ⟨k,hk⟩ := ho; omega
  have hbd := ChapterH.Section10To12.TripleDisplacement.eight_le_fixedCodim_odd_prime
    ⊤ ht generalizedFitting_eq_top_of_quasisimple M22TripleCover.binaryRepresentation
    M22TripleCover.binaryRepresentation_faithful M22TripleCover.binarySpace_finrank hp hp2 b hb
  have he := fixedCodim_map_equivariant M22TripleCover.binaryRepresentation
    M22TripleCover.Ambient.binaryAction coverInclusion
    (LinearEquiv.refl _ _) (fun _ _ => rfl) (zpowers b)
  rw [MonoidHom.map_zpowers] at he
  exact he ▸ hbd
end
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTriple
