module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.Geometry
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.SubspaceTransport
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.HigherFieldResiduals
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary
public import Theory.SpecificGroups.SymplecticFour.ParabolicCharacters
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Cubic residual actions exclude nonbinary parabolic intersections

The original residual has two-core quotient of order three. Every image
retains a quotient of order dividing three, whose automorphism group is a
two-group. A two-perfect normalizer must therefore centralize that section.
The component Sylow movement in 7.7.9(2) rules out two-perfectness of the
actual intersection in the reduced action.

Both point and line parabolics in nonbinary SL₃, and both point and plane
parabolics in nonbinary Sp₄, are two-perfect: their scalar characters have
odd image and perfect kernels. The Chapter 12 application excludes these
four actual group isomorphisms for the original reduced intersection.
Identifying that intersection with a model parabolic is a separate step.

Source: Aschbacher--Smith, proof after Lemma 7.7.10, printed p.708,
refs/quasithin.pdf. The argument retains the full SL₃ center and the
literal two-core of the residual.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped commutatorElement MatrixGroups
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryParabolicSection
variable {G : Type*} [Group G] [Finite G]

/-- A two-perfect normalizer acts trivially on a cubic two-core section. -/
theorem cubic_section_commutator (A B : Subgroup G)
    (hc : Nat.card (A ⧸ pCore 2 A) ∣ 3)
    (hn : B ≤ normalizer (A : Set G)) (hp : IsPPerfect 2 B) :
    ⁅A,B⁆ ≤ A.pCoreIn 2 := by
  let X := A ⧸ pCore 2 A
  have hAut : IsPGroup 2 (MulAut X) := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hc with hc | hc
    · let : Subsingleton X := (Nat.card_eq_one_iff_unique.mp hc).1
      let : Subsingleton (MulAut X) := ⟨fun a b => MulEquiv.ext (fun x => Subsingleton.elim _ _)⟩
      exact IsPGroup.of_card (n := 0) (by rw [Nat.card_unique]; rfl)
    · let : IsCyclic X := isCyclic_of_prime_card hc
      apply IsPGroup.of_card (n := 1)
      rw [IsCyclic.card_mulAut,hc,Nat.totient_prime Nat.prime_three]
      decide
  let a : B →* MulAut X := (quotientAut (pCore 2 A)).comp
    (A.normalizerMonoidHom.comp (inclusion hn))
  have ha : a = 1 := hp.hom_eq_one_of_isPGroup hAut a
  rw [commutator_comm,commutator_le]
  intro b hb x hx
  let x' : A := ⟨x,hx⟩
  let b' : B := ⟨b,hb⟩
  have he := congrArg (fun t : MulAut X => t (QuotientGroup.mk' (pCore 2 A) x'))
    (DFunLike.congr_fun ha b')
  change quotientAut (pCore 2 A) (A.normalizerMonoidHom (inclusion hn b'))
    (QuotientGroup.mk' (pCore 2 A) x') = QuotientGroup.mk' (pCore 2 A) x' at he
  rw [quotientAut_apply_mk] at he
  have hk : A.normalizerMonoidHom (inclusion hn b') x' * x'⁻¹ ∈ pCore 2 A := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 A)
      (A.normalizerMonoidHom (inclusion hn b') x' * x'⁻¹) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  exact mem_map_of_mem A.subtype hk

/-- Cubic two-core quotients remain of order dividing three in every image. -/
theorem image_cubic_quotient {X Z : Type*} [Group X] [Group Z]
    (r : X →* Z) (hr : Function.Surjective r)
    (hc : Nat.card (X ⧸ pCore 2 X) = 3) :
    Nat.card (Z ⧸ pCore 2 Z) ∣ 3 := by
  have hl : (pCore 2 X).map r ≤ pCore 2 Z :=
    le_sSup ⟨(inferInstance : (pCore 2 X).Normal).map r hr,pCore_isPGroup.map r⟩
  let q : (X ⧸ pCore 2 X) →* Z ⧸ pCore 2 Z :=
    QuotientGroup.map _ _ r (map_le_iff_le_comap.mp hl)
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 Z) z
    obtain ⟨x,rfl⟩ := hr z
    exact ⟨QuotientGroup.mk' (pCore 2 X) x,rfl⟩
  exact hc ▸ card_dvd_of_surjective q hq

/-- The actual moving Sylow section rules out two-perfectness of its normalizer. -/
theorem not_twoPerfect_of_cubic_movement (A B S : Subgroup G)
    (hc : Nat.card (A ⧸ pCore 2 A) ∣ 3)
    (hn : B ≤ normalizer (A : Set G)) (hS : S ≤ B)
    (hm : ¬ ⁅A,S⁆ ≤ A.pCoreIn 2) : ¬ IsPPerfect 2 B := by
  intro hp
  exact hm ((commutator_mono le_rfl hS).trans (cubic_section_commutator A B hc hn hp))

private theorem perfect_twoPerfect {X : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] : IsPPerfect 2 X := by
  intro N hN hp
  let := hN
  apply top_unique
  intro x _
  apply (QuotientGroup.eq_one_iff x).mp
  by_contra h
  let : Nontrivial (X ⧸ N) := ⟨⟨QuotientGroup.mk' N x,1,h⟩⟩
  exact Group.IsPerfect.not_isNilpotent (X ⧸ N) hp.isNilpotent

private theorem twoPerfect_of_odd_image {X Y : Type*} [Group X] [Finite X]
    [Group Y] [Finite Y] (f : X →* Y) (hY : Odd (Nat.card Y))
    (hk : IsPPerfect 2 f.ker) : IsPPerfect 2 X := by
  intro N hN hp
  let := hN
  have hz := hk.hom_eq_one_of_isPGroup hp ((QuotientGroup.mk' N).comp f.ker.subtype)
  have hle : f.ker ≤ N := by
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    exact DFunLike.congr_fun hz ⟨x,hx⟩
  have ho : Odd N.index := (hY.of_dvd_nat f.range.card_subgroup_dvd_card).of_dvd_nat
    (by simpa only [index_ker] using index_dvd_of_le hle)
  obtain ⟨n,he⟩ := hp.exists_card_eq
  change Odd (Nat.card (X ⧸ N)) at ho
  rw [he] at ho
  have hn : n = 0 := by
    by_contra hn
    have hd : 2 ∣ 2 ^ n := dvd_pow_self 2 hn
    exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr hd)
  apply index_eq_one.mp
  change Nat.card (X ⧸ N) = 1
  simpa only [hn,pow_zero] using he


private theorem units_odd {F : Type*} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) : Odd (Nat.card Fˣ) := by
  rw [Nat.card_units,hF,Nat.odd_iff]
  have hd : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have hh := Nat.mod_eq_zero_of_dvd hd
  have hp : 0 < 2 ^ n := pow_pos (by decide) n
  omega

open Matrix.PSL3.LinearThree
private def pointScalar (F : Type*) [Field F] [Finite F] : pointParabolicSL F →* F where
  toFun g := g.val.val 0 0
  map_one' := by simp
  map_mul' g h := by
    have hh := (mem_pointParabolicSL_iff F h).mp h.property
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hh.1, hh.2]
private def lineScalar (F : Type*) [Field F] [Finite F] : lineParabolicSL F →* F where
  toFun g := g.val.val 2 2
  map_one' := by simp
  map_mul' g h := by
    have hg := (mem_lineParabolicSL_iff F g).mp g.property
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hg.1, hg.2]

/-- The actual nonbinary SL₃ point parabolic is two-perfect. -/
theorem linear_point_twoPerfect {F : Type*} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    IsPPerfect 2 (pointParabolicSL F) := by
  let f := (pointScalar F).toHomUnits
  have he : f.ker.map (pointParabolicSL F).subtype = pointLocalSL F := by
    ext g
    constructor
    · rintro ⟨g,hg,rfl⟩
      have hs : g.val.val 0 0 = 1 := congrArg Units.val hg
      exact (mem_pointLocalSL_iff F g).mpr ⟨hs,(mem_pointParabolicSL_iff F g).mp g.property⟩
    · intro hg
      have hh := (mem_pointLocalSL_iff F g).mp hg
      refine ⟨⟨g,pointLocalSL_le F hg⟩,?_,rfl⟩
      exact Units.ext hh.1
  let e := (f.ker.equivMapOfInjective _ (pointParabolicSL F).subtype_injective).trans
    (MulEquiv.subgroupCongr he)
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
  let := pointLocalSL_isPerfect F hfour
  exact twoPerfect_of_odd_image f (units_odd hF hn)
    (perfect_twoPerfect.of_surjective e.symm.toMonoidHom e.symm.surjective)

/-- The actual nonbinary SL₃ line parabolic is two-perfect. -/
theorem linear_line_twoPerfect {F : Type*} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    IsPPerfect 2 (lineParabolicSL F) := by
  let f := (lineScalar F).toHomUnits
  have he : f.ker.map (lineParabolicSL F).subtype = lineLocalSL F := by
    ext g
    constructor
    · rintro ⟨g,hg,rfl⟩
      have hs : g.val.val 2 2 = 1 := congrArg Units.val hg
      have hp := (mem_lineParabolicSL_iff F g).mp g.property
      exact (mem_lineLocalSL_iff F g).mpr ⟨hp.1,hp.2,hs⟩
    · intro hg
      have hh := (mem_lineLocalSL_iff F g).mp hg
      refine ⟨⟨g,lineLocalSL_le F hg⟩,?_,rfl⟩
      exact Units.ext hh.2.2
  let e := (f.ker.equivMapOfInjective _ (lineParabolicSL F).subtype_injective).trans
    (MulEquiv.subgroupCongr he)
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
  let := lineLocalSL_isPerfect F hfour
  exact twoPerfect_of_odd_image f (units_odd hF hn)
    (perfect_twoPerfect.of_surjective e.symm.toMonoidHom e.symm.surjective)

open Theory.SpecificGroups.SymplecticFour

/-- The actual nonbinary Sp₄ point parabolic is two-perfect. -/
theorem symplectic_point_twoPerfect {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    IsPPerfect 2 (Theory.SpecificGroups.SymplecticFour.pointParabolic (F := F)) := by
  let f := determinantCharacter (point F)
  let e : f.ker ≃* Theory.SpecificGroups.SymplecticFour.pointLocal (F := F) :=
    f.ker.equivMapOfInjective _ (Theory.SpecificGroups.SymplecticFour.pointParabolic (F := F)).subtype_injective
  let := pointLocal_perfect hF hn
  exact twoPerfect_of_odd_image f (units_odd hF hn)
    (perfect_twoPerfect.of_surjective e.symm.toMonoidHom e.symm.surjective)

/-- The actual nonbinary Sp₄ plane parabolic is two-perfect. -/
theorem symplectic_plane_twoPerfect {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    IsPPerfect 2 (planeParabolic (F := F)) := by
  let f := determinantCharacter (plane F)
  let e : f.ker ≃* planeLocal (F := F) :=
    f.ker.equivMapOfInjective _ (planeParabolic (F := F)).subtype_injective
  let := planeLocal_perfect hF hn
  exact twoPerfect_of_odd_image f (units_odd hF hn)
    (perfect_twoPerfect.of_surjective e.symm.toMonoidHom e.symm.surjective)

/-- All four actual nonbinary maximal parabolics are excluded by the cubic action. -/
theorem no_nonbinary_parabolic {X : Type*} [Group X] (hX : ¬ IsPPerfect 2 X)
    (F : ChapterB.QuasisimpleSource.BinaryField) (hn : 1 < F.degree) :
    ¬ Nonempty (X ≃* pointParabolicSL F.Carrier) ∧
    ¬ Nonempty (X ≃* lineParabolicSL F.Carrier) ∧
    ¬ Nonempty (X ≃* Theory.SpecificGroups.SymplecticFour.pointParabolic (F := F.Carrier)) ∧
    ¬ Nonempty (X ≃* Theory.SpecificGroups.SymplecticFour.planeParabolic (F := F.Carrier)) := by
  refine ⟨?_,?_,?_,?_⟩
  · rintro ⟨e⟩
    exact hX ((linear_point_twoPerfect F.card_eq hn).of_surjective e.symm.toMonoidHom e.symm.surjective)
  · rintro ⟨e⟩
    exact hX ((linear_line_twoPerfect F.card_eq hn).of_surjective e.symm.toMonoidHom e.symm.surjective)
  · rintro ⟨e⟩
    exact hX ((symplectic_point_twoPerfect F.card_eq hn).of_surjective e.symm.toMonoidHom e.symm.surjective)
  · rintro ⟨e⟩
    exact hX ((symplectic_plane_twoPerfect F.card_eq hn).of_surjective e.symm.toMonoidHom e.symm.surjective)

open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

/-- The actual C.2.7 linear-three parabolic predicate is incompatible with
nontrivial cubic section movement over a nonbinary field. -/
theorem no_linearThree_maximalParabolic {X : Type*} [Group X] (P : Subgroup X)
    (hp : ¬ IsPPerfect 2 P) {F : Type*} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    ¬ IsLinearMaximalParabolic P 3 F := by
  rintro ⟨e,W,hW,hWt,he⟩
  have hs : linearStabilizer W = Matrix.HigherLinear.parabolicSL W := by
    ext g
    rw [linearStabilizer,Subgroup.mem_comap,Submodule.stabilizer_coe,
      MulAction.mem_stabilizer_set]
    rfl
  let a := (e.subgroupMap P).trans (MulEquiv.subgroupCongr (he.trans hs))
  rcases Matrix.PSL3.LinearThree.SubspaceTransport.exists_parabolic_equiv W hW hWt with hb | hb
  · obtain ⟨b⟩ := hb
    exact hp ((linear_point_twoPerfect hF hn).of_surjective
      (a.trans b).symm.toMonoidHom (a.trans b).symm.surjective)
  · obtain ⟨b⟩ := hb
    exact hp ((linear_line_twoPerfect hF hn).of_surjective
      (a.trans b).symm.toMonoidHom (a.trans b).symm.surjective)

/-- The actual C.2.7 Sp₄(4) parabolic predicate is incompatible with
nontrivial cubic section movement. -/
theorem no_sp4Four_maximalParabolic {X : Type*} [Group X] (P : Subgroup X)
    (hp : ¬ IsPPerfect 2 P) : ¬ IsSp4FourMaximalParabolic P := by
  rintro ⟨F,_,_,hF,e,he⟩
  let := Fintype.ofFinite F
  have hcard : Nat.card F = 2 ^ 2 := by omega
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  rcases he with he | he
  · let a := (e.subgroupMap P).trans (MulEquiv.subgroupCongr he)
    exact hp ((symplectic_point_twoPerfect hcard (by decide)).of_surjective
      a.symm.toMonoidHom a.symm.surjective)
  · let a := (e.subgroupMap P).trans (MulEquiv.subgroupCongr he)
    exact hp ((symplectic_plane_twoPerfect hcard (by decide)).of_surjective
      a.symm.toMonoidHom a.symm.surjective)

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryParabolicSection
