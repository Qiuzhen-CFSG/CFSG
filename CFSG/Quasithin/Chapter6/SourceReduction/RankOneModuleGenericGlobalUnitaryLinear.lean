module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryRankTwo
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import Theory.SpecificGroups.Janko4.Model.Cardinality
public import Theory.SpecificGroups.Rudvalis.Model.Order
public import Theory.Representation.BinaryPrimeDegree
public import Theory.SpecificGroups.Held.SylowOrderBound
public import Theory.SpecificGroups.Held.InvertedSevenCenter
public import Theory.Representation.BinaryCoprimeDegree.CentralQuotient
public import Theory.Representation.QuadraticFourGroup.Recognition.IrreducibleReduction.Section
public import Theory.Representation.BinaryOffender.QuasisimpleImage

/-!
# Eliminating the sporadic unitary overcomponent quotients

Let K = O²(H), Q = O₂(K), and R = O₂(J) in the proper-intersection
branch of 5.2.8. The actual centerless image B of K in J/R has two-core
of order q² and PSL₂(q) quotient, so q³ divides the order of the literal
central quotient of J/R. Characteristic two makes J/R act faithfully
on R/Φ(R), whose binary dimension is at most 3m+1 for q = 2^m.

For M₂₂, M₂₃, M₂₄, J₄ and Rudvalis, their two-parts bound m, and a
prime divisor of each actual carrier is absent from the corresponding
binary linear group. Held's Sylow bound gives dimension at most ten.
A nontrivial irreducible section of the perfect action has a faithful
image with the same central quotient; Held's extraspecial seven-subgroup
forces dimension at least twenty-one, including arbitrary central covers.

The preceding rank-two comparison therefore leaves only PSL₃(q) over
the original field. The source application below retains the original
quotient image and its full core. Identifying the full covering quotient,
its natural action on R, and the second-parabolic contradiction remain
required; this result does not establish unitary maximality or GlobalExit.

Source: Aschbacher–Smith 5.2.8, printed pp.652–653, and G.7.1(2),
printed p.347 (`refs/quasithin.pdf`). Native ATLAS carrier and extraspecial
certificates retain their source attribution and LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryLinear
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem three_power_dvd {B : Subgroup G} {m : ℕ}
    (hpsl : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^m))
    (hc : Nat.card (pCore 2 B) = (2^m)^2) (hz : center B = ⊥) :
    2^(3*m) ∣ Nat.card (G ⧸ center G) := by
  let q := QuotientGroup.mk' (center G)
  let f := q.comp B.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    have hxz : (x : G) ∈ center G := (QuotientGroup.eq_one_iff _).mp hx
    have hxb : x ∈ center B := mem_center_iff.mpr (fun y =>
      Subtype.ext (mem_center_iff.mp hxz y))
    simpa only [hz,mem_bot] using hxb
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hpsl
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hq : Nat.card (B ⧸ pCore 2 B) = 2^m*((2^m)^2-1) := by
    rw [Nat.card_congr (e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm).toEquiv,
      GorensteinWalter.sl2_card_formula,hF]
  have hB := card_eq_card_quotient_mul_card_subgroup (pCore 2 B)
  rw [hq,hc] at hB
  have hd : 2^(3*m) ∣ Nat.card B := by
    rw [hB]
    refine ⟨(2^m)^2-1,?_⟩
    rw [show 3*m = m*3 from Nat.mul_comm _ _,pow_mul]
    ring
  exact hd.trans (card_dvd_of_injective f hf)

private theorem quotient_linear_embedding (h : HasCharacteristicTwo G)
    {r : ℕ} (hc : Nat.card (pCore 2 G) ≤ 2^r) :
    ∃ f : (G ⧸ pCore 2 G) →* GL (Fin r) (ZMod 2), Function.Injective f := by
  let P := pCore 2 G
  let E := P ⧸ frattini P
  let a := (quotientAut (frattini P)).comp (MulAut.conjNormal : G →* MulAut P)
  have hk : a.ker = P := pCore_frattini_action_kernel 2 h
  let f := QuotientGroup.lift P a hk.ge
  have hf : Function.Injective f := (QuotientGroup.injective_lift_iff _ _ _).mpr hk.symm
  let : Fact (IsPGroup 2 P) := ⟨pCore_isPGroup⟩
  let : IsElementaryAbelian 2 E := isElementaryAbelian_quotient_frattini
  have hE : Nat.card E ≤ 2^r :=
    (Nat.card_le_card_of_surjective (QuotientGroup.mk' (frattini P))
      (QuotientGroup.mk'_surjective _)).trans hc
  obtain ⟨j,hj⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le E hE
  exact ⟨j.comp f,hj.comp hf⟩

private theorem exponent_bound {m b c : ℕ}
    (hd : 2^(3*m) ∣ c) (hb : ¬ 2^(3*(b+1)) ∣ c) : m ≤ b := by
  by_contra hh
  exact hb ((Nat.pow_dvd_pow 2 (by omega : 3*(b+1) ≤ 3*m)).trans hd)

omit [Finite G] in
private theorem core_bound {m b : ℕ} (hm : m ≤ b)
    (hc : Nat.card (pCore 2 G) ≤ 2*(2^m)^3) :
    Nat.card (pCore 2 G) ≤ 2^(3*b+1) := by
  calc
    Nat.card (pCore 2 G) ≤ 2*(2^m)^3 := hc
    _ = 2^(3*m+1) := by rw [←pow_mul, Nat.mul_comm m 3, pow_succ, Nat.mul_comm (2^(3*m)) 2]
    _ ≤ 2^(3*b+1) := Nat.pow_le_pow_right (by decide) (by omega)

private theorem not_small_model {X : Type*} [Group X]
    (h : HasCharacteristicTwo G) {B : Subgroup (G ⧸ pCore 2 G)} {m b c p : ℕ}
    (hpsl : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^m))
    (hc : Nat.card (pCore 2 B) = (2^m)^2) (hz : center B = ⊥)
    (hR : Nat.card (pCore 2 G) ≤ 2*(2^m)^3)
    (e : ((G ⧸ pCore 2 G) ⧸ center (G ⧸ pCore 2 G)) ≃* X)
    (hX : Nat.card X = c) (hb : ¬ 2^(3*(b+1)) ∣ c)
    (hp : p ∣ c) (hGL : ¬ p ∣ Nat.card (GL (Fin (3*b+1)) (ZMod 2))) : False := by
  have hd := three_power_dvd hpsl hc hz
  rw [Nat.card_congr e.toEquiv,hX] at hd
  obtain ⟨f,hf⟩ := quotient_linear_embedding h (core_bound (exponent_bound hd hb) hR)
  apply hGL
  apply hp.trans
  rw [←hX,←Nat.card_congr e.toEquiv]
  exact (card_quotient_dvd_card (center (G ⧸ pCore 2 G))).trans (card_dvd_of_injective f hf)

private theorem held_degree {X V : Type*} [Group X] [Finite X] [IsQuasisimple X]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) X V) (hf : Function.Injective ρ)
    (e : (X ⧸ center X) ≃* _root_.Held.He) :
    21 ≤ Module.finrank (ZMod 2) V := by
  let : IsSimpleGroup (X ⧸ center X) := IsQuasisimple.simple
  let : Nontrivial X := (QuotientGroup.mk'_surjective (center X)).nontrivial
  let : Group.IsPerfect (⊤ : Subgroup X) :=
    Group.IsPerfect.ofSurjective (f := (topEquiv (G := X)).symm.toMonoidHom)
      (topEquiv (G := X)).symm.surjective
  have hn : ¬ (⊤ : Subgroup X) ≤ ρ.ker := by
    intro hh
    have hz := (MonoidHom.ker_eq_bot_iff ρ).mpr hf
    exact top_ne_bot ((top_unique hh).symm.trans hz)
  obtain ⟨U,N,hi,hn⟩ := Representation.QuadraticFourGroup.exists_irreducible_section_surviving_perfect
    (⊤ : Subgroup X) hn
  let σ := N.quotientRepresentation
  have hk : σ.ker ≤ center X := by
    rcases IsQuasisimple.normal_le_center_or_eq_top σ.ker with hc | ht
    · exact hc
    · exact (hn ht.ge).elim
  open Representation.BinaryOffender in
  let Y := actionImage σ
  open Representation.BinaryOffender in
  let τ := imageRepresentation σ
  open Representation.BinaryOffender in
  let : IsQuasisimple Y := actionImage_isQuasisimple σ hk
  open Representation.BinaryOffender in
  let : τ.IsIrreducible := imageRepresentation_irreducible σ hi
  open Representation.BinaryOffender in
  let a : (Y ⧸ center Y) ≃* _root_.Held.He :=
    (actionImageQuotientCenterEquiv σ hk).symm.trans e
  let f := a.toMonoidHom.comp (QuotientGroup.mk' (center Y))
  have hsurj : Function.Surjective f := a.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker ≤ center Y := by
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective,QuotientGroup.ker_mk']
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : IsExtraspecial 7 _root_.Held.OddCubeCandidates.seven :=
    _root_.Held.InvertedSevenCenter.seven_isExtraspecial
  open Representation.BinaryOffender in
  have hl := Representation.BinaryCoprimeDegree.extraspecial_central_quotient_degree
    τ (imageRepresentation_injective σ) f hsurj hker (by decide : 7 ≠ 2)
    _root_.Held.OddCubeCandidates.seven _root_.Held.OddCubeCandidates.card_seven
  rw [Representation.BinaryPrimeDegree.orderOf_two_mod_seven] at hl
  exact hl.trans ((Submodule.finrank_quotient_le N.toSubmodule).trans
    (Submodule.finrank_le U.toSubmodule))

private theorem not_held (h : HasCharacteristicTwo G)
    [IsQuasisimple (G ⧸ pCore 2 G)]
    {B : Subgroup (G ⧸ pCore 2 G)} {m : ℕ}
    (hpsl : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^m))
    (hc : Nat.card (pCore 2 B) = (2^m)^2) (hz : center B = ⊥)
    (hR : Nat.card (pCore 2 G) ≤ 2*(2^m)^3)
    (e : ((G ⧸ pCore 2 G) ⧸ center (G ⧸ pCore 2 G)) ≃* _root_.Held.He) : False := by
  have hd := three_power_dvd hpsl hc hz
  rw [Nat.card_congr e.toEquiv] at hd
  have hm : m ≤ 3 := exponent_bound hd _root_.Held.not_two_pow_twelve_dvd_card
  obtain ⟨f,hf⟩ := quotient_linear_embedding h (core_bound hm hR)
  let ρ : Representation (ZMod 2) (G ⧸ pCore 2 G) (Fin 10 → ZMod 2) :=
    Matrix.toLinAlgEquiv'.toMonoidHom.comp ((Units.coeHom _).comp f)
  have hρ : Function.Injective ρ := Matrix.toLinAlgEquiv'.injective.comp (Units.val_injective.comp hf)
  have hh := held_degree ρ hρ e
  norm_num at hh

/-- None of the six sporadic central quotients can contain the actual
centerless unitary image and act faithfully on the bounded overcomponent core. -/
theorem not_sporadic (h : HasCharacteristicTwo G)
    [IsQuasisimple (G ⧸ pCore 2 G)]
    {B : Subgroup (G ⧸ pCore 2 G)} {m : ℕ}
    (hpsl : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^m))
    (hc : Nat.card (pCore 2 B) = (2^m)^2) (hz : center B = ⊥)
    (hR : Nat.card (pCore 2 G) ≤ 2*(2^m)^3)
    (hs : ∃ name : ClassificationModels.SporadicName,
      (name = .m22 ∨ name = .m23 ∨ name = .m24 ∨ name = .j4 ∨ name = .he ∨ name = .ru) ∧
      Nonempty (((G ⧸ pCore 2 G) ⧸ center (G ⧸ pCore 2 G)) ≃* name.Carrier)) : False := by
  obtain ⟨name,hn,⟨e⟩⟩ := hs
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_small_model (b := 2) (p := 11) h hpsl hc hz hR e
      Sporadic.Mathieu.m22_order (by norm_num) (by norm_num)
      (by rw [Matrix.card_GL_field]; norm_num [Fin.prod_univ_succ])
  · exact not_small_model (b := 2) (p := 11) h hpsl hc hz hR e
      Sporadic.Mathieu.m23_order (by norm_num) (by norm_num)
      (by rw [Matrix.card_GL_field]; norm_num [Fin.prod_univ_succ])
  · exact not_small_model (b := 3) (p := 23) h hpsl hc hz hR e
      Sporadic.Mathieu.m24_order (by norm_num) (by norm_num)
      (by rw [Matrix.card_GL_field]; norm_num [Fin.prod_univ_succ])
  · exact not_small_model (b := 7) (p := 37) h hpsl hc hz hR e
      Janko4.Cardinality.model_card (by norm_num) (by norm_num)
      (by rw [Matrix.card_GL_field]; norm_num [Fin.prod_univ_succ])
  · exact not_held h hpsl hc hz hR e
  · exact not_small_model (b := 4) (p := 29) h hpsl hc hz hR e
      Rudvalis.model_card (by norm_num) (by norm_num)
      (by rw [Matrix.card_GL_field]; norm_num [Fin.prod_univ_succ])

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryLinear

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
section Unitary
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
  (he : (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm).reverse)) ∨
    (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)))
include d h hH hp m hm he

/-- Every proper unitary overcomponent in the noncontainment branch has
actual central quotient PSL₃ over the original field. The full quotient and
its action are not identified with the central quotient. -/
theorem Preparation.unitary_overcomponent_central_quotient_linear
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H < J)
    (hQR : ¬ (residual H).pCoreIn 2 ≤ J.pCoreIn 2) :
    ClassicalGroup.IsPSL
      ((J ⧸ pCore 2 J) ⧸ center (J ⧸ pCore 2 J)) 3 (2^m) := by
  rcases d.unitary_overcomponent_central_quotient_linear_or_sporadic
      h hH hp m hm he hJ hKJ hQR with hlin | hs
  · exact hlin
  · have hq := (d.unitary_overcomponent_central_quotient_models
        h hH hp m hm he hJ hKJ hQR).1
    let := hq
    have hz := (d.unitary_overcomponent_proper_image_block
      h hH hp m hm he hJ hKJ.le hQR).2.2
    have hpsl := (d.unitary_overcomponent_quotient_image
      h hH hp m hm he hJ hKJ.le).2.2.2.1
    obtain ⟨hc,hR⟩ := d.unitary_overcomponent_proper_quotient_core
      h hH hp m hm he hJ hKJ.le hQR
    have hR' : Nat.card (pCore 2 J) ≤ 2*(2^m)^3 := by
      rw [Nat.card_congr ((pCore 2 J).equivMapOfInjective J.subtype J.subtype_injective).toEquiv]
      exact hR
    have hchar := Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo
      T (h.qtke.evenCharacteristic T) hJ
    exact (UnitaryLinear.not_sporadic hchar hpsl hc hz hR' hs).elim

end Unitary
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
