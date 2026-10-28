module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourTriality
public import Theory.SpecificGroups.PSL3.LargeInvolutionPrime
public import Theory.SpecificGroups.SU3.LargeInvolutionPrime
public import Theory.SpecificGroups.Tits.SylowFixedPrime

/-!
# Closing the ordinary-component branch of the outside centralizer

The marked involution fixes a full Sylow two-subgroup of the ordinary component,
since its intersection with the original H contains such a Sylow subgroup.
Fixed points therefore lift through the actual central cover. The large linear
and unitary quotients contribute a prime greater than three in this fixed group.
For Tits the inner representative centralizes a full Sylow subgroup, and its
centralizer has a factor of five. The original fixed subgroup embeds in H,
whose only prime divisors are two and three. This excludes all three remaining
families and proves C_G(x) ≤ H for the original outside involutions.

Source: Aschbacher–Smith 14.7.26, printed pp.1052–1053, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter15.Section03.Candidates.ComponentStructure

private theorem prime_of_cover {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (f : PerfectCentralCovering.Cover A B) (hz : center B = ⊥)
    (α : MulAut A) (hα : TwoCentralInner α)
    (hprime : ∀ y : B, orderOf y = 2 → ∀ P : Sylow 2 B,
      (∀ b ∈ P, Commute y b) → ∃ p : ℕ, p.Prime ∧ 3 < p ∧
        p ∣ Nat.card (centralizer ({y} : Set B))) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ Nat.card α.fixedSubgroup := by
  let := f.isPerfect
  obtain ⟨⟨x,hx⟩,ho,P,hP⟩ := hα
  let y := f.toMonoidHom x
  let β := MulAut.conj y
  have heq (a : A) : f.toMonoidHom (α a) = β (f.toMonoidHom a) := by
    rw [←hx]
    simp only [β,y,MulAut.conj_apply,map_mul,map_inv]
  have ha2 : α^2=1 := ho ▸ pow_orderOf_eq_one α
  have hb2 : β^2=1 := by
    ext b
    obtain ⟨a,rfl⟩ := f.surjective b
    change β (β (f.toMonoidHom a)) = f.toMonoidHom a
    rw [←heq,←heq]
    exact congrArg f.toMonoidHom (show α (α a) = a from DFunLike.congr_fun ha2 a)
  have hbne : β ≠ 1 := by
    intro hb
    have ha : α = 1 := MulAut.eq_one_of_central_displacement α (fun a => by
      apply f.ker_le_center
      rw [MonoidHom.mem_ker,map_mul,map_inv,heq,hb,MulAut.one_apply,inv_mul_cancel])
    rw [ha,orderOf_one] at ho
    contradiction
  have hy : orderOf y = 2 :=
    (MulAut.conj_orderOf_of_center_eq_bot hz y).symm.trans (orderOf_eq_prime hb2 hbne)
  let Q := P.mapSurjective f.surjective
  have hQ (b : B) (hb : b ∈ Q) : Commute y b := by
    obtain ⟨a,ha,rfl⟩ := hb
    have hh := heq a
    rw [hP ⟨a,ha⟩] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh.symm
  obtain ⟨p,hp,hp3,hd⟩ := hprime y hy Q hQ
  have hsurj := MulAut.fixedSubgroupMap_surjective_of_sylow_fixed α β f.toMonoidHom
    f.surjective f.ker_le_center heq ha2 P (fun a ha => hP ⟨a,ha⟩)
  refine ⟨p,hp,hp3,?_⟩
  have hd' : p ∣ Nat.card β.fixedSubgroup := by
    simpa only [β,MulAut.fixedSubgroup_conj] using hd
  exact hd'.trans (card_dvd_of_surjective _ hsurj)

open Representation Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08
open scoped IsMulCommutative Pointwise commutatorElement MatrixGroups
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem fixed_prime_false
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {x : G} (B : Subgroup (centralizer ({x} : Set G)))
    (z : G) (hz : zpowers z = F.Vi 1) (α : MulAut B)
    (ha : ∀ b : B, ((α b : centralizer ({x} : Set G)) : G) = z * (b : G) * z⁻¹)
    (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) (hd : p ∣ Nat.card α.fixedSubgroup) : False := by
  let C := centralizer ({x} : Set G)
  have hm (a : α.fixedSubgroup) : ((a.val : C) : G) ∈ F.H := by
    rw [F.H_eq_centralizer (by omega) z hz.symm]
    have hα : α a.val = a.val := (MulAut.mem_fixedSubgroup _ _).mp a.property
    have hh : z * (a.val : G) * z⁻¹ = (a.val : G) := by rw [←ha,hα]
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh).symm
  let f : α.fixedSubgroup →* F.H :=
    (C.subtype.comp (B.subtype.comp α.fixedSubgroup.subtype)).codRestrict F.H hm
  have hf : Function.Injective f := by
    intro a b hh
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : F.H => (y : G)) hh
  have hdiv := odd_prime_dvd_twoCore_quotient_residual hp (hp.odd_of_ne_two (by omega))
    (hd.trans (card_dvd_of_injective f hf))
  obtain ⟨e⟩ := he
  rw [Nat.card_congr ((residualStarEquiv F).symm.trans e).toEquiv,
    HeisenbergPrime.card] at hdiv
  have hh := hp.dvd_of_dvd_pow hdiv
  have hh' := Nat.le_of_dvd (by decide : 0 < 3) hh
  omega

/-- The actual original inner action fixes a full Sylow subgroup. This supplies
all the hypotheses needed to lift fixed points through the central cover. -/
theorem extraspecial_four_ordinary_twoCentralInner
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B)
    (z : G) (hzo : orderOf z = 2) (hz : zpowers z = F.Vi 1)
    (houtB : ¬ B.map (centralizer ({x} : Set G)).subtype ≤ F.H)
    (α : MulAut B)
    (ha : ∀ b : B, ((α b : centralizer ({x} : Set G)) : G) = z * (b : G) * z⁻¹)
    (hi : α ∈ (MulAut.conj (G := B)).range) : TwoCentralInner α := by
  let C := centralizer ({x} : Set G)
  have hfix (b : B) (hb : (b : G) ∈ F.H) : α b = b := by
    rw [F.H_eq_centralizer (by omega) z hz.symm] at hb
    apply Subtype.ext
    apply Subtype.ext
    exact (ha b).trans (mul_inv_eq_of_eq_mul (mem_centralizer_singleton_iff.mp hb).symm)
  have hne : α ≠ 1 := by
    intro hh
    apply houtB
    rintro _ ⟨b,hb,rfl⟩
    rw [F.H_eq_centralizer (by omega) z hz.symm]
    have heq := ha ⟨b,hb⟩
    rw [hh,MulAut.one_apply] at heq
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp heq.symm).symm
  have hpow : α^2=1 := by
    have hzpow : z^2=1 := hzo ▸ pow_orderOf_eq_one z
    have hzsq : z*z=1 := by simpa only [pow_two] using hzpow
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    apply Subtype.ext
    change ((α (α b) : C) : G) = (b : G)
    rw [ha,ha]
    calc
      z * (z * (b : G) * z⁻¹) * z⁻¹ = (z*z) * (b : G) * (z*z)⁻¹ := by group
      _ = (b : G) := by rw [hzsq]; simp
  obtain ⟨_,⟨P,hPJ⟩,_⟩ := extraspecial_four_ordinary_intersection
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  exact ⟨hi,orderOf_eq_prime hpow hne,P,fun b => hfix b (hPJ b.property)⟩

/-- The outside involution centralizer lies in the original H. All ordinary
component families are excluded under the original source hypotheses. -/
theorem extraspecial_four_outside_centralizer_le
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    : centralizer ({x} : Set G) ≤ F.H := by
  by_contra hout
  obtain ⟨B,z,hB,hn,hLB,hzo,hz,hmove,houtB,α,ha,hi,hmodel,hcases⟩ :=
    extraspecial_four_ordinary_three_family_source
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
  have ht := extraspecial_four_ordinary_twoCentralInner
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    B hB z hzo hz houtB α ha hi
  let : IsQuasisimple B := hB.2
  let Q := B ⧸ pCore 2 B
  let : IsSimpleGroup Q := (extraspecial_four_ordinary_structure
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB).2.2.2.2.1
  let : Group.IsPerfect Q := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (pCore 2 B)) (QuotientGroup.mk'_surjective _)
  have exclude {W : Type} [Group W] [Finite W] (e : Q ≃* W)
      (hprime : ∀ y : W, orderOf y = 2 → ∀ P : Sylow 2 W,
        (∀ b ∈ P, Commute y b) → ∃ p : ℕ, p.Prime ∧ 3 < p ∧
          p ∣ Nat.card (centralizer ({y} : Set W))) : False := by
    let : IsSimpleGroup W := e.symm.isSimpleGroup
    let : Group.IsPerfect W := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    let c : PerfectCentralCovering.Cover B W :=
      { toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B))
        surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
        isPerfect := inferInstance
        ker_le_center := by
          rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
          exact IsQuasisimple.pCore_le_center 2 }
    obtain ⟨p,hp,hp3,hd⟩ := prime_of_cover c Subgroup.center_eq_bot_of_simple_perfect α ht hprime
    exact fixed_prime_false he B z hz α ha p hp hp3 hd
  rcases hcases with hl | hu | htits
  · obtain ⟨n,hn,heven,k,_,_,hk,⟨e⟩⟩ := hl
    exact exclude e (fun y hy _ _ =>
      Matrix.PSL3.EvenInnerCentralizers.exists_prime_gt_three_dvd_involution_centralizer
        k hn heven hk y hy)
  · obtain ⟨n,hn,hodd,k,_,_,J,hk,hJ,⟨e⟩⟩ := hu
    let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card
      (show Nat.card k = 2^(n*2) by simpa only [pow_mul] using hk)
    have hfixed : Nat.card {a : k // J.conj a = a} = 2^n :=
      FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hk hJ
    exact exclude e (fun y hy _ _ =>
      BenderSuzuki.MatrixGroups.HermitianForm.EvenInvolutionTwoGroup.exists_prime_gt_three_dvd_involution_centralizer
        J (by omega) hodd hk hfixed y hy)
  · obtain ⟨e⟩ := htits
    exact exclude (e.trans Tits.parrottFiniteImageEquiv) (fun y hy P hP =>
      ⟨5,by decide,by decide,Tits.five_dvd_centralizer_of_sylow_fixed y hy P hP⟩)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
