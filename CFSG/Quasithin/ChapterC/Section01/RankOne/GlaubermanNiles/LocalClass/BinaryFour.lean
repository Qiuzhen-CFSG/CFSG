module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.NaturalAction
public import Theory.SpecificGroups.SL2.Affine.Action
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Theory.Representation.BinaryGroupAction
public import Stellmacher.SL2DerivedCard
public import Theory.GroupTheory.SpecificGroups.KleinFourFixedAut
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The binary four-group marking in the original local class

If the actual generalized-Fitting actor in H/C_H(V) has order three and
its actual moved subgroup has order four, the latter is the natural binary
plane. First, an actor fixing the moved subgroup is both quadratic and
cubic on the elementary group V, and therefore trivial. Its faithful
four-group action has no nonidentity fixed point. Compatible coordinates
then identify the actual cubic actor with PSL₂(2)' and the literal moved
quotient with the natural plane, preserving conjugation and actorProjection.

The final theorem supplies the complete C.1.17 membership from the marked
Sylow, minimal-parabolic, characteristic-two, and numerical source geometry.
No faithfulness, fixed-subgroup, or action-isomorphism premise is added.
The source construction of that geometry remains with the application.
Source: Aschbacher--Smith C.1.17, C.1.26, printed pp.126 and132, used in
15.4.7, p.1158.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
namespace BinaryFour

private abbrev Plane := Multiplicative (Fin 2 → ZMod 2)
private instance planeElementary : IsElementaryAbelian 2 Plane :=
  Representation.BinaryGroupAction.elementary
private instance planeKlein : IsKleinFour Plane := by
  let : Nontrivial Plane := inferInstance
  refine ⟨?_, IsElementaryAbelian.exponent_eq_prime⟩
  change Nat.card (Fin 2 → ZMod 2) = 4
  norm_num [Nat.card_fun]

private def naturalAutEquiv : SL(2,ZMod 2) ≃* MulAut Plane :=
  MulEquiv.ofBijective (Matrix.SL2.naturalAction (ZMod 2))
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨Matrix.SL2.naturalAction_injective _, by
      rw [IsKleinFour.card_mulAut]
      exact Stellmacher.SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨MulEquiv.refl _⟩⟩)

/-- A faithful cubic action on a four-group is the actual derived natural
PSL₂(2) action, with compatible coordinates on both actors and vectors. -/
theorem cubic_four_coordinates {A W : Type*} [Group A] [Finite A]
    [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (hA : Nat.card A = 3) (hW : Nat.card W = 4)
    (ρ : A →* MulAut W) (hρ : Function.Injective ρ) :
    ∃ (a : A ≃* commutator PSL(2,ZMod 2)) (c : W ≃* Multiplicative (Fin 2 → ZMod 2)),
      ∀ x w, c (ρ x w) = Matrix.SL2.naturalAction (ZMod 2)
        (Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm (a x : PSL(2,ZMod 2))) (c w) := by
  let : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour W := ⟨hW,IsElementaryAbelian.exponent_eq_prime⟩
  obtain ⟨c⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := W) (G₂ := Plane)
  let s : SL(2,ZMod 2) ≃* PSL(2,ZMod 2) := Atlas.RankOneFieldAutomorphisms.slEquivPSL
  let φ : A →* PSL(2,ZMod 2) := s.toMonoidHom.comp
    (naturalAutEquiv.symm.toMonoidHom.comp ((MulAut.congr c).toMonoidHom.comp ρ))
  have hφ : Function.Injective φ := s.injective.comp
    (naturalAutEquiv.symm.injective.comp ((MulAut.congr c).injective.comp hρ))
  have hcard : Nat.card φ.range = 3 :=
    (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm.trans hA
  have hd : Nat.card (commutator PSL(2,ZMod 2)) = 3 :=
    Stellmacher.isSL2Two_commutator_card ⟨s.symm⟩
  have hqcard : Nat.card (PSL(2,ZMod 2) ⧸ commutator PSL(2,ZMod 2)) = 2 := by
    have hmul := (commutator PSL(2,ZMod 2)).index_mul_card
    have hc : Nat.card PSL(2,ZMod 2) = 6 :=
      Stellmacher.SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨s.symm⟩
    rw [hd,hc] at hmul
    change (commutator PSL(2,ZMod 2)).index = 2
    omega
  have hle : φ.range ≤ commutator PSL(2,ZMod 2) := by
    rintro _ ⟨x,rfl⟩
    apply (QuotientGroup.eq_one_iff _).mp
    let q := QuotientGroup.mk' (commutator PSL(2,ZMod 2))
    change q (φ x) = 1
    have htwo : (q (φ x))^2 = 1 := by
      simpa only [hqcard] using (pow_card_eq_one' : (q (φ x)) ^ Nat.card (PSL(2,ZMod 2) ⧸ commutator PSL(2,ZMod 2)) = 1)
    have hthree : (q (φ x))^3 = 1 := by
      rw [←map_pow,←map_pow,←hA,pow_card_eq_one',map_one,map_one]
    simpa only [pow_succ,htwo,one_mul] using hthree
  have heq : φ.range = commutator PSL(2,ZMod 2) :=
    eq_of_le_of_card_ge hle (by rw [hcard,hd])
  let a := (MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr heq)
  refine ⟨a,c,?_⟩
  intro x w
  change c (ρ x w) = naturalAutEquiv (s.symm (φ x)) (c w)
  change c (ρ x w) = naturalAutEquiv
    (s.symm (s (naturalAutEquiv.symm ((MulAut.congr c) (ρ x))))) (c w)
  rw [s.symm_apply_apply,naturalAutEquiv.apply_symm_apply]
  simp only [MulAut.congr_apply,MulEquiv.trans_apply,c.symm_apply_apply]

end BinaryFour

private theorem cubic_quadratic_trivial {V : Type*} [Group V] [IsElementaryAbelian 2 V]
    (a : MulAut V) (hcube : a ^ 3 = 1)
    (hfix : ∀ v, a (v⁻¹ * a v) = v⁻¹ * a v) : a = 1 := by
  have hsquare (v : V) : v * v = 1 := by
    simpa only [pow_two] using (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) v)
  have hinv (v : V) : v⁻¹ = v := inv_eq_of_mul_eq_one_left (hsquare v)
  have htwo (v : V) : a (a v) = v := by
    have hv := hfix v
    rw [map_mul,map_inv,hinv,hinv] at hv
    calc
      a (a v) = a v * (a v * a (a v)) := by rw [←mul_assoc,hsquare,one_mul]
      _ = a v * (v * a v) := by rw [hv]
      _ = v * (a v * a v) := by ac_rfl
      _ = v := by rw [hsquare,mul_one]
  ext v
  have hc := congrArg (fun b : MulAut V => b v) hcube
  change a (a (a v)) = v at hc
  rwa [htwo] at hc

variable {B H : Type*} [Group B] [Group H] [Finite H] (e : B →* H)

/-- The whole original quotient acts on the actual moved subgroup before
dividing by fixed points. -/
theorem exists_moved_action :
    ∃ β : LocalStar e →* MulAut (moved e),
      ∀ (g : H) (w : moved e), β (QuotientGroup.mk' (localKernel e) g) w =
        movedConjugate e g w := by
  let δ : H →* MulAut (moved e) := MulAut.conjNormal
  have hk : localKernel e ≤ δ.ker := by
    rw [MulAut.conjNormal_ker_eq_centralizer]
    exact centralizer_le (moved_le_localV e)
  exact ⟨QuotientGroup.lift (localKernel e) δ hk,fun _ _ => rfl⟩

/-- A cubic generalized-Fitting actor is detected on the actual moved
subgroup. An actor in the kernel would act quadratically and cubically on
the original elementary module, and hence act trivially. -/
theorem moved_action_cubic_faithful [IsElementaryAbelian 2 (localV e)]
    (hc : Nat.card (generalizedFitting (LocalStar e)) = 3)
    (β : LocalStar e →* MulAut (moved e))
    (hβ : ∀ (g : H) (w : moved e), β (QuotientGroup.mk' (localKernel e) g) w =
      movedConjugate e g w) :
    Function.Injective (β.comp (generalizedFitting (LocalStar e)).subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  change a = 1
  let q := QuotientGroup.mk' (localKernel e)
  obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective (localKernel e) (a : LocalStar e)
  have hgA : g ∈ actorLift e := by
    change q g ∈ generalizedFitting (LocalStar e)
    rw [hg]
    exact a.property
  have hfix (w : moved e) : movedConjugate e g w = w := by
    rw [←hβ,hg]
    exact congrArg (fun f : MulAut (moved e) => f w) ha
  let f : MulAut (localV e) := MulAut.conjNormal g
  have hf3 : f^3 = 1 := by
    change (MulAut.conjNormal g : MulAut (localV e))^3 = 1
    rw [←map_pow]
    apply MonoidHom.mem_ker.mp
    rw [MulAut.conjNormal_ker_eq_centralizer]
    change g^3 ∈ localKernel e
    apply (QuotientGroup.eq_one_iff _).mp
    change q (g^3) = 1
    rw [map_pow,hg]
    exact congrArg Subtype.val (by simpa only [hc] using
      (pow_card_eq_one' : a^Nat.card (generalizedFitting (LocalStar e)) = 1))
  have hf : f = 1 := cubic_quadratic_trivial f hf3 (by
    intro v
    have hw : ((v⁻¹ * f v : localV e) : H) ∈ moved e := by
      change (v : H)⁻¹ * (g * (v : H) * g⁻¹) ∈ ⁅localV e,actorLift e⁆
      simpa only [commutatorElement_def,inv_inv,mul_assoc] using
        commutator_mem_commutator ((localV e).inv_mem v.property) hgA
    apply Subtype.ext
    exact congrArg (fun w : moved e => (w : H)) (hfix ⟨_,hw⟩))
  have hgker : g ∈ localKernel e := by
    change g ∈ centralizer (localV e : Set H)
    rw [←MulAut.conjNormal_ker_eq_centralizer]
    exact hf
  apply Subtype.ext
  exact hg.symm.trans ((QuotientGroup.eq_one_iff _).mpr hgker)

/-- In the cubic four-group case the literal moved fixed subgroup vanishes. -/
theorem movedFixed_eq_bot_of_cubic_four [IsElementaryAbelian 2 (localV e)]
    (hc : Nat.card (generalizedFitting (LocalStar e)) = 3)
    (hw : Nat.card (moved e) = 4) : movedFixed e = ⊥ := by
  let : IsElementaryAbelian 2 (moved e) := IsElementaryAbelian.of_le (moved_le_localV e)
  let : Nontrivial (moved e) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour (moved e) := ⟨hw,IsElementaryAbelian.exponent_eq_prime⟩
  obtain ⟨β,hβ⟩ := exists_moved_action e
  let ρ := β.comp (generalizedFitting (LocalStar e)).subtype
  have hi : Function.Injective ρ := moved_action_cubic_faithful e hc β hβ
  have hrc : Nat.card ρ.range = 3 :=
    (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).symm.trans hc
  apply bot_unique
  intro w hw
  change w = 1
  by_contra hne
  have hp : IsPGroup 2 ρ.range := IsKleinFour.isPGroup_aut_subgroup_of_fixed_ne_one
    ρ.range hne (by
      rintro _ ⟨a,rfl⟩
      obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective (localKernel e) (a : LocalStar e)
      have hgA : g ∈ actorLift e := by
        change QuotientGroup.mk' (localKernel e) g ∈ generalizedFitting (LocalStar e)
        rw [hg]
        exact a.property
      change β a w = w
      rw [←hg,hβ]
      apply Subtype.ext
      change g * (w : H) * g⁻¹ = w
      exact mul_inv_eq_iff_eq_mul.mpr (hw g hgA))
  have hcases : Nat.card ρ.range = 1 ∨ 2 ∣ Nat.card ρ.range := hp.card_eq_or_dvd
  rw [hrc] at hcases
  norm_num at hcases

/-- Cubic actor and four-element displacement in the original elementary
local module construct the full compatible C.1.17 marking over F₂. -/
theorem naturalModel_of_cubic_four [IsElementaryAbelian 2 (localV e)]
    (hc : Nat.card (generalizedFitting (LocalStar e)) = 3)
    (hw : Nat.card (moved e) = 4) : Nonempty (NaturalModel e (ZMod 2)) := by
  let : IsElementaryAbelian 2 (moved e) := IsElementaryAbelian.of_le (moved_le_localV e)
  obtain ⟨β,hβ⟩ := exists_moved_action e
  let ρ := β.comp (generalizedFitting (LocalStar e)).subtype
  have hi : Function.Injective ρ := moved_action_cubic_faithful e hc β hβ
  obtain ⟨a,c,hcρ⟩ := BinaryFour.cubic_four_coordinates hc hw ρ hi
  have hf := movedFixed_eq_bot_of_cubic_four e hc hw
  let f : MovedModule e →* Multiplicative (Fin 2 → ZMod 2) :=
    QuotientGroup.lift (movedFixed e) c.toMonoidHom (by rw [hf]; exact bot_le)
  have hfm (w : moved e) : f (QuotientGroup.mk' (movedFixed e) w) = c w := rfl
  have hfi : Function.Injective f := by
    intro x y hxy
    obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (movedFixed e) x
    obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (movedFixed e) y
    exact congrArg (QuotientGroup.mk' (movedFixed e)) (c.injective hxy)
  have hfs : Function.Surjective f := by
    intro v
    exact ⟨QuotientGroup.mk' (movedFixed e) (c.symm v),c.apply_symm_apply v⟩
  refine ⟨{
    actorIso := a
    moduleIso := MulEquiv.ofBijective f ⟨hfi,hfs⟩
    intertwining := ?_}⟩
  intro g w
  change (f (QuotientGroup.mk' (movedFixed e) (movedConjugate e g w))).toAdd = _
  rw [hfm]
  have hh := hcρ (actorProjection e g) w
  change c (β (QuotientGroup.mk' (localKernel e) g) w) = _ at hh
  rw [hβ] at hh
  exact congrArg Multiplicative.toAdd hh

/-- An original marked minimal parabolic with characteristic two belongs
to the binary C.1.17 class as soon as its actual cubic actor and moved
four-group have been computed. No module coordinates are assumed. -/
theorem inLocalClass_of_cubic_four [IsElementaryAbelian 2 (localV e)]
    (he : Function.Injective e)
    (hs : ∃ T : Sylow 2 H, e.range = (T : Subgroup H) ∧
      ChapterB.IsMinimalParabolicOver T ⊤)
    (hfit : generalizedFitting H = pCore 2 H)
    (hc : Nat.card (generalizedFitting (LocalStar e)) = 3)
    (hw : Nat.card (moved e) = 4) : InLocalClass e := by
  refine ⟨he,hs,hfit,1,by decide,ZMod 2,inferInstance,inferInstance,inferInstance,?_,
    naturalModel_of_cubic_four e hc hw⟩
  simp only [Nat.card_zmod,pow_one]

end CFSG.Quasithin.ChapterC.GlaubermanNiles
