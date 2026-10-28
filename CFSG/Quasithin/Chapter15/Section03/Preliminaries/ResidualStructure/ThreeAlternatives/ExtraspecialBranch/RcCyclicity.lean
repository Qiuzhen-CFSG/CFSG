module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.ThreeAlternatives.ExtraspecialBranch.Geometry
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.OrthogonalImage.CoreImage
public import Theory.GroupTheory.WreathTwoResidual
public import Theory.GroupAction.Extraspecial27ElementaryActor
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators


/-!
# Cyclicity of the Rc image in the extraspecial branch of 15.3.7

The actual conjugation action of Rc* on Y* is faithful. Indeed, an element
of its kernel has orthogonal image centralizing the full E₉ residual. The
intersection of this centralizer with a Sylow two-subgroup is normal in
that Sylow subgroup. If nontrivial, the wreath residual theorem supplies
an element inverting E₉, contradicting centralization. The already proved
injectivity of the orthogonal actor on Rc* then kills the original kernel.

This faithful action fixes Z(Y*) pointwise, so every elementary two-subgroup
of Rc* has order at most two. The orthogonal actor also embeds Rc* in its
actual D₈ Sylow subgroup. The rotation/reflection formulas show that a
subgroup of D₈ without an elementary four-group is cyclic. Passing to the
orthogonal image gives the required cyclicity of R̄c.

Only extraspeciality and order 27 are needed from the branch data; the
Heisenberg model need not be chosen. No identification of the whole
center-fixing automorphism group with Q₈ is asserted.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma 15.3.7,
printed p.1122 (PDF p.1139), final paragraph.
-/

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.ThreeAlternatives.ExtraspecialBranch

private theorem residual_notation (H : Subgroup OrthogonalActor) :
    twoResidualAmbient H = (pResidual 2 H).map H.subtype := by
  unfold twoResidualAmbient twoResidualSubgroup pResidual
  congr 1
  congr 1
  ext N
  constructor
  · rintro ⟨hN, n, hn⟩
    let := hN
    exact ⟨hN, IsPGroup.iff_card.mpr ⟨n, by simpa [Subgroup.index_eq_card] using hn⟩⟩
  · rintro ⟨hN, hp⟩
    let := hN
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
    exact ⟨hN, n, by simpa [Subgroup.index_eq_card] using hn⟩

private theorem actor_residual_notation :
    twoResidualAmbient (⊤ : Subgroup OrthogonalActor) = pResidual 2 OrthogonalActor := by
  rw [residual_notation]
  exact map_pResidual 2 Subgroup.topEquiv

private theorem sylow_inf_residual_centralizer (S : Sylow 2 OrthogonalActor) :
    (S : Subgroup OrthogonalActor) ⊓
      centralizer (pResidual 2 OrthogonalActor : Set OrthogonalActor) = ⊥ := by
  let C := centralizer (pResidual 2 OrthogonalActor : Set OrthogonalActor)
  let R := (S : Subgroup OrthogonalActor) ⊓ C
  by_contra hn
  have hnorm : (S : Subgroup OrthogonalActor) ≤ normalizer (R : Set OrthogonalActor) :=
    (le_inf (S : Subgroup OrthogonalActor).le_normalizer
      (le_normalizer_of_normal (H := C))).trans inf_normalizer_le_normalizer_inf
  obtain ⟨r, hr, _, hi⟩ := Theory.GroupTheory.WreathTwoResidual.exists_normal_sylow_inverter
    S R inf_le_left hnorm hn
  obtain ⟨e⟩ := Theory.GroupTheory.WreathTwoResidual.residual_equiv_elementaryNine
  let c : Multiplicative (Fin 2 → ZMod 3) := Multiplicative.ofAdd (fun _ => 1)
  let x := e.symm c
  have hc : c ≠ c⁻¹ := by decide
  apply hc
  have hcomm := mem_centralizer_iff.mp hr.2 (x : OrthogonalActor) x.property
  have hxinv : (x : OrthogonalActor) = (x : OrthogonalActor)⁻¹ := by
    rw [← hi _ x.property, ← hcomm, mul_inv_cancel_right]
  have he := congrArg e (show x = x⁻¹ from Subtype.ext hxinv)
  simpa only [map_inv, x, e.apply_symm_apply] using he

open DihedralGroup in
private theorem dihedral_cyclic_of_no_four (D : Subgroup (DihedralGroup 4))
    (hfour : ∀ a b : D, a * a = 1 → b * b = 1 → Commute a b →
      a = 1 ∨ b = 1 ∨ a = b) : IsCyclic D := by
  classical
  by_cases hrot : D ≤ zpowers (r 1)
  · exact Subgroup.isCyclic_of_le hrot
  obtain ⟨x, hx, hxr⟩ := SetLike.not_le_iff_exists.mp hrot
  have hrotmem (i : ZMod 4) : r i ∈ zpowers (r 1 : DihedralGroup 4) := by
    refine ⟨(i.val : ℤ), ?_⟩
    change (r 1 : DihedralGroup 4) ^ (i.val : ℤ) = r i
    rw [r_one_zpow]
    simp
  cases x with
  | r i => exact (hxr (hrotmem i)).elim
  | sr i =>
    have hcentral : r (2 : ZMod 4) ∉ D := by
      intro hz
      let a : D := ⟨sr i, hx⟩
      let b : D := ⟨r 2, hz⟩
      have hsq : b * b = 1 := Subtype.ext
        (show r (2 : ZMod 4) * r 2 = (1 : DihedralGroup 4) from by decide)
      have hcomm : Commute a b := by
        apply Subtype.ext
        exact (by decide : ∀ i : ZMod 4, sr i * r 2 = r 2 * sr i) i
      rcases hfour a b (Subtype.ext (by simp [a])) hsq hcomm with ha | hb | hab
      · have := congrArg D.subtype ha
        exact (by decide : ∀ i : ZMod 4, sr i ≠ (1 : DihedralGroup 4)) i this
      · exact (by decide : r (2 : ZMod 4) ≠ (1 : DihedralGroup 4)) (congrArg D.subtype hb)
      · have := congrArg D.subtype hab
        simp [a, b] at this
    apply Subgroup.isCyclic_of_le (H' := zpowers (sr i))
    intro y hy
    have hcases : y = 1 ∨ y = sr i := by
      by_contra hn
      have hn1 : y ≠ 1 := fun hh => hn (Or.inl hh)
      have hni : y ≠ sr i := fun hh => hn (Or.inr hh)
      have hfinite : ∀ (i : ZMod 4) (y : DihedralGroup 4), y ≠ 1 → y ≠ sr i →
          y = r 2 ∨ y ^ 2 = r 2 ∨ sr i * y = r 2 ∨ (sr i * y) ^ 2 = r 2 := by
        decide +kernel
      apply hcentral
      rcases hfinite i y hn1 hni with h | h | h | h
      · exact h ▸ hy
      · exact h ▸ D.pow_mem hy 2
      · exact h ▸ D.mul_mem hx hy
      · exact h ▸ D.pow_mem (D.mul_mem hx hy) 2
    rcases hcases with rfl | rfl
    · exact one_mem _
    · exact mem_zpowers _

private theorem center_preserving_no_four {F A : Type*} [Group F] [Finite F]
    [IsExtraspecial 3 F] [Group A] [Finite A]
    (hF : Nat.card F = 27) (action : A →* MulAut F) (hinj : Function.Injective action)
    (hcenter : ∀ a : A, ∀ z ∈ center F, action a z = z)
    (a b : A) (ha : a * a = 1) (hb : b * b = 1) (hab : Commute a b) :
    a = 1 ∨ b = 1 ∨ a = b := by
  by_contra hn
  have ha1 : a ≠ 1 := fun hh => hn (Or.inl hh)
  have hb1 : b ≠ 1 := fun hh => hn (Or.inr (Or.inl hh))
  have hne : a ≠ b := fun hh => hn (Or.inr (Or.inr hh))
  let E := closure ({a,b} : Set A)
  let : IsKleinFour E := isKleinFour_closure_pair a b ha hb ha1 hb1 hne hab
  let : IsElementaryAbelian 2 E := {
    toIsMulCommutative := IsKleinFour.isMulCommutative
    exponent_dvd_p := by rw [IsKleinFour.exponent_two] }
  have hsmall := MulAut.elementary_two_center_preserving_card_le_two hF
    (action.domRestrict E) (hinj.comp E.subtype_injective)
    (fun e z hz => hcenter e z hz)
  rw [IsKleinFour.card_four] at hsmall
  omega

private theorem cyclic_of_dihedral_embedding {F A : Type*} [Group F] [Finite F]
    [IsExtraspecial 3 F] [Group A] [Finite A]
    (hF : Nat.card F = 27) (action : A →* MulAut F) (hinj : Function.Injective action)
    (hcenter : ∀ a : A, ∀ z ∈ center F, action a z = z)
    (j : A →* DihedralGroup 4) (hj : Function.Injective j) : IsCyclic A := by
  let e := MonoidHom.ofInjective hj
  let aD := action.comp e.symm.toMonoidHom
  have hD : IsCyclic j.range := dihedral_cyclic_of_no_four j.range
    (center_preserving_no_four hF aD (hinj.comp e.symm.injective)
      (fun a z hz => hcenter (e.symm a) z hz))
  let := hD
  exact isCyclic_of_injective e.toMonoidHom e.injective

variable {G : Type*} [Group G] [Finite G]
variable {M Mc V : Subgroup G} {T : Sylow 2 G} {d : NaturalOrthogonalAction M V}

/-- The actual conjugation action of Rc* on the star residual is faithful. -/
public theorem star_rc_conjugation_injective (h : SourceInputs M Mc V T d) :
    Function.Injective
      ((MulAut.conjNormal : StarGroup M →* MulAut (star M (residualY M Mc))).domRestrict
        (star M (Rc M Mc))) := by
  let P := star M (residualY M Mc)
  let R := star M (Rc M Mc)
  let f := starActor d h.core_le_kernel
  let S := d.sylowImage T h.sylow_le
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro r hr
  have hrc : f r ∈ d.intersectionCoreImage Mc := by
    change f r ∈ ((Rc M Mc).subgroupOf M).map d.actor
    rw [← map_starActor d h.core_le_kernel (Rc M Mc)]
    exact mem_map_of_mem f r.property
  have hc : f r ∈ centralizer (pResidual 2 OrthogonalActor : Set OrthogonalActor) := by
    apply mem_centralizer_iff.mpr
    intro y hy
    have himage : P.map f = pResidual 2 OrthogonalActor :=
      (map_starActor d h.core_le_kernel _).trans (h.residual_image.trans actor_residual_notation)
    obtain ⟨x, hx, rfl⟩ := himage.symm ▸ hy
    have he : (r : StarGroup M) * x * (r : StarGroup M)⁻¹ = x :=
      congrArg (fun a : MulAut P => (a ⟨x, hx⟩ : StarGroup M)) hr
    have hcomm := (mul_inv_eq_iff_eq_mul.mp he).symm
    simpa only [map_mul] using congrArg f hcomm
  have hone : f r = 1 := mem_bot.mp
    ((sylow_inf_residual_centralizer S).le
      ⟨d.intersectionCoreImage_le_sylowImage Mc T h.sylow_le h.sylow_le_partner hrc, hc⟩)
  apply mem_bot.mpr
  exact star_rc_actor_injective h (hone.trans (map_one _).symm)

/-- In the extraspecial branch, the actual Rc action image is cyclic. -/
public theorem extraspecial_rc_image_cyclic (h : SourceInputs M Mc V T d)
    [IsExtraspecial 3 (star M (residualY M Mc))]
    (hcard : Nat.card (star M (residualY M Mc)) = 27) :
    IsCyclic (((Rc M Mc).subgroupOf M).map d.actor) := by
  let P := star M (residualY M Mc)
  let R := star M (Rc M Mc)
  let f := starActor d h.core_le_kernel
  let S := d.sylowImage T h.sylow_le
  have himage : R.map f = d.intersectionCoreImage Mc := map_starActor d h.core_le_kernel _
  let i : R →* S := (f.domRestrict R).codRestrict S (fun r =>
    d.intersectionCoreImage_le_sylowImage Mc T h.sylow_le h.sylow_le_partner
      (himage ▸ mem_map_of_mem f r.property))
  have hi : Function.Injective i := fun x y he =>
    star_rc_actor_injective h (congrArg Subtype.val he)
  obtain ⟨e⟩ := wreath_two_sylow_mulEquiv_dihedral_four S
  let a : R →* MulAut P := MulAut.conjNormal.domRestrict R
  let : IsCyclic R := cyclic_of_dihedral_embedding hcard a (star_rc_conjugation_injective h)
    (fun r z hz => star_residual_center_fixed_by_rc h r r.property z hz)
    (e.toMonoidHom.comp i) (e.injective.comp hi)
  have himage' : IsCyclic (R.map f) :=
    isCyclic_of_surjective (f.subgroupMap R) (f.subgroupMap_surjective R)
  rwa [map_starActor] at himage'

end CFSG.Quasithin.Chapter15.Section03.ThreeAlternatives.ExtraspecialBranch
