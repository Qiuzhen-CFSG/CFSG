module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.CentralAttachments.Upper
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.CoreAction.Descent.ComponentOffender.BestProjection.CentralTwist.Generation

/-!
# Excluding incompatible central attachments in FF-modules

Restriction to one marked transvection detects natural first cohomology.
It still detects upper extension classes when the natural quotient has a
fixed kernel: correcting a principal quotient cocycle leaves a cocycle
valued in fixed vectors, and perfectness makes that cocycle zero.

An FF-module for SL₃(2) has involution displacement at most two. Two natural
copies already use both dimensions. A four-dimensional fully moving central
cover also uses both, since three conjugate involutions generate the actor.
Equality of the restricted and ambient displacement dimensions gives a
supplement by the involution's fixed space; cohomological detection puts
that fixed space in C + D. Thus neither the doubled branch nor the lower
nonsplit branch admits an upper attachment.

The finite involution-conjugacy certificate is adapted from the private
calculation in ExtensionControl/Dimension.lean. The three-involution bound
is reused from CentralTwist/Generation.lean, with the central twist equal to one.
Source: Aschbacher–Smith B.4.8–9 and B.5.1(2),(5), printed pp.91–103;
Meierfrankenfeld–Stellmacher (1993), (3.2), printed p.863.
-/

@[expose] public section
open Representation Representation.BinaryOffender Representation.OneCohomology
open Matrix Matrix.SpecialLinearGroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.CentralAttachments
open AbelianCore.QuotientRecognition

private def transvection : SL :=
  SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) 1

/-- Restriction to the indicated involution detects natural first cohomology. -/
private theorem principal_of_zero_at_transvection
    (f : cocycles (specialLinearNatural (k := ZMod 2) 3)) (hf : f.val transvection = 0) :
    ∃ v : Fin 3 → ZMod 2, principal (specialLinearNatural (k := ZMod 2) 3) v = f := by
  obtain ⟨a, v, hv⟩ := SLHigherNatural.SLThreeBinary.normal_form f
  have hex : SLHigherNatural.SLThreeBinary.exceptional.val transvection 2 = 1 :=
    SLHigherNatural.SLThreeBinary.exceptional_spare 0 1 2 (by decide) (by decide) (by decide)
  have hp : (principal (specialLinearNatural (k := ZMod 2) 3) v).val transvection 2 = 0 := by
    unfold transvection
    rw [SLHigherNatural.principal_transvection]
    simp only [Pi.single_eq_of_ne (by decide : (2 : Fin 3) ≠ 0)]
  have ha : a = 0 := by
    have h := congrArg (fun c : cocycles (specialLinearNatural (k := ZMod 2) 3) =>
      c.val transvection 2) hv
    change f.val transvection 2 = a * SLHigherNatural.SLThreeBinary.exceptional.val transvection 2 +
      (principal (specialLinearNatural 3) v).val transvection 2 at h
    rw [hf, hex, hp, mul_one, add_zero] at h
    exact h.symm
  exact ⟨v, by simpa only [ha, zero_smul, zero_add] using hv.symm⟩

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) SL V}


/-- Perfect actors have no nonzero cocycles valued in a fixed subspace. -/
private theorem central_cocycle_zero
    (f : cocycles ρ) (hf : ∀ g, f.val g ∈ fixedSpace ρ ⊤) : f = 0 := by
  let : Group.IsPerfect SL := Atlas.sl_perfect (F := ZMod 2) 3 (by decide)
  let d : SL →* Multiplicative V := {
    toFun g := Multiplicative.ofAdd (f.val g)
    map_one' := by
      have h := f.property 1 1
      change f.val 1 = 0
      simpa only [one_mul, map_one, Module.End.one_apply, left_eq_add] using h
    map_mul' g h := by
      change f.val (g * h) = f.val g + f.val h
      rw [f.property]
      have hh : ρ g (f.val h) = f.val h := hf h ⟨g, Subgroup.mem_top g⟩
      rw [hh, add_comm]
  }
  let : Group.IsPerfect d.range := Group.IsPerfect.range d
  apply Subtype.ext
  funext g
  exact congrArg (fun x : d.range => Multiplicative.toAdd x.val)
    (Subsingleton.elim (⟨d g, g, rfl⟩ : d.range) 1)

/-- Restriction to the marked transvection detects upper extension classes
even when the moving natural quotient has a nonzero fixed kernel. -/
private theorem transvection_fixed_le_centralSum_of_quotient {m : ℕ}
    (q : ModuleQuotient (moving ρ).toRepresentation m) :
    fixedSpace ρ (Subgroup.zpowers (q.marking.symm transvection)) ≤ centralSum ρ := by
  classical
  intro v hv
  let d := displacementCocycle (moving ρ) (moving_hasTrivialQuotient ρ) v
  let f (i : Fin m) : cocycles (specialLinearNatural (k := ZMod 2) 3) :=
    ⟨fun g => q.projection (d.val (q.marking.symm g)) i, by
      intro g h
      dsimp only
      rw [map_mul, d.property, map_add]
      have he := q.equivariant (q.marking.symm g) (d.val (q.marking.symm h)) i
      rw [q.marking.apply_symm_apply] at he
      exact congrArg (fun w => w + q.projection (d.val (q.marking.symm g)) i) he⟩
  have hf (i : Fin m) : (f i).val transvection = 0 := by
    have hv' := (mem_fixedSpace_zpowers_iff ρ _ v).mp hv
    have hd : d.val (q.marking.symm transvection) = 0 := Subtype.ext (sub_eq_zero.mpr hv')
    change q.projection (d.val (q.marking.symm transvection)) i = 0
    rw [hd, map_zero]
    rfl
  choose w hw using fun i => principal_of_zero_at_transvection (f i) (hf i)
  obtain ⟨u, hu⟩ := q.surjective w
  have hc : d - principal (moving ρ).toRepresentation u = 0 := by
    apply central_cocycle_zero
    intro g
    rw [← q.kernel]
    change q.projection (d.val g - ((moving ρ).toRepresentation g u - u)) = 0
    ext i : 1
    simp only [map_sub, Pi.sub_apply, Pi.zero_apply]
    rw [q.equivariant, hu]
    have hi := congrArg (fun c : cocycles (specialLinearNatural (k := ZMod 2) 3) =>
      c.val (q.marking g)) (hw i)
    change specialLinearNatural 3 (q.marking g) (w i) - w i =
      q.projection (d.val (q.marking.symm (q.marking g))) i at hi
    rw [q.marking.symm_apply_apply] at hi
    exact sub_eq_zero.mpr hi.symm
  have hz : extensionClass (moving ρ) (moving_hasTrivialQuotient ρ) v = 0 :=
    (classMap_eq_zero_iff _ d).mpr ⟨u, (sub_eq_zero.mp hc).symm⟩
  rw [← extensionClass_kernel ρ]
  exact hz

/-- Natural copies are the special case of trivial fixed kernel. -/
private theorem transvection_fixed_le_centralSum {m : ℕ}
    (e : Copies (moving ρ).toRepresentation m) :
    fixedSpace ρ (Subgroup.zpowers (e.marking.symm transvection)) ≤ centralSum ρ :=
  transvection_fixed_le_centralSum_of_quotient e.toQuotient

variable [FiniteDimensional (ZMod 2) V]

/-- Each natural copy contributes one displacement dimension at the marked
transvection. This lower bound suffices for the doubled exclusion. -/
private theorem copies_le_transvection_fixedCodim {m : ℕ} (e : Copies ρ m) :
    m ≤ fixedCodim ρ (Subgroup.zpowers (e.marking.symm transvection)) := by
  let t := e.marking.symm transvection
  let f := ρ t - LinearMap.id
  let r : f.range →ₗ[ZMod 2] (Fin m → ZMod 2) := {
    toFun v := fun i => e.equiv v.val i 0
    map_add' v w := by ext i; simp
    map_smul' a v := by ext i; simp
  }
  have hr : Function.Surjective r := by
    intro w
    let v := e.equiv.symm (fun i => Pi.single (1 : Fin 3) (w i))
    refine ⟨⟨f v, v, rfl⟩, ?_⟩
    funext i
    change e.equiv (ρ t v - v) i 0 = w i
    rw [map_sub]
    change e.equiv (ρ t v) i 0 - e.equiv v i 0 = w i
    rw [e.equivariant]
    simp [t, transvection, SLHigherNatural.action_transvection, v]
  have h := LinearMap.finrank_le_finrank_of_surjective hr
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  rw [fixedCodim_zpowers_eq_displacement_rank]
  exact h

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem involution_conjugacy : ∀ a : SL, a ^ 2 = 1 → a ≠ 1 →
    ∃ c : SL, c * a = transvection * c := by decide +kernel

/-- In an FF-action every involution displaces at most two dimensions.
Conjugacy and the elementary rank bound use the actual SL₃(2). -/
theorem involution_fixedCodim_le_two (hFF : IsFFModule ρ) (t : SL)
    (ht : t ^ 2 = 1) (hne : t ≠ 1) : fixedCodim ρ (Subgroup.zpowers t) ≤ 2 := by
  obtain ⟨A, hA⟩ := hFF
  have ha : ∃ a ∈ A, a ≠ (1 : SL) := by
    by_contra! ha
    apply hA.1.1
    apply le_bot_iff.mp
    intro a haA
    exact ha a haA
  obtain ⟨a, ha, hane⟩ := ha
  let : IsElementaryAbelian 2 A := hA.1.2
  obtain ⟨c, hc⟩ := involution_conjugacy a
    (elemPow_eq_one_of_isElementaryAbelian a ha) hane
  obtain ⟨b, hb⟩ := involution_conjugacy t ht hne
  have hc' : c * a * c⁻¹ = transvection := by rw [hc, mul_inv_cancel_right]
  have hb' : b * t * b⁻¹ = transvection := by rw [hb, mul_inv_cancel_right]
  have he : fixedCodim ρ (Subgroup.zpowers t) = fixedCodim ρ (Subgroup.zpowers a) := by
    calc
      _ = fixedCodim ρ (Subgroup.zpowers transvection) := by
        rw [← hb', fixedCodim_zpowers_conj]
      _ = _ := by rw [← hc', fixedCodim_zpowers_conj]
  have hle := fixedSpace_antitone ρ ((Subgroup.zpowers_le).mpr ha)
  have hh := Submodule.finrank_mono hle
  have h₁ := fixedCodim_add_finrank ρ A
  have h₂ := fixedCodim_add_finrank ρ (Subgroup.zpowers a)
  have hr := ExtensionControl.elementary_rank_le_two A hA.1.2
  have hbudget := hA.2
  omega

/-- Upper attachments to a doubled natural commutator module violate the
FF budget. Hence V is the actual direct sum of C and its doubled natural D. -/
theorem doubled_isCompl (hFF : IsFFModule ρ)
    (e : Copies (moving ρ).toRepresentation 2) :
    IsCompl (fixedSpace ρ ⊤) (moving ρ).toSubmodule := by
  let t := e.marking.symm transvection
  have ht : t ^ 2 = 1 := by
    apply e.marking.injective
    rw [map_pow, map_one, e.marking.apply_symm_apply]
    decide
  have hne : t ≠ 1 := by
    intro h
    have he := congrArg e.marking h
    have hbad : transvection = 1 := by simpa only [t, e.marking.apply_symm_apply, map_one] using he
    exact (by decide : transvection ≠ 1) hbad
  have hsmall := involution_fixedCodim_le_two hFF t ht hne
  have hlarge := copies_le_transvection_fixedCodim e
  change 2 ≤ fixedCodim (moving ρ).toRepresentation (Subgroup.zpowers t) at hlarge
  have hmono := fixedCodim_subrepresentation_le ρ (moving ρ) (Subgroup.zpowers t)
  have he : fixedCodim (moving ρ).toRepresentation (Subgroup.zpowers t) =
      fixedCodim ρ (Subgroup.zpowers t) := by omega
  have hsup := (fixedCodim_subrepresentation_eq_iff ρ (moving ρ) _).mp he
  have htop : centralSum ρ = ⊤ := by
    apply top_unique
    rw [← hsup]
    exact sup_le le_sup_right (transvection_fixed_le_centralSum e)
  exact ⟨(disjoint_iff_fixedMoving_eq_bot ρ).mpr e.fixed_eq_bot, codisjoint_iff.mpr htop⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.CentralAttachments

@[expose] public section
open Representation Representation.BinaryOffender Representation.OneCohomology
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.CentralAttachments
open AbelianCore.QuotientRecognition

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) SL V)

/-- A nontrivial lower central attachment excludes an upper attachment in an
FF-module. The proof uses the actual four-dimensional commutator module:
three conjugate involutions span it, so each has displacement at least two;
the FF budget is at most two, and restriction detects the extension class. -/
theorem lower_excludes_upper
    (hFF : IsFFModule ρ) (q : ModuleQuotient (moving ρ).toRepresentation 1)
    (hker : Module.finrank (ZMod 2)
      (fixedSpace ρ ⊤ ⊓ (moving ρ).toSubmodule : Submodule (ZMod 2) V) = 1) :
    centralSum ρ = ⊤ := by
  let t := q.marking.symm transvection
  have ht : t ^ 2 = 1 := by
    apply q.marking.injective
    rw [map_pow, map_one, q.marking.apply_symm_apply]
    decide
  have hne : t ≠ 1 := by
    intro h
    have he := congrArg q.marking h
    have hbad : transvection = 1 := by simpa only [t, q.marking.apply_symm_apply, map_one] using he
    exact (by decide : transvection ≠ 1) hbad
  have hdim : Module.finrank (ZMod 2) (moving ρ).toSubmodule = 4 := by
    have h := q.projection.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr q.surjective, finrank_top, q.kernel,
      (fixedMovingEquiv ρ).finrank_eq, hker] at h
    have hn : Module.finrank (ZMod 2) (Fin 1 → Fin 3 → ZMod 2) = 3 := by
      simp [Module.finrank_pi_fintype]
    omega
  have hbound := ComponentOffender.BestProjection.CentralTwist.finrank_le_three_mul_twist_codim
    (moving ρ).toRepresentation (MonoidHom.id SL) 1 (by simp)
    (fun _ => Commute.one_left _) (by simpa using moving_full ρ) t ht hne
  simp only [MonoidHom.id_apply, mul_one, hdim] at hbound
  have hsmall := involution_fixedCodim_le_two hFF t ht hne
  have hmono := fixedCodim_subrepresentation_le ρ (moving ρ) (Subgroup.zpowers t)
  have he : fixedCodim (moving ρ).toRepresentation (Subgroup.zpowers t) =
      fixedCodim ρ (Subgroup.zpowers t) := by omega
  have hsup := (fixedCodim_subrepresentation_eq_iff ρ (moving ρ) _).mp he
  apply top_unique
  rw [← hsup]
  exact sup_le le_sup_right (transvection_fixed_le_centralSum_of_quotient q)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.CentralAttachments
