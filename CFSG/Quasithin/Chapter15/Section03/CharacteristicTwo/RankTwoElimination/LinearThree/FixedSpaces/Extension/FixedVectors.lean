module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.CentralAttachments.Upper
public import Theory.Representation.PSL3Two.FourGroupGeometry.FixedSpaces.Certificates

/-!
# Fixed vectors in binary linear-three extensions

If the moving part of an SL₃(2)-module has a homogeneous natural quotient
whose kernel is its fixed space, every involution-fixed vector lies in the
sum of the moving part and the full fixed space. The quotient cocycle is
principal because restriction to a transvection detects natural H¹. The
remaining central cocycle vanishes by perfectness. Involution conjugacy
then removes any dependence on the marking or on a chosen radical.

The cocycle argument is adapted locally from the private proof in
`ModuleAlternatives.CentralAttachments.Involution`, without changing that
shared module. No splitting, FF bound or finite-dimensional hypothesis is
needed. This supplies the extension calculation used in 15.3.23; the actual
natural quotient and a nontrivial involution in the radical image still
have to be constructed in its application.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.8,
printed pp.91–92, and 15.3.23, printed p.1128.
-/

@[expose] public section

open Representation Representation.BinaryOffender Representation.OneCohomology
open Matrix Matrix.SpecialLinearGroup
open CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.CentralAttachments
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension

private def transvection : SL :=
  SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) 1

/-- Restriction to the indicated involution detects natural first cohomology. -/
private theorem principal_of_zero_at_transvection
    (f : cocycles (specialLinearNatural (k := ZMod 2) 3)) (hf : f.val transvection = 0) :
    ∃ v : Fin 3 → ZMod 2, principal (specialLinearNatural (k := ZMod 2) 3) v = f := by
  obtain ⟨a, v, hv⟩ := SLHigherNatural.SLThreeBinary.normal_form f
  have hex : SLHigherNatural.SLThreeBinary.exceptional.val transvection 1 = 1 :=
    SLHigherNatural.SLThreeBinary.exceptional_spare 0 2 1 (by decide) (by decide) (by decide)
  have hp : (principal (specialLinearNatural (k := ZMod 2) 3) v).val transvection 1 = 0 := by
    unfold transvection
    rw [SLHigherNatural.principal_transvection]
    simp only [Pi.single_eq_of_ne (by decide : (1 : Fin 3) ≠ 0)]
  have ha : a = 0 := by
    have h := congrArg (fun c : cocycles (specialLinearNatural (k := ZMod 2) 3) =>
      c.val transvection 1) hv
    change f.val transvection 1 = a * SLHigherNatural.SLThreeBinary.exceptional.val transvection 1 +
      (principal (specialLinearNatural 3) v).val transvection 1 at h
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

/-- Involution fixed points lie in the moving-plus-fixed sum, including nonsplit extensions. -/
theorem involution_fixed_le_centralSum {m : ℕ}
    (q : ModuleQuotient (moving ρ).toRepresentation m)
    (t : SL) (ht : t ^ 2 = 1) (hne : t ≠ 1) :
    fixedSpace ρ (Subgroup.zpowers t) ≤ centralSum ρ := by
  have hnt : q.marking t ≠ 1 := by
    intro h
    exact hne (q.marking.injective (h.trans (map_one q.marking).symm))
  have hsq : q.marking t * q.marking t = 1 := by
    rw [← map_mul, ← pow_two, ht, map_one]
  obtain ⟨c, hc⟩ := BinaryLinearThree.FourGroupGeometry.FixedSpaces.exists_involution_conjugator
    (q.marking t) hnt hsq
  have he : BinaryLinearThree.FourGroupGeometry.FixedSpaces.involution = transvection := by
    decide
  rw [he] at hc
  let k := q.marking.symm c
  let b := q.marking.symm transvection
  have htk : t * k = k * b := by
    apply q.marking.injective
    simpa only [map_mul, k, b, q.marking.apply_symm_apply] using hc
  have hb : b * k⁻¹ = k⁻¹ * t := by
    calc b * k⁻¹ = k⁻¹ * (k * b) * k⁻¹ := by group
         _ = k⁻¹ * (t * k) * k⁻¹ := by rw [htk]
         _ = k⁻¹ * t := by group
  intro v hv
  have htv := (mem_fixedSpace_zpowers_iff ρ t v).mp hv
  have hw : ρ k⁻¹ v ∈ fixedSpace ρ (Subgroup.zpowers b) := by
    apply (mem_fixedSpace_zpowers_iff ρ b _).mpr
    calc ρ b (ρ k⁻¹ v) = ρ (b * k⁻¹) v := by rw [map_mul]; rfl
         _ = ρ (k⁻¹ * t) v := by rw [hb]
         _ = ρ k⁻¹ (ρ t v) := by rw [map_mul]; rfl
         _ = ρ k⁻¹ v := by rw [htv]
  have hsum := transvection_fixed_le_centralSum_of_quotient q hw
  obtain ⟨u, hu, z, hz, huz⟩ := Submodule.mem_sup.mp hsum
  have hu' : ρ k u = u := hu ⟨k, Subgroup.mem_top k⟩
  have hz' := (moving ρ).apply_mem_toSubmodule k hz
  have hv' : ρ k (ρ k⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [← huz, map_add, hu'] at hv'
  exact hv' ▸ Submodule.add_mem_sup hu hz'

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension

end
