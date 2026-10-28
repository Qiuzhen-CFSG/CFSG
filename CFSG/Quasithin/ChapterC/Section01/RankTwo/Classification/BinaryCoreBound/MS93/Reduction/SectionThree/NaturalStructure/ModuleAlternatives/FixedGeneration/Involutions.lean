module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.FixedGeneration.Defs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.CentralAttachments

/-!
# Full two-subgroup fixed spaces lie in the central sum

Restriction to a marked transvection detects natural first cohomology. A
principal natural quotient cocycle lifts to the moving module: its remaining
central cocycle vanishes by perfectness. Involution conjugacy then puts the
fixed space of every nontrivial two-subgroup inside C + D.

The private detection argument and finite conjugacy certificate are adapted
from `CentralAttachments.Involution`, whose public boundary is preserved.
Source: Meierfrankenfeld–Stellmacher (1993), (3.2), printed p.863;
Aschbacher–Smith B.4.8–9 and B.5.1, printed pp.91–103.
-/

@[expose] public section
open Representation Representation.BinaryOffender Representation.OneCohomology
open Matrix Matrix.SpecialLinearGroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.FixedGeneration
open AbelianCore.QuotientRecognition CentralAttachments
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


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem involution_conjugacy : ∀ a : SL, a ^ 2 = 1 → a ≠ 1 →
    ∃ c : SL, c * a = transvection * c := by decide +kernel

/-- Involution fixed vectors cannot reach an upper central attachment. -/
theorem involution_fixed_le_centralSum {m : ℕ}
    (q : ModuleQuotient (moving ρ).toRepresentation m)
    (t : SL) (ht : t ^ 2 = 1) (hne : t ≠ 1) :
    fixedSpace ρ (Subgroup.zpowers t) ≤ centralSum ρ := by
  obtain ⟨c, hc⟩ := involution_conjugacy (q.marking t)
    (by rw [← map_pow, ht, map_one])
    (fun h => hne (q.marking.injective (h.trans (map_one q.marking).symm)))
  let b := q.marking.symm c
  have hb : b * t = q.marking.symm transvection * b := by
    apply q.marking.injective
    simpa only [b, map_mul, q.marking.apply_symm_apply] using hc
  intro v hv
  have hf : ρ t v = v := (mem_fixedSpace_zpowers_iff ρ t v).mp hv
  have hfixed : ρ b v ∈ fixedSpace ρ (Subgroup.zpowers (q.marking.symm transvection)) := by
    apply (mem_fixedSpace_zpowers_iff ρ _ _).mpr
    calc
      ρ (q.marking.symm transvection) (ρ b v) = ρ b (ρ t v) := by
        rw [← Module.End.mul_apply, ← map_mul, ← hb, map_mul, Module.End.mul_apply]
      _ = ρ b v := congrArg (ρ b) hf
  have hmem := transvection_fixed_le_centralSum_of_quotient q hfixed
  have hdiff : ρ b v - v ∈ centralSum ρ :=
    (show (moving ρ).toSubmodule ≤ centralSum ρ from le_sup_right)
      (moving_hasTrivialQuotient ρ b v)
  simpa only [sub_sub_cancel] using (centralSum ρ).sub_mem hmem hdiff

/-- The full fixed space of every nontrivial two-subgroup lies in C + D. -/
theorem two_fixed_le_centralSum {m : ℕ}
    (q : ModuleQuotient (moving ρ).toRepresentation m)
    (A : Subgroup SL) (hA : IsPGroup 2 A) (hne : A ≠ ⊥) :
    fixedSpace ρ A ≤ centralSum ρ := by
  let : Nontrivial A := A.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := A) 2
    ((hA.dvd_orderOf ha).trans (orderOf_dvd_natCard a))
  have hpow : (t : SL) ^ 2 = 1 := by
    have h : t ^ 2 = 1 := by simpa only [ht] using pow_orderOf_eq_one t
    exact congrArg Subtype.val h
  have htne : (t : SL) ≠ 1 := by
    intro he
    have he' : t = 1 := Subtype.ext he
    simp [he'] at ht
  exact (fixedSpace_antitone ρ (Subgroup.zpowers_le.mpr t.property)).trans
    (involution_fixed_le_centralSum q t hpow htne)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.FixedGeneration
