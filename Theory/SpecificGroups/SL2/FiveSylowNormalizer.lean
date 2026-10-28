module
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv
public import Theory.SpecificGroups.Alternating.FiveSylowNormalizerCard
public import Theory.GroupTheory.SylowNormalizerCommutingFamily

/-!
# A cubic element in a Sylow normalizer above SL₂(5)

A surjection onto SL₂(5) induces a surjection onto A₅. Sylow normalizers
map onto their image normalizers, whose order in A₅ is twelve. Thus every
Sylow two-normalizer upstairs has order divisible by three, without any
restriction on the kernel.

The actual component application is in CartanCore.Actions.FieldDetection.
NilpotentNormalizer, in the analysis of Aschbacher--Smith 11.5.6(3),
printed pp.780--781.
-/

public noncomputable section
open Subgroup

namespace Theory.GroupTheory
/-- Every Sylow two-normalizer above SL₂(5) has a cubic divisor. -/
theorem three_dvd_sylow_normalizer_of_sl2_five_quotient
    {B F : Type*} [Group B] [Finite B] [Field F] [Finite F]
    (hF : Nat.card F = 5)
    (f : B →* Matrix.SpecialLinearGroup (Fin 2) F) (hf : Function.Surjective f)
    (S : Sylow 2 B) : 3 ∣ Nat.card (normalizer (S : Set B)) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 5 := (ZMod.ringEquivOfPrime F (by decide : Nat.Prime 5)
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let e := (Atlas.fieldEquivPSL 2 eF).trans
    Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five.some
  let π := QuotientGroup.mk' (center (Matrix.SpecialLinearGroup (Fin 2) F))
  let q := e.toMonoidHom.comp (π.comp f)
  have hq : Function.Surjective q := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp hf)
  let Q := S.mapSurjective hq
  have hm : (normalizer (S : Set B)).map q = normalizer (Q : Set _) :=
    S.normalizer_map_surjective q hq
  have hc := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_card Q
  have hd : 3 ∣ Nat.card ((normalizer (S : Set B)).map q) := by
    rw [hm,hc]
    decide
  exact hd.trans (card_map_dvd _ q)
end Theory.GroupTheory
