module
public import Theory.Representation.BinaryAlternatingSevenControl.PointGeneration
public import Theory.Representation.AlternatingSevenConjugatePair.Model.InnerElements
public import Theory.LinearAlgebra.BinaryFourPointStabilizer
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.SpecificGroups.FifteenPointSubgroups.AlternatingSeven
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Theory.Representation.BinaryOffender.IrreducibleMovedGeneration

/-!
# The central-line action in the binary A₇ four-space

The point stabilizer acts faithfully on the quotient by its fixed line:
a kernel element has square one and displacement rank at most one, whereas
every nonidentity involution of A₇ moves a plane. Its order is 168, so this
literal quotient action is the full GL₃(2), with a concrete PSL₃(2) marking.

The fifteen-point coset action is two-transitive. Consequently the point
stabilizer is transitive on the fourteen vectors outside its line, and its
commutator space is the entire original four-space. The Chapter 12 consumer
lifts these operators through the actual solvable residual of C_L(z).

Source: Aschbacher--Smith, Lemma 12.3.3, printed p.808, using B.4.12(2).
-/

@[expose] public noncomputable section
open Subgroup Representation.BinaryOffender
namespace Representation.BinaryAlternatingSevenControl
open Theory.LinearAlgebra
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

abbrev pointStabilizer (ρ : Representation (ZMod 2) A7 V) (z : V) : Subgroup A7 :=
  subspaceKernel ρ (Submodule.span (ZMod 2) {z}) ⊤

omit [FiniteDimensional (ZMod 2) V] in
theorem mem_pointStabilizer (ρ : Representation (ZMod 2) A7 V) (z : V) (g : A7) :
    g ∈ pointStabilizer ρ z ↔ ρ g z = z := by
  constructor
  · exact fun h => h.2 z (Submodule.subset_span (by simp))
  · intro h
    refine ⟨mem_top _, ?_⟩
    intro w hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_smul, h]

def pointAction (ρ : Representation (ZMod 2) A7 V) (z : V) :
    pointStabilizer ρ z →* BinaryFivePointStabilizer.stabilizer z :=
  (((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp
    ρ.asGroupHom).comp (pointStabilizer ρ z).subtype).codRestrict _
      (fun g => (mem_pointStabilizer ρ z g).mp g.property)

def pointQuotientAction (ρ : Representation (ZMod 2) A7 V) (z : V) :
    pointStabilizer ρ z →*
      (BinaryFivePointStabilizer.QuotientSpace z ≃ₗ[ZMod 2]
        BinaryFivePointStabilizer.QuotientSpace z) :=
  (BinaryFivePointStabilizer.quotientAction z).comp (pointAction ρ z)

omit [FiniteDimensional (ZMod 2) V] in
@[simp] theorem pointQuotientAction_mk (ρ : Representation (ZMod 2) A7 V)
    (z v : V) (g : pointStabilizer ρ z) :
    pointQuotientAction ρ z g ((BinaryFivePointStabilizer.line z).mkQ v) =
      (BinaryFivePointStabilizer.line z).mkQ (ρ g v) := rfl

theorem pointStabilizer_card (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    {z : V} (hz : z ≠ 0) : Nat.card (pointStabilizer ρ z) = 168 := by
  obtain ⟨P,hP⟩ := exists_sylow_fixed_span ρ hf hd hz
  have hi : (pointStabilizer ρ z).index = 15 := by
    rw [pointStabilizer, ← hP]
    exact sylow_fixedKernel_index ρ hf hd P
  have hc := (pointStabilizer ρ z).card_mul_index
  have hA : Nat.card A7 = 2520 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  rw [hi, hA] at hc
  omega

theorem pointQuotientAction_injective (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    {z : V} (hz : z ≠ 0) : Function.Injective (pointQuotientAction ρ z) := by
  apply (injective_iff_map_eq_one (pointQuotientAction ρ z)).mpr
  intro g hg
  by_contra hne
  have hgi : Function.Injective (pointAction ρ z) := by
    intro a b hab
    apply Subtype.ext
    apply hf
    exact congrArg (fun x : BinaryFivePointStabilizer.stabilizer z =>
      x.val.toLinearMap) hab
  have hk : pointAction ρ z g ∈ BinaryFivePointStabilizer.kernel z := hg
  have hsq : g ^ 2 = 1 := by
    apply hgi
    have hs := congrArg Subtype.val
      (BinaryFivePointStabilizer.kernel_sq z ⟨pointAction ρ z g, hk⟩)
    change (pointAction ρ z g) ^ 2 = 1 at hs
    simpa only [map_pow, map_one] using hs
  have horder : orderOf (g : A7) = 2 := by
    apply orderOf_eq_prime
    · exact congrArg Subtype.val hsq
    · exact fun he => hne (Subtype.ext he)
  have hr : LinearMap.range (ρ g - LinearMap.id) ≤ BinaryFivePointStabilizer.line z := by
    rintro _ ⟨v, rfl⟩
    exact (BinaryFivePointStabilizer.mem_kernel_iff z (pointAction ρ z g)).mp hk v
  have hb := Submodule.finrank_mono hr
  rw [← fixedCodim_zpowers_eq_displacement_rank,
    AlternatingSevenConjugatePair.Model.involution_fixedCodim ρ hf hd g horder,
    finrank_span_singleton hz] at hb
  omega

theorem pointQuotientAction_bijective (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    {z : V} (hz : z ≠ 0) : Function.Bijective (pointQuotientAction ρ z) := by
  let : Finite (BinaryFivePointStabilizer.QuotientSpace z) :=
    Module.finite_of_finite (ZMod 2)
  let : Finite (BinaryFivePointStabilizer.QuotientSpace z ≃ₗ[ZMod 2]
      BinaryFivePointStabilizer.QuotientSpace z) :=
    Finite.of_injective (fun g => (g : _ → _)) DFunLike.coe_injective
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨pointQuotientAction_injective ρ hf hd hz, ?_⟩
  rw [pointStabilizer_card ρ hf hd hz,
    BinaryFourPointStabilizer.card_linearGroup_three
      (BinaryFourPointStabilizer.quotient_finrank z hz hd)]

/-- The marking uses the actual action on the quotient by the fixed vector. -/
def pointStabilizerEquivLinear (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    {z : V} (hz : z ≠ 0) : pointStabilizer ρ z ≃* BinaryLinear.OuterCyclic.LinearGroup 3 :=
  (MulEquiv.ofBijective (pointQuotientAction ρ z)
    (pointQuotientAction_bijective ρ hf hd hz)).trans
      (BinaryLinear.SmallParabolicLevi.linearGroupCongr
        (LinearEquiv.ofFinrankEq _ _ (by
          rw [BinaryFourPointStabilizer.quotient_finrank z hz hd]
          simp [BinaryLinear.OuterCyclic.Space])))

def pointStabilizerEquivPSL (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    {z : V} (hz : z ≠ 0) : pointStabilizer ρ z ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
  (pointStabilizerEquivLinear ρ hf hd hz).trans
    BinaryLinear.SmallParabolicLevi.linearThreeEquivProjective

theorem pointStabilizer_perfect (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    {z : V} (hz : z ≠ 0) : Group.IsPerfect (pointStabilizer ρ z) := by
  let := BinaryLinear.linearGroup_isPerfect 3 (by decide)
  exact Group.IsPerfect.ofSurjective
    (f := (pointStabilizerEquivLinear ρ hf hd hz).symm.toMonoidHom)
    (pointStabilizerEquivLinear ρ hf hd hz).symm.surjective

/-- The stabilizer of z is transitive on the fourteen vectors outside its line. -/
theorem pointStabilizer_transitive (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    {z x y : V} (hz : z ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ g : pointStabilizer ρ z, ρ g x = y := by
  let : MulAction A7 V := MulAction.compHom V ρ
  have he : pointStabilizer ρ z = MulAction.stabilizer A7 z := by
    ext g
    exact mem_pointStabilizer ρ z g
  have hmodel : Nonempty (MulAction.stabilizer A7 z ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
    ⟨(MulEquiv.subgroupCongr he).symm.trans (pointStabilizerEquivPSL ρ hf hd hz)⟩
  have ht := FifteenPointSubgroups.alternating7_two_pretransitive _ hmodel
  obtain ⟨a,ha⟩ := transitive ρ hf hd hz hx
  obtain ⟨b,hb⟩ := transitive ρ hf hd hz hy
  let q : A7 → A7 ⧸ MulAction.stabilizer A7 z := QuotientGroup.mk
  let f := MulAction.ofQuotientStabilizer A7 z
  have hfa : f (q a) = x := ha
  have hfb : f (q b) = y := hb
  have hf1 : f (q 1) = z := by change ρ 1 z = z; simp
  have hfsmul (g : A7) (u) : f (g • u) = ρ g (f u) :=
    MulAction.ofQuotientStabilizer_smul A7 z g u
  have hqa : q 1 ≠ q a := fun h => hxz (hfa.symm.trans ((congrArg f h).symm.trans hf1))
  have hqb : q 1 ≠ q b := fun h => hyz (hfb.symm.trans ((congrArg f h).symm.trans hf1))
  obtain ⟨g,hg1,hgab⟩ := MulAction.is_two_pretransitive_iff.mp ht hqa hqb
  have hg : ρ g z = z := by
    have hh := congrArg f hg1
    rw [hfsmul, hf1] at hh
    exact hh
  refine ⟨⟨g,(mem_pointStabilizer ρ z g).mpr hg⟩, ?_⟩
  have hh := congrArg f hgab
  rw [hfsmul, hfa, hfb] at hh
  exact hh

/-- The entire four-space is moved by its point stabilizer. -/
theorem pointStabilizer_moved (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    {z : V} (hz : z ≠ 0) : subspaceCommutator ρ ⊤ (pointStabilizer ρ z) = ⊤ := by
  let W := subspaceCommutator ρ ⊤ (pointStabilizer ρ z)
  have hn : ¬ W ≤ BinaryFivePointStabilizer.line z := by
    intro h
    have hone (g : pointStabilizer ρ z) : g = 1 := by
      apply pointQuotientAction_injective ρ hf hd hz
      rw [map_one]
      apply (BinaryFivePointStabilizer.mem_kernel_iff z (pointAction ρ z g)).mpr
      intro v
      exact h (Submodule.subset_span ⟨g,g.property,v,Submodule.mem_top,rfl⟩)
    have hc : Nat.card (pointStabilizer ρ z) = 1 :=
      Nat.card_eq_one_iff_exists.mpr ⟨1,hone⟩
    rw [pointStabilizer_card ρ hf hd hz] at hc
    omega
  obtain ⟨x,hx,hxz⟩ := SetLike.not_le_iff_exists.mp hn
  have hx0 : x ≠ 0 := fun he => hxz (he.symm ▸ Submodule.zero_mem _)
  have hxz' : x ≠ z := fun he => hxz (he.symm ▸ Submodule.mem_span_singleton_self z)
  have hmem (y : V) (hy : y ≠ 0) (hyz : y ≠ z) : y ∈ W := by
    obtain ⟨g,hg⟩ := pointStabilizer_transitive ρ hf hd hz hx0 hy hxz' hyz
    rw [← hg]
    exact ((subspaceCommutator_invariant ρ ⊤ (pointStabilizer ρ z)) g.property x).mpr hx
  have hzW : z ∈ W := by
    have hxz0 : x + z ≠ 0 := by
      intro he
      apply hxz'
      have hh := congrArg (fun v => v + z) he
      simpa only [add_assoc, ZModModule.add_self, add_zero, zero_add] using hh
    have hxzz : x + z ≠ z := by simpa using hx0
    have hh := W.sub_mem (hmem (x+z) hxz0 hxzz) hx
    simpa only [add_sub_cancel_left] using hh
  apply top_unique
  intro y _
  by_cases hy0 : y = 0
  · exact hy0.symm ▸ W.zero_mem
  by_cases hyz : y = z
  · exact hyz.symm ▸ hzW
  exact hmem y hy0 hyz

end Representation.BinaryAlternatingSevenControl
