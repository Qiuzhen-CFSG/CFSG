module
public import Theory.Representation.BinaryCoprimeDegree
public import Theory.Representation.BinaryOffender.NormalOddSeed
public import Theory.Representation.NormalInvariants
public import Theory.Representation.TwoDimensionalOddOrder
public import Mathlib.LinearAlgebra.Projection

/-!
# Extraspecial binary actions with a small common fixed space

A modular p-group module embeds by matrix coefficients in copies of its
regular module, one for each fixed dimension. Thus its dimension is at
most the group order times its fixed dimension.

For a faithful binary action of an extraspecial group of order 27 with
normal center, the central moving summand has positive dimension divisible
by six. A four-group fixing at most a plane bounds that dimension by eight.
Its fixed plane exhausts the whole fixed space, so the complementary
central fixed summand vanishes. The whole module has dimension six.

The actual Heisenberg extension application is in
`Theory.GroupAction.MarkedCubicRecognition.BinaryDegree`.
Source: Aschbacher--Smith 13.4.7(1iii), printed p.902, and the coprime
extraspecial degree calculation in G.7.1.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.ExtraspecialSmallFixedSpace

/-- The dimension of a modular p-group module is bounded by its order times
its fixed dimension. -/
theorem finrank_le_card_mul_invariants
    {k P V : Type*} [Field k] [Group P] [Finite P]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k P V) (hc : ringChar k ≠ 0)
    (hp : IsPGroup (ringChar k) P) :
    Module.finrank k V ≤ Nat.card P * Module.finrank k ρ.invariants := by
  classical
  let : Fintype P := Fintype.ofFinite P
  obtain ⟨C,hC⟩ := Submodule.exists_isCompl ρ.invariants
  let p := ρ.invariants.projectionOnto C hC
  let f : V →ₗ[k] (P → ρ.invariants) :=
    { toFun := fun v x => p (ρ x⁻¹ v)
      map_add' := by intro v w; ext x; simp
      map_smul' := by intro c v; ext x; simp }
  have heq (g : P) (v : V) (x : P) : f (ρ g v) x = f v (g⁻¹*x) := by
    change p (ρ x⁻¹ (ρ g v)) = p (ρ (g⁻¹*x)⁻¹ v)
    rw [←Module.End.mul_apply,←map_mul]
    simp
  let U : Subrepresentation ρ :=
    { toSubmodule := f.ker
      apply_mem_toSubmodule := by
        intro g v hv
        apply funext
        intro x
        change f (ρ g v) x = 0
        rw [heq]
        exact congrFun hv _ }
  have hi : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    by_contra hn
    let : Nontrivial U.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hn
    obtain ⟨v,hv,hfix⟩ := pGroup_fix_nonzero_vector hc hp U.toRepresentation
    have hfv : (v : V) ∈ ρ.invariants := fun g => congrArg Subtype.val (hfix g)
    have hz := congrFun (show f (v : V) = 0 from v.property) 1
    change p (ρ (1 : P)⁻¹ (v : V)) = 0 at hz
    simp only [inv_one,map_one,Module.End.one_apply] at hz
    have hv0 : (v : V) = 0 := by
      have hh := congrArg Subtype.val hz
      change (p (v : V) : V) = 0 at hh
      rw [show p (v : V) = ⟨v,hfv⟩ from Submodule.projectionOnto_apply_of_mem_left hC hfv] at hh
      exact hh
    exact hv (Subtype.ext hv0)
  have hb := LinearMap.finrank_le_finrank_of_injective hi
  simpa only [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,
    smul_eq_mul,←Nat.card_eq_fintype_card] using hb

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- An extraspecial subgroup of order 27 with normal center and a four-group
of actors fixing at most a plane forces the whole module to have dimension six. -/
theorem finrank_six
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (P S : Subgroup G) [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (hn : ((center P).map P.subtype).Normal)
    (hS : IsPGroup 2 S) (hcS : Nat.card S = 4)
    (hfix : Module.finrank (ZMod 2) (fixedSpace ρ S) ≤ 2) :
    Module.finrank (ZMod 2) V = 6 ∧
      fixedSpace ρ ((center P).map P.subtype) = ⊥ := by
  let Z := (center P).map P.subtype
  let : Z.Normal := hn
  have hZ : Nat.card Z = 3 := by
    rw [card_map_of_injective P.subtype_injective]
    exact IsExtraspecial.center_order_p 3 P
  let C := fixedSubrepresentationOfNormal ρ Z
  let W : Subrepresentation ρ :=
    { toSubmodule := subspaceCommutator ρ ⊤ Z
      apply_mem_toSubmodule := by
        intro g v hv
        exact (subspaceCommutator_invariant_normalizer ρ
          (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
          (show (⊤ : Subgroup G) ≤ normalizer (Z : Set G) from le_normalizer_of_normal)
          (mem_top g) v).mpr hv }
  have hcompl : IsCompl C.toSubmodule W.toSubmodule := by
    change IsCompl (fixedSpace ρ Z) (subspaceCommutator ρ ⊤ Z)
    simpa only [RegularCyclicNormalClosure.displacementSpan,subspaceCommutator,eq_comm] using
      (GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := ρ) (Y := Z) (by rw [hZ]; decide))
  have hWfix : invariants ((W.toRepresentation.comp P.subtype).comp (center P).subtype) = ⊥ := by
    apply bot_unique
    intro w hw
    apply Subtype.ext
    apply Submodule.disjoint_def.mp hcompl.disjoint
    · rintro ⟨z,hz⟩
      obtain ⟨z,hz,rfl⟩ := hz
      exact congrArg Subtype.val (hw ⟨z,hz⟩)
    · exact w.property
  have hd : 6 ∣ Module.finrank (ZMod 2) W.toSubmodule :=
    BinaryCoprimeDegree.six_dvd_finrank_of_extraspecial_twentySeven
      (W.toRepresentation.comp P.subtype) hP hWfix
  have hWne : W.toSubmodule ≠ ⊥ := by
    intro hw
    have hC : C.toSubmodule = ⊤ := by simpa only [hw,sup_bot_eq] using hcompl.sup_eq_top
    have hzbot : Z = ⊥ := by
      apply bot_unique
      intro z hz
      apply hf
      ext v
      have hv : v ∈ C.toSubmodule := hC ▸ Submodule.mem_top
      rw [map_one]
      exact hv ⟨z,hz⟩
    rw [hzbot,card_bot] at hZ
    omega
  have hpos : 0 < Module.finrank (ZMod 2) W.toSubmodule :=
    Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hWne)
  let F := invariants (W.toRepresentation.comp S.subtype)
  let j : F →ₗ[ZMod 2] fixedSpace ρ S :=
    { toFun := fun w => ⟨w.val.val,fun s => congrArg Subtype.val (w.property s)⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro v w he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : fixedSpace ρ S => x.val) he
  have hjdim := LinearMap.finrank_le_finrank_of_injective hj
  have hb := finrank_le_card_mul_invariants (W.toRepresentation.comp S.subtype)
    (by simp [ZMod.ringChar_zmod_n]) (by simpa only [ZMod.ringChar_zmod_n] using hS)
  change Module.finrank (ZMod 2) W.toSubmodule ≤ Nat.card S * Module.finrank (ZMod 2) F at hb
  rw [hcS] at hb
  have hdim : Module.finrank (ZMod 2) W.toSubmodule = 6 := by omega
  have hfdim : Module.finrank (ZMod 2) F = Module.finrank (ZMod 2) (fixedSpace ρ S) := by omega
  have hjs : Function.Surjective j :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfdim).mp hj
  have hCF : C.toSubmodule = ⊥ := by
    by_contra hnC
    let : Nontrivial C.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hnC
    obtain ⟨v,hv,hfv⟩ := pGroup_fix_nonzero_vector (by simp [ZMod.ringChar_zmod_n] : ringChar (ZMod 2) ≠ 0)
      (by simpa only [ZMod.ringChar_zmod_n] using hS) (C.toRepresentation.comp S.subtype)
    obtain ⟨w,hw⟩ := hjs ⟨v.val,fun s => congrArg Subtype.val (hfv s)⟩
    have hwv : w.val.val = v.val := congrArg Subtype.val hw
    exact hv (Subtype.ext (Submodule.disjoint_def.mp hcompl.disjoint v.val
      v.property (hwv ▸ w.val.property)))
  have htop : W.toSubmodule = ⊤ := by simpa only [hCF,bot_sup_eq] using hcompl.sup_eq_top
  refine ⟨?_,hCF⟩
  rw [htop,finrank_top] at hdim
  exact hdim
end Representation.ExtraspecialSmallFixedSpace
