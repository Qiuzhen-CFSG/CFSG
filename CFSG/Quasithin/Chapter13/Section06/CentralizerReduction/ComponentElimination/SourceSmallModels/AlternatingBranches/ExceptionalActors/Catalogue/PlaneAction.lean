module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Intrinsic
public import Theory.Representation.BinaryPlaneNormalizer
public import Theory.Representation.NormalPSubgroupKernel

/-!
# The plane action of a permitted exceptional A₇ actor

A two-perfect group fixing a nonzero vector of a binary plane acts trivially
on that plane. The full-commutator hypothesis excludes this, so the plane
has zero common fixed space and is irreducible. Its normal two-core therefore
acts trivially. When the two-core is nontrivial, Cauchy's theorem produces the
involution needed by the full-space fixed-vector argument in `Intrinsic`.

All actions here are restrictions of the original representation. In particular,
no statement that a diagonal actor's cubic elements are fixed-point-free is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.6.22, printed p.932.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) A7 W} {P : Submodule (ZMod 2) W}
  {S : Sylow 2 A7} {D : Subgroup A7}

def PermittedActor.planeRepresentation (h : PermittedActor ρ P S D) :
    Representation (ZMod 2) D P :=
  (stabilizerRepresentation ρ P).comp (inclusion h.stabilizes)

theorem PermittedActor.plane_fixed_eq_zero (h : PermittedActor ρ P S D)
    (hP : Module.finrank (ZMod 2) P = 2) :
    ∀ w ∈ P, (∀ d : D, ρ d w = w) → w = 0 := by
  intro w hw hfixed
  by_contra hn
  have htriv := BinaryPlaneNormalizer.twoPerfect_plane_fixed h.planeRepresentation
    h.twoPerfect hP (⟨w, hw⟩ : P)
    (fun he => hn (congrArg Subtype.val he)) (fun d => Subtype.ext (hfixed d))
  have hbot : subspaceCommutator ρ P D = ⊥ :=
    (subspaceCommutator_eq_bot_iff ρ P D).mpr (by
      intro x hx d
      exact congrArg Subtype.val (LinearMap.congr_fun (htriv d) ⟨x, hx⟩))
  rw [h.commutator_eq] at hbot
  apply hn
  change w ∈ (⊥ : Submodule (ZMod 2) W)
  rw [← hbot]
  exact hw

theorem PermittedActor.plane_irreducible (h : PermittedActor ρ P S D)
    (hP : Module.finrank (ZMod 2) P = 2) : IsIrreducible h.planeRepresentation := by
  let := Module.finite_of_finrank_pos (R := ZMod 2) (M := P) (by omega)
  have : Nontrivial P := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank (ZMod 2) P)
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun Q => ?_⟩
  by_cases hb : Q = ⊥
  · exact Or.inl hb
  right
  by_contra ht
  have hb' : Q.toSubmodule ≠ ⊥ := fun he => hb (Subrepresentation.toSubmodule_injective he)
  have ht' : Q.toSubmodule ≠ ⊤ := fun he => ht (Subrepresentation.toSubmodule_injective he)
  have : Nontrivial Q.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hb'
  have hp : 0 < Module.finrank (ZMod 2) Q.toSubmodule := Module.finrank_pos
  have hlt := Submodule.finrank_lt ht'
  have hdim : Module.finrank (ZMod 2) Q.toSubmodule = 1 := by
    rw [hP] at hlt
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb'
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hdim hw hw0
  have hfixed (d : D) : h.planeRepresentation d w = w := by
    have hm := Q.apply_mem_toSubmodule d hw
    rw [hspan] at hm
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
    have hn : h.planeRepresentation d w ≠ 0 := by
      intro he
      have hh := congrArg (h.planeRepresentation d⁻¹) he
      simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
        map_one, Module.End.one_apply, map_zero] at hh
      exact hw0 hh
    have hc0 : c ≠ 0 := fun he => hn (by simpa [he] using hc.symm)
    have hc1 : c = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc0
    simpa [hc1] using hc.symm
  exact hw0 (Subtype.ext (h.plane_fixed_eq_zero hP w w.property
    (fun d => congrArg Subtype.val (hfixed d))))

theorem PermittedActor.twoCore_fixes_plane (h : PermittedActor ρ P S D)
    (hP : Module.finrank (ZMod 2) P = 2) :
    ∀ d : D, d ∈ pCore 2 D → ∀ w ∈ P, ρ d w = w := by
  let := Module.finite_of_finrank_pos (R := ZMod 2) (M := P) (by omega)
  let := h.plane_irreducible hP
  have hk := normal_p_subgroup_le_ker h.planeRepresentation (pCore 2 D) pCore_isPGroup
  intro d hd w hw
  exact congrArg Subtype.val (LinearMap.congr_fun (MonoidHom.mem_ker.mp (hk hd)) ⟨w, hw⟩)

/-- The plane kernel is exactly the actor's two-core, as a subgroup of `D`. -/
theorem PermittedActor.twoCore_eq_planeKernel (h : PermittedActor ρ P S D)
    (hP : Module.finrank (ZMod 2) P = 2) :
    pCore 2 D = (subspaceKernel ρ P D).subgroupOf D := by
  let K := (subspaceKernel ρ P D).subgroupOf D
  have hle : pCore 2 D ≤ K := fun d hd =>
    ⟨d.property, h.twoCore_fixes_plane hP d hd⟩
  have hproper : K ≠ ⊤ := by
    intro he
    have : Nontrivial P := Module.nontrivial_of_finrank_pos
      (by omega : 0 < Module.finrank (ZMod 2) P)
    obtain ⟨w, hw⟩ := exists_ne (0 : P)
    apply hw
    apply Subtype.ext
    apply h.plane_fixed_eq_zero hP w w.property
    intro d
    have hd : d ∈ K := by rw [he]; trivial
    exact hd.2 w w.property
  have hc : (pCore 2 D).index = 3 := h.quotient_card
  have hm := relIndex_mul_index hle
  rw [hc] at hm
  have hp : Nat.Prime ((pCore 2 D).relIndex K * K.index) := by rw [hm]; decide
  rcases Nat.prime_mul_iff.mp hp with ⟨_, hi⟩ | ⟨_, hr⟩
  · exact False.elim (hproper (index_eq_one.mp hi))
  · exact le_antisymm hle (relIndex_eq_one.mp hr)

/-- The cubic two-core quotient is identified with the literal action image
on the marked plane, through the original action map. -/
noncomputable def PermittedActor.quotientEquivPlaneImage (h : PermittedActor ρ P S D)
    (hP : Module.finrank (ZMod 2) P = 2) :
    (D ⧸ pCore 2 D) ≃* restrictedSubgroup ρ P D := by
  let := subspaceKernel_normal ρ P D h.stabilizes
  exact (QuotientGroup.quotientMulEquivOfEq (h.twoCore_eq_planeKernel hP)).trans
    (subspaceQuotientEquiv ρ P D h.stabilizes)

theorem PermittedActor.planeImage_card (h : PermittedActor ρ P S D)
    (hP : Module.finrank (ZMod 2) P = 2) :
    Nat.card (restrictedSubgroup ρ P D) = 3 :=
  (Nat.card_congr (h.quotientEquivPlaneImage hP).toEquiv).symm.trans h.quotient_card

theorem PermittedActor.actorWitness_of_twoCore_ne_bot (h : PermittedActor ρ P S D)
    (hP : Module.finrank (ZMod 2) P = 2) (hcore : pCore 2 D ≠ ⊥) :
    ActorWitness ρ P D := by
  have hc : 2 ∣ Nat.card (pCore 2 D) := by
    rcases (pCore_isPGroup (p := 2) (G := D)).card_eq_or_dvd with he | he
    · exact False.elim (hcore (Subgroup.card_eq_one.mp he))
    · exact he
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 hc
  exact Or.inr ⟨t.val.val, t.val.property,
    (Subgroup.orderOf_coe t.val).trans ((Subgroup.orderOf_coe t).trans ht),
    h.twoCore_fixes_plane hP t.val t.property⟩
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors
