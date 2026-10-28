module

public import Theory.SpecificGroups.AlternatingSix.TwoCoverInvolutions
public import Theory.Representation.BinaryPermutation.CoreFixedLine
public import Theory.Representation.FirstCohomologyAutomorphism.Cocycle
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# Central two-kernels and the six-letter augmentation core

A cocycle on a finite perfect central two-cover of A₆, valued in the
inflated five-dimensional augmentation core, vanishes on the central
kernel. The Schur multiplier bounds that kernel by two. In the double
cover, a double transposition lifts to an element with nontrivial square.
The cocycle on its square is constant, while a fixed coordinate makes
that constant zero. Thus the whole kernel is killed.

Consequently an automorphism whose displacements lie in this module and
which fixes it pointwise also fixes the larger action kernel, provided
the quotient by the module is a perfect central two-cover. This supplies
the five-dimensional case of Aschbacher–Smith C.1.13(d), printed p.125,
used in 13.4.8, p.904. The proof uses GLS3 5.2.3–4's actual cover theorem;
it does not identify the full two-core with the augmentation module.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.OneCohomology
open GLS3.Chapter5 GLS3.Chapter5.SchurPresentation
namespace BinaryPermutation.SixCoreCentralKernel
abbrev A := alternatingGroup (Fin 6)
abbrev V := core (Fin 6)

private def t : A := ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
  simp [Equiv.Perm.mem_alternatingGroup]⟩
private theorem t_sq : t ^ 2 = 1 := by decide
private theorem t_ne : t ≠ 1 := by decide
private theorem t_fixed : t.val.symm 4 = 4 := by decide

/-- The cocycle kills the literal central two-kernel of the perfect cover. -/
theorem cocycle_eq_zero_on_kernel
    {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E A)
    (hp : IsPGroup 2 f.toMonoidHom.ker)
    (c : cocycles ((alternatingCoreRepresentation (Fin 6)).comp f.toMonoidHom)) :
    ∀ x ∈ f.toMonoidHom.ker, c.val x = 0 := by
  let : IsQuasisimple A := alternatingGroup_isQuasisimple 1
  let : IsQuasisimple E := f.isQuasisimple
  have hk : f.toMonoidHom.ker = center E :=
    ker_eq_center_of_surjective_of_center_eq_bot f.toMonoidHom f.surjective
      f.ker_le_center (alternatingGroup.center_eq_bot (by simp))
  let e : (E ⧸ center E) ≃* A :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f.toMonoidHom f.surjective)
  have hdvd : Nat.card f.toMonoidHom.ker ∣ 6 := by
    rw [hk]
    exact exceptional_alternating_center_card_dvd_six 6 e (Or.inl rfl)
  obtain ⟨k,hkcard⟩ := IsPGroup.iff_card.mp hp
  have hcop : Nat.Coprime (Nat.card f.toMonoidHom.ker) 3 := by
    rw [hkcard]
    exact (by norm_num : Nat.Coprime 2 3).pow_left k
  have htwo : Nat.card f.toMonoidHom.ker ∣ 2 := hcop.dvd_mul_right.mp hdvd
  have c_one : c.val 1 = 0 := by
    have h := c.property 1 1
    simpa using h
  have hconstant (x : E) (hx : x ∈ f.toMonoidHom.ker) :
      (c.val x).val ∈ constants (Fin 6) := by
    apply (core_fixed_iff_constant (by simp) _).mp
    intro a
    obtain ⟨g,rfl⟩ := f.surjective a
    have h := (c.property g x).symm.trans
      ((congrArg c.val (mem_center_iff.mp (f.ker_le_center hx) g)).trans
        (c.property x g))
    have hx1 : f.toMonoidHom x = 1 := hx
    change alternatingCoreRepresentation (Fin 6) (f.toMonoidHom g) (c.val x) + c.val g =
      alternatingCoreRepresentation (Fin 6) (f.toMonoidHom x) (c.val g) + c.val x at h
    rw [hx1,map_one,Module.End.one_apply,add_comm (c.val g)] at h
    exact add_right_cancel h
  rcases (Nat.dvd_prime Nat.prime_two).mp htwo with hone | htwo
  · have hbot := Subgroup.card_eq_one.mp hone
    intro x hx
    rw [hbot,mem_bot] at hx
    simpa only [hx] using c_one
  · let cf : Covering E A := {toMonoidHom := f.toMonoidHom, surjective := f.surjective}
    obtain ⟨u,hu⟩ := f.surjective t
    have husq : u ^ 2 ∈ f.toMonoidHom.ker := by
      rw [MonoidHom.mem_ker,map_pow,hu,t_sq]
    have hune : u ^ 2 ≠ 1 := by
      intro he
      have hh := AlternatingSix.TwoCoverInvolutions.involution_mem_ker_of_double_cover
        cf htwo u he
      exact t_ne (hu.symm.trans hh)
    have hzero : c.val (u ^ 2) = 0 := by
      obtain ⟨b,hb⟩ := Submodule.mem_span_singleton.mp (hconstant (u ^ 2) husq)
      have hcu := congrArg (fun v : V => v.val 4) (c.property u u)
      have hval : (c.val (u ^ 2)).val 4 = 0 := by
        rw [pow_two]
        change (c.val (u * u)).val 4 =
          (c.val u).val ((f.toMonoidHom u).val.symm 4) + (c.val u).val 4 at hcu
        simpa only [hu,t_fixed,CharTwo.add_self_eq_zero] using hcu
      have hb0 : b = 0 := by
        have hh := congrFun hb 4
        simpa only [Pi.smul_apply,allOne,smul_eq_mul,mul_one,hval] using hh
      apply Subtype.ext
      simpa only [hb0,zero_smul,Submodule.coe_zero] using hb.symm
    intro x hx
    obtain ⟨y,hy,hyuniq⟩ := (Nat.card_eq_two_iff' (1 : f.toMonoidHom.ker)).mp htwo
    have husqne : (⟨u ^ 2,husq⟩ : f.toMonoidHom.ker) ≠ 1 :=
      fun hh => hune (congrArg Subtype.val hh)
    by_cases hx1 : x = 1
    · simpa only [hx1] using c_one
    · have hxy : (⟨x,hx⟩ : f.toMonoidHom.ker) = ⟨u ^ 2,husq⟩ :=
        (hyuniq _ (fun hh => hx1 (congrArg Subtype.val hh))).trans
          (hyuniq _ husqne).symm
      have hxx : x = u ^ 2 := congrArg Subtype.val hxy
      rw [hxx]
      exact hzero

/-- Fixing the augmentation module and its quotient forces fixation of the full action kernel. -/
theorem automorphism_fixes_kernel
    {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    (N : Subgroup X) [N.Normal]
    (f : X →* A) (hf : Function.Surjective f)
    (hp : IsPGroup 2 f.ker) (hN : N ≤ f.ker)
    (hc : ⁅f.ker, (⊤ : Subgroup X)⁆ ≤ N)
    (e : N ≃* Multiplicative V)
    (he : ∀ (g : X) (v : V),
      (e.symm (Multiplicative.ofAdd (alternatingCoreRepresentation (Fin 6) (f g) v)) : X) =
        g * (e.symm (Multiplicative.ofAdd v) : X) * g⁻¹)
    (α : MulAut X) (hd : ∀ g, α g * g⁻¹ ∈ N)
    (hfix : ∀ n ∈ N, α n = n) : ∀ x ∈ f.ker, α x = x := by
  let q := QuotientGroup.mk' N
  let fbar : (X ⧸ N) →* A := QuotientGroup.lift N f hN
  have hbar : Function.Surjective fbar :=
    QuotientGroup.lift_surjective_of_surjective N f hf hN
  have hker : fbar.ker = f.ker.map q := QuotientGroup.ker_lift N f hN
  have hcentral : fbar.ker ≤ center (X ⧸ N) := by
    rw [hker,← commutator_top_right_eq_bot_iff_le_center]
    have htop : (⊤ : Subgroup X).map q = ⊤ := by
      rw [← MonoidHom.range_eq_map,MonoidHom.range_eq_top]
      exact QuotientGroup.mk'_surjective N
    rw [← htop,← map_commutator]
    rw [Subgroup.map_eq_bot_iff]
    simpa only [q,QuotientGroup.ker_mk'] using hc
  let cbar : PerfectCentralCovering.Cover (X ⧸ N) A := {
    toMonoidHom := fbar
    surjective := hbar
    ker_le_center := hcentral
    isPerfect := inferInstance }
  let ρ := (alternatingCoreRepresentation (Fin 6)).comp fbar
  obtain ⟨c,hc⟩ := exists_automorphism_cocycle_of_subkernel N q
    (QuotientGroup.mk'_surjective N) e ρ he α hd
    (by simpa only [q,QuotientGroup.ker_mk'] using hfix)
  have hzero := cocycle_eq_zero_on_kernel cbar (by
    change IsPGroup 2 fbar.ker
    rw [hker]
    exact hp.map q) c
  intro x hx
  have hqx : q x ∈ fbar.ker := by
    change f x = 1
    exact hx
  have hz := (hc x).symm.trans (hzero (q x) hqx)
  have hz' : e ⟨α x * x⁻¹,hd x⟩ = 1 := Multiplicative.toAdd.injective hz
  have hd1 : α x * x⁻¹ = 1 := congrArg Subtype.val (e.injective (hz'.trans (map_one e).symm))
  exact mul_inv_eq_one.mp hd1
end BinaryPermutation.SixCoreCentralKernel
