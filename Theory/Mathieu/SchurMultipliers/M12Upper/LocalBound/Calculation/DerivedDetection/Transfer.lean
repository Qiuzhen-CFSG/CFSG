module

public import Theory.GroupTheory.Commutator.CentralSylowTransfer
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Perm.Fin
public import Theory.Mathieu.SchurMultipliers.M12Upper.LocalBound.Calculation.DerivedDetection.CubicNorm

/-!
# Transfer for an abelian two-kernel over S₃

A central two-extension of S₃ has abelian Sylow-two subgroups: their images
have order two and their kernels are central. Central Sylow transfer therefore
kills its derived kernel. Factoring by the cubic norm's normal complement
reduces an abelian two-kernel with central cubic fixed points to this case.

The final theorem retains the given epimorphism and cubic lift, with no
perfectness assumption. Its consumer is the literal quotient of the M₁₂
parabolic extension in `DerivedDetection`.
Source context: Aschbacher–Smith I.1.3(1), printed p.407.
-/

open Subgroup
open scoped IsMulCommutative
namespace Subgroup
noncomputable section
variable {E : Type*} [Group E] [Finite E]

/-- A central two-extension of the actual permutation group S₃ has trivial
derived kernel. -/
public theorem central_two_kernel_perm_three_derived
    (f : E →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) (hp : IsPGroup 2 f.ker) :
    f.ker ⊓ _root_.commutator E ≤ ⊥ := by
  let P : Sylow 2 E := Classical.choice inferInstance
  let Q := P.mapSurjective hf
  have hQ : Nat.card Q = 2 := by
    rw [Q.card_eq_multiplicity, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    norm_num [Nat.factorial]
    decide +kernel
  let : IsCyclic Q := isCyclic_of_prime_card hQ
  let g : P →* Q := (f.comp (P : Subgroup E).subtype).codRestrict _
    (fun x => (show f x ∈ (P : Subgroup E).map f from ⟨x,x.property,rfl⟩))
  have hgk : g.ker ≤ center P := by
    intro x hx
    have hxk : (x : E) ∈ f.ker := congrArg Subtype.val hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp (hk hxk) y)
  have hP := g.isMulCommutative_of_isCyclic_of_ker_le_center hgk
  intro x hx
  have hmem := center_inf_commutator_inf_sylow_le_commutator P
    ⟨⟨hk hx.1,hx.2⟩,hp.le_sylow_of_normal P hx.1⟩
  rwa [commutator_self_eq_bot_iff.mpr hP] at hmem

/-- An ambient normal complement to the central part of an abelian two-kernel
reduces the central derived intersection to the cyclic Sylow calculation. -/
public theorem central_derived_two_kernel_eq_bot_of_normal_complement
    (f : E →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (hp : IsPGroup 2 f.ker)
    (U : Subgroup E) [U.Normal] (hU : U ≤ f.ker)
    (hdis : Disjoint U (center E)) (hsup : f.ker ≤ U ⊔ center E) :
    (center E ⊓ _root_.commutator E) ⊓ f.ker ≤ ⊥ := by
  let π := QuotientGroup.mk' U
  let fbar := QuotientGroup.lift U f hU
  have hfbar : Function.Surjective fbar :=
    QuotientGroup.lift_surjective_of_surjective U f hf hU
  have hker : fbar.ker = f.ker.map π := QuotientGroup.ker_lift U f hU
  have hcentral : fbar.ker ≤ center (E ⧸ U) := by
    rw [hker]
    apply (map_mono (f := π) hsup).trans
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    rintro _ ⟨z,hz,rfl⟩
    apply mem_center_iff.mpr
    intro y
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective U y
    exact congrArg π (mem_center_iff.mp hz a)
  have hpbar : IsPGroup 2 fbar.ker := by rw [hker]; exact hp.map π
  have hvanish := central_two_kernel_perm_three_derived fbar hfbar hcentral hpbar
  intro x hx
  have hxker : π x ∈ fbar.ker := by
    change f x = 1
    exact hx.2
  have hxder : π x ∈ _root_.commutator (E ⧸ U) := by
    have hm : (_root_.commutator E).map π ≤ _root_.commutator (E ⧸ U) := by
      rw [map_commutator_eq]
      exact commutator_mono le_top le_top
    exact hm ⟨x,hx.1.2,rfl⟩
  have hxU : x ∈ U := (QuotientGroup.eq_one_iff _).mp (hvanish ⟨hxker,hxder⟩)
  exact hdis.le_bot ⟨hxU,hx.1.1⟩

/-- Central elements of the derived subgroup cannot lie in an abelian two-kernel
whose cubic fixed points are all central. -/
public theorem center_inf_derived_inf_two_kernel_of_cubic_fixed_central
    (f : E →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (hab : IsMulCommutative f.ker) (hp : IsPGroup 2 f.ker)
    (t : E) (ht : f t = List.formPerm [0,2,1])
    (hfixed : ∀ x ∈ f.ker, Commute t x → x ∈ center E) :
    (center E ⊓ _root_.commutator E) ⊓ f.ker ≤ ⊥ := by
  obtain ⟨U,hUnormal,hU,hdis,hsup⟩ :=
    exists_normal_complement_of_cubic_fixed_central f hf hab hp t ht hfixed
  let : U.Normal := hUnormal
  exact central_derived_two_kernel_eq_bot_of_normal_complement f hf hp U hU hdis hsup

end
end Subgroup
