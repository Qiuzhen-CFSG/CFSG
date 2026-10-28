module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ModuleDecomposition
/-!
# Faithfulness on the exceptional hyperplane

A group acts trivially on a one-dimensional binary quotient. The kernel on
an invariant hyperplane therefore has square-zero displacement, so every
kernel element squares to one. In a faithful action that normal kernel lies
in O₂(D). When O₂(D)=1 the hyperplane action is faithful.

Applying this to the sum of two invariant subspaces proves the faithful
second-factor action in the exceptional branch of B.5.11: the second factor
already fixes the first moved space. No splitting of the ambient module is
assumed.
Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.5.10(3) and
B.5.11(1), printed p.109.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]

private theorem binary_line_fixed (ρ : Representation (ZMod 2) D V)
    (hd : Module.finrank (ZMod 2) V = 1) (g : D) (v : V) : ρ g v = v := by
  by_cases hv : v = 0
  · simp [hv]
  obtain ⟨c,hc⟩ := exists_smul_eq_of_finrank_eq_one hd hv (ρ g v)
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · have hz : ρ g v = 0 := by simpa only [zero_smul] using hc.symm
    have he := congrArg (ρ g⁻¹) hz
    have : v = 0 := by
      simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
        map_one, Module.End.one_apply, map_zero] using he
    exact (hv this).elim
  · simpa only [one_smul] using hc.symm

private theorem binary_add_self (v : V) : v + v = 0 := by
  calc
    v + v = ((1 : ZMod 2) + 1) • v := by rw [add_smul, one_smul]
    _ = 0 := by rw [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul]

/-- A faithful binary action with trivial two-core is faithful on each
invariant hyperplane. -/
theorem faithful_on_hyperplane (ρ : Representation (ZMod 2) D V)
    (hρ : Function.Injective ρ) (hcore : pCore 2 D = ⊥)
    (S : Subrepresentation ρ) (hd : Module.finrank (ZMod 2) (V ⧸ S.toSubmodule) = 1) :
    Function.Injective S.toRepresentation := by
  have hdis (g : D) (v : V) : ρ g v - v ∈ S.toSubmodule := by
    apply (Submodule.Quotient.eq S.toSubmodule).mp
    exact binary_line_fixed S.quotientRepresentation hd g (S.toSubmodule.mkQ v)
  have hp : IsPGroup 2 S.toRepresentation.ker := by
    intro k
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply hρ
    change ρ ((k : D) ^ (2 ^ 1)) = ρ (1 : D)
    ext v
    have hd' : ρ (k : D) (ρ (k : D) v - v) = ρ (k : D) v - v :=
      congrArg Subtype.val (LinearMap.congr_fun k.property ⟨_, hdis k v⟩)
    rw [map_sub] at hd'
    have hv : ρ (k : D) (ρ (k : D) v) = v := by
      apply add_right_cancel (b := v)
      exact (sub_eq_sub_iff_add_eq_add.mp hd').trans
        ((binary_add_self _).trans (binary_add_self v).symm)
    simpa only [pow_one, pow_two, map_mul, Module.End.mul_apply,
      map_one, Module.End.one_apply] using hv
  have hle : S.toRepresentation.ker ≤ pCore 2 D := le_sSup ⟨inferInstance, hp⟩
  rw [hcore] at hle
  exact S.toRepresentation.ker_eq_bot_iff.mp (le_antisymm hle bot_le)

/-- B.5.11's exceptional faithfulness step on the literal second subspace. -/
theorem faithful_on_hyperplane_supplement (ρ : Representation (ZMod 2) D V)
    (hρ : Function.Injective ρ) (hcore : pCore 2 D = ⊥) (B : Subgroup D)
    (U W : Subrepresentation ρ)
    (hd : Module.finrank (ZMod 2) (V ⧸ (U.toSubmodule ⊔ W.toSubmodule)) = 1)
    (hc : U.toSubmodule ≤ fixedSpace ρ B) :
    Function.Injective (W.toRepresentation.comp B.subtype) := by
  have hf := faithful_on_hyperplane ρ hρ hcore (U ⊔ W) hd
  intro b c he
  apply Subtype.ext
  apply hf
  ext v
  obtain ⟨u,hu,w,hw,heq⟩ := Submodule.mem_sup.mp v.property
  change ρ (b : D) (v : V) = ρ (c : D) (v : V)
  rw [← heq, map_add, map_add, (show ρ (b : D) u = u from hc hu b),
    (show ρ (c : D) u = u from hc hu c)]
  exact congrArg (u + ·) (congrArg Subtype.val (LinearMap.congr_fun he (⟨w,hw⟩ : W)))
end CFSG.Quasithin.ChapterB.SourceInduction
