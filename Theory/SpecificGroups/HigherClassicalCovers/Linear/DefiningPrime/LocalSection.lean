module

public import Theory.SpecificGroups.HigherClassicalCovers.Linear.DefiningPrime.Positive
public import Theory.GroupTheory.PerfectCentralCoverPrimeReduction

/-!
# From lifted roots to a local section and a kernel exclusion

A root family satisfying the elementary relations defines a homomorphism
from the Steinberg presentation. Its restriction to the positive subgroup,
identified with its literal projective image by `Positive`, is a section.
That subgroup has index prime to the defining prime. Prime-kernel reduction
and transfer therefore exclude the defining prime from every finite perfect
central kernel as soon as these root lifts exist in prime-degree covers.

`PrimeKernelRootLifts` states that remaining mathematical obligation. It
requires actual elements and their relations, not an assumed section or
kernel bound. The source theorem is not complete until this input is proved,
in particular over the three-element field excluded by Steinberg Theorem 10.
Source: Steinberg §§6–7, and Aschbacher–Smith I.1.1, I.1.4(1),(3), printed
pp.407–408 of `refs/quasithin.pdf`, citing GLS3 §6.1.
-/

@[expose] public section

open Theory.SpecificGroups.LinearHigher
open scoped MatrixGroups
namespace Theory.SpecificGroups.HigherClassicalCovers.Linear.DefiningPrime

universe u v
variable {F : Type u} [Field F]

/-- Compatible elementary root lifts give a section on the literal projective
upper subgroup. Only positive-root faithfulness is used. -/
theorem exists_upper_section_of_root_lifts {E : Type v} [Group E]
    (f : E →* PSL(4, F)) (x : Root 4 → F → E) (hrel : Relations x)
    (hx : ∀ r a, f (x r a) = projectiveRoot r a) :
    ∃ s : projectiveUpper F →* E, f.comp s = (projectiveUpper F).subtype := by
  have hfac : f.comp (lift hrel) = projectiveMap := by
    apply PresentedGroup.ext
    rintro ⟨r,a⟩
    change f (lift hrel (generator r a)) = projectiveMap (generator r a)
    rw [lift_generator, projectiveMap_generator, hx]
  let e : upper F ≃* projectiveUpper F := upperEquivProjective
  let s : projectiveUpper F →* E :=
    (lift hrel).comp ((upper F).subtype.comp e.symm.toMonoidHom)
  refine ⟨s, ?_⟩
  ext g
  change f (lift hrel (e.symm g).val) = (g : PSL(4,F))
  calc
    _ = projectiveMap (e.symm g).val := DFunLike.congr_fun hfac _
    _ = (e (e.symm g) : PSL(4,F)) := rfl
    _ = g := congrArg Subtype.val (e.apply_symm_apply g)

/-- The only outstanding local input: lift the elementary Steinberg relations
in covers whose kernel has the defining prime order. This does not assume
faithfulness, a global section, or any bound for a covering kernel. -/
def PrimeKernelRootLifts (F : Type u) [Field F] (p : ℕ) : Prop :=
  ∀ (E : Type u) [Group E] [Finite E] (c : PerfectCentralCovering.Cover E PSL(4,F)),
    Nat.card c.toMonoidHom.ker = p →
      ∃ x : Root 4 → F → E, Relations x ∧
        ∀ r a, c.toMonoidHom (x r a) = projectiveRoot r a

/-- Local collection and transfer turn the root-lifting input into the
required defining-prime exclusion for every finite perfect central cover. -/
theorem not_dvd_kernel_of_primeKernelRootLifts [Finite F] {p : ℕ}
    (hp : p.Prime) (hF : Nat.card F = p) (hlifts : PrimeKernelRootLifts F p)
    {E : Type u} [Group E] [Finite E] (c : PerfectCentralCovering.Cover E PSL(4,F)) :
    ¬ p ∣ Nat.card c.toMonoidHom.ker := by
  let : Fact p.Prime := ⟨hp⟩
  apply c.not_dvd_card_kernel_of_prime_kernel_local_sections
  intro E _ _ d hd
  obtain ⟨x, hrel, hx⟩ := hlifts E d hd
  obtain ⟨s,hs⟩ := exists_upper_section_of_root_lifts d.toMonoidHom x hrel hx
  exact ⟨projectiveUpper F, s, prime_not_dvd_projectiveUpper_index hp hF, hs⟩


end Theory.SpecificGroups.HigherClassicalCovers.Linear.DefiningPrime
