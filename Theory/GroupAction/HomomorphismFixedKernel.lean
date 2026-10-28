module
public import Theory.GroupAction.HomomorphismFixingAutomorphisms
import all Theory.GroupAction.HomomorphismFixingAutomorphisms

/-!
# Actions fixing a kernel and its quotient

An automorphism acting trivially on both the kernel and the values of a
homomorphism with p-group kernel lies in a p-group. An action with p-group
kernel therefore has a p-group actor. This is the subgroup-and-quotient
automorphism argument, applied to the literal tilded-to-hatted map in
Aschbacher--Smith 12.8 and 14.3.15, printed pp.853--855 and994.

This internal extension imports the implementation of
`HomomorphismFixingAutomorphisms` to identify its restriction kernel. The
public theorem uses only pointwise action equations and leaves that
implementation boundary unchanged.
-/

public section
namespace MonoidHom
variable {P D A : Type*} [Group P] [Finite P] [Group D] [Group A]

/-- Fixing both the kernel and the values of a homomorphism with a p-group
kernel gives a p-group actor, provided its action kernel is a p-group. -/
theorem isPGroup_of_fixes_kernel_and_quotient {p : ℕ}
    (d : P →* D) (hP : IsPGroup p d.ker) (f : A →* MulAut P)
    (hf : IsPGroup p f.ker)
    (hq : ∀ a x, d (f a x) = d x)
    (hk : ∀ (a : A) (x : d.ker), f a x = x) : IsPGroup p A := by
  let g : A →* d.fixingAut := f.codRestrict _ hq
  have hg : ∀ a, g a ∈ d.fixingAutRestriction.ker := by
    intro a
    apply MulEquiv.ext
    intro x
    exact Subtype.ext (hk a x)
  let k : A →* d.fixingAutRestriction.ker := g.codRestrict _ hg
  have he : k.ker = f.ker := by
    ext a
    constructor
    · intro ha
      exact congrArg (fun b : d.fixingAutRestriction.ker => (b : MulAut P)) ha
    · intro ha
      apply Subtype.ext
      exact Subtype.ext ha
  have ht := ((d.isPGroup_fixingAutRestriction_ker hP).to_subgroup ⊤).comap_of_ker_isPGroup
    k (he.symm ▸ hf)
  rw [Subgroup.comap_top] at ht
  exact ht.of_surjective (⊤ : Subgroup A).subtype (fun a => ⟨⟨a,Subgroup.mem_top a⟩,rfl⟩)
end MonoidHom
