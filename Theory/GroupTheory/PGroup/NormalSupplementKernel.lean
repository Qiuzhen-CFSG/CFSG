module
public import Theory.GroupTheory.PGroup.CharacteristicKernel

/-!
# Prime-group action kernels with a normal supplement

Suppose E = LP with L normal and P a p-group. If the restriction to L
of a homomorphism f has p-group kernel, the whole kernel is a p-group:
map it to E/L and identify the restricted kernel inside the given one.
This keeps the original maps and does not assume any faithful quotient.

Source application: the action of L₀T on its original tensor module,
Aschbacher–Smith 9.2.2, printed p.730.
-/

public section
open Subgroup
namespace MonoidHom
variable {E A : Type*} [Group E] [Group A]

theorem kernel_isPGroup_of_normal_supplement {p : ℕ}
    (f : E →* A) (L P : Subgroup E) [L.Normal]
    (hP : IsPGroup p P) (hgen : L ⊔ P = ⊤)
    (hk : IsPGroup p (f.comp L.subtype).ker) : IsPGroup p f.ker := by
  have hquot : IsPGroup p (E ⧸ L) := quotient_isPGroup_of_sup_eq_top P L hP ((sup_comm P L).trans hgen)
  let q := (QuotientGroup.mk' L).comp f.ker.subtype
  have hqker : IsPGroup p q.ker := by
    let r : q.ker →* L :=
      (f.ker.subtype.comp q.ker.subtype).codRestrict L (by
        intro x
        exact (QuotientGroup.eq_one_iff (N := L) x.val.val).mp x.property)
    let r' : q.ker →* (f.comp L.subtype).ker := r.codRestrict _ (by
      intro x
      exact x.val.property)
    apply hk.of_injective r'
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : (f.comp L.subtype).ker => (x.val : E)) hab
  have ht := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup q hqker
  rw [comap_top] at ht
  exact ht.of_equiv topEquiv
end MonoidHom
