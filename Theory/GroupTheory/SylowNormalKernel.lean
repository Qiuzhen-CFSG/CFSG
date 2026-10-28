module
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Sylow

/-!
# Normal Sylows through a homomorphism with prime-group kernel

If the target p-core has prime-to-p index, its unique Sylow contains every
p-subgroup image. Its inverse image has p-group kernel and is normal.
Maximality identifies each source Sylow with that inverse image. The map
need not be onto. This applies to fixed subgroups of central covers.
-/

public section
open Subgroup
namespace Sylow
variable {A B : Type*} [Group A] [Group B] [Finite B]

/-- A normal Sylow in the target lifts across a p-group kernel, even without surjectivity. -/
theorem normal_of_pGroup_kernel_of_core_index {p : ℕ} [Fact p.Prime]
    (f : A →* B) (hk : IsPGroup p f.ker) (hind : ¬ p ∣ (pCore p B).index)
    (Q : Sylow p A) : (Q : Subgroup A).Normal := by
  let R : Sylow p B := (pCore_isPGroup (p := p) (G := B)).toSylow hind
  let : (R : Subgroup B).Normal := inferInstanceAs (pCore p B).Normal
  let : Unique (Sylow p B) := Sylow.unique_of_normal R inferInstance
  obtain ⟨S,hS⟩ := (Q.isPGroup'.map f).exists_le_sylow
  have hSR : S=R := Subsingleton.elim _ _
  have hQN : (Q : Subgroup A) ≤ (R : Subgroup B).comap f :=
    map_le_iff_le_comap.mp (hSR ▸ hS)
  have he := Q.is_maximal' (R.isPGroup'.comap_of_ker_isPGroup f hk) hQN
  rw [← he]
  infer_instance
end Sylow
