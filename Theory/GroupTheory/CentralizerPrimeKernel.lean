module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# A prime-group centralizer kernel

If G/L and Z(L) are p-groups, then C_G(L) is a p-group. Restrict the
quotient map to the centralizer; its kernel embeds in Z(L), and its image
is a subgroup of G/L. The extension property of p-groups finishes.

Source application: the kernel of the component-action quotient in
Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.41, p.1138.
-/

public section

namespace Subgroup
variable {G : Type*} [Group G] {p : ℕ}

/-- The centralizer is an extension of subgroups of the center and G/L. -/
theorem isPGroup_centralizer_of_quotient (L : Subgroup G) [L.Normal]
    (hq : IsPGroup p (G ⧸ L)) (hZ : IsPGroup p (center L)) :
    IsPGroup p (centralizer (L : Set G)) := by
  let C := centralizer (L : Set G)
  let f := (QuotientGroup.mk' L).comp C.subtype
  let j : f.ker →* center L :=
    { toFun := fun x => ⟨⟨x.val.val, (QuotientGroup.eq_one_iff _).mp x.property⟩,
        mem_center_iff.mpr (fun l => Subtype.ext (x.val.property l l.property))⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun a : center L => a.val.val) h))
  have hk : IsPGroup p f.ker := hZ.of_injective j hj
  have hall := (hq.to_subgroup ⊤).comap_of_ker_isPGroup f hk
  rw [Subgroup.comap_top] at hall
  exact hall.of_surjective (Subgroup.topEquiv (G := C)).toMonoidHom
    (Subgroup.topEquiv (G := C)).surjective
end Subgroup

end
