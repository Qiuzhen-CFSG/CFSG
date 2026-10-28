module

public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.PGroupCore

/-!
# Action kernels over a normal subgroup with a prime-group supplement

If an action has prime-group kernel on a normal subgroup and the quotient by
that subgroup is a prime group, its whole kernel is a prime group. Restrict
the quotient map to the whole kernel and use closure under extensions. In
particular, a prime-group supplement gives the required quotient hypothesis.
-/

public section
open Subgroup
namespace MonoidHom
variable {G H : Type*} [Group G] [Group H] {p : ℕ}

/-- A prime-group restricted kernel and prime-group quotient force the whole
kernel to be a prime group. -/
theorem isPGroup_ker_of_normal_restriction
    (f : G →* H) (B : Subgroup G) [B.Normal]
    (hquot : IsPGroup p (G ⧸ B))
    (hker : IsPGroup p (f.comp B.subtype).ker) : IsPGroup p f.ker := by
  let r : f.ker →* G ⧸ B := (QuotientGroup.mk' B).comp f.ker.subtype
  have hr : IsPGroup p r.ker := by
    let i : r.ker →* (f.comp B.subtype).ker :=
      { toFun := fun x => ⟨⟨x.val.val,
          (QuotientGroup.eq_one_iff _).mp x.property⟩, x.val.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    apply hker.of_injective i
    intro x y he
    exact Subtype.ext (Subtype.ext
      (congrArg (fun z : (f.comp B.subtype).ker => ((z : B) : G)) he))
  have hh := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup r hr
  rw [comap_top] at hh
  exact hh.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup f.ker) ≃* f.ker)

/-- It suffices that a prime subgroup supplements the normal subgroup. -/
theorem isPGroup_ker_of_normal_join
    (f : G →* H) (B S : Subgroup G) [B.Normal]
    (hS : IsPGroup p S) (hjoin : B ⊔ S = ⊤)
    (hker : IsPGroup p (f.comp B.subtype).ker) : IsPGroup p f.ker :=
  f.isPGroup_ker_of_normal_restriction B
    (isPGroup_quotient_of_sup_eq_top B S hS hjoin) hker

/-- The whole action kernel lies in the ambient prime core. -/
theorem ker_le_pCore_of_normal_join
    (f : G →* H) (B S : Subgroup G) [B.Normal]
    (hS : IsPGroup p S) (hjoin : B ⊔ S = ⊤)
    (hker : IsPGroup p (f.comp B.subtype).ker) : f.ker ≤ pCore p G :=
  le_sSup ⟨inferInstance, f.isPGroup_ker_of_normal_join B S hS hjoin hker⟩

end MonoidHom
