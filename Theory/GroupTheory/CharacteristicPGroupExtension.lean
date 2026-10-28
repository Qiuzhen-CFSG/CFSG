module
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.SelfCentralizingCoreInheritance

/-!
# Characteristic-p normal extensions

If a normal subgroup has self-centralizing p-core and its quotient is a
p-group, the whole group has self-centralizing p-core. The centralizer of
the ambient core has p-group kernel and image in the quotient.

This supplies the normalized two-local join used in Aschbacher–Smith
2.4.25, printed p.543, with the actual half-Sylow actor retained.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

theorem centralizer_pCore_le_of_normal_pGroup_quotient
    (p : ℕ) [Fact p.Prime] (N : Subgroup G) [N.Normal]
    (hN : centralizer (pCore p N : Set N) ≤ pCore p N)
    (hQ : IsPGroup p (G ⧸ N)) :
    centralizer (pCore p G : Set G) ≤ pCore p G := by
  let C := centralizer (pCore p G : Set G)
  let f : C →* G ⧸ N := (QuotientGroup.mk' N).comp C.subtype
  have hcore : (pCore p N).map N.subtype ≤ pCore p G :=
    le_sSup ⟨inferInstance, pCore_isPGroup.map N.subtype⟩
  let k : f.ker →* pCore p N :=
    { toFun := fun x => ⟨⟨x.val.val, by
        have hx := x.property
        change QuotientGroup.mk' N x.val.val = 1 at hx
        exact (QuotientGroup.eq_one_iff _).mp hx⟩, by
          apply hN
          intro n hn
          apply Subtype.ext
          exact x.val.property n.val (hcore (mem_map_of_mem N.subtype hn))⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hk : Function.Injective k := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : pCore p N => z.val.val) he))
  have hpker : IsPGroup p f.ker := pCore_isPGroup.of_injective k hk
  have hC : IsPGroup p C := by
    have h := (hQ.to_subgroup (⊤ : Subgroup (G ⧸ N))).comap_of_ker_isPGroup f hpker
    rw [comap_top] at h
    exact h.of_surjective (topEquiv (G := C)).toMonoidHom (topEquiv (G := C)).surjective
  exact le_sSup ⟨inferInstance,hC⟩

end Subgroup
