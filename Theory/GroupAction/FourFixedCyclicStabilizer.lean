module

public import Theory.GroupTheory.PermutationFourCyclicKernel
public import Mathlib.GroupTheory.GroupAction.SubMulAction

/-!
# Four fixed points and cyclic two-point stabilizers

An element with exactly four fixed points gives a permutation representation
of its centralizer in `S₄`. If the stabilizer of two of those points is cyclic,
the representation has cyclic kernel. The element itself lies in that kernel.
This is the fixed-point action needed for the order-eight obstruction in
Suzuki (1965), Section II, Lemma 6 at q = 3.
-/

namespace MulAction

/-- Restricting a centralizer to four fixed points gives a homomorphism to
`S₄` with cyclic kernel whenever a two-point stabilizer is cyclic. -/
public theorem exists_perm_four_cyclic_kernel_of_fixed_card_four
    {G Ω : Type*} [Group G] [MulAction G Ω]
    (a b : Ω) [IsCyclic (stabilizer (stabilizer G a) b)]
    (j : G) (hja : j • a = a) (hjb : j • b = b)
    (hfixed : Nat.card {x : Ω // j • x = x} = 4) :
    ∃ f : Subgroup.centralizer ({j} : Set G) →* Equiv.Perm (Fin 4),
      IsCyclic f.ker ∧
      (⟨j, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
        Subgroup.centralizer ({j} : Set G)) ∈ f.ker := by
  classical
  let C := Subgroup.centralizer ({j} : Set G)
  let F : SubMulAction C Ω := {
    carrier := {x | j • x = x}
    smul_mem' := by
      intro c x hx
      change j • ((c : G) • x) = (c : G) • x
      rw [← mul_smul,
        (Subgroup.mem_centralizer_singleton_iff.mp c.property).symm,
        mul_smul, hx] }
  have hF : Nat.card F = 4 := hfixed
  let : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; decide)
  let e : F ≃ Fin 4 := (Finite.equivFin F).trans (finCongr hF)
  let r : C →* Equiv.Perm F := MulAction.toPermHom C F
  let f : C →* Equiv.Perm (Fin 4) := e.permCongrHom.toMonoidHom.comp r
  have hf (c : C) (hc : c ∈ f.ker) : ∀ x : F, (c : G) • (x : Ω) = x := by
    have he : r c = 1 := by
      apply e.permCongrHom.injective
      simpa only [map_one] using (show e.permCongrHom (r c) = 1 from hc)
    intro x
    exact congrArg Subtype.val (Equiv.congr_fun he x)
  let inclusion : f.ker →* stabilizer (stabilizer G a) b := {
    toFun := fun c => ⟨⟨c.val.val, hf c.val c.property ⟨a, hja⟩⟩,
      hf c.val c.property ⟨b, hjb⟩⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hinj : Function.Injective inclusion := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : stabilizer (stabilizer G a) b => z.val.val) he
  refine ⟨f, isCyclic_of_injective inclusion hinj, ?_⟩
  change e.permCongrHom (r ⟨j, _⟩) = 1
  suffices hr : r ⟨j, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ = 1 by
    rw [hr, map_one]
  apply Equiv.ext
  intro x
  exact Subtype.ext x.property

end MulAction
