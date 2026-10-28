module

public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.Commutator.EqualImages
public import Theory.GroupTheory.PResidual.NormalSubgroup.SimpleQuotient

/-!
# Projections from a product with interchanged factors

Multiplication constructs the projection onto one of two disjoint commuting
subgroups. Its kernel is the other factor. An invariant nontrivial subgroup
cannot project trivially when an automorphism interchanges the factors.
If the projected factor is p-perfect with simple quotient by a normal
p-subgroup, every nontrivial normal p-perfect invariant actor surjects onto
it. Two such actors therefore have equal images.

The resulting commutator contradiction is the algebraic projection argument
in Aschbacher--Smith, 15.3.39, printed pp.1137--1138. The source application
must still establish the actor normality, residual properties, and simple
quotient for its actual factors.
-/

namespace Subgroup

variable {G : Type*} [Group G]

/-- Multiplication coordinates give the left projection, with its exact kernel
and its values on both embedded factors. -/
public theorem exists_left_projection_of_disjoint_of_commuting (A B : Subgroup G)
    (hd : Disjoint A B) (hc : A ≤ centralizer (B : Set G)) :
    ∃ f : (A ⊔ B : Subgroup G) →* A,
      Function.Surjective f ∧ f.ker = B.subgroupOf (A ⊔ B) ∧
      (∀ a : A, f (inclusion le_sup_left a) = a) ∧
      (∀ b : B, f (inclusion le_sup_right b) = 1) := by
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hd hc
  let f : (A ⊔ B : Subgroup G) →* A :=
    (MonoidHom.fst A B).comp e.symm.toMonoidHom
  have hleft (a : A) : e (a, 1) = inclusion le_sup_left a := by
    apply Subtype.ext
    simpa using he a 1
  have hright (b : B) : e (1, b) = inclusion le_sup_right b := by
    apply Subtype.ext
    simpa using he 1 b
  have hfleft (a : A) : f (inclusion le_sup_left a) = a := by
    rw [← hleft]
    exact congrArg Prod.fst (e.symm_apply_apply (a, 1))
  have hfright (b : B) : f (inclusion le_sup_right b) = 1 := by
    rw [← hright]
    exact congrArg Prod.fst (e.symm_apply_apply (1, b))
  refine ⟨f, fun a => ⟨inclusion le_sup_left a, hfleft a⟩, ?_, hfleft, hfright⟩
  ext x
  constructor
  · intro hx
    have hfst : (e.symm x).1 = 1 := hx
    have heq : (x : G) = ((e.symm x).2 : G) := by
      calc
        (x : G) = (e (e.symm x) : G) := congrArg Subtype.val (e.apply_symm_apply x).symm
        _ = ((e.symm x).1 : G) * ((e.symm x).2 : G) := he _ _
        _ = ((e.symm x).2 : G) := by rw [hfst]; simp
    change (x : G) ∈ B
    rw [heq]
    exact (e.symm x).2.property
  · intro hx
    exact hfright ⟨x, hx⟩

/-- A nontrivial invariant subgroup has nontrivial projection when the
automorphism sends the projection kernel into a disjoint factor. No diagonal
embedding or injectivity of the restricted projection is assumed. -/
public theorem map_ne_bot_of_kernel_swapped {H A B V : Subgroup G}
    {D : Type*} [Group D] (f : H →* D)
    (hk : f.ker = B.subgroupOf H) (hd : Disjoint A B)
    (e : G ≃* G) (hBA : B.map e.toMonoidHom = A)
    (hV : V.map e.toMonoidHom = V) (hVH : V ≤ H) (hne : V ≠ ⊥) :
    (V.subgroupOf H).map f ≠ ⊥ := by
  intro hz
  have hVB : V ≤ B := by
    have hv := (map_eq_bot_iff (V.subgroupOf H)).mp hz
    rw [hk] at hv
    intro x hx
    exact hv (show (⟨x, hVH hx⟩ : H) ∈ V.subgroupOf H from hx)
  have hVA : V ≤ A := by
    have hm := map_mono (f := e.toMonoidHom) hVB
    rwa [hBA, hV] at hm
  exact hne (le_bot_iff.mp ((le_inf hVA hVB).trans (disjoint_iff.mp hd).le))

/-- A normal invariant p-perfect actor surjects onto a p-perfect factor
with simple quotient by a normal p-subgroup. -/
public theorem map_eq_top_of_normal_isPPerfect_of_kernel_swapped {D : Type*} [Group D] {p : ℕ}
    {H A B N : Subgroup G} (f : H →* D) (hf : Function.Surjective f)
    (hk : f.ker = B.subgroupOf H) (hd : Disjoint A B)
    (e : G ≃* G) (hBA : B.map e.toMonoidHom = A)
    (hNH : N ≤ H) (hNs : N.map e.toMonoidHom = N)
    (hNn : (N.subgroupOf H).Normal) (hNp : IsPPerfect p N) (hne : N ≠ ⊥)
    (Q : Subgroup D) [Q.Normal] [IsSimpleGroup (D ⧸ Q)]
    (hQ : IsPGroup p Q) (hD : IsPPerfect p D) :
    (N.subgroupOf H).map f = ⊤ := by
  have hn : IsPPerfect p (N.subgroupOf H) :=
    hNp.of_surjective (subgroupOfEquivOfLe hNH).symm.toMonoidHom
      (subgroupOfEquivOfLe hNH).symm.surjective
  let : ((N.subgroupOf H).map f).Normal := hNn.map f hf
  exact eq_top_of_normal_isPPerfect_of_simple_quotient Q hQ hD _
    (hn.of_surjective (f.subgroupMap _) (f.subgroupMap_surjective _))
    (map_ne_bot_of_kernel_swapped f hk hd e hBA hNs hNH hne)

/-- Two normal p-perfect invariant actors cannot respectively centralize
and generate a nontrivial invariant plane in a product with swapped factors.
The projections, equal actor images, and nontrivial plane image are constructed. -/
public theorem no_commutator_plane_in_swapped_product {p : ℕ}
    (A B N₁ N₂ V : Subgroup G)
    (hd : Disjoint A B) (hc : A ≤ centralizer (B : Set G))
    (e : G ≃* G) (hBA : B.map e.toMonoidHom = A)
    (Q : Subgroup A) [Q.Normal] [IsSimpleGroup (A ⧸ Q)]
    (hQ : IsPGroup p Q) (hA : IsPPerfect p A)
    (h₁le : N₁ ≤ A ⊔ B) (h₂le : N₂ ≤ A ⊔ B)
    (h₁n : (N₁.subgroupOf (A ⊔ B)).Normal)
    (h₂n : (N₂.subgroupOf (A ⊔ B)).Normal)
    (h₁p : IsPPerfect p N₁) (h₂p : IsPPerfect p N₂)
    (h₁ne : N₁ ≠ ⊥) (h₂ne : N₂ ≠ ⊥)
    (h₁s : N₁.map e.toMonoidHom = N₁)
    (h₂s : N₂.map e.toMonoidHom = N₂)
    (hVs : V.map e.toMonoidHom = V)
    (hVle : V ≤ A ⊔ B) (hVne : V ≠ ⊥)
    (hcent : N₁ ≤ centralizer (V : Set G)) (hgen : ⁅V, N₂⁆ = V) : False := by
  obtain ⟨f, hf, hk, _, _⟩ := exists_left_projection_of_disjoint_of_commuting A B hd hc
  have h₁ := map_eq_top_of_normal_isPPerfect_of_kernel_swapped f hf hk hd e hBA h₁le h₁s h₁n h₁p h₁ne Q hQ hA
  have h₂ := map_eq_top_of_normal_isPPerfect_of_kernel_swapped f hf hk hd e hBA h₂le h₂s h₂n h₂p h₂ne Q hQ hA
  have hc' : N₁.subgroupOf (A ⊔ B) ≤
      centralizer (V.subgroupOf (A ⊔ B) : Set (A ⊔ B : Subgroup G)) := by
    intro x hx v hv
    exact Subtype.ext (hcent hx v hv)
  have hg' : ⁅V.subgroupOf (A ⊔ B), N₂.subgroupOf (A ⊔ B)⁆ =
      V.subgroupOf (A ⊔ B) := by
    apply Subgroup.map_injective (A ⊔ B).subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hVle, map_subgroupOf_eq_of_le h₂le, hgen]
  exact map_ne_bot_of_kernel_swapped f hk hd e hBA hVs hVle hVne
    (map_eq_bot_of_equal_actor_images f _ _ _ hc' (h₁.trans h₂.symm) hg')

end Subgroup
