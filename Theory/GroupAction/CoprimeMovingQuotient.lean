module
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.Lemmas

/-!
# Coprime moving subgroups through fixed kernels

An equivariant surjection carries action commutators onto action commutators.
For an abelian coprime action, the moving subgroup is disjoint from the fixed
subgroup. Thus an equivariant quotient with fixed kernel restricts to an
actual isomorphism of moving subgroups. The original projection is retained
in its pointwise formula. Surjective changes of actors are also allowed.

Source application: the central fixed layer of the ordinary A₇ block in
Aschbacher–Smith C.1.29, printed p.134.
-/
public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupAction
variable {A V W : Type*} [Group A] [Group V] [Group W]
    [MulDistribMulAction A V] [MulDistribMulAction A W]

theorem commutatorAction_map_surjective (f : V →* W)
    (hf : Function.Surjective f) (he : ∀ a : A, ∀ v : V, f (a • v) = a • f v) :
    (commutatorAction A V).map f = commutatorAction A W := by
  rw [commutatorAction_eq_closure, commutatorAction_eq_closure, MonoidHom.map_closure]
  congr 1
  ext w
  constructor
  · rintro ⟨_, ⟨a, v, rfl⟩, rfl⟩
    exact ⟨a, f v, by rw [map_mul, map_inv, he]⟩
  · rintro ⟨a, w, rfl⟩
    obtain ⟨v, rfl⟩ := hf w
    exact ⟨v⁻¹ * (a • v), ⟨a, v, rfl⟩, by rw [map_mul, map_inv, he]⟩

/-- A fixed kernel disappears on the moving subgroup of an abelian coprime action. -/
@[expose] noncomputable def movingEquivOfFixedKernel [Finite V] [Finite A] [IsMulCommutative V]
    (f : V →* W) (hf : Function.Surjective f)
    (he : ∀ a : A, ∀ v : V, f (a • v) = a • f v)
    (hc : Nat.Coprime (Nat.card A) (Nat.card V))
    (hk : f.ker ≤ FixedPoints.subgroup A V) :
    commutatorAction A V ≃* commutatorAction A W := by
  let M := commutatorAction A V
  have hdis : Disjoint (FixedPoints.subgroup A V) M :=
    (isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (Group.isSolvable_of_comm (fun x y : V => mul_comm x y)) hc inferInstance).disjoint
  have hi : Function.Injective (f.comp M.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro x hx
    exact mem_bot.mpr (Subtype.ext (hdis.le_bot ⟨hk hx, x.property⟩))
  let e : M ≃* M.map f := MulEquiv.ofBijective (f.subgroupMap M)
    ⟨fun x y h => hi (congrArg Subtype.val h), f.subgroupMap_surjective M⟩
  exact e.trans (MulEquiv.subgroupCongr (commutatorAction_map_surjective f hf he))

@[simp] theorem movingEquivOfFixedKernel_apply [Finite V] [Finite A] [IsMulCommutative V]
    (f : V →* W) (hf : Function.Surjective f)
    (he : ∀ a : A, ∀ v : V, f (a • v) = a • f v)
    (hc : Nat.Coprime (Nat.card A) (Nat.card V))
    (hk : f.ker ≤ FixedPoints.subgroup A V) (v : commutatorAction A V) :
    (movingEquivOfFixedKernel f hf he hc hk v : W) = f v := rfl

/-- Replacing the actor by a surjective marked actor homomorphism leaves
the moving subgroup unchanged. -/
theorem commutatorAction_eq_of_actor_surjective
    {B : Type*} [Group B] (a : B →* A) (ha : Function.Surjective a) :
    let _ := MulDistribMulAction.compHom V a
    commutatorAction B V = commutatorAction A V := by
  let _ := MulDistribMulAction.compHom V a
  change commutatorAction B V = commutatorAction A V
  rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
  congr 1
  ext v
  constructor
  · rintro ⟨b, w, rfl⟩
    exact ⟨a b, w, rfl⟩
  · rintro ⟨b, w, rfl⟩
    obtain ⟨c, rfl⟩ := ha b
    exact ⟨c, w, rfl⟩
end Theory.GroupAction
