module
public import Theory.SpecificGroups.PSL3Two.Parabolics.WreathPair

/-!
# Cubic centralizers in the paired binary-three actor

A cubic subgroup of SL₃(2) has a cyclic centralizer of order three. In the
regular wreath square, centralizing the two independent cubic coordinates
forces the factor permutation to be trivial. Thus a cubic plane has a
three-group centralizer, and every two-subgroup centralizing it is trivial.
Sylow conjugacy transports the explicit coordinate calculation to any
subgroup of order nine. The only finite check enumerates SL₃(2), not the
whole wreath group.

Source application: Aschbacher--Smith 10.2.5, printed p.748, comparing the
original parabolic radical with the original module-action kernel.
The imported matrix model retains the attribution in LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup
namespace Matrix.PSL3Two.WreathPair

private def cubic : SL := ⟨!![0,1,0;0,0,1;1,0,0], by decide⟩
private theorem cubic_ne_one : cubic ≠ 1 := by decide +kernel
private theorem cubic_order : orderOf cubic = 3 := by
  exact orderOf_eq_prime (by decide +kernel) cubic_ne_one
private theorem cubic_centralizer_cube : ∀ a : SL, a * cubic = cubic * a → a ^ 3 = 1 := by
  decide +kernel

private def planeHom : (Bit → zpowers cubic) →* Actor where
  toFun a := ⟨fun i => (a i : SL),1⟩
  map_one' := rfl
  map_mul' a b := by ext <;> simp

private theorem planeHom_injective : Function.Injective planeHom := by
  intro a b he
  funext i
  exact Subtype.ext (congrArg (fun w : Actor => w.left i) he)

private theorem plane_card : Nat.card planeHom.range = 9 := by
  rw [Nat.card_congr (MonoidHom.ofInjective planeHom_injective).toEquiv.symm,
    Nat.card_fun, Nat.card_zpowers, cubic_order]
  change 3 ^ Nat.card (ZMod 2) = 9
  rw [Nat.card_zmod]
  norm_num

private def planeSylow : Sylow 3 Actor := Sylow.ofCard planeHom.range (by
  rw [plane_card,RegularWreathProduct.card,card_SL]
  change 9 = 3 ^ (168 ^ Nat.card (ZMod 2) * Nat.card (ZMod 2)).factorization 3
  rw [Nat.card_zmod]
  decide +kernel)

private theorem centralizer_plane_cube (x : Actor)
    (hx : x ∈ centralizer (planeHom.range : Set Actor)) : x ^ 3 = 1 := by
  classical
  let a (i : Bit) : Bit → zpowers cubic :=
    Pi.mulSingle i ⟨cubic,mem_zpowers cubic⟩
  have he (i : Bit) : planeHom (a i) * x = x * planeHom (a i) :=
    mem_centralizer_iff.mp hx _ ⟨a i,rfl⟩
  have hr : x.right = 1 := by
    by_contra hn
    have hn' : x.right⁻¹ * (1 : Bit) ≠ 1 := by simpa using hn
    have hh := congrArg (fun w : Actor => w.left 1) (he 1)
    have hh' : cubic * x.left 1 = x.left 1 := by
      simpa [planeHom,a,Pi.mulSingle_apply,hn',hn] using hh
    exact cubic_ne_one (mul_right_cancel (hh'.trans (one_mul _).symm))
  have hl (i : Bit) : (x.left i) ^ 3 = 1 := by
    apply cubic_centralizer_cube
    have hh := congrArg (fun w : Actor => w.left i) (he i)
    simpa [planeHom,a,Pi.mulSingle_apply,hr] using hh.symm
  apply RegularWreathProduct.ext
  · funext i
    simpa [pow_succ,hr,mul_assoc] using hl i
  · simp [pow_succ,hr]

private theorem centralizer_isThree_of_map {A : Type*} [Group A]
    (e : MulAut A) (P : Subgroup A)
    (hp : IsPGroup 3 (centralizer (P.map e.toMonoidHom : Set A))) :
    IsPGroup 3 (centralizer (P : Set A)) := by
  let f : centralizer (P : Set A) →* centralizer (P.map e.toMonoidHom : Set A) :=
    (e.toMonoidHom.comp (centralizer (P : Set A)).subtype).codRestrict _ (by
      intro x
      rw [mem_centralizer_iff]
      rintro _ ⟨z,hz,rfl⟩
      have hh := mem_centralizer_iff.mp x.property z hz
      exact (map_mul e.toMonoidHom z (x : A)).symm.trans
        ((congrArg e.toMonoidHom hh).trans (map_mul e.toMonoidHom (x : A) z)))
  exact hp.of_injective f (fun x y he => Subtype.ext (e.injective (congrArg Subtype.val he)))

private theorem exists_plane_conjugacy (P : Subgroup Actor) (hP : Nat.card P = 9) :
    ∃ e : MulAut Actor, P.map e.toMonoidHom = planeHom.range := by
  let S : Sylow 3 Actor := Sylow.ofCard P (by
    rw [hP,RegularWreathProduct.card,card_SL]
    change 9 = 3 ^ (168 ^ Nat.card (ZMod 2) * Nat.card (ZMod 2)).factorization 3
    rw [Nat.card_zmod]
    decide +kernel)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Actor S planeSylow
  exact ⟨MulAut.conj g,congrArg Sylow.toSubgroup hg⟩

/-- A cubic plane in the paired binary-three actor has a three-group centralizer. -/
theorem centralizer_cubic_plane_isThree (P : Subgroup Actor) (hP : Nat.card P = 9) :
    IsPGroup 3 (centralizer (P : Set Actor)) := by
  obtain ⟨e,he⟩ := exists_plane_conjugacy P hP
  apply centralizer_isThree_of_map e P
  rw [he]
  intro x
  exact ⟨1,Subtype.ext (centralizer_plane_cube x x.property)⟩

/-- No nontrivial two-subgroup of the actor centralizes a cubic plane. -/
theorem two_subgroup_centralizing_cubic_plane_eq_bot (P U : Subgroup Actor)
    (hP : Nat.card P = 9) (hU : IsPGroup 2 U)
    (hc : U ≤ centralizer (P : Set Actor)) : U = ⊥ := by
  have hd := hU.disjoint_of_coprime (centralizer_cubic_plane_isThree P hP) (by decide)
  exact bot_unique (fun _ hx => hd.le_bot ⟨hx,hc hx⟩)

end Matrix.PSL3Two.WreathPair
