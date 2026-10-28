module

public import Theory.GroupTheory.AlternatingPowerTwoExtension
public import Theory.Quasithin.EvenCharacteristic

/-!
# Local characteristic and quotients of direct powers

A direct power of a finite group of characteristic p again has characteristic
p. The product of the factor p-cores is a normal p-subgroup, and testing on
single-coordinate elements puts its centralizer inside that product.

Applying a supplied surjection coordinatewise constructs a surjection of
direct powers. Its kernel embeds into the corresponding power of the
original kernel, preserving the p-group property. These facts supply the
local-factor step in the component-orbit construction motivated by
Aschbacher–Smith 2.3.9(7), printed pp.525–526.
-/

public section

open Subgroup
namespace Theory.GroupTheory
variable {G H I : Type*} [Group G] [Group H]

private theorem pgroup_functions [Finite G] {p : ℕ} (hG : IsPGroup p G) :
    IsPGroup p (I → G) := by
  obtain ⟨n, hn⟩ := hG.exists_card_dvd_pow
  intro x
  refine ⟨n, funext fun i => ?_⟩
  exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard (x i)).trans hn)

/-- A direct power of a finite group of characteristic p has characteristic p. -/
theorem centralizer_pCore_power_le [Finite G] {p : ℕ}
    (hG : centralizer (pCore p G : Set G) ≤ pCore p G) :
    centralizer (pCore p (I → G) : Set (I → G)) ≤ pCore p (I → G) := by
  classical
  let Q : Subgroup (I → G) := pi Set.univ (fun _ => pCore p G)
  have hQ (x : I → G) : x ∈ Q ↔ ∀ i, x i ∈ pCore p G := by simp [Q, mem_pi]
  let : Q.Normal := ⟨by
    intro x hx y
    apply (hQ _).mpr
    intro i
    exact (pCore_normal (p := p) (G := G)).conj_mem _ ((hQ _).mp hx i) _⟩
  let q : Q →* (I → pCore p G) := {
    toFun := fun x i => ⟨x.val i, (hQ _).mp x.property i⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hq : Function.Injective q := by
    intro x y h
    apply Subtype.ext
    funext i
    exact congrArg (fun f : I → pCore p G => (f i : G)) h
  have hQp : IsPGroup p Q := (pgroup_functions pCore_isPGroup).of_injective q hq
  have hQcore : Q ≤ pCore p (I → G) := le_sSup ⟨inferInstance, hQp⟩
  intro x hx
  apply hQcore
  apply (hQ _).mpr
  intro i
  apply hG
  rw [mem_centralizer_iff]
  intro y hy
  have hsingle : Pi.mulSingle i y ∈ Q := by
    change Pi.mulSingle i y ∈ pi Set.univ (fun _ : I => pCore p G)
    exact (mulSingle_mem_pi (H := fun _ : I => pCore p G) i y).mpr (fun _ => hy)
  have he := mem_centralizer_iff.mp hx _ (hQcore hsingle)
  simpa only [Pi.mul_apply, Pi.mulSingle_eq_same] using congrFun he i

/-- A surjection with p-group kernel gives such a surjection on every direct power. -/
theorem power_surjection_kernel_isPGroup [Finite G] {p : ℕ}
    (f : G →* H) (hf : Function.Surjective f) (hk : IsPGroup p f.ker) :
    ∃ F : (I → G) →* (I → H), Function.Surjective F ∧ IsPGroup p F.ker := by
  classical
  let F : (I → G) →* (I → H) := MonoidHom.piMap (fun _ => f)
  have hF : Function.Surjective F := by
    intro y
    choose x hx using fun i => hf (y i)
    exact ⟨x, funext hx⟩
  let k : F.ker →* (I → f.ker) := {
    toFun := fun x i => ⟨x.val i, congrFun x.property i⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hinj : Function.Injective k := by
    intro x y he
    apply Subtype.ext
    funext i
    exact congrArg (fun z : I → f.ker => (z i : G)) he
  exact ⟨F, hF, (pgroup_functions hk).of_injective k hinj⟩

end Theory.GroupTheory

end
