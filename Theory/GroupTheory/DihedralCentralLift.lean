module
public import Theory.GroupTheory.CyclicDihedralKernel

/-!
# Rotation conjugators through central kernels

The preimage of a cyclic subgroup under a homomorphism with central kernel is
abelian. In an odd dihedral group every involution is a reflection, and any
two reflections are conjugate by a rotation. Lifting that rotation therefore
supplies a conjugator which centralizes the product of two marked involutions.

The point-local application is the dihedral exclusion in Aschbacher--Smith,
G.4.9, printed p.341. No complement or splitting theorem is needed.
-/

public noncomputable section
open Subgroup
namespace MonoidHom
variable {G H : Type*} [Group G] [Group H]

theorem commute_of_mem_cyclic_image_preimage (f : G →* H)
    (hc : f.ker≤center G) (R : Subgroup H) [IsCyclic R]
    (x y : G) (hx : f x∈R) (hy : f y∈R) : Commute x y := by
  let T := R.comap f
  let g : T →* R :=
    { toFun := fun t => ⟨f t,t.property⟩
      map_one' := Subtype.ext (f.map_one)
      map_mul' := fun a b => Subtype.ext (f.map_mul a b) }
  have hg : g.ker≤center T := by
    intro t ht
    apply mem_center_iff.mpr
    intro s
    apply Subtype.ext
    have htf : f t.val=1 := congrArg Subtype.val (show g t=1 from ht)
    exact mem_center_iff.mp (hc htf) s.val
  let : IsMulCommutative T := g.isMulCommutative_of_isCyclic_of_ker_le_center hg
  exact congrArg (fun t : T => t.val)
    ((IsMulCommutative.is_comm (M := T)).comm (⟨x,hx⟩ : T) ⟨y,hy⟩)
end MonoidHom

namespace DihedralGroup
variable {m : ℕ}

theorem exists_reflection_of_order_two (hm : Odd m) (x : DihedralGroup m)
    (hx : orderOf x=2) : ∃i, x=sr i := by
  cases x with
  | r i =>
    have hp : (r i : DihedralGroup m)^m=1 := by simp
    have hd := orderOf_dvd_of_pow_eq_one hp
    rw [hx] at hd
    exact (hm.not_two_dvd_nat hd).elim
  | sr i => exact ⟨i,rfl⟩

theorem exists_rotation_conjugate_reflection (hm : Odd m) (i j : ZMod m) :
    ∃k : ZMod m, r k*sr i*(r k)⁻¹=sr j := by
  obtain ⟨n,hn⟩ := hm
  let k : ZMod m := (n+1)*(i-j)
  refine ⟨k,?_⟩
  rw [inv_r,r_mul_sr,sr_mul_r]
  congr 1
  have hmz : (m : ZMod m)=0 := ZMod.natCast_self m
  have htwo : (2 : ZMod m)*(n+1)=1 := by
    have hnat : 2*(n+1)=m+1 := by omega
    have h := congrArg (fun t : ℕ => (t : ZMod m)) hnat
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,hmz,zero_add] using h
  dsimp [k]
  calc
    i-(n+1)*(i-j)+ -((n+1)*(i-j))=i-(2*(n+1))*(i-j) := by ring
    _ = j := by rw [htwo]; ring
end DihedralGroup

namespace MonoidHom
variable {G : Type*} [Group G] {m : ℕ}

/-- Rotation conjugators lift through a central kernel while centralizing the
product of the marked first two involutions. -/
theorem exists_dihedral_conjugator_centralizing_product
    (f : G →* DihedralGroup m) (hf : Function.Surjective f) (hc : f.ker≤center G)
    (hm : Odd m) (a b c : G) (ha : orderOf (f a)=2)
    (hb : orderOf (f b)=2) (hcc : orderOf (f c)=2) :
    ∃g : G, Commute g (a*b) ∧ f (g*a*g⁻¹)=f c := by
  obtain ⟨i,hi⟩ := DihedralGroup.exists_reflection_of_order_two hm (f a) ha
  obtain ⟨j,hj⟩ := DihedralGroup.exists_reflection_of_order_two hm (f b) hb
  obtain ⟨k,hk⟩ := DihedralGroup.exists_reflection_of_order_two hm (f c) hcc
  obtain ⟨r,hr⟩ := DihedralGroup.exists_rotation_conjugate_reflection hm i k
  obtain ⟨g,hg⟩ := hf (DihedralGroup.r r)
  have hrot (z : ZMod m) : DihedralGroup.r z∈zpowers (DihedralGroup.r (1 : ZMod m)) := by
    let : NeZero m := ⟨hm.pos.ne'⟩
    have hz : DihedralGroup.r z=(DihedralGroup.r (1 : ZMod m))^z.val := by simp
    rw [hz]
    exact pow_mem (mem_zpowers _) _
  refine ⟨g,?_,?_⟩
  · apply f.commute_of_mem_cyclic_image_preimage hc (zpowers (DihedralGroup.r (1 : ZMod m)))
    · rw [hg]
      exact hrot r
    · rw [map_mul,hi,hj,DihedralGroup.sr_mul_sr]
      exact hrot _
  · rw [map_mul,map_mul,map_inv,hg,hi,hk]
    exact hr
end MonoidHom
