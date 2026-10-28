module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Index

/-!
# Faithful normalizer actions beside an odd inverter

If an odd subgroup E is self-centralizing and t inverts E, then the
normalizer of E intersected with C_G(t) acts faithfully on E. Its action
kernel lies in E and is fixed by inversion, hence is trivial. Any element
acting by a power map is central in this faithful actor group, since power
maps commute with every group automorphism.

Source application: the prime-plane and cyclic-four scalar action before
Aschbacher–Smith J.4.8, printed p.443.
-/

@[expose] public section
noncomputable section
namespace Subgroup
variable {G : Type*} [Group G]

abbrev centralizingNormalizer (E:Subgroup G) (t:G) : Subgroup G :=
  normalizer (E:Set G) ⊓ centralizer ({t}:Set G)

def centralizingNormalizerAction (E:Subgroup G) (t:G) :
    centralizingNormalizer E t →* MulAut E :=
  E.normalizerMonoidHom.comp (inclusion inf_le_left)

theorem centralizingNormalizerAction_injective [Finite G] (E:Subgroup G) (t:G)
    (hC:centralizer (E:Set G)=E) (hodd:Odd (Nat.card E))
    (hinv:∀x∈E,t*x*t⁻¹=x⁻¹) : Function.Injective (centralizingNormalizerAction E t) := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  have hxC : (x:G)∈centralizer (E:Set G) := by
    intro a ha
    have he := congrArg (fun f:MulAut E => (f ⟨a,ha⟩:G)) hx
    change (x:G)*a*(x:G)⁻¹=a at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hxE : (x:G)∈E := hC.le hxC
  have hcomm := mem_centralizer_singleton_iff.mp x.property.2
  have he := hinv x hxE
  have he' : (x:G)=(x:G)⁻¹ := by
    simpa only [← hcomm,mul_inv_cancel_right] using he
  have hx2 : (x:G)^2=1 := by
    calc
      (x:G)^2 = (x:G)*(x:G) := pow_two _
      _ = (x:G)⁻¹*(x:G) := congrArg (· * (x:G)) he'
      _ = 1 := inv_mul_cancel _
  have hc := _root_.orderOf_dvd_natCard (⟨x,hxE⟩:E)
  rw [← orderOf_coe] at hc
  have hd : orderOf (x:G)∣1 := (Nat.coprime_two_left.mpr hodd).gcd_eq_one ▸
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hx2) hc
  exact Subtype.ext (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd))

theorem mem_center_of_power_action [Finite G] (E:Subgroup G) (t:G)
    (hC:centralizer (E:Set G)=E) (hodd:Odd (Nat.card E))
    (hinv:∀x∈E,t*x*t⁻¹=x⁻¹) (a:centralizingNormalizer E t) (n:ℕ)
    (ha:∀x:E,centralizingNormalizerAction E t a x=x^n) :
    a∈center (centralizingNormalizer E t) := by
  apply mem_center_iff.mpr
  intro b
  apply centralizingNormalizerAction_injective E t hC hodd hinv
  rw [map_mul,map_mul]
  apply MulEquiv.ext
  intro x
  change centralizingNormalizerAction E t b (centralizingNormalizerAction E t a x)=
    centralizingNormalizerAction E t a (centralizingNormalizerAction E t b x)
  rw [ha,ha,map_pow]

end Subgroup
