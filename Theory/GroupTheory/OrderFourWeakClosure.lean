module
public import Theory.Frattini.PGroup
public import Mathlib.GroupTheory.Subgroup.Centralizer
/-!
# An order-four class controlled by its weakly closed square

If the square z is weakly closed in P and the squares of S lie in P,
any conjugator taking an element whose square is z into S centralizes z.
A subgroup F containing S and normalized by C_G(z) therefore separates
this class from S whenever the original element lies outside F.

Source: the transfer argument in Aschbacher--Smith 2.4.29, printed p.546.
-/
public section
namespace Subgroup

/-- Weak closure of the square forces fusion of an order-four element into
its subgroup to be realized by the centralizer of the square. -/
theorem order_four_class_avoids_of_square_weak_closed
    {G : Type*} [Group G] [Finite G]
    (S P F : Subgroup G) (hS : IsPGroup 2 S) (hSF : S≤F)
    (hphi : (frattini S).map S.subtype≤P)
    (j z : G) (hjsq : j^2=z) (hjF : j∉F)
    (hn : centralizer ({z}:Set G)≤normalizer (F:Set G))
    (hweak : ∀x∈P, IsConj z x → x=z) :
    ∀x∈S, ¬IsConj j x := by
  intro x hx hconj
  let : Fact (IsPGroup 2 S) := ⟨hS⟩
  have hxP : x^2∈P := hphi ⟨(⟨x,hx⟩:S)^2,
    pth_power_mem_frattini_of_isPGroup (⟨x,hx⟩:S),rfl⟩
  have hxz : x^2=z := hweak _ hxP (hjsq ▸ hconj.pow 2)
  obtain ⟨g,hg⟩ := isConj_iff.mp hconj
  have hgz : g*z*g⁻¹=z := by
    have hh := congrArg (fun a:G=>a^2) hg
    simpa only [conj_pow, hjsq, hxz] using hh
  have hgc : g∈centralizer ({z}:Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    calc
      g*z=(g*z*g⁻¹)*g := by simp [mul_assoc]
      _=z*g := by rw [hgz]
  have hjmem : j∈F := (mem_normalizer_iff.mp (hn hgc) j).mpr (hg ▸ hSF hx)
  exact hjF hjmem
end Subgroup
