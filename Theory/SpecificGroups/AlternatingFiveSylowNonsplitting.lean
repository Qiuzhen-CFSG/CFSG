module
public import Theory.SpecificGroups.AlternatingFiveFixedCentralizer
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# A Sylow four-group cannot lie in the derived centralizer of a normal A₅

An actor fixing the Sylow four-group pointwise induces an inner automorphism
from that four-group. Such automorphisms commute, so the derived subgroup of
the actor group centralizes A₅. Its intersection with the four-group is then
trivial because A₅ is centerless. This is the nonsplitting contradiction used
in Aschbacher--Smith F.4.42, printed p.295.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

theorem alternating_five_sylow_not_le_commutator_centralizer
    (A V Q : Subgroup G) [A.Normal] [IsMulCommutative V]
    (e : A ≃* alternatingGroup (Fin 5)) (P : Sylow 2 A)
    (hP : (P : Subgroup A).map A.subtype = V)
    (hQ : Q ≤ centralizer (V : Set G)) (hVQ : V ≤ ⁅Q,Q⁆) : V = ⊥ := by
  let : Finite A := Finite.of_injective e e.injective
  let α := MulAut.conjNormal (H := A)
  have hinner (x : G) (hx : x ∈ Q) : ∃ a ∈ P, α x = MulAut.conj a := by
    apply Theory.PSL2.SylowFixedQuotients.fixed_inner_transport e (P : Subgroup A)
      (Theory.PSL2.SylowFixedQuotients.alternating_sylow_fixed_inner
        (P.mapSurjective (f := e.toMonoidHom) e.surjective))
    intro a ha
    have hav : (a : G) ∈ V := hP ▸ mem_map_of_mem A.subtype ha
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.mpr ((hQ hx) a hav).symm)
  have hderived : ⁅Q,Q⁆ ≤ α.ker := by
    apply commutator_le.mpr
    intro x hx y hy
    obtain ⟨a,ha,he⟩ := hinner x hx
    obtain ⟨b,hb,hf⟩ := hinner y hy
    have hav : (a : G) ∈ V := hP ▸ mem_map_of_mem A.subtype ha
    have hbv : (b : G) ∈ V := hP ▸ mem_map_of_mem A.subtype hb
    have hab : a*b=b*a := Subtype.ext ((V.le_centralizer hav) b hbv).symm
    have hc : ⁅a,b⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hab
    change α ⁅x,y⁆ = 1
    rw [map_commutatorElement,he,hf,←map_commutatorElement,hc,map_one]
  apply bot_unique
  intro v hv
  have hvA : v ∈ A := by rw [←hP] at hv; exact map_subtype_le _ hv
  have hfix : α v = 1 := hderived (hVQ hv)
  have hz : (⟨v,hvA⟩ : A) ∈ center A := by
    apply mem_center_iff.mpr
    intro a
    have hh := congrArg (fun β : MulAut A => (β a).val) hfix
    change v*(a:G)*v⁻¹=(a:G) at hh
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hh := (centerCongr e ⟨⟨v,hvA⟩,hz⟩).property
  change e ⟨v,hvA⟩ ∈ center (alternatingGroup (Fin 5)) at hh
  rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hh
  exact mem_bot.mpr (congrArg Subtype.val (e.injective (hh.trans (map_one e).symm)))

end Subgroup
