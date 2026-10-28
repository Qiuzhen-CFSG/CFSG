module
public import Theory.SpecificGroups.PSL2.SylowFixedQuotients.Five
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# Fixed elements centralize a normal A₅

The pointwise fixer of a Sylow four-group in Aut(A₅) consists of inner
automorphisms from that four-group. An element of an abelian overgroup
therefore acts in this way. If it commutes with an actor that fixes no
nonidentity Sylow element, its inner conjugator must be trivial because
A₅ is centerless. Thus it centralizes the whole normal A₅.

Source application: the cubic-fixed four-group in Aschbacher–Smith F.4.42,
printed pp.295–296. The actual Sylow and ambient embeddings are retained.
-/

open Subgroup
open scoped IsMulCommutative
public noncomputable section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A fixed element of an abelian Sylow overgroup centralizes A₅ when the
same automorphism has no nonidentity fixed element in that Sylow subgroup. -/
theorem alternating_five_fixed_centralizes
    (A Q : Subgroup G) [A.Normal] [IsMulCommutative Q]
    (e : A ≃* alternatingGroup (Fin 5)) (P : Sylow 2 A)
    (hPQ : (P : Subgroup A).map A.subtype ≤ Q)
    (c : G) (hfix : ∀ a : A, a ∈ P → c * a.val * c⁻¹ = a.val → a = 1)
    {x : G} (hxQ : x ∈ Q) (hxc : x * c = c * x) :
    x ∈ centralizer (A : Set G) := by
  let α := MulAut.conjNormal (H := A) x
  have hα : ∀ a ∈ P, α a = a := by
    intro a ha
    have haQ : a.val ∈ Q := hPQ ⟨a,ha,rfl⟩
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (Q.le_centralizer haQ x hxQ)
  obtain ⟨a,ha,hαa⟩ := Theory.PSL2.SylowFixedQuotients.fixed_inner_transport e
    (P : Subgroup A)
    (Theory.PSL2.SylowFixedQuotients.alternating_sylow_fixed_inner
      (P.mapSurjective (f := e.toMonoidHom) e.surjective)) α hα
  have hcenter : center A = ⊥ := by
    apply bot_unique
    intro a ha
    have hh := (centerCongr e ⟨a,ha⟩).property
    change e a ∈ center (alternatingGroup (Fin 5)) at hh
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hh
    exact mem_bot.mpr (e.injective (hh.trans (map_one e).symm))
  let β := MulAut.conjNormal (H := A) c
  have hβα : β * α * β⁻¹ = α := by
    have hh : c * x * c⁻¹ = x := mul_inv_eq_iff_eq_mul.mpr hxc.symm
    have h := congrArg (MulAut.conjNormal : G →* MulAut A) hh
    simpa only [map_mul,map_inv] using h
  have hac : β a = a := by
    apply MulAut.conj_injective_of_center_eq_bot hcenter
    calc
      MulAut.conj (β a) = β * MulAut.conj a * β⁻¹ := by
        apply MulEquiv.ext
        intro b
        change β a * b * (β a)⁻¹ = β (a * β.symm b * a⁻¹)
        simp only [map_mul,map_inv,β.apply_symm_apply]
      _ = MulAut.conj a := by rw [← hαa]; exact hβα
  have ha1 : a = 1 := hfix a ha (congrArg Subtype.val hac)
  have hαone : α = 1 := by rw [hαa,ha1,map_one]
  intro b hb
  have he := congrArg (fun γ : MulAut A => (γ ⟨b,hb⟩).val) hαone
  change x * b * x⁻¹ = b at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm
end Subgroup
