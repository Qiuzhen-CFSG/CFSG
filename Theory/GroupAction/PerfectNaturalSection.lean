module

public import Theory.GroupAction.PPerfectFixedCentralizer
public import Theory.Representation.BinaryParabolicNatural.Basic
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.Basic

/-!
# A two-group fixes an elementary natural central extension

A two-perfect actor has full binary linear action on an elementary group's
central quotient. If its commutator with a normal two-group acts trivially
on the whole elementary group, Thompson's lemma makes the fixed subgroup
larger than the central kernel. Transitivity on nonzero quotient vectors
then makes that fixed subgroup the whole elementary group.

Source: Aschbacher--Smith 12.7.16, printed p.844.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupAction
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Thompson's lemma and the actual full quotient action force the whole
normal two-group to centralize the unchanged elementary group. -/
theorem centralizes_of_perfect_full_natural_section
    (B Q W : Subgroup G) [Q.Normal] [W.Normal] [IsElementaryAbelian 2 W]
    (hB : IsPPerfect 2 B) (hQ : IsPGroup 2 Q) (hcomm : ⁅Q,B⁆≤W)
    (π : W →* Multiplicative V) (hπ : Function.Surjective π)
    (hk : ∀ w : W, π w=1 → (w:G)∈center G)
    (ρ : G →* (V ≃ₗ[ZMod 2] V)) (hρ : B.map ρ=⊤)
    (heq : ∀ (g : G) (w : W),
      (π ((MulAut.conjNormal g : MulAut W) w)).toAdd = ρ g (π w).toAdd)
    (hdim : 2≤Module.finrank (ZMod 2) V) : W≤centralizer (Q : Set G) := by
  have hnonzero : ∃ w : W, (w:G)∈centralizer (Q : Set G) ∧ (π w).toAdd≠0 := by
    by_contra hn
    push Not at hn
    have hfix : ⁅W ⊓ centralizer (Q : Set G),B⁆=⊥ := by
      apply commutator_eq_bot_iff_le_centralizer.mpr
      intro w hw
      have hwker : π ⟨w,hw.1⟩=1 := hn ⟨w,hw.1⟩ hw.2
      exact (center_le_centralizer (B : Set G)) (hk ⟨w,hw.1⟩ hwker)
    have hBW : ⁅W,B⁆=⊥ := hB.centralizes_of_commuting_fixed B Q W hQ
      le_normalizer_of_normal le_normalizer_of_normal
      (hcomm.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)) hfix
    have hfixed (v : V) : v∈(Representation.BinaryParabolicNatural.natural V).invariants := by
      intro g
      obtain ⟨w,hw⟩ := hπ (Multiplicative.ofAdd v)
      obtain ⟨b,hb,hbg⟩ := (show g∈B.map ρ from hρ.symm ▸ mem_top g)
      have hc : (MulAut.conjNormal b : MulAut W) w=w := by
        apply Subtype.ext
        change b*(w:G)*b⁻¹=(w:G)
        exact mul_inv_eq_of_eq_mul
          ((commutator_eq_bot_iff_le_centralizer.mp hBW) w.property b hb)
      have hh := heq b w
      rw [hc,hw,hbg] at hh
      exact hh.symm
    have ht : (Representation.BinaryParabolicNatural.natural V).invariants=⊤ :=
      top_unique (fun v _=>hfixed v)
    rw [Representation.BinaryParabolicNatural.natural_invariants hdim] at ht
    have hv : Module.finrank (ZMod 2) V=0 := by
      have hh := congrArg (fun S : Submodule (ZMod 2) V=>Module.finrank (ZMod 2) S) ht
      simpa using hh.symm
    omega
  obtain ⟨w,hwQ,hw0⟩ := hnonzero
  intro y hy
  let yW : W := ⟨y,hy⟩
  by_cases hy0 : (π yW).toAdd=0
  · exact (center_le_centralizer (Q : Set G)) (hk yW hy0)
  · obtain ⟨a,ha⟩ := BinaryLinear.OuterCyclic.exists_linearEquiv_apply_eq hw0 hy0
    obtain ⟨b,hb,hba⟩ := (show a∈B.map ρ from hρ.symm ▸ mem_top a)
    let v : W := (MulAut.conjNormal b : MulAut W) w
    have hvQ : (v:G)∈centralizer (Q : Set G) :=
      (inferInstance : (centralizer (Q : Set G)).Normal).conj_mem w hwQ b
    have hvπ : π v=π yW := by
      change (π v).toAdd=(π yW).toAdd
      rw [show v=(MulAut.conjNormal b : MulAut W) w from rfl,heq,hba,ha]
    have hdiff : π (yW/v)=1 := by rw [map_div,hvπ]; exact div_self' _
    have hdQ : (yW/v:G)∈centralizer (Q : Set G) :=
      (center_le_centralizer (Q : Set G)) (hk (yW/v) hdiff)
    have hh := (centralizer (Q : Set G)).mul_mem hdQ hvQ
    simpa only [coe_div,coe_mul,div_mul_cancel] using hh

end Theory.GroupAction
