module
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Transfer
public import Mathlib.GroupTheory.IsPerfect

/-!
# Perfect normalizer action on a Sylow complement

Suppose a perfect actor normalizes X, contains O₂(X), and X/O₂(X) is
an odd p-group. Frattini factorization expresses each actor as an element
of O₂(X) times an element normalizing the chosen Sylow p-subgroup.
The first factor acts trivially on the literal radical Frattini quotient.
Transport through the complement equivalence therefore identifies the
normalizer action image as an image of the perfect actor.

Source: Aschbacher--Smith, 13.1.12(3), printed p.875.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter1.RadicalActions
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Conjugation of an ambient subgroup commutes with taking its trace in P
and then projecting to the actual Frattini quotient. -/
theorem frattini_trace_conjugate (P N A : Subgroup G) (hn : N ≤ normalizer (P : Set G))
    (n : N) :
    ((A.subgroupOf P).map (QuotientGroup.mk' (frattini P))).map
      (frattiniConjugationAction N P hn n).toMonoidHom =
    ((A.conjBy (n : G)).subgroupOf P).map (QuotientGroup.mk' (frattini P)) := by
  let f : MulAut P := P.normalizerMonoidHom ⟨n,hn n.property⟩
  have he (a : P) : frattiniConjugationAction N P hn n
      (QuotientGroup.mk' (frattini P) a) = QuotientGroup.mk' (frattini P) (f a) := by
    simp only [frattiniConjugationAction,MonoidHom.comp_apply,quotientAut_apply_mk]
    rfl
  apply le_antisymm
  · rintro a ⟨b,⟨c,hc,rfl⟩,rfl⟩
    exact ⟨f c,⟨(c : G),hc,rfl⟩,(he c).symm⟩
  · rintro a ⟨b,⟨c,hc,hcb⟩,rfl⟩
    have hcP : c ∈ P := by
      apply (mem_normalizer_iff.mp (hn n.property) c).mpr
      rw [show (n : G) * c * (n : G)⁻¹ = (b : G) from hcb]
      exact b.property
    refine ⟨QuotientGroup.mk' (frattini P) ⟨c,hcP⟩,⟨⟨c,hcP⟩,hc,rfl⟩,?_⟩
    exact (he ⟨c,hcP⟩).trans
      (congrArg (QuotientGroup.mk' (frattini P)) (Subtype.ext hcb))

/-- Perfectness belongs to the actual action image; the Sylow normalizer
itself need not be perfect. -/
theorem normalizer_frattini_image_perfect {D X : Subgroup G} [Group.IsPerfect D]
    (hn : D ≤ normalizer (X : Set G)) (hcD : X.pCoreIn 2 ≤ D)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hq : IsPGroup p (XiQuotient X))
    (P : Sylow p X) :
    Group.IsPerfect (frattiniConjugationAction
      (D ⊓ normalizer ((P : Subgroup X).map X.subtype : Set G))
      ((P : Subgroup X).map X.subtype) inf_le_right).range := by
  let P₀ := (P : Subgroup X).map X.subtype
  let N := D ⊓ normalizer (P₀ : Set G)
  let e := sylowFrattiniEquiv ho hq P
  let ρ := frattiniConjugationAction N P₀ inf_le_right
  let σ := xiFrattiniAction D X hn
  let f : D →* MulAut (P₀ ⧸ frattini P₀) := (MulAut.congr e.symm).toMonoidHom.comp σ
  have he (n : N) : f ⟨n,n.property.1⟩ = ρ n := by
    ext a : 1
    apply e.injective
    exact (e.apply_symm_apply _).trans (sylowFrattiniEquiv_equivariant hn ho hq P n a).symm
  have hf (d : D) : f d ∈ ρ.range := by
    have hN : N ≤ normalizer (X.pCoreIn 2 : Set G) :=
      inf_le_left.trans (hn.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
    have hd : (d : G) ∈ X.pCoreIn 2 ⊔ N := normalizer_factor hn hcD hq P ▸ d.property
    rw [← SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hN] at hd
    obtain ⟨c,hc,n,hn',hcn⟩ := hd
    let cD : D := ⟨c,hcD hc⟩
    let nD : D := ⟨n,hn'.1⟩
    have hd' : d = cD * nD := Subtype.ext hcn.symm
    have hfc : f cD = 1 := by
      ext a : 1
      change e.symm (σ cD (e a)) = a
      rw [show σ cD (e a) = e a from core_fixes_frattini hn cD hc (e a)]
      exact e.symm_apply_apply a
    refine ⟨⟨n,hn'⟩,?_⟩
    rw [hd',map_mul,hfc,one_mul]
    exact (he ⟨n,hn'⟩).symm
  let f' : D →* ρ.range := f.codRestrict ρ.range hf
  have hs : Function.Surjective f' := by
    rintro ⟨a,n,hn'⟩
    refine ⟨⟨n,n.property.1⟩,Subtype.ext ?_⟩
    exact (he n).trans hn'
  exact Group.IsPerfect.ofSurjective hs

end CFSG.Quasithin.Chapter1.RadicalActions
