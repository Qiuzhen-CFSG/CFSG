module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrdinaryLocal
public import Theory.GroupAction.SylowFixedCentralQuotient
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PCorePreimageCentralizer

/-!
# The linear-three seed in a central two-cover of Higman--Sims

Pull back the actual elementary-eight normalizer through the given central
quotient. Its Sylow invariance and characteristic-two property lift through
that full two-kernel. Fixed points of the original Sylow-fixing involution
lift by the central displacement theorem, so the seed and those fixed points
generate the cover. The seed maps onto the actual SL₃(2) with two-group kernel.

This adapts the central-cover argument of the J₄ Mathieu seed to the checked
HS geometry. It supplies the model input for original 15.1.22 on printed
p.1100 of refs/quasithin.pdf; it does not assert characteristicity in any
larger Sylow group. The imported concrete geometry retains the ATLAS carrier,
word convention and source attribution.
-/

public section
open Subgroup
namespace Sporadic.LeechRelated.HS.BlockNormalizer
variable {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]

/-- A Sylow-fixing involution on a perfect central two-cover of HS has an
invariant linear-three seed with its full two-kernel retained. -/
theorem exists_sylow_seed_of_central_two_cover (e : (X ⧸ center X) ≃* Carrier)
    (hZ : IsPGroup 2 (center X)) (P : Sylow 2 X)
    (a : MulAut X) (ha : a ^ 2 = 1) (hne : a ≠ 1)
    (hfix : ∀ x ∈ P, a x = x) :
    ∃ B : Subgroup X, (P : Subgroup X) ≤ B ∧
      (∀ b : MulAut X, (P : Subgroup X).map b.toMonoidHom = P → B.map b.toMonoidHom = B) ∧
      a.fixedSubgroup ⊔ B = ⊤ ∧
      centralizer (pCore 2 B : Set B) ≤ pCore 2 B ∧
      ∃ f : B →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), Function.Surjective f ∧ IsPGroup 2 f.ker := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center X))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = center X := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let Q := P.mapSurjective hq
  let ac := MulAut.centralQuotientAction e a
  have heq (x : X) : q (a x) = ac (q x) := (MulAut.centralQuotientAction_apply e a x).symm
  have hfixc : ∀ x ∈ Q, ac x = x := by
    rintro _ ⟨x,hx,rfl⟩
    rw [←heq,hfix x hx]
  obtain ⟨t,ht⟩ := OrdinaryLocal.automorphism_inner_of_fixes_sylow Q ac hfixc
  have hac : orderOf ac = 2 := by
    have ha2 : ac ^ 2 = 1 := by
      rw [← map_pow,ha,map_one]
    have hane : ac ≠ 1 := by
      intro hh
      apply hne
      apply MulAut.centralQuotientAction_injective e
      simpa only [map_one] using hh
    exact orderOf_eq_prime_iff.mpr ⟨ha2,hane⟩
  obtain ⟨r⟩ := geometry.seed Q ac hac ⟨t,ht.symm⟩ hfixc
  let R := r.localSubgroup
  let B := R.comap q
  have hPB : (P : Subgroup X) ≤ B := fun x hx => r.sylow_le (mem_map_of_mem q hx)
  have him : a.fixedSubgroup.map q = ac.fixedSubgroup := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      rw [MulAut.mem_fixedSubgroup,←heq,(MulAut.mem_fixedSubgroup _ _).mp hx]
    · intro y hy
      obtain ⟨x,hx⟩ := MulAut.fixedSubgroupMap_surjective_of_sylow_fixed
        a ac q hq hk.le heq ha P hfix ⟨y,hy⟩
      exact ⟨x,x.property,congrArg Subtype.val hx⟩
  have hinner : ∃ x : X, a = MulAut.conj x :=
    (MulAut.centralQuotientAction_inner_iff e a).mp ⟨t,ht⟩
  have hker : q.ker ≤ a.fixedSubgroup := by
    obtain ⟨x,rfl⟩ := hinner
    intro y hy
    rw [MulAut.mem_fixedSubgroup]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_center_iff.mp (hk ▸ hy) x)
  have hfull : a.fixedSubgroup ⊔ B = ⊤ := by
    have hg : ac.fixedSubgroup ⊔ R = ⊤ := r.generated
    have hm := congrArg (Subgroup.comap q) hg
    rw [←comap_sup_eq _ _ _ hq,←him,comap_map_eq_self hker,comap_top] at hm
    exact hm
  let qr : B →* R := q.subgroupComap R
  have hqr : Function.Surjective qr := by
    intro y
    obtain ⟨x,hx⟩ := hq y
    have hxB : x ∈ B := by
      change q x ∈ R
      rw [hx]
      exact y.property
    exact ⟨⟨x,hxB⟩,Subtype.ext hx⟩
  have hqrker : IsPGroup 2 qr.ker := by
    have he : qr.ker = q.ker.subgroupOf B := by
      ext x
      change qr x = 1 ↔ q x = 1
      exact Subtype.ext_iff
    rw [he,hk]
    exact hZ.comap_subtype
  have hself : centralizer (pCore 2 B : Set B) ≤ pCore 2 B :=
    qr.centralizer_pCore_le_of_surjective_pKernel hqr hqrker r.selfCentralizing
  refine ⟨B,hPB,?_,hfull,hself,?_⟩
  · intro b hb
    let bc := MulAut.centralQuotientAction e b
    have heqb (x : X) : q (b x) = bc (q x) := (MulAut.centralQuotientAction_apply e b x).symm
    have hQ : (Q : Subgroup Carrier).map bc.toMonoidHom = Q := by
      change ((P : Subgroup X).map q).map bc.toMonoidHom = (P : Subgroup X).map q
      rw [map_map]
      have he : bc.toMonoidHom.comp q = q.comp b.toMonoidHom := by
        apply MonoidHom.ext
        intro x
        exact (heqb x).symm
      rw [he,←map_map,hb]
    have hR : R.map bc.toMonoidHom = R := r.invariant bc hQ
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      change q (b x) ∈ R
      rw [heqb,←hR]
      exact mem_map_of_mem _ hx
    · exact (Nat.card_congr (b.subgroupMap B).toEquiv).le
  · let g := r.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))
    have hg : Function.Surjective g := r.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
    have hgker : g.ker = pCore 2 R := by
      rw [MonoidHom.ker_comp_of_injective _ _ r.quotientIso.injective,QuotientGroup.ker_mk']
    refine ⟨g.comp qr,hg.comp hqr,?_⟩
    rw [←MonoidHom.comap_ker,hgker]
    exact pCore_isPGroup.comap_of_ker_isPGroup qr hqrker
end Sporadic.LeechRelated.HS.BlockNormalizer
