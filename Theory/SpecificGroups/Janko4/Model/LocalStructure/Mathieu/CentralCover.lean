module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowGeometry
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal
public import Theory.GroupAction.SylowFixedCentralQuotient
public import Theory.GroupTheory.PCoreSurjective

/-!
# The Mathieu seed in a central two-cover of J₄

The native Sylow-compatible max1 subgroup pulls back through the central
quotient. Every Sylow-preserving automorphism preserves this full preimage.
The native inner-automorphism theorem and fixed-point lifting show that it
generates the cover with the fixed subgroup of a nontrivial involution fixing
the Sylow subgroup. The full kernel is retained; no splitting is assumed.

The same preimage has a self-centralizing two-core and maps onto the actual
M₂₄ carrier with two-group kernel. These are the precise model facts used by
the ordinary J₄ exclusion in Aschbacher--Smith 15.1.20(3), printed p.1097.
The transport adapts the checked Chapter 2 J₄ seed construction; native
matrix and local subgroup facts are imported with their ATLAS attribution.
-/

public section
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
  Janko4.Cardinality.max1Subgroup Janko4.Cardinality.localKernel
open Subgroup
namespace Janko4.LocalStructure
variable {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]

/-- A Sylow-fixing involution on a perfect central two-cover has a
Sylow-invariant Mathieu seed with self-centralizing two-core. -/
theorem exists_sylow_mathieu_seed_of_central_two_cover (e : (X ⧸ center X) ≃* Janko4.Model)
    (hZ : IsPGroup 2 (center X)) (P : Sylow 2 X)
    (a : MulAut X) (ha : a ^ 2 = 1) (hne : a ≠ 1)
    (hfix : ∀ x ∈ P, a x = x) :
    ∃ B : Subgroup X, (P : Subgroup X) ≤ B ∧
      (∀ b : MulAut X, (P : Subgroup X).map b.toMonoidHom = P → B.map b.toMonoidHom = B) ∧
      a.fixedSubgroup ⊔ B = ⊤ ∧
      centralizer (pCore 2 B : Set B) ≤ pCore 2 B ∧
      ∃ f : B →* Sporadic.Mathieu.M24, Function.Surjective f ∧ IsPGroup 2 f.ker := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center X))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = center X := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let Q := P.mapSurjective hq
  let ac := MulAut.centralQuotientAction e a
  have heq (x : X) : q (a x) = ac (q x) := (MulAut.centralQuotientAction_apply e a x).symm
  obtain ⟨R,hQR,⟨fR⟩,hRi,hgen⟩ := exists_sylow_mathieu_seed Q
  let B := R.comap q
  have hPB : (P : Subgroup X) ≤ B := fun x hx => hQR (mem_map_of_mem q hx)
  obtain ⟨t,ht⟩ := AdequateLocal.exists_eq_conj ac
  have htne : t ≠ 1 := by
    intro he
    apply hne
    apply MulAut.centralQuotientAction_injective e
    change ac = (MulAut.centralQuotientAction e) 1
    rw [ht,he,map_one]
    ext x
    simp
  have htc : t ∈ centralizer (Q : Set Janko4.Model) := by
    rintro y ⟨x,hx,rfl⟩
    have hh := heq x
    rw [hfix x hx,ht] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
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
    have hg : ac.fixedSubgroup ⊔ R = ⊤ := by rw [ht,MulAut.fixedSubgroup_conj]; exact hgen t htne htc
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
  let r := fR.toMonoidHom.comp qr
  have hr : Function.Surjective r := fR.surjective.comp hqr
  have hrker : IsPGroup 2 r.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ fR.injective]
    exact hqrker
  have hcore := r.comap_pCore_of_ker_isPGroup hr hrker
  have hself : centralizer (pCore 2 B : Set B) ≤ pCore 2 B := by
    intro x hx
    rw [←hcore]
    rw [←localKernel_eq_twoCore]
    apply (centralizer_localKernel _ _).le
    intro y hy
    obtain ⟨y,rfl⟩ := hr y
    have hy' : y ∈ pCore 2 B := by
      rw [←hcore,←localKernel_eq_twoCore]
      exact hy
    simpa only [map_mul] using congrArg r (hx y hy')
  refine ⟨B,hPB,?_,hfull,hself,?_⟩
  · intro b hb
    let bc := MulAut.centralQuotientAction e b
    have heqb (x : X) : q (b x) = bc (q x) := (MulAut.centralQuotientAction_apply e b x).symm
    have hQ : (Q : Subgroup Janko4.Model).map bc.toMonoidHom = Q := by
      change ((P : Subgroup X).map q).map bc.toMonoidHom = (P : Subgroup X).map q
      rw [map_map]
      have he : bc.toMonoidHom.comp q = q.comp b.toMonoidHom := by ext x; exact (heqb x).symm
      rw [he,←map_map,hb]
    have hR := hRi bc hQ
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      change q (b x) ∈ R
      rw [heqb,←hR]
      exact mem_map_of_mem _ hx
    · exact (Nat.card_congr (b.subgroupMap B).toEquiv).le
  · let g := (localQuotientEquivM24 matrixA_mul_self matrixB_pow_four).toMonoidHom.comp
      (QuotientGroup.mk' (Cardinality.localKernel matrixA_mul_self matrixB_pow_four))
    have hg : Function.Surjective g :=
      (localQuotientEquivM24 _ _).surjective.comp (QuotientGroup.mk'_surjective _)
    have hgker : g.ker = pCore 2 (Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four) := by
      rw [MonoidHom.ker_comp_of_injective _ _ (localQuotientEquivM24 _ _).injective,
        QuotientGroup.ker_mk',localKernel_eq_twoCore]
    refine ⟨g.comp r,hg.comp hr,?_⟩
    rw [←MonoidHom.comap_ker,hgker]
    exact pCore_isPGroup.comap_of_ker_isPGroup r hrker
end Janko4.LocalStructure
