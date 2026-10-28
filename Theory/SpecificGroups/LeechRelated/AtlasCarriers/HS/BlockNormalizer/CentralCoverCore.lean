module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.CentralCoverSeed
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.CoreGeometry.Action

/-!
# The actual HS normalizer through central two-covers

Sylow conjugacy constructs the normalizer seed together with an isomorphism
to the concrete elementary-eight normalizer. Pulling it back through the
central quotient retains a surjection with central two-group kernel, as well
as Sylow invariance, generation and characteristic two. In particular the
construction remembers the whole normalizer, beyond its SL₃(2) quotient.

The checked order-seven actor moves the full C₄³ core. Surjective two-core
transport therefore identifies the image of the moving core in every
two-kernel cover with that same C₄³, ruling out an elementary moving core.
The Chapter 15 application uses the actual escaping perfect residual and
keeps its literal covering map. No MS classification is assumed here.

Source: Aschbacher--Smith 15.1.22, printed p.1100 of refs/quasithin.pdf;
GLS3 Table 5.3m and the checked HS normalizer geometry.
-/

public section
open Subgroup
namespace Sporadic.LeechRelated.HS.BlockNormalizer
open EvenLocalCandidates
private theorem map_congr_transport (K : Subgroup Carrier) (e β : MulAut Carrier) :
    (K.map (MulAut.congr e.symm β).toMonoidHom).map e.toMonoidHom =
      (K.map e.toMonoidHom).map β.toMonoidHom := by
  rw [map_map, map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  change e (e.symm (β (e x))) = β (e x)
  exact e.apply_symm_apply _

private theorem fixedSubgroup_map_congr (e : MulAut Carrier) (α : MulAut Carrier) :
    (MulAut.congr e.symm α).fixedSubgroup.map e.toMonoidHom = α.fixedSubgroup := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    apply (MulAut.mem_fixedSubgroup α (e y)).mpr
    have hy' := (MulAut.mem_fixedSubgroup (MulAut.congr e.symm α) y).mp hy
    change e.symm (α (e y)) = y at hy'
    exact e.symm_apply_eq.mp hy'
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply (MulAut.mem_fixedSubgroup (MulAut.congr e.symm α) (e.symm x)).mpr
    have hx' := (MulAut.mem_fixedSubgroup α x).mp hx
    change e.symm (α (e (e.symm x))) = e.symm x
    rw [e.apply_symm_apply, hx']

/-- Sylow conjugacy assembles the intrinsic geometry once the actual marked
quotient and centralizer generation calculations have been supplied. -/
theorem exists_seed_with_model (R : Sylow 2 Carrier) (α : MulAut Carrier)
    (hα : orderOf α = 2) (hi : α ∈ (MulAut.conj (G := Carrier)).range)
    (hfix : ∀ r ∈ (R : Subgroup Carrier), α r = r) :
    ∃ r : LocalSeed R α, Nonempty (r.localSubgroup ≃* baseNormalizer) := by
  obtain ⟨q⟩ := baseNormalizer_quotient_of_surjective baseNormalizer_action_surjective
  have hgen := centralizer_sup_baseNormalizer_eq_top
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Carrier baseSylow R
  let e := MulAut.conj g
  have hR : subgroup.map e.toMonoidHom = R := congrArg Sylow.toSubgroup hg
  let δ := MulAut.congr e.symm α
  have hδorder : orderOf δ = 2 := ((MulAut.congr e.symm).orderOf_eq α).trans hα
  have hδinner : δ ∈ (MulAut.conj (G := Carrier)).range := by
    obtain ⟨a, rfl⟩ := hi
    exact ⟨e.symm a, (MulAut.congr_conj e.symm a).symm⟩
  have hδfix : ∀ r ∈ (baseSylow : Subgroup Carrier), δ r = r := by
    intro r hr
    have her : e r ∈ (R : Subgroup Carrier) := hR ▸ mem_map_of_mem e.toMonoidHom hr
    change e.symm (α (e r)) = r
    rw [hfix _ her, e.symm_apply_apply]
  have hδ : δ = MulAut.conj e0 := base_inner_eq_conj_e0 δ hδorder hδinner hδfix
  refine ⟨{
    localSubgroup := baseNormalizer.map e.toMonoidHom
    sylow_le := ?_
    invariant := ?_
    selfCentralizing := ?_
    quotientIso := ?_
    generated := ?_
  }, ⟨(e.subgroupMap baseNormalizer).symm⟩⟩
  · rw [← hR]
    exact map_mono baseSylow_le_normalizer
  · intro β hβ
    have hb : subgroup.map (MulAut.congr e.symm β).toMonoidHom = subgroup := by
      apply map_injective (f := e.toMonoidHom) e.injective
      rw [map_congr_transport, hR, hβ]
    rw [← map_congr_transport, baseNormalizer_invariant _ hb]
  · exact (Theory.Quasithin.centralizer_pCore_map_le_iff 2 e baseNormalizer).mpr
      baseNormalizer_selfCentralizing
  · let f := e.subgroupMap baseNormalizer
    exact (QuotientGroup.congr (pCore 2 baseNormalizer)
      (pCore 2 (baseNormalizer.map e.toMonoidHom)) f (pCore_map_iso 2 f)).symm.trans q
  · have hh : δ.fixedSubgroup ⊔ baseNormalizer = ⊤ := by
      rw [hδ, MulAut.fixedSubgroup_conj]
      exact hgen
    have hm := congrArg (Subgroup.map e.toMonoidHom) hh
    rw [Subgroup.map_sup, fixedSubgroup_map_congr, map_top_of_surjective _ e.surjective] at hm
    exact hm


variable {X : Type*} [Group X] [Finite X]

/-- A Sylow-fixing involution on a perfect central two-cover of HS has an
invariant linear-three seed with its full two-kernel retained. -/
theorem exists_sylow_seed_covering_normalizer [Group.IsPerfect X] (e : (X ⧸ center X) ≃* Carrier)
    (hZ : IsPGroup 2 (center X)) (P : Sylow 2 X)
    (a : MulAut X) (ha : a ^ 2 = 1) (hne : a ≠ 1)
    (hfix : ∀ x ∈ P, a x = x) :
    ∃ B : Subgroup X, (P : Subgroup X) ≤ B ∧
      (∀ b : MulAut X, (P : Subgroup X).map b.toMonoidHom = P → B.map b.toMonoidHom = B) ∧
      a.fixedSubgroup ⊔ B = ⊤ ∧
      centralizer (pCore 2 B : Set B) ≤ pCore 2 B ∧
      ∃ f : B →* baseNormalizer, Function.Surjective f ∧ IsPGroup 2 f.ker ∧ f.ker ≤ center B := by
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
  obtain ⟨r,⟨er⟩⟩ := exists_seed_with_model Q ac hac ⟨t,ht.symm⟩ hfixc
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
  · refine ⟨er.toMonoidHom.comp qr,er.surjective.comp hqr,?_,?_⟩
    · rwa [MonoidHom.ker_comp_of_injective _ _ er.injective]
    · rw [MonoidHom.ker_comp_of_injective _ _ er.injective]
      intro x hx
      have hxq : q (x : X) = 1 := congrArg Subtype.val hx
      have hxZ : (x : X) ∈ center X := hk ▸ hxq
      exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp hxZ y))


/-- The order-seven actor moves the entire literal normalizer core. -/
theorem normalizer_core_fully_moved :
    ⁅pCore 2 baseNormalizer, (⊤ : Subgroup baseNormalizer)⁆ = pCore 2 baseNormalizer := by
  apply le_antisymm (commutator_le_left _ _)
  obtain ⟨y,_,hfree⟩ := CoreGeometry.exists_seven_fixedPointFree
  intro q hq
  obtain ⟨a,ha⟩ := hfree.commutatorMap_surjective (⟨q,hq⟩ : pCore 2 baseNormalizer)
  have he : (a : baseNormalizer) / (y * (a : baseNormalizer) * y⁻¹) = q :=
    congrArg Subtype.val ha
  rw [←he]
  have hc := commutator_mem_commutator a.property (mem_top y)
  simpa only [commutatorElement_def,div_eq_mul_inv,mul_inv_rev,inv_inv,mul_assoc] using hc

/-- Every two-kernel cover retains the whole C₄³ core in its moving core image. -/
theorem moving_core_image (f : X →* baseNormalizer) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) :
    (⁅pCore 2 X, (⊤ : Subgroup X)⁆).map f = pCore 2 baseNormalizer := by
  have hm : (pCore 2 X).map f = pCore 2 baseNormalizer := by
    rw [←f.comap_pCore_of_ker_isPGroup hf hk,map_comap_eq_self]
    rw [f.range_eq_top_of_surjective hf]
    exact le_top
  rw [map_commutator,hm,map_top_of_surjective _ hf,normalizer_core_fully_moved]

/-- The original HS moving core cannot be elementary, including through a central cover. -/
theorem moving_core_not_elementary (f : X →* baseNormalizer) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) : ¬ IsElementaryAbelian 2 (⁅pCore 2 X, (⊤ : Subgroup X)⁆ : Subgroup X) := by
  intro hel
  let := hel
  let v : Multiplicative (Fin 3 → ZMod 4) := Multiplicative.ofAdd (fun _ => 1)
  let q := CoreGeometry.coreEquiv.symm v
  have hm := moving_core_image f hf hk
  obtain ⟨x,hx,hxq⟩ := (show (q : baseNormalizer) ∈
      (⁅pCore 2 X, (⊤ : Subgroup X)⁆).map f from hm.symm ▸ q.property)
  have hx2 : x ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian x hx
  have hq2 : q ^ 2 = 1 := Subtype.ext (by
    change (q : baseNormalizer) ^ 2 = 1
    rw [←hxq,←map_pow,hx2,map_one])
  have hv2 : v ^ 2 = 1 := CoreGeometry.coreEquiv.symm.injective (by
    simpa only [map_pow,map_one] using hq2)
  have hc := congrArg (fun z : Multiplicative (Fin 3 → ZMod 4) => z.toAdd 0) hv2
  norm_num [v,pow_two] at hc
  exact (by decide : (2 : ZMod 4) ≠ 0) hc

end Sporadic.LeechRelated.HS.BlockNormalizer
