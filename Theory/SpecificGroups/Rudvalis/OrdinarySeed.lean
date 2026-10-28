module
public import Theory.SpecificGroups.Rudvalis.ComponentFacts
public import Theory.SpecificGroups.Rudvalis.OrdinaryLocal
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Basic
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.Max4Perfect
public import Theory.GroupAction.FourGroupSylowCentralizer
public import Theory.GroupAction.SylowFixedCentralQuotient
public import Theory.GroupTheory.PCorePreimageCentralizer
public import Theory.GroupTheory.PCoreSurjective
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models

/-!
# The original linear-three seed in Rudvalis and its central two-covers

The marked max4 subgroup is the invariant normalizer of the characteristic
Sylow eight-group. Its literal action has two-core kernel and quotient
SL₃(2), and that core is self-centralizing. The nontrivial inner involution
fixing the Sylow group is the marked central involution. A certified max4
generator moves it, so maximality of its centralizer proves generation.
Sylow conjugacy transports the whole construction to the given marking.

Pulling this seed back through the central quotient retains its full two-kernel.
Fixed points lift by central displacement, and the inner action fixes the
covering center, so generation and characteristic two lift as well. Model
simplicity is inherited from the source component; the earlier odd-index
maximal two-core premise is discharged by the original source adapter.

This is the local-seed step of Aschbacher--Smith 15.1.22, printed p.1100 of
refs/quasithin.pdf, using GLS3 Table 5.3r, pp.291--292. The full-S
characteristic-subgroup exclusion is separate. The imported ATLAS carrier,
word conventions, certificate attribution and license are preserved.
-/

public section
open Subgroup Theory.GroupTheory Theory.GroupAction
open Theory.GroupTheory.DoubleCoverCentralizer
namespace Rudvalis.OrdinarySeed
open SylowOvergroups SylowOvergroups.RadicalCoverage.LocalCover
open RankOneEightCharacteristic

private theorem first_selfCentralizing :
    centralizer (pCore 2 max4 : Set max4) ≤ pCore 2 max4 := by
  intro x hx
  rw [←CoreQuotients.max4_centralizer_eq_pCore]
  intro y hy
  obtain ⟨z,hz,he⟩ := CoveringIncidence.marked_eight_le_core hy
  change (z : Model) = y at he
  rw [←he]
  exact congrArg Subtype.val (hx z hz)

private theorem one_ne_one : elementaryGenerator 1 ≠ 1 := by
  intro he
  have hh := congrArg (fun x : Model => x.val (0 : Fin 4060)) he
  have hv : (elementaryGenerator 1).val (0 : Fin 4060) = 1738 := by
    change (modelSubgroup.subtype (elementaryGenerator 1)) (0 : Fin 4060) = 1738
    rw [←CatalogueCertificate.elementaryPermutation_eq]
    decide +kernel
  rw [hv] at hh
  exact (by decide : (1738 : Fin 4060) ≠ 0) hh

private theorem first_escapes : ¬ max4 ≤ centralizer ({elementaryGenerator 0} : Set Model) := by
  intro hh
  have hc := mem_centralizer_singleton_iff.mp (hh (subset_closure (by simp) : max4Generators.2 ∈ max4))
  have he : max4Generators.2 * elementaryGenerator 0 * max4Generators.2⁻¹ = elementaryGenerator 0 :=
    mul_inv_eq_iff_eq_mul.mpr hc
  rw [RankOneEightAction.second_conj_zero] at he
  exact one_ne_one (mul_left_cancel (he.trans (mul_one _).symm))

private theorem fixed_marked [IsSimpleGroup Model]
    (a : MulAut Model) (ha : a^2=1) (hne : a≠1)
    (hfix : ∀ x ∈ SylowInvariantPair.sylow, a x=x) :
    a = MulAut.conj (elementaryGenerator 0) := by
  let P := SylowInvariantPair.sylow
  let : IsCyclic (center P) := isCyclic_of_prime_card (InvolutionCentralizers.sylow_center_card P)
  have hz : elementaryGenerator 0 ∈ (center (P : Subgroup Model)).map (P : Subgroup Model).subtype := by
    change elementaryGenerator 0 ∈ (center localP).map localP.subtype
    rw [←SylowInvariantPair.elementary_zero_eq_center]
    exact subset_closure (by simp)
  have hc : elementaryGenerator 0 ∈ centralizer (P : Set Model) := by
    obtain ⟨z,hz,he⟩ := hz
    rw [←he]
    exact fun y hy => congrArg Subtype.val (mem_center_iff.mp hz ⟨y,hy⟩)
  apply inner_involutions_fixing_sylow_eq P LowCentralizers.model_center_eq_bot ha
  · rw [←map_pow,←Max6Certificate.elementary_zero_order,pow_orderOf_eq_one,map_one]
  · exact hne
  · intro hh
    have hz : elementaryGenerator 0 ∈ center Model := by
      rw [mem_center_iff]
      intro y
      have hy := congrArg (fun a : MulAut Model => a y) hh
      change elementaryGenerator 0 * y * (elementaryGenerator 0)⁻¹ = y at hy
      exact (mul_inv_eq_iff_eq_mul.mp hy).symm
    have hz1 : elementaryGenerator 0 = 1 := mem_bot.mp (LowCentralizers.model_center_eq_bot ▸ hz)
    have ho := Max6Certificate.elementary_zero_order
    rw [hz1,orderOf_one] at ho
    omega
  · exact fun x => hfix x x.property
  · intro x
    change elementaryGenerator 0 * (x : Model) * (elementaryGenerator 0)⁻¹ = x
    exact mul_inv_eq_iff_eq_mul.mpr (hc x x.property).symm
  · obtain ⟨g,hg⟩ := component_conj_surjective a
    exact ⟨g,hg.symm⟩
  · exact ⟨_,rfl⟩

/-- The concrete max4 seed transported to any original Sylow subgroup and
 its nontrivial pointwise-fixing involution. -/
theorem exists_sylow_seed_with_alignment [IsSimpleGroup Model]
    (hcore : OddIndexMaximalTwoCore) (P : Sylow 2 Model)
    (a : MulAut Model) (ha : a^2=1) (hne : a≠1)
    (hfix : ∀ x ∈ P, a x=x) :
    ∃ B : Subgroup Model, (P : Subgroup Model) ≤ B ∧
      (∀ b : MulAut Model, (P : Subgroup Model).map b.toMonoidHom = P → B.map b.toMonoidHom = B) ∧
      a.fixedSubgroup ⊔ B = ⊤ ∧
      centralizer (pCore 2 B : Set B) ≤ pCore 2 B ∧
      Nonempty (B ≃* max4) ∧
      ∃ γ : MulAut Model, localP.map γ.toMonoidHom = P ∧
        max4.map γ.toMonoidHom = B := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Model SylowInvariantPair.sylow P
  let e := MulAut.conj g
  have hP : localP.map e.toMonoidHom = P := congrArg Sylow.toSubgroup hg
  let δ := MulAut.congr e.symm a
  have hδ : δ = MulAut.conj (elementaryGenerator 0) := fixed_marked δ
    (by rw [←map_pow,ha,map_one])
    (fun hh => hne ((MulAut.congr e.symm).injective (hh.trans (map_one _).symm)))
    (by
      intro x hx
      change e.symm (a (e x)) = x
      have hxP : e x ∈ (P : Subgroup Model) := hP ▸ mem_map_of_mem e.toMonoidHom hx
      rw [hfix (e x) hxP,e.symm_apply_apply])
  have hfixed : δ.fixedSubgroup = centralizer ({elementaryGenerator 0} : Set Model) := by
    rw [hδ]
    ext x
    rw [MulAut.mem_fixedSubgroup,mem_centralizer_singleton_iff]
    change _ * x * _ = x ↔ x * _ = _ * x
    exact mul_inv_eq_iff_eq_mul.trans eq_comm
  have hmax := OrdinaryLocal.twoCentral_centralizer_isCoatom hcore
    (elementaryGenerator 0) Max6Certificate.elementary_zero_order
    ⟨SylowInvariantPair.sylow,by
      have hh : elementaryGenerator 0 ∈ (center localP).map localP.subtype := by
        rw [←SylowInvariantPair.elementary_zero_eq_center]
        exact subset_closure (by simp)
      obtain ⟨z,hz,he⟩ := hh
      rw [←he]
      exact ⟨z.property,hz⟩⟩
  have hgen : δ.fixedSubgroup ⊔ max4 = ⊤ := by
    rw [hfixed]
    exact hmax.2 _ (lt_of_le_of_ne le_sup_left (fun he => first_escapes (he.symm ▸ le_sup_right)))
  let B := max4.map e.toMonoidHom
  let eb : max4 ≃* B := e.subgroupMap max4
  refine ⟨B,(by rw [←hP]; exact map_mono localP_le_max4),?_,?_,?_,?_⟩
  · intro β hβ
    let γ := MulAut.congr e.symm β
    have he : e.toMonoidHom.comp γ.toMonoidHom = β.toMonoidHom.comp e.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      exact e.apply_symm_apply (β (e x))
    have hγ : localP.map γ.toMonoidHom = localP := by
      apply (map_injective (f := e.toMonoidHom) e.injective)
      rw [map_map,he,←map_map,hP,hβ]
    have hb : max4.map γ.toMonoidHom = max4 := SylowInvariantPair.locals_invariant 0 γ hγ
    change (max4.map e.toMonoidHom).map β.toMonoidHom = _
    rw [map_map,←he,←map_map,hb]
  · have him : δ.fixedSubgroup.map e.toMonoidHom = a.fixedSubgroup := by
      ext x
      rw [mem_map_equiv,MulAut.mem_fixedSubgroup,MulAut.mem_fixedSubgroup]
      change e.symm (a (e (e.symm x))) = e.symm x ↔ a x = x
      rw [e.apply_symm_apply,e.symm.injective.eq_iff]
    have hh := congrArg (map e.toMonoidHom) hgen
    rwa [Subgroup.map_sup,him,map_top_of_surjective _ e.surjective] at hh
  · exact eb.symm.toMonoidHom.centralizer_pCore_le_of_surjective_pKernel eb.symm.surjective
      (by rw [eb.symm.toMonoidHom.ker_eq_bot eb.symm.injective]; exact IsPGroup.of_subsingleton 2 _)
      first_selfCentralizing
  · exact ⟨⟨eb.symm⟩,e,hP,rfl⟩

/-- The concrete seed with its actual max4 carrier. -/
theorem exists_sylow_seed_with_model [IsSimpleGroup Model]
    (hcore : OddIndexMaximalTwoCore) (P : Sylow 2 Model)
    (a : MulAut Model) (ha : a^2=1) (hne : a≠1)
    (hfix : ∀ x ∈ P, a x=x) :
    ∃ B : Subgroup Model, (P : Subgroup Model) ≤ B ∧
      (∀ b : MulAut Model, (P : Subgroup Model).map b.toMonoidHom = P → B.map b.toMonoidHom = B) ∧
      a.fixedSubgroup ⊔ B = ⊤ ∧
      centralizer (pCore 2 B : Set B) ≤ pCore 2 B ∧
      Nonempty (B ≃* max4) := by
  obtain ⟨B,hP,hi,hg,hc,he,_⟩ := exists_sylow_seed_with_alignment hcore P a ha hne hfix
  exact ⟨B,hP,hi,hg,hc,he⟩

/-- The concrete max4 seed transported to any original Sylow subgroup and
 its nontrivial pointwise-fixing involution. -/
theorem exists_sylow_seed [IsSimpleGroup Model]
    (hcore : OddIndexMaximalTwoCore) (P : Sylow 2 Model)
    (a : MulAut Model) (ha : a^2=1) (hne : a≠1)
    (hfix : ∀ x ∈ P, a x=x) :
    ∃ B : Subgroup Model, (P : Subgroup Model) ≤ B ∧
      (∀ b : MulAut Model, (P : Subgroup Model).map b.toMonoidHom = P → B.map b.toMonoidHom = B) ∧
      a.fixedSubgroup ⊔ B = ⊤ ∧
      centralizer (pCore 2 B : Set B) ≤ pCore 2 B ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  obtain ⟨B,hPB,hi,hg,hself,⟨eb⟩⟩ := exists_sylow_seed_with_model hcore P a ha hne hfix
  exact ⟨B,hPB,hi,hg,hself,⟨((QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)).trans
    CoreQuotients.max4QuotientEquiv).trans Atlas.Comparisons.Exceptional.sl3TwoEquivPsl3Two.symm⟩⟩

variable {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]

/-- A Sylow-fixing involution on a perfect central two-cover of Rudvalis has an
invariant linear-three seed with its full two-kernel retained. -/
theorem exists_sylow_seed_covering_alignment [IsSimpleGroup Model]
    (hcore : OddIndexMaximalTwoCore) (e : (X ⧸ center X) ≃* Model)
    (hZ : IsPGroup 2 (center X)) (P : Sylow 2 X)
    (a : MulAut X) (ha : a ^ 2 = 1) (hne : a ≠ 1)
    (hfix : ∀ x ∈ P, a x = x) :
    ∃ B : Subgroup X, (P : Subgroup X) ≤ B ∧
      (∀ b : MulAut X, (P : Subgroup X).map b.toMonoidHom = P → B.map b.toMonoidHom = B) ∧
      a.fixedSubgroup ⊔ B = ⊤ ∧
      centralizer (pCore 2 B : Set B) ≤ pCore 2 B ∧
      (∃ f : B →* max4, Function.Surjective f ∧ IsPGroup 2 f.ker ∧ f.ker ≤ center B) ∧
      ∃ γ : MulAut Model,
        (P : Subgroup X).map (e.toMonoidHom.comp (QuotientGroup.mk' (center X))) =
          localP.map γ.toMonoidHom ∧
        B.map (e.toMonoidHom.comp (QuotientGroup.mk' (center X))) =
          max4.map γ.toMonoidHom := by
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
  obtain ⟨t,ht⟩ := component_conj_surjective ac
  have hac : orderOf ac = 2 := by
    have ha2 : ac ^ 2 = 1 := by
      rw [← map_pow,ha,map_one]
    have hane : ac ≠ 1 := by
      intro hh
      apply hne
      apply MulAut.centralQuotientAction_injective e
      simpa only [map_one] using hh
    exact orderOf_eq_prime_iff.mpr ⟨ha2,hane⟩
  obtain ⟨R,hQR,hi,hg,hself,⟨er⟩,⟨γ,hγP,hγB⟩⟩ := exists_sylow_seed_with_alignment hcore Q ac
    (by rw [←hac,pow_orderOf_eq_one])
    (fun hh => by rw [hh,orderOf_one] at hac; omega) hfixc
  let B := R.comap q
  have hPB : (P : Subgroup X) ≤ B := fun x hx => hQR (mem_map_of_mem q hx)
  have him : a.fixedSubgroup.map q = ac.fixedSubgroup := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      rw [MulAut.mem_fixedSubgroup,←heq,(MulAut.mem_fixedSubgroup _ _).mp hx]
    · intro y hy
      obtain ⟨x,hx⟩ := MulAut.fixedSubgroupMap_surjective_of_sylow_fixed
        a ac q hq hk.le heq ha P hfix ⟨y,hy⟩
      exact ⟨x,x.property,congrArg Subtype.val hx⟩
  have hinner : ∃ x : X, a = MulAut.conj x :=
    (MulAut.centralQuotientAction_inner_iff e a).mp ⟨t,ht.symm⟩
  have hker : q.ker ≤ a.fixedSubgroup := by
    obtain ⟨x,rfl⟩ := hinner
    intro y hy
    rw [MulAut.mem_fixedSubgroup]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_center_iff.mp (hk ▸ hy) x)
  have hfull : a.fixedSubgroup ⊔ B = ⊤ := by
    have hg : ac.fixedSubgroup ⊔ R = ⊤ := hg
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
    qr.centralizer_pCore_le_of_surjective_pKernel hqr hqrker hself
  refine ⟨B,hPB,?_,hfull,hself,?_,γ,hγP.symm,?_⟩
  · intro b hb
    let bc := MulAut.centralQuotientAction e b
    have heqb (x : X) : q (b x) = bc (q x) := (MulAut.centralQuotientAction_apply e b x).symm
    have hQ : (Q : Subgroup Model).map bc.toMonoidHom = Q := by
      change ((P : Subgroup X).map q).map bc.toMonoidHom = (P : Subgroup X).map q
      rw [map_map]
      have he : bc.toMonoidHom.comp q = q.comp b.toMonoidHom := by
        apply MonoidHom.ext
        intro x
        exact (heqb x).symm
      rw [he,←map_map,hb]
    have hR : R.map bc.toMonoidHom = R := hi bc hQ
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      change q (b x) ∈ R
      rw [heqb,←hR]
      exact mem_map_of_mem _ hx
    · exact (Nat.card_congr (b.subgroupMap B).toEquiv).le
  · refine ⟨er.toMonoidHom.comp qr,er.surjective.comp hqr,?_,?_⟩
    · rwa [MonoidHom.ker_comp_of_injective _ _ er.injective]
    · intro x hx
      have hxR : qr x = 1 := er.injective (hx.trans er.map_one.symm)
      have hxq : q (x : X) = 1 := congrArg Subtype.val hxR
      have hxZ : (x : X) ∈ center X := hk ▸ hxq
      exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp hxZ y)

  · change (R.comap q).map q = _
    rw [map_comap_eq_self_of_surjective hq]
    exact hγB.symm

/-- The concrete covering seed, with a central two-group kernel retained. -/
theorem exists_sylow_seed_covering_normalizer [IsSimpleGroup Model]
    (hcore : OddIndexMaximalTwoCore) (e : (X ⧸ center X) ≃* Model)
    (hZ : IsPGroup 2 (center X)) (P : Sylow 2 X)
    (a : MulAut X) (ha : a ^ 2 = 1) (hne : a ≠ 1)
    (hfix : ∀ x ∈ P, a x = x) :
    ∃ B : Subgroup X, (P : Subgroup X) ≤ B ∧
      (∀ b : MulAut X, (P : Subgroup X).map b.toMonoidHom = P → B.map b.toMonoidHom = B) ∧
      a.fixedSubgroup ⊔ B = ⊤ ∧
      centralizer (pCore 2 B : Set B) ≤ pCore 2 B ∧
      ∃ f : B →* max4, Function.Surjective f ∧ IsPGroup 2 f.ker ∧ f.ker ≤ center B := by
  obtain ⟨B,hP,hi,hg,hc,he,_⟩ :=
    exists_sylow_seed_covering_alignment hcore e hZ P a ha hne hfix
  exact ⟨B,hP,hi,hg,hc,he⟩

/-- A Sylow-fixing involution on a perfect central two-cover of Rudvalis has an
invariant linear-three seed with its full two-kernel retained. -/
theorem exists_sylow_seed_of_central_two_cover [IsSimpleGroup Model]
    (hcore : OddIndexMaximalTwoCore) (e : (X ⧸ center X) ≃* Model)
    (hZ : IsPGroup 2 (center X)) (P : Sylow 2 X)
    (a : MulAut X) (ha : a ^ 2 = 1) (hne : a ≠ 1)
    (hfix : ∀ x ∈ P, a x = x) :
    ∃ B : Subgroup X, (P : Subgroup X) ≤ B ∧
      (∀ b : MulAut X, (P : Subgroup X).map b.toMonoidHom = P → B.map b.toMonoidHom = B) ∧
      a.fixedSubgroup ⊔ B = ⊤ ∧
      centralizer (pCore 2 B : Set B) ≤ pCore 2 B ∧
      ∃ f : B →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), Function.Surjective f ∧ IsPGroup 2 f.ker := by
  obtain ⟨B,hPB,hi,hg,hself,u,hu,hku,_⟩ :=
    exists_sylow_seed_covering_normalizer hcore e hZ P a ha hne hfix
  let eq := CoreQuotients.max4QuotientEquiv.trans
    Atlas.Comparisons.Exceptional.sl3TwoEquivPsl3Two.symm
  let f := eq.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 max4))
  have hf : Function.Surjective f := eq.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 max4 := by
    rw [MonoidHom.ker_comp_of_injective _ _ eq.injective,QuotientGroup.ker_mk']
  refine ⟨B,hPB,hi,hg,hself,f.comp u,hf.comp hu,?_⟩
  rw [←MonoidHom.comap_ker,hk]
  exact pCore_isPGroup.comap_of_ker_isPGroup u hku

end Rudvalis.OrdinarySeed
