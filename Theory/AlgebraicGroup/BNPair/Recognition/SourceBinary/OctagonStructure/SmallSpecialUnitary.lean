module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.SmallUnitaryDegree
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SmallSpecialUnitary
public import Theory.Representation.ExtraspecialFixedPoints
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.SmallProjectiveUnitary
import all Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.SmallProjectiveUnitary
import all Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SmallSpecialUnitary

/-!
# The small special-unitary octagon against larger linear fields

A binary SU3(2) representation of degree below six kills its normal
extraspecial subgroup of order 27. Indeed, detecting its cubic center
makes the order-27 restriction faithful, contrary to the small general
linear orders. Killing that center gives a projective action; the regular
nine-point action forces every non-two-group image to have degree at least
eight. This proves the required degree bound without perfectness.

A crossed root prevents a two-group action on each of the fixed radical's
two Frattini layers. They therefore have order at least 64 each, while
unique root coordinates give radical order 512. Separating Cartan elements
of order five or seven supply the contradiction against linear fields of
orders 16 and 64. The actual scalar cover is retained throughout.

The two import-all edges intentionally reuse the internal root separation
and scalar-Cartan calculations of the same recognition family, preserving
its established public boundaries. The original-factor and Chapter 12
consumers use both endpoint orientations and the full marked amalgam.
Source: Fong--Seitz I (4D), (5D), (6F), printed pp.21--22,26--27,46.
The quadratic-degree case remains a separate commutator argument.
-/

public noncomputable section
open Subgroup MulAction BenderSuzuki.MatrixGroups BenderSuzuki.External
open scoped LinearAlgebra.Projectivization IsMulCommutative MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure

private theorem small_projective_three_core_killed
    {F V : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F=4) (hconj : ∀ x,J.conj x=x^2)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) V)
    (hd : Module.finrank (ZMod 2) V < 8) :
    pCore 3 (ProjectiveSpecialUnitaryMatrixGroup J) ≤ ρ.ker := by
  let D := ProjectiveSpecialUnitaryMatrixGroup J
  let : Finite D := Finite.of_surjective _ J.specialToProjective_surjective
  have hf : Nat.card {x : F // J.conj x=x}=2 := by
    simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 1
      (by decide) (by simpa using hc) (by simpa using hconj)
  obtain ⟨hΩ,a,o,hi,_,_,_,ht,_⟩ := huppert_II_10_12 J 2 hc hf hJ
  let Ω := {x : Projectivization F (Fin 3 → F) // x ∈
    {x | ∃ (v : Fin 3 → F) (hv : v ≠ 0), x = Projectivization.mk F v hv ∧
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}}
  let : MulAction D Ω := MulAction.compHom _ a
  let : FaithfulSMul D Ω := ⟨fun {g h} he => hi (Equiv.ext he)⟩
  have ht' : IsMultiplyPretransitive D Ω 2 := is_two_pretransitive_iff.mpr
    (fun {x y z t} => ht x y z t)
  have htwo : IsPGroup 2 ρ.toHomUnits.range := by
    by_contra hn
    have hinj := BinaryPanel.injective_of_non_two_image ht' hΩ
      (HermitianForm.FixedFieldTwo.card_projective J hc hconj) o ρ.toHomUnits hn
    have hinj' : Function.Injective ρ := by
      intro x y hxy
      apply hinj
      exact Units.ext hxy
    exact (not_le_of_gt hd) (QuadrangleStructure.small_projective_unitary_degree J hc hconj hJ ρ hinj')
  have hthree : IsPGroup 3 ((pCore 3 D).map ρ.toHomUnits) := pCore_isPGroup.map _
  have htwo' : IsPGroup 2 ((pCore 3 D).map ρ.toHomUnits) :=
    htwo.to_le (map_le_range _ _)
  have hz : (pCore 3 D).map ρ.toHomUnits = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    exact (hthree.disjoint_of_coprime htwo' (by decide : Nat.Coprime 3 2)).le_bot ⟨hx,hx⟩
  intro x hx
  exact congrArg Units.val ((Subgroup.map_eq_bot_iff _).mp hz hx)

/-- A binary representation of SU3(2) below degree six kills its full
normal group of order 27, including the scalar center. -/
theorem small_special_three_core_killed
    {F V : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F=4) (hconj : ∀ x,J.conj x=x^2)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) J.specialSubgroup V)
    (hd : Module.finrank (ZMod 2) V < 6) : pCore 3 J.specialSubgroup ≤ ρ.ker := by
  let N := pCore 3 J.specialSubgroup
  let : IsExtraspecial 3 N := HermitianForm.SmallThreeCore.special_core_extraspecial J hc hconj
  have hscalar : J.specialToProjective.ker ≤ ρ.ker := by
    by_contra hn
    have hZ : ¬ center N ≤ (ρ.comp N.subtype).ker := by
      intro hZ
      apply hn
      intro z hz
      let zN : N := ⟨z,HermitianForm.SmallThreeCore.scalar_kernel_le_special_core J hz⟩
      change zN ∈ (ρ.comp N.subtype).ker
      apply hZ
      rw [HermitianForm.SmallThreeCore.special_core_center J hc hconj,
        HermitianForm.SmallThreeCore.specialCoreProjection_ker]
      exact hz
    have hinj := (ρ.comp N.subtype).ker_eq_bot_iff.mp
      (Representation.ker_eq_bot_of_center_not_le_ker_of_isExtraspecial (q:=3) (ρ.comp N.subtype) hZ)
    have hdiv := Representation.card_dvd_card_GL_of_injective (ρ.comp N.subtype) hinj
    rw [show Nat.card N=27 from HermitianForm.SmallThreeCore.special_core_card J hc hconj,
      Matrix.card_GL_field] at hdiv
    simp only [ZMod.card] at hdiv
    generalize Module.finrank (ZMod 2) V = n at hd hdiv
    interval_cases n <;> norm_num [Fin.prod_univ_succ] at hdiv
  let eπ := QuotientGroup.quotientKerEquivOfSurjective J.specialToProjective J.specialToProjective_surjective
  let σ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) V :=
    (QuotientGroup.lift J.specialToProjective.ker ρ hscalar).comp eπ.symm.toMonoidHom
  have he (x : J.specialSubgroup) : σ (J.specialToProjective x) = ρ x := by
    have hh : eπ.symm (J.specialToProjective x) = QuotientGroup.mk' J.specialToProjective.ker x :=
      eπ.symm_apply_eq.mpr rfl
    change QuotientGroup.lift J.specialToProjective.ker ρ hscalar
      (eπ.symm (J.specialToProjective x)) = ρ x
    rw [hh]
    rfl
  have hk := small_projective_three_core_killed J hc hconj hJ σ (by omega)
  intro x hx
  rw [←HermitianForm.SmallThreeCore.special_core_preimage J] at hx
  exact (he x).symm.trans (hk hx)


open RootCoordinates UnitarySource GTwoSource HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (j : Fin 2)

private theorem small_special_section_not_two
    (hT : (Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split j) ≤ center (rankOne Q split j))
    (hZ : Nat.card (center (rankOne Q split j)) = 3)
    (hroot : Nat.card (simpleRoot Q split j) = 8)
    (hm : rotationOrder Q = 8) (i : Fin 2) (hij : i ≠ j)
    (s : RootReflection Q split j) (d : RootSection Q split j) (hden : d.denominator = ⊥)
    (a : rootAt Q split j (Q.simple i)) (ha : a ≠ 1)
    (hax : (a : X ⧸ Q.D) ∈ d.numerator) : ¬ IsPGroup 2 d.action.range := by
  let f := d.action.rangeRestrict
  let R := rankOne Q split j
  let B := Q.tits.B.subgroupOf R
  let A := (simpleRoot Q split j).subgroupOf R
  intro htwo
  have hAB : A.map f = B.map f := by
    apply le_antisymm (map_mono (subgroupOf_mono _ ((simpleRoot_le Q split j).trans split.U_le)))
    rintro _ ⟨r,hr,rfl⟩
    obtain ⟨u,hu,t,ht,he⟩ := rootActor_borel_factorization Q split j r.property hr
    let u' : R := ⟨u,(show simpleRoot Q split j ≤ R from le_sup_left) hu⟩
    let t' : R := ⟨t,ht.1⟩
    have ht3 : t'^3 = 1 := by
      have hh := pow_card_eq_one' (x := (⟨t',hT ht.2⟩ : center R))
      rw [hZ] at hh
      exact congrArg Subtype.val hh
    have ht1 : f t' = 1 := by
      obtain ⟨n,hn⟩ := htwo (f t')
      apply orderOf_eq_one_iff.mp
      apply Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 3 2).pow_right n)
      · exact orderOf_dvd_of_pow_eq_one (by rw [←map_pow,ht3,map_one])
      · exact orderOf_dvd_of_pow_eq_one hn
    have he' : r = u'*t' := Subtype.ext he
    exact ⟨u',hu,by rw [he',map_mul,ht1,mul_one]⟩
  have hp : Nat.card (Panel Q j) = 9 := by
    have hh := singleton_parabolic_root_index Q split j
    change Nat.card (Panel Q j) = 1 + Nat.card (simpleRoot Q split j) at hh
    omega
  have hind : (B.map f).index ∣ 9 := by
    have hh := B.index_map_dvd d.action.rangeRestrict_surjective
    rwa [rankOne_borel_index Q split j,hp] at hh
  obtain ⟨n,hn⟩ := htwo.exists_card_eq
  have hidx : (B.map f).index = 1 := Nat.eq_one_of_dvd_coprimes
    (by simpa using (by decide : Nat.Coprime 9 2).pow_right n)
    hind (hn ▸ (B.map f).index_dvd_card)
  have htop : A.map f = ⊤ := hAB.trans (index_eq_one.mp hidx)
  have hr : f ⟨s.val,s.mem_rankOne⟩ ∈ A.map f := htop ▸ mem_top _
  obtain ⟨u,hu,he⟩ := hr
  exact cross_section_reflection_ne_root Q split j hm i hij s d hden a ha hax u hu
    (congrArg Subtype.val he).symm

/-- A crossed-root section of the actual SU3(2) actor has at least six
binary dimensions, with no perfectness assumption and its scalar kernel retained. -/
theorem small_special_section_bound
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F=4) (hconj : ∀ x,J.conj x=x^2)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hK : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : rankOne Q split j ≃* J.specialSubgroup)
    (hroot : Nat.card (simpleRoot Q split j) = 8)
    (hm : rotationOrder Q = 8) (i : Fin 2) (hij : i ≠ j)
    (s : RootReflection Q split j) (d : RootSection Q split j) (hden : d.denominator = ⊥)
    (a : rootAt Q split j (Q.simple i)) (ha : a ≠ 1)
    (hax : (a : X ⧸ Q.D) ∈ d.numerator) : 64 ≤ Nat.card d.EffectiveCarrier := by
  obtain ⟨hT,hZ⟩ := small_special_cartan Q split j J hc hconj hK μ hroot
  have hnot := small_special_section_not_two Q split j hT.le hZ hroot hm i hij s d hden a ha hax
  by_contra! hsmall
  let ρ := d.effectiveRepresentation.comp μ.symm.toMonoidHom
  have hcV := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive d.EffectiveCarrier)
  simp only [Nat.card_zmod] at hcV
  have hd : Module.finrank (ZMod 2) (Additive d.EffectiveCarrier) < 6 := by
    have hh : 2^Module.finrank (ZMod 2) (Additive d.EffectiveCarrier) < 2^6 := hcV ▸ hsmall
    exact (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp hh
  have hkill := small_special_three_core_killed J hc hconj hJ ρ hd
  let α := d.action.comp μ.symm.toMonoidHom
  let N := pCore 3 J.specialSubgroup
  have hk : N ≤ α.ker := by
    intro g hg
    apply d.action_eq_one_of_odd (μ.symm g)
    · have hgorder : orderOf g ∣ 27 := by
        rw [←HermitianForm.SmallThreeCore.special_core_card J hc hconj]
        exact (Subgroup.orderOf_coe (⟨g,hg⟩ : N)) ▸ orderOf_dvd_natCard (⟨g,hg⟩ : N)
      rw [μ.symm.orderOf_eq]
      exact (by decide : Nat.Coprime 27 2).of_dvd_left hgorder
    · ext v
      exact Additive.ofMul.injective (congrArg
        (fun f : Module.End (ZMod 2) (Additive d.EffectiveCarrier) => f (Additive.ofMul v)) (hkill hg))
  have hidx : N.index = 8 := by
    have hh := N.card_mul_index
    rw [show Nat.card N = 27 from HermitianForm.SmallThreeCore.special_core_card J hc hconj,
      HermitianForm.SmallThreeCore.special_group_card J hc hconj] at hh
    omega
  have hα : IsPGroup 2 α.range := IsPGroup.of_card_dvd_pow (p:=2) (n:=3) (by
    have hh := index_dvd_of_le hk
    rwa [hidx,index_ker] at hh)
  have he : α.range = d.action.range := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr μ.symm.surjective,←MonoidHom.range_eq_map]
  exact hnot (he ▸ hα)


private theorem small_special_roots_centralized
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F=4) (hconj : ∀ x,J.conj x=x^2)
    (hK : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : rankOne Q split j ≃* J.specialSubgroup)
    (hroot : Nat.card (simpleRoot Q split j) = 8)
    {t : X ⧸ Q.D} (ht : t ∈ Q.tits.B ⊓ Q.tits.N)
    (ho : (orderOf t).Coprime 24) (w : Weyl Q) :
    t ∈ centralizer (rootAt Q split j w : Set (X ⧸ Q.D)) := by
  have hR := (Nat.card_congr μ.toEquiv).trans
    (HermitianForm.SmallThreeCore.special_group_card J hc hconj)
  have hZ := (small_special_cartan Q split j J hc hconj hK μ hroot).2
  obtain ⟨a,ha⟩ := central_nine_root_square Q split j hK hR hZ hroot
  let A := simpleRoot Q split j
  let : Fact (IsPGroup 2 A) := ⟨split.isTwo.to_le (simpleRoot_le Q split j)⟩
  have hnon : frattini A ≠ ⊥ := by
    intro hz
    have hh := pth_power_mem_frattini_of_isPGroup (p:=2) a
    rw [hz,mem_bot] at hh
    exact ha hh
  have hPhi := (frattini A).one_lt_card_iff_ne_bot.mpr hnon
  have he := (frattini A).index_mul_card
  rw [show Nat.card A=8 from hroot] at he
  have hbound : Nat.card (rootAt Q split j w ⧸ frattini (rootAt Q split j w)) ≤ 4 := by
    rw [Nat.card_congr (rootAtFrattiniEquiv Q split j w).toEquiv]
    change (frattini A).index ≤ 4
    nlinarith
  let V := rootAt Q split j w ⧸ frattini (rootAt Q split j w)
  let α := rootAtCartanFrattiniAction Q split j w
  let z : ↥(Q.tits.B ⊓ Q.tits.N) := ⟨t,ht⟩
  have hd : orderOf (α z) ∣ 24 := by
    apply (orderOf_dvd_natCard (α z)).trans
    apply (card_dvd_of_injective (MulAut.toPerm V) MulEquiv.toEquiv_injective).trans
    rw [Nat.card_perm]
    exact Nat.factorial_dvd_factorial hbound
  have hα : α z = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes ho
      ((orderOf_map_dvd α z).trans (Subgroup.orderOf_coe z).symm.dvd) hd)
  have hk : z ∈ (rootAtCartanFrattiniRepresentation Q split j w).ker := by
    change rootAtCartanFrattiniRepresentation Q split j w z = 1
    ext a
    change Additive.ofMul (α z a.toMul) = a
    rw [hα]
    rfl
  rw [rootAtCartanFrattiniRepresentation_kernel] at hk
  intro a ha
  have he := congrArg (fun f : MulAut (rootAt Q split j w) => (f ⟨a,ha⟩ : X ⧸ Q.D)) hk
  change t*a*t⁻¹=a at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The fixed radical of three small special-unitary roots has order 512,
whereas its two moved Frattini layers force order at least 4096. -/
theorem separated_small_special_radical_false
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F=4) (hconj : ∀ x,J.conj x=x^2)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hK : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : rankOne Q split j ≃* J.specialSubgroup)
    (hroot : Nat.card (simpleRoot Q split j) = 8)
    (hm : rotationOrder Q = 8) (i : Fin 2) (hij : i ≠ j)
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)))
    (hsep : ∀ w : Weyl Q,
      (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split j w : Set (X ⧸ Q.D)) ∧
      rootAt Q split i w ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥) : False := by
  let d : RootSection Q split j := {
    numerator := simpleRemainder Q split j ⊓ centralizer ({(c : X ⧸ Q.D)} : Set _)
    le_radical := inf_le_left
    normalized := separated_radical_centralizer_normalized Q split j hK c (fun w => (hsep w).1)
    denominator := ⊥
    invariant _ := map_bot _ }
  let f := frattiniSection Q split j d
  let A := rootAt Q split j (Q.simple i)
  have hAd : A ≤ d.numerator := by
    change A ≤ simpleRemainder Q split j ⊓ centralizer ({(c : X ⧸ Q.D)} : Set _)
    rw [←separated_radical_centralizer_sup Q split hm j i hij.symm c hsep]
    exact le_sup_left.trans le_sup_left
  have hR := (Nat.card_congr μ.toEquiv).trans
    (HermitianForm.SmallThreeCore.special_group_card J hc hconj)
  have hZ := (small_special_cartan Q split j J hc hconj hK μ hroot).2
  obtain ⟨a,ha⟩ : ∃ a : A, a^2 ≠ 1 := by
    obtain ⟨u,hu⟩ := central_nine_root_square Q split j hK hR hZ hroot
    let e : A ≃* simpleRoot Q split j :=
      ReeSource.RootAction.conjugateEquiv (simpleRoot Q split j) (representative (Q.simple i))
    refine ⟨e.symm u,?_⟩
    intro he
    apply hu
    simpa only [map_pow,map_one,e.apply_symm_apply] using congrArg e he
  have hane : a ≠ 1 := fun he => ha (by rw [he,one_pow])
  let s := actorReflection Q split j
  have h1 := small_special_section_bound Q split j J hc hconj hJ hK μ hroot hm i hij s d rfl a hane (hAd a.property)
  let v : d.numerator := inclusion hAd a
  let : Fact (IsPGroup 2 d.numerator) := ⟨d.isTwo⟩
  have h2 := small_special_section_bound Q split j J hc hconj hJ hK μ hroot hm i hij s f rfl (a^2) ha
    (show ((a^2 : A) : X ⧸ Q.D) ∈ f.numerator from
      ⟨v^2,pth_power_mem_frattini_of_isPGroup (p:=2) v,rfl⟩)
  have hden : d.effectiveDenominator = frattini d.numerator := by
    rw [d.effectiveDenominator_eq]
    exact sup_bot_eq _
  have h1' : 64 ≤ Nat.card (d.numerator ⧸ frattini d.numerator) := by
    change 64 ≤ d.effectiveDenominator.index at h1
    rwa [hden] at h1
  have h2' : 64 ≤ Nat.card (frattini d.numerator) := by
    have hh := h2.trans (Nat.card_le_card_of_surjective _
      (QuotientGroup.mk'_surjective f.effectiveDenominator))
    exact hh.trans_eq (Nat.card_congr
      ((frattini d.numerator).equivMapOfInjective d.numerator.subtype
        d.numerator.subtype_injective).symm.toEquiv)
  have hlo : 4096 ≤ Nat.card d.numerator := by
    calc
      _ = 64*64 := rfl
      _ ≤ Nat.card (d.numerator ⧸ frattini d.numerator)*Nat.card (frattini d.numerator) :=
        Nat.mul_le_mul h1' h2'
      _ = _ := (frattini d.numerator).index_mul_card
  have hsize : Nat.card d.numerator = 512 := by
    have hh := (octagon_separated_root_centralizer_orders Q split hm j i hij.symm c hsep).1
    simpa only [hroot,Nat.reducePow] using hh
  omega

/-- The genuine SU3(2) scalar cover is impossible opposite linear fields
of order 16 or 64. The scalar subgroup is retained throughout. -/
theorem small_special_large_linear_false
    {F E : Type*} [Field F] [Finite F] [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 F)
    (hc : Nat.card F=4) (hconj : ∀ x,J.conj x=x^2)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hK : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : rankOne Q split j ≃* J.specialSubgroup)
    (hroot : Nat.card (simpleRoot Q split j) = 8)
    (hm : rotationOrder Q = 8) (i : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (hE : Nat.card E=16 ∨ Nat.card E=64) : False := by
  obtain ⟨r,hr,hd,hcop⟩ : ∃ r : ℕ, r.Prime ∧ r ∣ Nat.card E-1 ∧ r.Coprime 24 := by
    rcases hE with hE | hE
    · exact ⟨5,by decide,by rw [hE]; decide,by decide⟩
    · exact ⟨7,by decide,by rw [hE]; decide,by decide⟩
  let : Fact r.Prime := ⟨hr⟩
  let si := actorReflection Q split i
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥((Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split i)) r
    (by rwa [rankOne_cartan_card Q split i hKi μi si])
  have ho : orderOf (t : X ⧸ Q.D) = r := (Subgroup.orderOf_coe t).trans ht
  have hfix := small_special_roots_centralized Q split j J hc hconj hK μ hroot t.property.1 (ho ▸ hcop)
  have hne : (t : X ⧸ Q.D) ≠ 1 := by
    intro he
    rw [he,orderOf_one] at ho
    exact hr.ne_one ho.symm
  have hfree := linear_cartan_separated_roots Q split i j hij hKi μi t.property.1 t.property.2 hne hfix
  exact separated_small_special_radical_false Q split j J hc hconj hJ hK μ hroot hm i hij
    ⟨t,t.property.1⟩ (fun w => ⟨hfix w,hfree w⟩)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
