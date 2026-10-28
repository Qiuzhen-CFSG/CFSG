module
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PGroup.NormalPrimeImage
public import Theory.GroupTheory.PGroup.NormalChain
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.Commutator.SubnormalAbsorption
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.SpecificGroups.SymmetricThree.CubicSelection
public import Theory.SpecificGroups.GL2.ThreeConjugacy
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
/-!
# Cubics acting on subnormal symmetric-three residuals

The cubic residual of a subnormal S₃ is central in the ambient three-core:
S₃ is three-perfect, so the three-core normalizes it, and a normal subgroup
of order three in a three-group is central. Its normal closure is therefore
elementary abelian. In ambient three-rank at most two it is a line or a plane.

In the plane case, the involution in S₃ acts as a non-scalar reflection.
Its action image is a subnormal two-subgroup and lies in the image's two-core.
A cubic moving this reflection would give a product of reflections of order
three or six, incompatible with that two-core. The two small matrix identities
are checked on the 81 matrices over F₃. The original cubic consequently fixes
the plane, and in either case normalizes the literal S₃ residual.

This supplies the solvable residual-normalization step in Aschbacher–Smith
6.1.19, printed p.675, without identifying a solvable residual as a component
or assuming that the cubic preserves W. The companion ResidualNormalization
module applies it to the original factor preimages on W/Z_S. Full-factor
normalization, the parabolic/amalgam contradiction, initial 6.1.4–5 and the
remaining escape geometry remain with qt-d-1222-rankone-recognition-natural.
-/

public section
open Subgroup Matrix
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalSolvableFactor
variable {G : Type*} [Group G] [Finite G]

private theorem threePerfect {X : Type*} [Group X] (e : X ≃* Equiv.Perm (Fin 3)) :
    IsPPerfect 3 X := by
  apply (pResidual_eq_top_iff 3 X).mp
  apply top_unique
  intro x _
  have hword : ∀ a : Equiv.Perm (Fin 3), ∃ b c : Equiv.Perm (Fin 3),
      b^2=1 ∧ c^2=1 ∧ a=b*c := by decide +kernel
  obtain ⟨b,c,hb,hc,he⟩ := hword (e x)
  have hh (a : Equiv.Perm (Fin 3)) (ha : a^2=1) : e.symm a ∈ pResidual 3 X :=
    mem_pResidual_of_orderOf_coprime ((by decide : Nat.Coprime 3 2).of_dvd_right
      (orderOf_dvd_of_pow_eq_one (by rw [←map_pow,ha,map_one])))
  have hx := (pResidual 3 X).mul_mem (hh b hb) (hh c hc)
  simpa only [←map_mul,←he,e.symm_apply_apply] using hx

private theorem residual_card {X : Type*} [Group X] (e : X ≃* Equiv.Perm (Fin 3)) :
    Nat.card (pResidual 2 X)=3 := by
  let : Finite X := Finite.of_injective e e.injective
  rw [←card_map_of_injective (K:=pResidual 2 X) (f:=e.toMonoidHom) e.injective,
    map_pResidual_of_surjective 2 e.toMonoidHom e.surjective]
  exact Theory.SpecificGroups.SymmetricThree.CubicSelection.residual_card

private theorem threeCore_eq_residual {X : Type*} [Group X] [Finite X]
    (e : X ≃* Equiv.Perm (Fin 3)) : pCore 3 X = pResidual 2 X := by
  have hp : IsPGroup 3 (pResidual 2 X) := IsPGroup.of_card (n:=1) (by
    simpa using residual_card e)
  have hlo : pResidual 2 X ≤ pCore 3 X := le_sSup ⟨inferInstance,hp⟩
  have hcard : Nat.card X=6 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    rfl
  have hd : Nat.card (pCore 3 X) ∣ 6 := hcard ▸ card_subgroup_dvd_card _
  have hc : Nat.Coprime (Nat.card (pCore 3 X)) 2 := by
    obtain ⟨m,hm⟩ := (pCore_isPGroup (p:=3) (G:=X)).exists_card_eq
    rw [hm]; exact (by decide : Nat.Coprime 3 2).pow_left m
  exact (eq_of_le_of_card_ge hlo (by
    rw [residual_card e]
    exact Nat.le_of_dvd (by decide) (hc.dvd_of_dvd_mul_left hd))).symm

/-- The cubic residual of a subnormal S₃ lies in the center of the ambient three-core. -/
theorem residual_le_threeCore_center (X : Subgroup G) (hX : X.IsSubnormal)
    (e : X ≃* Equiv.Perm (Fin 3)) :
    (pResidual 2 X).map X.subtype ≤ (center (pCore 3 G)).map (pCore 3 G).subtype := by
  let D := (pResidual 2 X).map X.subtype
  let Q := pCore 3 G
  have hDQ : D ≤ Q := by
    change (pResidual 2 X).map X.subtype ≤ pCore 3 G
    rw [←threeCore_eq_residual e]
    exact pCoreIn_le_of_subnormal 3 hX
  have hQX : Q ≤ normalizer (X : Set G) :=
    le_normalizer_of_isSubnormal_isPPerfect X Q hX (threePerfect e)
      pCore_isPGroup le_normalizer_of_normal
  have hQD : Q ≤ normalizer (D : Set G) := hQX.trans
    (normalizer_le_normalizer_characteristic_image X (pResidual 2 X))
  let : (D.subgroupOf Q).Normal := normal_subgroupOf_of_le_normalizer hQD
  have hc : Nat.card (D.subgroupOf Q)=3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hDQ).toEquiv,
      card_map_of_injective X.subtype_injective]
    exact residual_card e
  have hh := (pCore_isPGroup (p:=3) (G:=G)).normal_le_center_of_card_dvd_prime
    (D.subgroupOf Q) (by rw [hc])
  have hm := map_mono (f:=Q.subtype) hh
  rwa [map_subgroupOf_eq_of_le hDQ] at hm

private theorem matrix_cubic_reflection :
    ∀ a c : Matrix (Fin 2) (Fin 2) (ZMod 3),
      a^2=1 → a≠1 → a≠ -1 → c^3=1 →
      (a*c*a*c^2)^2=1 → c=1 := by decide +kernel

private theorem matrix_product_six :
    ∀ a c : Matrix (Fin 2) (Fin 2) (ZMod 3),
      a^2=1 → c^3=1 → (a*c*a*c^2)^6=1 := by decide +kernel

/-- A cubic centralizes a subnormal reflection in the actual ternary plane. -/
private theorem cubic_eq_one_of_reflection_in_core
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)))
    (t c : H) (ht : t ∈ pCore 2 H) (ht2 : t^2=1)
    (ht1 : t≠1) (htscalar : t.val.val ≠ -1) (hc : c^3=1) : c=1 := by
  let w : H := t*c*t*c^2
  have hcinv : c^2=c⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [←pow_succ,hc]
  have hw : w ∈ pCore 2 H := by
    rw [show w=t*(c*t*c⁻¹) by dsimp [w]; simp only [hcinv,mul_assoc]]
    exact (pCore 2 H).mul_mem ht ((inferInstance : (pCore 2 H).Normal).conj_mem t ht c)
  have hw6 : w^6=1 := by
    apply Subtype.ext
    apply Units.ext
    exact matrix_product_six t.val.val c.val.val
      (congrArg (fun x : H => x.val.val) ht2) (congrArg (fun x : H => x.val.val) hc)
  have hw2 : w^2=1 := by
    have hcop := (pCore_isPGroup (p:=2) (G:=H)).orderOf_coprime
      (by decide : Nat.Coprime 2 3) (⟨w,hw⟩ : pCore 2 H)
    rw [←Subgroup.orderOf_coe (⟨w,hw⟩ : pCore 2 H)] at hcop
    exact orderOf_dvd_iff_pow_eq_one.mp
      (hcop.dvd_of_dvd_mul_left (orderOf_dvd_of_pow_eq_one hw6))
  apply Subtype.ext
  apply Units.ext
  exact matrix_cubic_reflection t.val.val c.val.val
    (congrArg (fun x : H => x.val.val) ht2)
    (fun he => ht1 (Subtype.ext (Units.ext he))) htscalar
    (congrArg (fun x : H => x.val.val) hc)
    (congrArg (fun x : H => x.val.val) hw2)


private theorem ternary_plane_coordinates
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 3 E]
    (hE : Nat.card E=9) :
    ∃ f : MulAut E →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3),
      Function.Injective f ∧ ∀ a, (f a).val = -1 → ∀ x, a x=x⁻¹ := by
  let V := Additive E
  have hc := Module.natCard_eq_pow_finrank (K:=ZMod 3) (V:=V)
  change Nat.card E = _ at hc
  rw [hE,Nat.card_zmod] at hc
  have hd : Module.finrank (ZMod 3) V=2 := by
    apply (Nat.pow_right_injective (by decide : 2≤3))
    exact hc.symm
  let b := Module.finBasisOfFinrankEq (ZMod 3) V hd
  let al : MulAut E →* (V ≃ₗ[ZMod 3] V) := {
    toFun := fun a => {a.toAdditive with map_smul' := ZMod.map_smul a.toAdditive}
    map_one' := by ext; rfl
    map_mul' := by intros; ext; rfl }
  let q := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) V).symm.trans
    (Matrix.GeneralLinearGroup.toLin' b).symm
  let f := q.toMonoidHom.comp al
  refine ⟨f,?_,?_⟩
  · intro a c he
    have hh := q.injective he
    ext x
    exact congrArg (fun e : V ≃ₗ[ZMod 3] V => e (Additive.ofMul x)) hh
  · intro a ha x
    have he := Matrix.GeneralLinearGroup.toLin'_apply b (f a) (Additive.ofMul x)
    have heq : (Matrix.GeneralLinearGroup.toLin' b (f a)).toLinearEquiv = al a := by
      change (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) V)
        ((Matrix.GeneralLinearGroup.toLin' b) (f a)) = al a
      simp [f,q]
    rw [heq,ha] at he
    have hs : Fintype.linearCombination (ZMod 3) (fun i => b i)
        ((- (1 : Matrix (Fin 2) (Fin 2) (ZMod 3))) *ᵥ b.repr (Additive.ofMul x)) =
          - Additive.ofMul x := by
      rw [Matrix.neg_mulVec,Matrix.one_mulVec,map_neg]
      exact congrArg Neg.neg (b.sum_repr (Additive.ofMul x))
    exact he.trans hs

private theorem subnormal_image_twoCore
    {B : Type*} [Group B] (f : G →* B) (X : Subgroup G) (hX : X.IsSubnormal)
    (hker : pResidual 2 X ≤ (f.comp X.subtype).ker) :
    X.map f.rangeRestrict ≤ pCore 2 f.range := by
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let g := f.rangeRestrict.comp X.subtype
  have hk : pResidual 2 X ≤ g.ker := fun x hx => Subtype.ext (hker hx)
  let q := QuotientGroup.lift (pResidual 2 X) g hk
  have hq : Function.Surjective q.rangeRestrict := q.rangeRestrict_surjective
  have hr : q.range = X.map f.rangeRestrict := by
    have he : q.comp (QuotientGroup.mk' (pResidual 2 X)) = g := rfl
    have hh := congrArg MonoidHom.range he
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),
      ←MonoidHom.range_eq_map,MonoidHom.range_comp,range_subtype] at hh
    exact hh
  have hp : IsPGroup 2 (X.map f.rangeRestrict) := hr ▸
    (isPGroup_quotient_pResidual (G:=X) 2).of_surjective q.rangeRestrict hq
  have hn := hX.map f.rangeRestrict_surjective
  have ht : pCore 2 (X.map f.rangeRestrict) = ⊤ :=
    top_unique (le_sSup ⟨inferInstance,hp.to_subgroup ⊤⟩)
  have hh := pCoreIn_le_of_subnormal 2 hn
  change (pCore 2 (X.map f.rangeRestrict)).map (X.map f.rangeRestrict).subtype ≤ _ at hh
  rwa [ht,←MonoidHom.range_eq_map,range_subtype] at hh

omit [Finite G] in
private theorem involution_witness (X : Subgroup G)
    (e : X ≃* Equiv.Perm (Fin 3)) :
    ∃ t : X, t^2=1 ∧ ∃ d : pResidual 2 X,
      d≠1 ∧ t*(d:X)*t⁻¹=(d:X)⁻¹ := by
  let t := e.symm (Equiv.swap 0 1)
  let a : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
  let d := e.symm a
  have ha : orderOf a=3 := orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  have hd : d ∈ pResidual 2 X := mem_pResidual_of_orderOf_coprime (by
    rw [e.symm.orderOf_eq,ha]; decide)
  refine ⟨t,?_,⟨d,hd⟩,?_,?_⟩
  · apply e.injective
    simp only [map_pow,map_one,e.apply_symm_apply,t]
    decide +kernel
  · intro he
    have hh := congrArg e (congrArg Subtype.val he)
    exact (by decide +kernel : a≠1) (by simpa [d] using hh)
  · apply e.injective
    simp only [map_mul,map_inv,e.apply_symm_apply,t,d]
    decide +kernel

/-- Every cubic preserves the cubic residual of an ambient subnormal S₃
when the ambient three-rank is at most two. -/
theorem cubic_normalizes_residual (X : Subgroup G) (hX : X.IsSubnormal)
    (e : X ≃* Equiv.Perm (Fin 3)) (hr : primeRank 3 G≤2)
    (c : G) (hc : c^3=1) :
    c ∈ normalizer ((pResidual 2 X).map X.subtype : Set G) := by
  let D := (pResidual 2 X).map X.subtype
  let Q := pCore 3 G
  let Z := (center Q).map Q.subtype
  let E := normalClosure (D : Set G)
  have hDZ : D ≤ Z := residual_le_threeCore_center X hX e
  let : Z.Normal := inferInstance
  have hEZ : E ≤ Z := normalClosure_le_normal hDZ
  let : IsMulCommutative Z := Subgroup.map_isMulCommutative (center Q) Q.subtype
  let : IsMulCommutative E := ⟨⟨fun x y => Subtype.ext
    (setLike_mul_comm (hEZ x.property) (hEZ y.property))⟩⟩
  have hDe : IsElementaryAbelian 3 D := by
    let : IsCyclic (pResidual 2 X) := isCyclic_of_prime_card (residual_card e)
    let : IsElementaryAbelian 3 (pResidual 2 X) := {
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun d => by
        simpa only [residual_card e] using pow_card_eq_one' (x:=d)) }
    exact IsElementaryAbelian.map_subtype
  let := hDe
  have hEe : IsElementaryAbelian 3 E := IsElementaryAbelian.normalClosure_of_isMulCommutative D
  let := hEe
  have hEc : Nat.card E≤9 := (primeRank_le_iff_elementary_card_le G).mp hr E hEe
  have hDc : Nat.card D=3 := (card_map_of_injective X.subtype_injective).trans (residual_card e)
  have hDE : D≤E := le_normalClosure
  by_cases hEq : D=E
  · change c ∈ normalizer (D : Set G)
    rw [hEq]
    exact le_normalizer_of_normal (mem_top c)
  have hE9 : Nat.card E=9 := by
    obtain ⟨m,hm⟩ := (IsElementaryAbelian.isPGroup 3 E).exists_card_eq
    have hm2 : m≤2 := (Nat.pow_le_pow_iff_right (by decide : 1<3)).mp (hm ▸ hEc)
    have hlow : 3<Nat.card E := lt_of_not_ge (fun hh =>
      hEq (eq_of_le_of_card_ge hDE (hDc.symm ▸ hh)))
    interval_cases m
    · norm_num only [pow_zero] at hm; omega
    · norm_num only [pow_one] at hm; omega
    · exact hm
  let α : G →* MulAut E := MulAut.conjNormal
  have hker : pResidual 2 X≤(α.comp X.subtype).ker := by
    intro d hd
    ext x
    have hh : Commute (d:G) (x:G) := congrArg Subtype.val
      (mul_comm (⟨(d:G),hDE (mem_map_of_mem X.subtype hd)⟩:E) x)
    change (d:G)*(x:G)*(d:G)⁻¹=(x:G)
    rw [hh.eq,mul_inv_cancel_right]
  obtain ⟨f,hf,hscalar⟩ := ternary_plane_coordinates hE9
  let β := f.comp α
  obtain ⟨t,ht,d,hd,hinv⟩ := involution_witness X e
  have htk : β.rangeRestrict t ∈ pCore 2 β.range :=
    subnormal_image_twoCore β X hX (fun x hx => by
      change f (α x)=1
      rw [show α x=1 from hker hx,map_one]) (mem_map_of_mem β.rangeRestrict t.property)
  have ht2 : (β.rangeRestrict t)^2=1 := by
    rw [←map_pow,show (t:G)^2=1 from congrArg Subtype.val ht,map_one]
  have ht1 : β.rangeRestrict t≠1 := by
    intro he
    have ha : α (t:G)=1 := hf ((congrArg Subtype.val he).trans (map_one f).symm)
    have hv := congrArg (fun a : MulAut E => (a ⟨((d:pResidual 2 X):X),hDE (mem_map_of_mem X.subtype d.property)⟩:G)) ha
    have hi := congrArg Subtype.val hinv
    have hd2 : ((d:pResidual 2 X):X)^2=1 := by
      apply Subtype.ext
      have hh : (d.val:G)⁻¹=(d.val:G) := hi.symm.trans hv
      change (d.val:G)^2=1
      rw [pow_two]
      nth_rw 1 [←hh]
      exact inv_mul_cancel _
    have hd3 : ((d:pResidual 2 X):X)^3=1 := congrArg Subtype.val (by
      simpa only [residual_card e] using pow_card_eq_one' (x:=d))
    apply hd
    apply Subtype.ext
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (by
      simpa using Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hd2) (orderOf_dvd_of_pow_eq_one hd3)))
  have hnscalar : (β.rangeRestrict t).val.val ≠ -1 := by
    intro hh
    have hi := hscalar (α t) hh
    have hEX : E≤X := by
      apply le_of_isSubnormal_of_le_commutator E X hX
      intro x hx
      have hx3 : x^3=1 := elemPow_eq_one_of_isElementaryAbelian x hx
      have he : ⁅x,(t:G)⁆=x⁻¹ := by
        have hh : (t:G)*x*(t:G)⁻¹=x⁻¹ := congrArg Subtype.val (hi ⟨x,hx⟩)
        calc
          ⁅x,(t:G)⁆ = x*((t:G)*x*(t:G)⁻¹)⁻¹ := by
            simp only [commutatorElement_def]; group
          _ = x^2 := by rw [hh,inv_inv,pow_two]
          _=x⁻¹ := eq_inv_of_mul_eq_one_left (by rw [←pow_succ,hx3])
      exact inv_mem_iff.mp (he ▸ commutator_mem_commutator hx t.property)
    have hED : E≤D := by
      intro x hx
      have hx3 : (⟨x,hEX hx⟩:X)^3=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian x hx)
      exact mem_map_of_mem X.subtype (mem_pResidual_of_orderOf_coprime
        ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hx3)))
    exact hEq (le_antisymm hDE hED)
  have hb : β.rangeRestrict c=1 := cubic_eq_one_of_reflection_in_core β.range
    (β.rangeRestrict t) (β.rangeRestrict c) htk ht2 ht1 hnscalar
    (by rw [←map_pow,hc,map_one])
  have ha : α c=1 := hf ((congrArg Subtype.val hb).trans (map_one f).symm)
  apply Subgroup.centralizer_le_normalizer
  intro d hd
  have he := congrArg (fun a : MulAut E => (a ⟨d,hDE hd⟩:G)) ha
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalSolvableFactor
