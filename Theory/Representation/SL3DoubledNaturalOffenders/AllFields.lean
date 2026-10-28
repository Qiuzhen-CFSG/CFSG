module
public import Theory.Representation.SL3DoubledNaturalOffenders.TensorAllFields
public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.FiniteFieldSemilinearDisplacement

/-!
# Doubled-natural offender localization, including even degree

An elementary actor in the full binary normalizer maps to Aut(PSL₃).
The kernel is a multiplicity subgroup of order at most q. If the image
contains an outer automorphism, the proved sharp outer rank bound gives
order at most 2^(n+1), so the whole actor has rank at most 2n+1.
A nontrivial field involution moves exactly 3n binary dimensions. Since
n>1, an offender cannot contain one. The tensor estimate then puts every
offender in the original full SL₃ component, retaining its cubic center.

The final theorem transports this calculation to any faithful representation
with the same normal component and whole doubled-natural model. C.1.34's
DoubledRadical consumer applies it to the literal centralizer quotient.
Source: Aschbacher--Smith B.5.9--10, pp.107--109, C.1.34(2), pp.136--137,
and the outer rank bound E.1.14(1), p.214.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Representation.SL3DoubledNaturalOffenders.AllFields
open Matrix BinaryOffender
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] [Finite F]

local instance : Finite (Module.End (ZMod 2) (Space F)) :=
  Finite.of_injective (fun f : Module.End (ZMod 2) (Space F) => (f : Space F → Space F))
    DFunLike.coe_injective

private def componentEquiv : SL F ≃* component F :=
  MonoidHom.ofInjective (fun _ _ h => representation_injective F (congrArg Units.val h))

private def componentAction : normalizer F →* MulAut (SL F) :=
  (MulAut.congr (componentEquiv (F := F)).symm).toMonoidHom.comp
    (component F).normalizerMonoidHom

omit [Finite F] in
private theorem componentAction_apply (a : normalizer F) (g : SL F) :
    (representation F).asGroupHom (componentAction a g) =
      a.val * (representation F).asGroupHom g * a.val⁻¹ := by
  exact congrArg Subtype.val ((componentEquiv (F := F)).apply_symm_apply _)

private def projectiveAction : normalizer F →* MulAut (SpecialLinearGroup (Fin 3) F ⧸ center (SL F)) :=
  (MulAut.centralQuotientAction (MulEquiv.refl _)).comp componentAction

omit [Finite F] in
private theorem action_kernel_centralizes (a : normalizer F)
    (ha : projectiveAction a = 1) : a.val ∈ centralizer (component F : Set (Ambient F)) := by
  let : Group.IsPerfect (SL F) := Atlas.sl_perfect 3 (by decide)
  have hi : componentAction a = 1 :=
    MulAut.centralQuotientAction_injective (MulEquiv.refl _) (ha.trans (map_one _).symm)
  rw [mem_centralizer_iff]
  rintro _ ⟨g,rfl⟩
  have he := componentAction_apply a g
  rw [hi,MulAut.one_apply] at he
  exact eq_mul_inv_iff_mul_eq.mp he

omit [Finite F] in
private theorem inner_action_linear (a : normalizer F)
    (ha : projectiveAction a ∈ MulAut.innerSubgroup (SpecialLinearGroup (Fin 3) F ⧸ center (SL F))) :
    ∀ (c : F) (v : Space F), a.val.val (c • v) = c • a.val.val v := by
  let : Group.IsPerfect (SL F) := Atlas.sl_perfect 3 (by decide)
  obtain ⟨g,hg⟩ := (MulAut.centralQuotientAction_inner_iff (MulEquiv.refl _) (componentAction a)).mp
    (by obtain ⟨x,hx⟩ := ha; exact ⟨x,hx.symm⟩)
  let r := (representation F).asGroupHom g
  have hc : r⁻¹ * a.val ∈ centralizer (component F : Set (Ambient F)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨x,rfl⟩
    have he := componentAction_apply a x
    rw [hg,MulAut.conj_apply,map_mul,map_mul,map_inv] at he
    change r * (representation F).asGroupHom x * r⁻¹ =
      a.val * (representation F).asGroupHom x * a.val⁻¹ at he
    have hh := congrArg (fun b : Ambient F => r⁻¹ * b * a.val) he
    simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using hh
  obtain ⟨c,hc⟩ := centralizer_units (r⁻¹*a.val) hc
  have hb : a.val.val = representation F g * multiplicity F c.val := by
    calc
      a.val.val = (r*(r⁻¹*a.val)).val := by simp
      _ = representation F g * multiplicity F c.val := by
        change r.val * (r⁻¹*a.val).val = _
        rw [hc]
        rfl
  intro d v
  rw [hb]
  ext i j
  change (g.val.mulVec (multiplicity F c.val (d • v) i)) j =
    (d • g.val.mulVec (multiplicity F c.val v i)) j
  have hm : multiplicity F c.val (d • v) i = d • multiplicity F c.val v i := by
    ext k
    simp only [multiplicity_apply,Pi.smul_apply,Pi.add_apply,smul_eq_mul]
    ring
  rw [hm,Matrix.mulVec_smul]

private theorem centralizer_elementary_card_le (A : Subgroup (Ambient F))
    [IsElementaryAbelian 2 A] (hA : A ≤ centralizer (component F : Set (Ambient F))) :
    Nat.card A ≤ Nat.card F := by
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  let μ := (multiplicityRepresentation F).asGroupHom
  have hμ : Function.Injective μ := by
    intro x y h
    exact Subtype.ext (multiplicity_injective F (congrArg Units.val h))
  have hr : A ≤ μ.range := by
    intro a ha
    obtain ⟨c,hc⟩ := centralizer_units a (hA ha)
    have hs : c.val*c.val=1 := by
      apply multiplicity_injective F
      rw [multiplicity_mul,←hc,multiplicity_one]
      exact congrArg Units.val (elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha)
    have hd : c.val.det=1 := CharTwo.sq_injective (by
      simpa only [pow_two,Matrix.det_mul,Matrix.det_one,one_mul] using congrArg Matrix.det hs)
    exact ⟨⟨c.val,hd⟩,Units.ext hc.symm⟩
  let B := A.comap μ
  let e : B ≃* A := (B.equivMapOfInjective μ hμ).trans (MulEquiv.subgroupCongr (map_comap_eq_self hr))
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  exact (Nat.card_congr e.toEquiv).symm.trans_le (multiplicity_elementary_card_le B)

private theorem outer_elementary_card_le {n : ℕ} (hn : 0<n) (hF : Nat.card F=2^n)
    (A : Subgroup (Ambient F)) [IsElementaryAbelian 2 A] (hAN : A ≤ normalizer F)
    (hout : ¬ (A.subgroupOf (normalizer F)).map projectiveAction ≤
      MulAut.innerSubgroup (SpecialLinearGroup (Fin 3) F ⧸ center (SL F))) :
    Nat.card A ≤ 2^(2*n+1) := by
  let B := A.subgroupOf (normalizer F)
  let e := subgroupOfEquivOfLe hAN
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  let φ := (projectiveAction (F := F)).comp B.subtype
  have him : φ.range = B.map projectiveAction := by rw [MonoidHom.range_comp,range_subtype]
  let : IsElementaryAbelian 2 φ.range := IsElementaryAbelian.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  let : IsElementaryAbelian 2 (B.map projectiveAction) := IsElementaryAbelian.map _
  have hr : Group.rank φ.range ≤ n+1 := by
    apply (Group.rank_congr (MulEquiv.subgroupCongr him)).trans_le
    exact PSL3Even.OuterElementaryRank.rank_le_of_not_le_inner hn hF _ inferInstance hout
  have hcard : Nat.card φ.range ≤ 2^(n+1) := by
    have hd := card_dvd_exponent_pow_rank' φ.range
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 φ.range))
    exact (Nat.le_of_dvd (by positivity) hd).trans (Nat.pow_le_pow_right (by decide) hr)
  let j : φ.ker →* Ambient F := (normalizer F).subtype.comp (B.subtype.comp φ.ker.subtype)
  have hj : Function.Injective j := Subtype.val_injective.comp (Subtype.val_injective.comp Subtype.val_injective)
  let : IsElementaryAbelian 2 φ.ker := IsElementaryAbelian.of_injective φ.ker.subtype Subtype.val_injective
  let : IsElementaryAbelian 2 j.range := IsElementaryAbelian.of_surjective j.rangeRestrict j.rangeRestrict_surjective
  have hjc : j.range ≤ centralizer (component F : Set (Ambient F)) := by
    rintro _ ⟨x,rfl⟩
    exact action_kernel_centralizes x.val.val x.property
  have hk : Nat.card φ.ker ≤ 2^n := by
    rw [Nat.card_congr (MonoidHom.ofInjective hj).toEquiv]
    exact (centralizer_elementary_card_le j.range hjc).trans_eq hF
  calc
    Nat.card A = Nat.card B := (Nat.card_congr e.toEquiv).symm
    _ = Nat.card φ.ker * Nat.card φ.range := by rw [←φ.ker.card_mul_index,index_ker]
    _ ≤ 2^n*2^(n+1) := Nat.mul_le_mul hk hcard
    _ = _ := by rw [←pow_add]; congr 1; omega

/-- Every nonbinary doubled-normalizer offender acts linearly over the original field. -/
theorem offender_fieldLinear {n : ℕ} (hn : 1<n) (hF : Nat.card F=2^n)
    {A : Subgroup (Ambient F)} (hA : IsOffender (action F) A) (hAN : A ≤ normalizer F) :
    ∀ a ∈ A, ∀ (c : F) (v : Space F), a.val (c • v) = c • a.val v := by
  let := hA.1.2
  intro a ha
  obtain ⟨σ,hσ⟩ := normalizer_semilinear a (hAN ha)
  by_cases hs : σ=1
  · simpa only [hs,RingAut.one_apply] using hσ
  have ha2 : a^2=1 := elemPow_eq_one_of_isElementaryAbelian a ha
  have hsq (v : Space F) : a.val (a.val v)=v := congrArg (fun b : Ambient F => b.val v) ha2
  have hs2 : σ^2=1 := by
    ext c
    change σ (σ c) = c
    have he := hsq (c • (fun _ _ => 1))
    rw [hσ,hσ,hsq] at he
    simpa only [Pi.smul_apply,smul_eq_mul,mul_one] using congrFun (congrFun he 0) 0
  have hane : a≠1 := by
    intro he
    apply hs
    ext c
    simpa only [he,Units.val_one,Module.End.one_apply,Pi.smul_apply,smul_eq_mul,mul_one,RingAut.one_apply]
      using (congrFun (congrFun (hσ c (fun _ _ => 1)) 0) 0).symm
  have hout : ¬ (A.subgroupOf (normalizer F)).map projectiveAction ≤
      MulAut.innerSubgroup (SpecialLinearGroup (Fin 3) F ⧸ center (SL F)) := by
    intro hi
    have hl := inner_action_linear ⟨a,hAN ha⟩ (hi (mem_map_of_mem _ ha))
    apply hs
    ext c
    have he := hσ c (fun _ _ => 1)
    rw [hl] at he
    have hne : a.val (fun _ _ => 1) ≠ 0 := by
      intro hz
      have hh := congrArg (fun w => a.val w) hz
      rw [hsq,map_zero] at hh
      have hh' := congrFun (congrFun hh 0) 0
      exact one_ne_zero hh'
    exact (smul_left_injective F hne) he.symm
  have hb := outer_elementary_card_le (by omega) hF A hAN hout
  have hr : rank A ≤ 2*n+1 := by
    rw [hA.1.card_eq_two_pow_rank] at hb
    exact (Nat.pow_le_pow_iff_right (by decide : 1<(2:ℕ))).mp hb
  have hd := FiniteFieldSemilinearDisplacement.fixedCodim_formula (action F)
    (by decide : 0<2) a (orderOf_eq_prime ha2 hane) σ (orderOf_eq_prime hs2 hs) hσ
  have hf : Module.finrank (ZMod 2) F=n := by
    apply Nat.pow_right_injective (by decide : 1<(2:ℕ))
    exact (FiniteField.pow_finrank_eq_natCard 2 F).trans hF
  have hv : Module.finrank F (Space F) = 6 := by
    simp [Space,Natural,Module.finrank_pi_fintype]
  rw [hf,hv] at hd
  have hle : fixedSpace (action F) A ≤ fixedSpace (action F) (Subgroup.zpowers a) := by
    intro v hv b
    exact hv ⟨b,zpowers_le.mpr ha b.property⟩
  have he := Submodule.finrank_mono hle
  have h1 := fixedCodim_add_finrank (action F) A
  have h2 := fixedCodim_add_finrank (action F) (Subgroup.zpowers a)
  have ho := hA.2
  omega

/-- In every nonbinary degree, all doubled-normalizer offenders lie in full SL₃. -/
theorem offender_le_component_of_le_normalizer {n : ℕ} (hn : 1<n) (hF : Nat.card F=2^n)
    {A : Subgroup (Ambient F)} (hA : IsOffender (action F) A) (hAN : A ≤ normalizer F) :
    A ≤ component F := by
  have hl := offender_fieldLinear hn hF hA hAN
  have ht : A ≤ tensorSubgroup F := by
    intro a ha
    obtain ⟨g,c,hf⟩ := normalizer_linear_tensor_factors a (hAN ha) (hl a ha)
    let := hA.1.2
    exact involution_mem_tensorSubgroup_of_gl_factors a g c hf
      (elemPow_eq_one_of_isElementaryAbelian a ha)
  exact offender_le_component_of_le_tensorSubgroup hF (by omega) hA ht

variable {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U] {n : ℕ}

/-- Every offender lies in the original normal component; the whole actor may have a nontrivial two-core. -/
theorem offender_le_normal_component (σ : Representation (ZMod 2) G U)
    (hfaith : Function.Injective σ) (L : Subgroup G) [L.Normal]
    (hF : Nat.card F = 2^n) (hn : 1 < n)
    (mark : L ≃* SL F) (E : U ≃ₗ[ZMod 2] Space F)
    (he : ∀ l : L, ∀ v, E (σ l v) = representation F (mark l) (E v))
    {D : Subgroup G} (hD : IsOffender σ D) : D ≤ L := by
  let τ : Representation (ZMod 2) G (SL3DoubledNaturalOffenders.Space F) :=
    E.conjRingEquiv.toMonoidHom.comp σ
  let f := τ.asGroupHom
  have hf : Function.Injective f := by
    intro g h he
    apply E.conjRingEquiv.injective.comp hfaith
    exact congrArg Units.val he
  have ht (g : G) (v : U) :
      E (σ g v) = SL3DoubledNaturalOffenders.action F (f g)
        (E v) := by
    change _ = E (σ g (E.symm (E v)))
    rw [E.symm_apply_apply]
  have hmark (g : L) : f g =
      (SL3DoubledNaturalOffenders.representation F).asGroupHom (mark g) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    change E (σ g (E.symm v)) = _
    exact (he g (E.symm v)).trans
      (congrArg (representation F (mark g))
        (E.apply_symm_apply v))
  have he : L.map f = SL3DoubledNaturalOffenders.component F := by
    apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      exact ⟨mark ⟨g, hg⟩, (hmark ⟨g, hg⟩).symm⟩
    · rintro _ ⟨g, rfl⟩
      exact ⟨mark.symm g, (mark.symm g).property,
        (hmark (mark.symm g)).trans
          (congrArg (SL3DoubledNaturalOffenders.representation F).asGroupHom
            (mark.apply_symm_apply g))⟩
  have hDN : D.map f ≤ SL3DoubledNaturalOffenders.normalizer F := by
    change D.map f ≤ Subgroup.normalizer (SL3DoubledNaturalOffenders.component F)
    rw [← he]
    exact (Subgroup.map_mono (show D ≤ Subgroup.normalizer L by
      rw [Subgroup.normalizer_eq_top]; exact le_top)).trans (Subgroup.le_normalizer_map f)
  have hd := AllFields.offender_le_component_of_le_normalizer
    hn hF
    (hD.map_equivariant σ (SL3DoubledNaturalOffenders.action F) f hf E ht) hDN
  rw [← he] at hd
  intro g hg
  obtain ⟨l, hl, heq⟩ := hd (Subgroup.mem_map_of_mem f hg)
  exact hf heq ▸ hl


end Representation.SL3DoubledNaturalOffenders.AllFields
