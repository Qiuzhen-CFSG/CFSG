module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Counting.SectionCounts
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.QuaternionCosetInvolutions
public import Theory.GroupTheory.CoprimeQuotientSubgroups
/-!
# The original two-element quaternion fiber

The original inverter and H_B generate a two-group on which the marked
cubic quotient map is injective. The actual central commutator condition
places its image in the two-element natural-involution coset calculation.
The previously proved natural/diagonal fusion dichotomy then identifies
this model predicate with the original z-class, preserving the binary
section and the left/right coset conventions.

Source: Aschbacher--Smith J.2.7(8), printed p.437. This supplies the final
factor two in the original middle-layer count 4·4·2·15=480.
-/

public section
noncomputable section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d:LocalSetup G} (c:Choices d)
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private theorem HB_commutator_central (i : d.toTypeRuSetup.H)
    (hiK : (i:G)∈d.toTypeRuSetup.K) (hbi : c.InvertsB (i:G))
    (a : Fusion.HB d.toTypeRuSetup c.sylowThree) :
    ⁅(i:G),(a:G)⁆∈(center (Fusion.HB d.toTypeRuSetup c.sylowThree)).map
      (Fusion.HB d.toTypeRuSetup c.sylowThree).subtype := by
  let A:=Fusion.HB d.toTypeRuSetup c.sylowThree
  have hn:=c.HB_normalized_by_inverter (i:G) i.property hbi
  have hca : ⁅(i:G),(a:G)⁆∈A := A.mul_mem
    ((mem_normalizer_iff.mp hn a).mp a.property) (A.inv_mem a.property)
  have hcu := d.HC_commutator_K_mem_U ⟨a,c.HB_le_HC_source a.property⟩ ⟨i,hiK⟩
  have cp:=Fusion.centralProductData_of_quaternion d c.sylowThree (SourceCompletion.quaternion c.sylowThree)
  have hcz : ⁅(i:G),(a:G)⁆∈d.toTypeRuSetup.Z := cp.intersection_eq ▸ ⟨hca,hcu⟩
  refine ⟨⟨_,hca⟩,?_,rfl⟩
  apply mem_center_iff.mpr
  intro b
  exact Subtype.ext ((c.HB_le_HC_source b.property).1 _ hcz).symm

/-- The original quaternion binary section contributes exactly two z-class lifts. -/
theorem quaternion_inverting_z_class_card (i : d.toTypeRuSetup.H)
    (hiK : (i:G)∈d.toTypeRuSetup.K) (hiQ : (i:G)∉d.toTypeRuSetup.Q)
    (hi : orderOf (i:G)=2) (hbi : c.InvertsB (i:G)) (hzi : IsConj c.z (i:G)) :
    Nat.card {a:BinaryConjugationSection.Inverting (Fusion.HB d.toTypeRuSetup c.sylowThree) (i:G) //
      IsConj c.z ((a.val:G)*(i:G))}=2 := by
  let A:=Fusion.HB d.toTypeRuSetup c.sylowThree
  have hn:=c.HB_normalized_by_inverter (i:G) i.property hbi
  let T:=A⊔zpowers (i:G)
  obtain ⟨eA⟩:=SourceCompletion.quaternion c.sylowThree
  have hAp : IsPGroup 2 A := IsPGroup.of_card (n:=3) (by
    rw [Nat.card_congr eA.toEquiv,Nat.card_eq_fintype_card];decide +kernel)
  have hip : IsPGroup 2 (zpowers (i:G)) := IsPGroup.of_card (n:=1) (by
    rw [Nat.card_zpowers,hi,pow_one])
  have hTp : IsPGroup 2 T := hAp.to_sup_of_normal_left' hip (zpowers_le.mpr hn)
  have hAN : A≤c.NB := inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have hTN : T≤c.NB := sup_le hAN (zpowers_le.mpr (c.mem_NB_of_inverts hbi))
  have hiT : (i:G)∈T := mem_sup_right (mem_zpowers _)
  let iT:T:=⟨i,hiT⟩
  obtain ⟨e,hM⟩:=c.normalizer_equiv_autA6_source
  let φ:=CubicSylow.markedMap c e
  have hker : Nat.Coprime 2 (Nat.card φ.ker) := by
    rw [CubicSylow.markedMap_ker,CubicSylow.normalizerKernel_card c (SourceCompletion.B_card c)]
    decide
  let f:T→*AlternatingSix.ShadowLocal.AutA6:=φ.comp (inclusion hTN)
  have hf : Function.Injective f :=
    (injective_comp_subtype_of_coprime_ker φ hker (T.subgroupOf c.NB) hTp.comap_subtype).comp
      (subgroupOfEquivOfLe hTN).symm.injective
  let j:A→*AlternatingSix.ShadowLocal.AutA6:=f.comp (inclusion (show A≤T from le_sup_left))
  have hj : Function.Injective j:=hf.comp (inclusion_injective le_sup_left)
  let Q:=j.range
  let eqv:A≃*Q:=MonoidHom.ofInjective hj
  let β:=f iT
  have hβ : orderOf β=2 := (orderOf_injective f hf iT).trans ((orderOf_coe iT).symm.trans hi)
  have hQM : Q≤AlternatingSix.M10.extension := by
    rintro x ⟨a,rfl⟩
    rw [←hM]
    refine ⟨c.normalizerQuotientMap (inclusion hAN a),?_,rfl⟩
    exact mem_map_of_mem c.normalizerQuotientMap a.property.2
  let iN:c.NB:=⟨i,c.mem_NB_of_inverts hbi⟩
  have hβM : β∉AlternatingSix.M10.extension := by
    intro hm
    rw [←hM] at hm
    obtain ⟨a,ha,he⟩:=hm
    have he' : a=c.normalizerQuotientMap iN:=e.injective he
    have ha' : c.normalizerQuotientMap iN∈c.centralizerImage:=he' ▸ ha
    have hh : iN∈c.centralizerImage.comap c.normalizerQuotientMap:=ha'
    rw [c.centralizerImage_comap (SourceCompletion.B_card c)] at hh
    exact c.not_mem_GB_of_inverts (SourceCompletion.B_card c) hbi hh
  have hβn : β∈AlternatingSix.ShadowLocal.natural := by
    by_contra hn
    exact c.diagonal_not_z_fused_source e hM iN hβ hn hzi.symm
  have hc (q:Q) : ⁅β,(q:AlternatingSix.ShadowLocal.AutA6)⁆∈(center Q).map Q.subtype := by
    obtain ⟨a,rfl⟩:=eqv.surjective q
    obtain ⟨z,hz,hze⟩:=c.HB_commutator_central i hiK hbi a
    refine ⟨eqv z,(centerCongr eqv ⟨z,hz⟩).property,?_⟩
    have hh : (inclusion (show A≤T from le_sup_left) z)=⁅iT,inclusion (show A≤T from le_sup_left) a⁆ :=
      Subtype.ext hze
    exact (congrArg f hh).trans (map_commutatorElement f _ _)
  have hcount:=AlternatingSix.ShadowLocal.QuaternionCosetInvolutions.natural_involutions_in_coset_card
    Q ⟨eqv.symm.trans eA⟩ hQM β hβ hβn hβM hc
  have his : (i:G)^2=1 := (orderOf_eq_prime_iff.mp hi).1
  have hiinv : (i:G)⁻¹=i := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using his)
  have hiff (a:A) :
      ((i:G)*a*(i:G)⁻¹=(a:G)⁻¹ ∧ IsConj c.z ((a:G)*i)) ↔
      (orderOf (β*(eqv a:AlternatingSix.ShadowLocal.AutA6))=2 ∧
        β*(eqv a:AlternatingSix.ShadowLocal.AutA6)∈AlternatingSix.ShadowLocal.natural) := by
    let aT:T:=inclusion (show A≤T from le_sup_left) a
    let v:T:=iT*aT
    let vN:c.NB:=inclusion hTN v
    have hvi : c.InvertsB (vN:G) := by
      intro b hb
      change ((i:G)*(a:G))*b*((i:G)*(a:G))⁻¹=b⁻¹
      have hab : (a:G)*b*(a:G)⁻¹=b := by
        rw [← a.property.2 b hb,mul_inv_cancel_right]
      calc ((i:G)*(a:G))*b*((i:G)*(a:G))⁻¹=(i:G)*((a:G)*b*(a:G)⁻¹)*(i:G)⁻¹ := by group
           _=b⁻¹ := by rw [hab]; exact hbi b hb
    have hne : (v:G)≠1 := by
      intro he
      have hia : (i:G)=(a:G)⁻¹ := mul_eq_one_iff_eq_inv.mp he
      exact hiQ (hia ▸ d.toTypeRuSetup.Q.inv_mem a.property.1)
    have hpow : ((i:G)*a*(i:G)⁻¹=(a:G)⁻¹) ↔ (v:G)^2=1 := by
      change ((i:G)*(a:G)*(i:G)⁻¹=(a:G)⁻¹) ↔ ((i:G)*(a:G))^2=1
      rw [hiinv,pow_two]
      constructor
      · intro hh
        calc (i:G)*(a:G)*((i:G)*(a:G))=((i:G)*(a:G)*(i:G))*(a:G) := by group
             _=1 := by rw [hh,inv_mul_cancel]
      · intro hh
        apply (mul_eq_one_iff_eq_inv).mp
        simpa only [mul_assoc] using hh
    have hord : orderOf (β*(eqv a:AlternatingSix.ShadowLocal.AutA6))=orderOf (v:G) := by
      change orderOf (f iT*j a)=_
      change orderOf (f iT*f aT)=_
      rw [←map_mul,orderOf_injective f hf]
      exact (orderOf_coe v).symm
    have hconj : IsConj c.z ((a:G)*i) ↔ IsConj c.z (v:G) := by
      constructor
      · intro hh
        exact hh.trans (isConj_iff.mpr ⟨i,by change (i:G)*((a:G)*(i:G))*(i:G)⁻¹=(i:G)*(a:G);group⟩)
      · intro hh
        exact hh.trans (isConj_iff.mpr ⟨a,by change (a:G)*((i:G)*(a:G))*(a:G)⁻¹=(a:G)*(i:G);group⟩)
    have hem : β*(eqv a:AlternatingSix.ShadowLocal.AutA6)=e (c.normalizerQuotientMap vN) := by
      change f iT*f aT=f (iT*aT)
      exact (map_mul f iT aT).symm
    rw [hord,orderOf_eq_prime_iff,and_iff_left hne,←hpow,hconj,hem]
    constructor
    · rintro ⟨ha,hz⟩
      refine ⟨ha,?_⟩
      by_contra hnat
      apply c.diagonal_not_z_fused_source e hM vN _ hnat hz.symm
      change orderOf (f v)=2
      rw [orderOf_injective f hf,←orderOf_coe]
      exact orderOf_eq_prime (hpow.mp ha) hne
    · rintro ⟨ha,hnat⟩
      refine ⟨ha,?_⟩
      exact (c.natural_inverter_z_fused_source e hM vN hvi
        ((orderOf_coe vN).symm.trans (orderOf_eq_prime (hpow.mp ha) hne)) hnat).symm
  let flatten :
      {a:BinaryConjugationSection.Inverting A (i:G) // IsConj c.z ((a.val:G)*(i:G))} ≃
      {a:A // (i:G)*a*(i:G)⁻¹=(a:G)⁻¹ ∧ IsConj c.z ((a:G)*i)} := {
    toFun a:=⟨a.val.val,a.val.property,a.property⟩
    invFun a:=⟨⟨a.val,a.property.1⟩,a.property.2⟩
    left_inv _:=rfl
    right_inv _:=rfl }
  let ecount : {a:A // (i:G)*a*(i:G)⁻¹=(a:G)⁻¹ ∧ IsConj c.z ((a:G)*i)} ≃
      {q:Q // orderOf (β*(q:AlternatingSix.ShadowLocal.AutA6))=2 ∧
        β*(q:AlternatingSix.ShadowLocal.AutA6)∈AlternatingSix.ShadowLocal.natural} :=
    eqv.toEquiv.subtypeEquiv hiff
  exact (Nat.card_congr (flatten.trans ecount)).trans hcount

end CFSG.Quasithin.ChapterJ.Centralizers.Choices

