module

public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceTripleModule
public import Theory.Representation.SL2.EightRegularKernelSplitting
public import Theory.GroupTheory.CentralExtensionSections
public import Theory.SpecificGroups.PSL2.EightCentralCovers

/-!
# Splitting the original full eight-field endpoint

The original core quotient has its regular binary Sylow restriction.
Its canonical conjugation coordinates split H/Z(Q) over Q/Z(Q). Lifting
that complement gives a central extension of PSL₂(8); its derived cover
has trivial kernel, giving a section of the prescribed original quotient.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open Matrix.SpecialLinearGroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCoreSplitting
variable {G : Type*} [Group G] [Finite G]

private theorem section_of_triple_core (P : Subgroup G)
    (ε : (P ⧸ pCore 2 P) ≃* Theory.PSL2.BinaryGroup 3)
    (hs : SourceTripleModule.HasTripleExtraspecialCore P ε) :
    ∃ s : Theory.PSL2.BinaryGroup 3 →* P,
      (ε.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P))).comp s =
        MonoidHom.id _ := by
  classical
  obtain ⟨hex,C,hC,hN,hel,ρ,d,hcoord,hirr,hcard,_⟩ := hs
  let _ := hN
  let _ := hel
  let _ := hirr
  let _ := hex
  let Q := P.pCoreIn 2
  have hQP : Q ≤ P := pCoreIn_le 2 P
  have hCQ : C ≤ Q := by rw [hC]; exact inf_le_left
  have hCP : C ≤ P := hCQ.trans hQP
  have hCN : P ≤ normalizer C := by
    rw [hC]
    exact normalizes_centerIn d.normalized
  let : (C.subgroupOf P).Normal := (normal_subgroupOf_iff_le_normalizer hCP).mpr hCN
  let E := P ⧸ C.subgroupOf P
  let π : P →* E := QuotientGroup.mk' (C.subgroupOf P)
  let eSL := ε.trans (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).symm
  let q₀ : P →* SL(2,GaloisField 2 3) := eSL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P))
  have hk₀ : q₀.ker = pCore 2 P := by
    rw [MonoidHom.ker_comp_of_injective _ _ eSL.injective,QuotientGroup.ker_mk']
  have hQmem (x : P) : q₀ x=1 ↔ (x:G)∈Q := by
    change x∈q₀.ker ↔ x∈Q.subgroupOf P
    rw [hk₀]
    exact Iff.of_eq (congrArg (fun N : Subgroup P => x∈N)
      (comap_map_eq_self_of_injective P.subtype_injective (pCore 2 P))).symm
  have hCkill : C.subgroupOf P ≤ q₀.ker := fun x hx => (hQmem x).mpr (hCQ hx)
  let q : E →* SL(2,GaloisField 2 3) := QuotientGroup.lift (C.subgroupOf P) q₀ hCkill
  have hq : Function.Surjective q := QuotientGroup.lift_surjective_of_surjective _ q₀
    (eSL.surjective.comp (QuotientGroup.mk'_surjective _)) hCkill
  let f : Q →* q.ker :=
    (π.comp (inclusion hQP)).codRestrict q.ker (fun x => (hQmem (inclusion hQP x)).mpr x.property)
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective (C.subgroupOf P) (v:E)
    have hxQ : (x:G)∈Q := (hQmem x).mp (by
      change q (π x)=1
      rw [hx]
      exact v.property)
    exact ⟨⟨x,hxQ⟩,Subtype.ext hx⟩
  have hfk : f.ker = C.subgroupOf Q := by
    ext x
    change (⟨π (inclusion hQP x),_⟩ : q.ker)=1 ↔ (x:G)∈C
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff (N := C.subgroupOf P) (inclusion hQP x)
  let ek : (Q ⧸ C.subgroupOf Q) ≃* q.ker :=
    (QuotientGroup.quotientMulEquivOfEq hfk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hek (x : Q) : ek (QuotientGroup.mk' (C.subgroupOf Q) x)=f x := by
    change (QuotientGroup.quotientKerEquivOfSurjective f hf)
      ((QuotientGroup.quotientMulEquivOfEq hfk.symm) (QuotientGroup.mk x))=f x
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  let V := Additive (Q ⧸ C.subgroupOf Q)
  let : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  let σ : Representation (ZMod 2) SL(2,GaloisField 2 3) V := ρ.comp eSL.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff eSL.symm.toMonoidHom eSL.symm.surjective ρ).mpr hirr
  have hd : Module.finrank (ZMod 2) V=8 := by
    have hc := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=V)
    rw [Nat.card_zmod] at hc
    exact Nat.pow_right_injective (by decide : 1<2) (hc.symm.trans hcard : 2^Module.finrank (ZMod 2) V=2^8)
  let U := upperUnipotent (GaloisField 2 3)
  obtain ⟨r,hr⟩ := Representation.SL2.BinarySmall.eight_irreducible_upper_regular σ hd
  let em : q.ker ≃* (U → Multiplicative (ZMod 2)) := ek.symm.trans
    (r.toAddEquiv.toMultiplicative.trans (MulEquiv.funMultiplicative U (ZMod 2)))
  have hact (g : P) (v : q.ker) :
      Additive.ofMul (ek.symm (MulAut.conjNormal (π g) v)) =
        σ (q₀ g) (Additive.ofMul (ek.symm v)) := by
    obtain ⟨x,rfl⟩ := hf v
    let y : Q := ⟨(g:G)*x*(g:G)⁻¹,
      (mem_normalizer_iff.mp (d.normalized g.property) x).mp x.property⟩
    have hy : MulAut.conjNormal (π g) (f x)=f y := by
      apply Subtype.ext
      change π g * π (inclusion hQP x) * (π g)⁻¹=π (inclusion hQP y)
      rw [← map_inv,← map_mul,← map_mul]
      rfl
    rw [hy,← hek,← hek,ek.symm_apply_apply,ek.symm_apply_apply]
    have hh := d.equivariant g x
    rw [hcoord,hcoord] at hh
    simpa only [σ,q₀,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,eSL.symm_apply_apply] using hh
  obtain ⟨L,hL⟩ := exists_complement_of_regular_preimage q hq U em (by
    intro g v x
    obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective (C.subgroupOf P) (g:E)
    change Multiplicative.ofAdd (r (Additive.ofMul (ek.symm (MulAut.conjNormal (g:E) v))) x)=_
    have hh := hact a v
    have hqa : q₀ a=q (g:E) := congrArg q ha
    rw [ha,hqa] at hh
    rw [hh]
    exact congrArg Multiplicative.ofAdd (hr ⟨q (g:E),g.property⟩
      (Additive.ofMul (ek.symm v)) x)) (by
    have hc : Nat.card q.ker=256 := (Nat.card_congr ek.toEquiv).symm.trans hcard
    rw [hc,U.index_comap_of_surjective hq]
    exact (Nat.Prime.coprime_pow_of_not_dvd Nat.prime_two
      (upperUnipotentSylow (GaloisField 2 3) 2).not_dvd_index (m:=8)).symm)
  let R := L.comap π
  let j : R →* Theory.PSL2.BinaryGroup 3 :=
    (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).toMonoidHom.comp (q₀.comp R.subtype)
  have hj : Function.Surjective j := by
    intro b
    obtain ⟨v,hv⟩ := hq ((Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).symm b)
    obtain ⟨⟨k,l⟩,he⟩ := hL.2 v
    obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective (C.subgroupOf P) (l:E)
    refine ⟨⟨a,by change π a∈L; rw [ha]; exact l.property⟩,?_⟩
    change (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)) (q (π a))=b
    rw [ha]
    have hqv : q (l:E)=q v := by rw [← he,map_mul,show q (k:E)=1 from k.property,one_mul]
    rw [hqv,hv,MulEquiv.apply_symm_apply]
  have hCC : C ≤ centralizer (P:Set G) := by
    rw [hC]
    apply centerIn_centralizes_of_card_two _ d.normalized
    rw [centerIn_eq_map_center,card_map_of_injective Q.subtype_injective]
    exact IsExtraspecial.center_order_p 2 Q
  have hjc : j.ker ≤ center R := by
    intro a ha
    have hqa : q₀ (a:P)=1 := (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).injective
      (ha.trans (map_one _).symm)
    have hπa : π (a:P)=1 := hL.disjoint.le_bot ⟨hqa,a.property⟩
    have hCa : ((a:P):G)∈C := (QuotientGroup.eq_one_iff (N:=C.subgroupOf P) (a:P)).mp hπa
    apply Subgroup.mem_center_iff.mpr
    intro b
    apply Subtype.ext
    apply Subtype.ext
    exact hCC hCa (b:P) (b:P).property
  let : Group.IsPerfect (Theory.PSL2.BinaryGroup 3) :=
    GorensteinWalter.psl2_isPerfect_of_card_gt_three (GaloisField 2 3)
      (by rw [GaloisField.card 2 3 (by decide)]; decide)
  let cv := CentralExtension.derivedCover j hj hjc
  let ec := Theory.SpecificGroups.PSL2Eight.coverEquiv cv
  let s := R.subtype.comp ((_root_.commutator R).subtype.comp ec.symm.toMonoidHom)
  refine ⟨s,?_⟩
  apply MonoidHom.ext
  intro b
  have hh := ec.apply_symm_apply b
  change Theory.SpecificGroups.PSL2Eight.coverEquiv cv (ec.symm b)=b at hh
  rw [Theory.SpecificGroups.PSL2Eight.coverEquiv_apply] at hh
  simpa only [cv,CentralExtension.derivedCover,j,MonoidHom.comp_apply,q₀,eSL,s,
    MonoidHom.id_apply,MulEquiv.coe_toMonoidHom,MulEquiv.trans_apply,MulEquiv.apply_symm_apply] using hh

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR

/-- The prescribed original full quotient of H has an actual homomorphic section. -/
theorem source_first_quotient_section :
    ∃ s : Theory.PSL2.BinaryGroup 3 →* H,
      ((sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR).toMonoidHom.comp
        (QuotientGroup.mk' (pCore 2 H))).comp s = MonoidHom.id _ :=
  section_of_triple_core H _ (SourceTripleModule.source_core_triple hG T hempty hM hu hmany hcard e H hH eR)

/-- The full original two-core has a complement whose isomorphism to PSL₂(8)
is exactly the restriction of the prescribed source quotient map. -/
theorem source_first_core_complement :
    ∃ R : Subgroup H, (pCore 2 H).IsComplement' R ∧
      ∃ f : R ≃* Theory.PSL2.BinaryGroup 3,
        ∀ r : R, f r = (sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR)
          (QuotientGroup.mk' (pCore 2 H) (r:H)) := by
  let ε := sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR
  let q := ε.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  obtain ⟨s,hs⟩ := source_first_quotient_section hG T hempty hM hu hmany hcard e H hH eR
  have hqs (x : Theory.PSL2.BinaryGroup 3) : q (s x)=x := DFunLike.congr_fun hs x
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ ε.injective,QuotientGroup.ker_mk']
  have hcomp : q.ker.IsComplement' s.range := by
    apply isComplement'_of_disjoint_and_mul_eq_univ
    · apply disjoint_def.mpr
      intro x hx hxs
      obtain ⟨y,rfl⟩ := hxs
      have hy : y=1 := (hqs y).symm.trans hx
      rw [hy,map_one]
    · apply Set.eq_univ_iff_forall.mpr
      intro x
      refine ⟨x*(s (q x))⁻¹,?_,s (q x),⟨q x,rfl⟩,?_⟩
      · change q (x*(s (q x))⁻¹)=1
        rw [map_mul,map_inv,hqs,mul_inv_cancel]
      · exact inv_mul_cancel_right _ _
  let f := q.comp s.range.subtype
  have hfi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    exact Subtype.ext (hcomp.disjoint.le_bot ⟨hx,x.property⟩)
  have hfs : Function.Surjective f := fun x => ⟨⟨s x,⟨x,rfl⟩⟩,hqs x⟩
  exact ⟨s.range,hk ▸ hcomp,MulEquiv.ofBijective f ⟨hfi,hfs⟩,fun _ => rfl⟩

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCoreSplitting
