module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.BinaryAlternatingSix
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.ModelConjugacyAbsolute
public import Theory.SpecificGroups.SymplecticFour.AbsoluteCentralizer
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.SymplecticFour.TransvectionSquares
public import Theory.Representation.InjectiveDescent

/-!
# Recognizing a binary symplectic overgroup of an A₆ socle

The degree-four A₆ representation theorem gives binary natural coordinates,
including its diagram twist. Absolute irreducibility rescales that intertwiner
to a symplectic conjugator. The conjugated socle is fixed pointwise by
Frobenius, and its trivial symplectic centralizer makes every normalizer fixed
as well. Thus the whole given overgroup lies in the binary coefficient group.

The supplied c₂ involution and the single A₆ involution class put every
normalizing transvection outside the socle. A₆ has order360 and the binary
coefficient group has order720, so the original overgroup is the whole
coefficient copy. The conclusion retains its original ambient embedding.

Source: Aschbacher--Smith G.4.1, printed p.342, the A₆ socle row, applied to
E.2.7 on pp.219--220. SourceAlternatingSixRecognized supplies all the geometric
and c₂ premises from the original local group.
-/

public noncomputable section
open Subgroup Representation
open scoped TensorProduct
namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.BinaryA6
open DiagramAutomorphisms DiagramAutomorphisms.FieldFixedResidual InvolutionTypes InvolutionCentralizers
variable {F:Type*} [Field F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

private def inclusion : Sp (ZMod 2) →* Sp F where
  toFun g := ⟨g.val.map (algebraMap (ZMod 2) F),SymplecticGroup.map_mem g.property _⟩
  map_one' := by apply Subtype.ext; exact map_one (algebraMap (ZMod 2) F).mapMatrix
  map_mul' g h := by apply Subtype.ext; exact Matrix.map_mul

private theorem inclusion_injective : Function.Injective (inclusion (F:=F)) := by
  intro g h he
  apply Subtype.ext
  exact Matrix.map_injective (algebraMap (ZMod 2) F).injective (congrArg Subtype.val he)

private theorem inclusion_range : (inclusion (F:=F)).range=
    (coefficientInclusion (algebraMap (ZMod 2) F).fieldRange).range := by
  let K := (algebraMap (ZMod 2) F).fieldRange
  let e := Binary.fieldEquivSp (algebraMap (ZMod 2) F).rangeRestrictFieldEquiv
  have he : inclusion (F:=F)=(coefficientInclusion K).comp e.toMonoidHom := by
    ext g i j
    simp only [MonoidHom.comp_apply,coefficientInclusion_apply,e]
    rfl
  rw [he,MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.surjective,
    ←MonoidHom.range_eq_map]

private theorem first_model_coordinates (g:alternatingGroup (Fin 6)) :
    mapCoefficients (algebraMap (ZMod 2) F) BinaryAlternatingSix.firstAlternating g=
      symplecticNatural 2 (inclusion (Binary.symmetricSixEquiv g.val)) := by
  apply LinearMap.toMatrix'.injective
  rw [mapCoefficients_toMatrix,Binary.symmetricSixEquiv_apply]
  change (LinearMap.toMatrix' (Theory.SpecificGroups.SymmetricSix.polarLinearMap g.val)).map
    (algebraMap (ZMod 2) F)=LinearMap.toMatrix'
      (Matrix.toLin' ((inclusion (Theory.SpecificGroups.SymmetricSix.polarRepresentation g.val)).val))
  rw [LinearMap.toMatrix'_toLin']
  rfl

private theorem normalizer_fixed {D:Type*} [Group D] (σ:MulAut D) (N:Subgroup D)
    (hN:N≤σ.fixedSubgroup) (hC:centralizer (N:Set D)=⊥) :
    normalizer (N:Set D)≤σ.fixedSubgroup := by
  intro g hg
  have hc:g⁻¹*σ g∈centralizer (N:Set D) := by
    apply mem_centralizer_iff.mpr
    intro n hn
    have hσn:σ n=n := (MulAut.mem_fixedSubgroup σ n).mp (hN hn)
    have hσgn:σ (g*n*g⁻¹)=g*n*g⁻¹ := (MulAut.mem_fixedSubgroup σ _).mp
      (hN ((mem_normalizer_iff.mp hg n).mp hn))
    rw [map_mul,map_mul,map_inv,hσn] at hσgn
    have he:σ g*n=(g*n*g⁻¹)*σ g := mul_inv_eq_iff_eq_mul.mp hσgn
    calc
      n*(g⁻¹*σ g)=g⁻¹*((g*n*g⁻¹)*σ g) := by group
      _ = g⁻¹*(σ g*n) := by rw [←he]
      _ = (g⁻¹*σ g)*n := by group
  have h1:g⁻¹*σ g=1 := by simpa only [hC,mem_bot] using hc
  apply (MulAut.mem_fixedSubgroup σ g).mpr
  exact (inv_mul_eq_one.mp h1).symm

variable [Finite F]

private theorem inclusion_fixed (g:Sp (ZMod 2)) :
    fieldAutomorphism (frobeniusEquiv F 2) (inclusion g)=inclusion (F:=F) g := by
  apply Subtype.ext
  ext i j
  change (algebraMap (ZMod 2) F (g.val i j))^2=algebraMap (ZMod 2) F (g.val i j)
  rw [←map_pow]
  congr 1
  exact (show ∀x:ZMod 2,x^2=x from by decide) (g.val i j)

private theorem fixed_le_inclusion :
    (fieldAutomorphism (frobeniusEquiv F 2)).fixedSubgroup≤(inclusion (F:=F)).range := by
  intro g hg
  rw [inclusion_range]
  apply (mem_coefficient_range_iff _ g).mpr
  intro i j
  have hs:(g.val i j)^2=g.val i j := congrArg (fun t:Sp F => t.val i j)
    ((MulAut.mem_fixedSubgroup _ _).mp hg)
  have hz:g.val i j=0 ∨ g.val i j=1 := by
    have hmul:g.val i j*(g.val i j-1)=0 := by
      rw [mul_sub,mul_one,←pow_two,hs,sub_self]
    exact (mul_eq_zero.mp hmul).imp_right sub_eq_zero.mp
  rcases hz with hz|hz
  · rw [hz]; exact Subfield.zero_mem _
  · rw [hz]; exact Subfield.one_mem _

/-- The actual irreducible A₆ matrix subgroup has symplectic coordinates
in the binary coefficient group. Both diagram-twisted natural models are
absorbed in the retained A₆ marking. -/
private theorem exists_binary_symplectic_coordinates (N:Subgroup (Sp F))
    (e:N≃*alternatingGroup (Fin 6))
    (hi:IsIrreducible ((symplecticNatural 2).comp N.subtype))
    (ha:IsAbsolutelyIrreducible ((symplecticNatural 2).comp N.subtype)) :
    ∃ e':N≃*alternatingGroup (Fin 6), ∃ g:Sp F,
      ∀ n:N, g*(n:Sp F)*g⁻¹=inclusion (Binary.symmetricSixEquiv (e' n).val) := by
  obtain ⟨A,hA⟩ := exists_alternatingSix_intertwiner N e hi
  obtain ⟨e',A,hA⟩ : ∃ e':N≃*alternatingGroup (Fin 6),
      ∃ A:Vector F≃ₗ[F]F ⊗[ZMod 2] Theory.SpecificGroups.SymmetricSix.NaturalModule,
        ∀n:N,∀v,A ((n:Sp F) • v)=extendScalars F BinaryAlternatingSix.firstAlternating (e' n) (A v) := by
    rcases hA with hA|hA
    · exact ⟨e,A,hA⟩
    · exact ⟨e.trans BinaryAlternatingSix.alternatingDiagramAut,A,hA⟩
  let E := extendScalarsMapCoefficientsEquiv (E:=F) BinaryAlternatingSix.firstAlternating
  let B := A.trans E.toLinearEquiv
  let j:N→*Sp F := inclusion.comp (Binary.symmetricSixEquiv.toMonoidHom.comp
    ((alternatingGroup (Fin 6)).subtype.comp e'.toMonoidHom))
  have hB:∀n:N,∀v,B ((n:Sp F) • v)=j n • B v := by
    intro n v
    change E (A ((n:Sp F) • v))=_
    rw [hA]
    have he := LinearMap.congr_fun (E.isIntertwining' (e' n)) (A v)
    change E (extendScalars F BinaryAlternatingSix.firstAlternating (e' n) (A v))=_ at he
    rw [first_model_coordinates] at he
    exact he
  obtain ⟨g,hg⟩ := exists_symplectic_intertwiner_of_absolutelyIrreducible N.subtype j ha B hB
  exact ⟨e',g,hg⟩

private theorem six_involution_cycleType (x:alternatingGroup (Fin 6)) (hx:orderOf x=2) :
    (x:Equiv.Perm (Fin 6)).cycleType={2,2} := by
  have ho:orderOf (x:Equiv.Perm (Fin 6))=2 := (orderOf_coe x).trans hx
  obtain ⟨k,hk⟩ := Equiv.Perm.cycleType_prime_order (ho ▸ Nat.prime_two)
  rw [ho] at hk
  have hb := (x:Equiv.Perm (Fin 6)).sum_cycleType_le
  rw [hk] at hb
  simp only [Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,Fintype.card_fin] at hb
  have hs := Equiv.Perm.mem_alternatingGroup.mp x.property
  rw [Equiv.Perm.sign_of_cycleType',hk] at hs
  have hkb:k≤2 := by omega
  have hk1:k=1 := by
    interval_cases k
    · norm_num at hs
    · rfl
    · norm_num at hs
  simpa [hk1] using hk

private theorem six_involutions_conjugate (x y:alternatingGroup (Fin 6))
    (hx:orderOf x=2) (hy:orderOf y=2) : IsConj x y := by
  apply alternatingGroup.isConj_of (Equiv.Perm.isConj_iff_cycleType_eq.mpr
    ((six_involution_cycleType x hx).trans (six_involution_cycleType y hy).symm))
  rw [←Equiv.Perm.sum_cycleType,six_involution_cycleType x hx]
  decide

omit [CharP F 2] [Finite F] in
private theorem not_isB1_mem_of_isC2 (N:Subgroup (Sp F))
    (e:N≃*alternatingGroup (Fin 6)) (hc2:∃i:N,IsC2 (i:Sp F))
    (t:Sp F) (ht:IsB1 t) : t∉N := by
  intro htn
  obtain ⟨i,hi⟩ := hc2
  let u:N := ⟨t,htn⟩
  have hui:orderOf (e u)=2 := (e.orderOf_eq u).trans ((orderOf_coe u).symm.trans ht.1)
  have hii:orderOf (e i)=2 := (e.orderOf_eq i).trans ((orderOf_coe i).symm.trans hi.1)
  have hconj:IsConj i u := by
    simpa only [MulEquiv.coe_toMonoidHom,MulEquiv.symm_apply_apply] using
      e.symm.toMonoidHom.map_isConj (six_involutions_conjugate (e i) (e u) hii hui)
  obtain ⟨g,hg⟩ := isConj_iff.mp hconj
  have he:(g:Sp F)*(i:Sp F)*(g:Sp F)⁻¹=t := congrArg Subtype.val hg
  have hc:IsC2 t := he ▸ (isC2_conj_iff (g:Sp F) (i:Sp F)).mpr hi
  have h1:=ht.2
  have h2:=hc.2.1
  omega

/-- An absolutely irreducible A₆ subgroup with a c₂ involution, normalized
by a transvection-containing overgroup, identifies that entire overgroup
with a conjugate of the binary coefficient symplectic group. -/
theorem coefficient_copy_of_alternatingSix_socle (H N:Subgroup (Sp F))
    (hNH:N≤H) (hHN:H≤normalizer (N:Set (Sp F)))
    (e:N≃*alternatingGroup (Fin 6))
    (hi:IsIrreducible ((symplecticNatural 2).comp N.subtype))
    (ha:IsAbsolutelyIrreducible ((symplecticNatural 2).comp N.subtype))
    (hc2:∃i:N,IsC2 (i:Sp F)) (ht:∃t∈H,IsB1 t) :
    ∃ K:Subfield F, Nat.card K=2 ∧ ∃ c:Sp F,
      H=(coefficientInclusion K).range.map (MulAut.conj c).toMonoidHom := by
  obtain ⟨e',g,hg⟩ := exists_binary_symplectic_coordinates N e hi ha
  let f := (MulAut.conj g).toMonoidHom
  let N' := N.map f
  let H' := H.map f
  let σ := fieldAutomorphism (frobeniusEquiv F 2)
  have hNfixed:N'≤σ.fixedSubgroup := by
    rintro x ⟨n,hn,rfl⟩
    apply (MulAut.mem_fixedSubgroup σ _).mpr
    change σ (g*n*g⁻¹)=g*n*g⁻¹
    rw [hg ⟨n,hn⟩]
    exact inclusion_fixed _
  have hC':centralizer (N':Set (Sp F))=⊥ := by
    apply le_bot_iff.mp
    intro z hz
    have hc:g⁻¹*z*g∈centralizer (N:Set (Sp F)) := by
      apply mem_centralizer_iff.mpr
      intro n hn
      have he := mem_centralizer_iff.mp hz (f n) (mem_map_of_mem f hn)
      change (g*n*g⁻¹)*z=z*(g*n*g⁻¹) at he
      have hm := congrArg (fun v:Sp F => g⁻¹*v*g) he
      simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left,inv_mul_cancel,mul_one] using hm
    have h1:g⁻¹*z*g=1 := by
      simpa only [centralizer_eq_bot_of_absolutelyIrreducible N ha,mem_bot] using hc
    change z=1
    have he := congrArg (fun v:Sp F => g*v*g⁻¹) h1
    simpa only [mul_assoc,mul_inv_cancel_left,inv_mul_cancel_left,mul_one,mul_inv_cancel] using he
  have hHbin:H'≤(inclusion (F:=F)).range := by
    apply (show H'≤normalizer (N':Set (Sp F)) from ?_).trans
      ((normalizer_fixed σ N' hNfixed hC').trans fixed_le_inclusion)
    have hmap := map_mono (f:=f) hHN
    rw [map_normalizer_eq_of_bijective N (MulAut.conj g).bijective] at hmap
    exact hmap
  have hNcard:Nat.card N=360 := (Nat.card_congr e.toEquiv).trans
    Theory.SpecificGroups.SymmetricSix.a6_order
  have hdiv:360∣Nat.card H := hNcard ▸ card_dvd_of_le hNH
  have hHgt:360<Nat.card H := by
    by_contra hh
    have he:N=H := eq_of_le_of_card_ge hNH (by omega)
    obtain ⟨t,htH,htB⟩ := ht
    exact not_isB1_mem_of_isC2 N e hc2 t htB (he.symm ▸ htH)
  have hbinCard:Nat.card (inclusion (F:=F)).range=720 :=
    (Nat.card_congr (MonoidHom.ofInjective (inclusion_injective (F:=F))).toEquiv).symm.trans
      Binary.card_sp_two
  have hHcard:Nat.card H'=Nat.card H := card_map_of_injective (MulAut.conj g).injective
  have hbin:H'=(inclusion (F:=F)).range := by
    apply eq_of_le_of_card_ge hHbin
    rw [hbinCard,hHcard]
    obtain ⟨k,hk⟩ := hdiv
    omega
  let K := (algebraMap (ZMod 2) F).fieldRange
  have hK:Nat.card K=2 := (Nat.card_congr (algebraMap (ZMod 2) F).rangeRestrictFieldEquiv.toEquiv).symm.trans
    (Nat.card_zmod 2)
  refine ⟨K,hK,g⁻¹,?_⟩
  rw [inclusion_range] at hbin
  have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hbin
  have hid: (MulAut.conj g⁻¹).toMonoidHom.comp f=MonoidHom.id (Sp F) := by
    ext x
    simp [f,MulAut.conj_apply,mul_assoc]
  simpa only [H',map_map,hid,map_id] using he

end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.BinaryA6
