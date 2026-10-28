module

public import Theory.Representation.G2BinaryNondegeneratePlane.Second
public import Mathlib.GroupTheory.NoncommCoprod
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# The actual nondegenerate-plane stabilizer in G₂(2)

The pointwise stabilizer lifts from the quotient six-space to the octonions:
preservation of the norm kills the possible scalar error. It is the literal
opposite-pair SL₂. The second commuting SL₂ acts as every invertible binary
matrix on the plane. Factoring that action leaves the pointwise stabilizer,
so the full setwise stabilizer is exactly S₃ × S₃.

Source: Aschbacher–Smith, Lemma 13.3.12, printed p.889.
-/

@[expose] public noncomputable section
open Atlas.SplitOctonion Module Submodule Matrix
open scoped MatrixGroups
namespace Atlas.G2.Natural.BinaryNondegeneratePlane
open Atlas.G2.Restricted.NaturalCoordinates Representation.BinaryOffender

theorem rho_injective : Function.Injective rho := by
  intro g h hgh
  apply Natural.action_injective K
  apply LinearMap.ext
  intro x
  apply (equiv K).injective
  have he := LinearMap.congr_fun hgh (equiv K x)
  change equiv K (Natural.action K g ((equiv K).symm (equiv K x))) =
    equiv K (Natural.action K h ((equiv K).symm (equiv K x))) at he
  simpa only [LinearEquiv.symm_apply_apply] using he

theorem form_invariant (g : Model K) (v w : W) :
    form (rho g v) (rho g w)=form v w := by
  change InvariantPolar.form K (Natural.action K g ((equiv K).symm v))
    (Natural.action K g ((equiv K).symm w)) = _
  exact InvariantPolar.form_invariant K g _ _

theorem firstHom_action (M : SL(2,K)) (v : W) :
    rho (PairStabilizer.blockHom M) v=![v 0,
      M.val 0 0*v 1+M.val 0 1*v 2,M.val 1 0*v 1+M.val 1 1*v 2,
      M.val 0 0*v 3+M.val 0 1*v 4,M.val 1 0*v 3+M.val 1 1*v 4,v 5] := by
  ext i
  fin_cases i <;> simp [action_apply,PairStabilizer.blockHom,PairStabilizer.blockEquiv,
    PairStabilizer.blockLinear,Atlas.G2.Restricted.NaturalCoordinates.projection,
    representative,traceZeroAction_val,sub_eq_add_neg,CharTwo.neg_eq]

theorem factors_commute (M N : SL(2,K)) :
    Commute (PairStabilizer.blockHom M) (secondHom N) := by
  apply rho_injective
  apply LinearMap.ext
  intro v
  ext i
  simp only [map_mul,Module.End.mul_apply,firstHom_action,secondHom_action]
  fin_cases i <;> simp <;> ring

private theorem fixes_basis_of_fixes_quotient (g : Model K) (i : Fin 8)
    (hi : i≠3) (hi' : i≠4)
    (hx : rho g (Atlas.G2.Restricted.NaturalCoordinates.projection K
      ⟨basisVector i,by simp [mem_traceZero,SplitOctonion.trace,basisVector,Ne.symm hi,Ne.symm hi']⟩)=
      Atlas.G2.Restricted.NaturalCoordinates.projection K
      ⟨basisVector i,by simp [mem_traceZero,SplitOctonion.trace,basisVector,Ne.symm hi,Ne.symm hi']⟩) :
    g.val (basisVector i)=basisVector i := by
  have ht : SplitOctonion.trace (basisVector i : Carrier K)=0 := by
    simp [SplitOctonion.trace,basisVector,Ne.symm hi,Ne.symm hi']
  have he : Natural.action K g (mk K ⟨basisVector i,ht⟩)=mk K ⟨basisVector i,ht⟩ := by
    apply (equiv K).injective
    change rho g (equiv K (mk K ⟨basisVector i,ht⟩))=equiv K (mk K ⟨basisVector i,ht⟩) at hx
    change equiv K (Natural.action K g ((equiv K).symm (equiv K _)))=_ at hx
    simpa only [LinearEquiv.symm_apply_apply] using hx
  obtain ⟨r,hr⟩ := (mk_eq_mk_iff K _ _).mp he
  change r • unit=g.val (basisVector i)-basisVector i at hr
  have hv : g.val (basisVector i)=r • unit+basisVector i := (eq_sub_iff_add_eq.mp hr).symm
  have hn := automorphism_norm g (basisVector i)
  rw [hv] at hn
  have hr0 : r=0 := by
    clear hx he ht hv hr
    fin_cases i <;> simp_all [SplitOctonion.norm,unit,basisVector]
  simpa [hr0] using hv

theorem pointwise_plane_eq_pair : subspaceKernel rho plane ⊤=PairStabilizer.fixingPair := by
  ext g
  constructor
  · rintro ⟨_,hg⟩
    constructor
    · exact fixes_basis_of_fixes_quotient g 0 (by decide) (by decide)
        (hg firstVector (subset_span (by simp)))
    · exact fixes_basis_of_fixes_quotient g 7 (by decide) (by decide)
        (hg secondVector (subset_span (by simp)))
  · intro hg
    obtain ⟨M,hM⟩ := PairStabilizer.fixingPairEquivSL2.symm.surjective ⟨g,hg⟩
    have he : PairStabilizer.blockHom M=g := congrArg Subtype.val hM
    refine ⟨Subgroup.mem_top _,?_⟩
    intro v hv
    rw [←he,firstHom_action]
    have h := (mem_plane v).mp hv
    ext i
    fin_cases i <;> simp [h.1,h.2.1,h.2.2.1,h.2.2.2]

theorem pointwise_plane_equiv_s3 : Nonempty (subspaceKernel rho plane ⊤ ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  exact ⟨(MulEquiv.subgroupCongr pointwise_plane_eq_pair).trans
    (PairStabilizer.fixingPairEquivSL2.trans e)⟩

private theorem second_preserves_plane (M : SL(2,K)) (v : W) (hv : v∈plane) :
    rho (secondHom M) v∈plane := by
  have h := (mem_plane v).mp hv
  rw [secondHom_action,mem_plane]
  simp [h.1,h.2.1,h.2.2.1,h.2.2.2]

theorem second_mem_stabilizer (M : SL(2,K)) : secondHom M∈subspaceStabilizer rho plane := by
  intro v
  constructor
  · intro hv
    have hi := second_preserves_plane M⁻¹ _ hv
    simpa only [map_inv,← Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,
      Module.End.one_apply] using hi
  · exact second_preserves_plane M v

theorem first_fixes_plane (M : SL(2,K)) (v : W) (hv : v∈plane) :
    rho (PairStabilizer.blockHom M) v=v := by
  have h := (mem_plane v).mp hv
  rw [firstHom_action]
  ext i
  fin_cases i <;> simp [h.1,h.2.1,h.2.2.1,h.2.2.2]

theorem first_mem_stabilizer (M : SL(2,K)) :
    PairStabilizer.blockHom M∈subspaceStabilizer rho plane := by
  intro v
  constructor
  · intro hv
    have hi := first_fixes_plane M⁻¹ _ hv
    have he : rho (PairStabilizer.blockHom M⁻¹) (rho (PairStabilizer.blockHom M) v)=v := by
      simp only [← Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
    rw [he] at hi
    exact hi.symm ▸ hv
  · intro hv
    rwa [first_fixes_plane M v hv]

def productHom : (SL(2,K)×SL(2,K)) →* Model K :=
  MonoidHom.noncommCoprod PairStabilizer.blockHom secondHom factors_commute

@[simp] theorem productHom_apply (p : SL(2,K)×SL(2,K)) :
    productHom p=PairStabilizer.blockHom p.1*secondHom p.2 := rfl

private theorem second_trivial_of_product_one (M N : SL(2,K))
    (h : productHom (M,N)=1) : N=1 := by
  have h0 := congrArg (fun g => rho g firstVector) h
  have h5 := congrArg (fun g => rho g secondVector) h
  simp only [productHom_apply,map_mul,Module.End.mul_apply,firstHom_action,
    secondHom_action,map_one,Module.End.one_apply] at h0 h5
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [firstVector,secondVector] using congrFun h0 0
  · simpa [firstVector,secondVector] using congrFun h5 0
  · simpa [firstVector,secondVector] using congrFun h0 5
  · simpa [firstVector,secondVector] using congrFun h5 5

theorem productHom_injective : Function.Injective productHom := by
  apply productHom.ker_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  rintro ⟨M,N⟩ h
  change productHom (M,N)=1 at h
  have hN := second_trivial_of_product_one M N h
  subst N
  have hM : M=1 := PairStabilizer.blockToPair_injective (show PairStabilizer.blockToPair M=PairStabilizer.blockToPair 1 from Subtype.ext (by
      change PairStabilizer.blockHom M=PairStabilizer.blockHom 1
      simpa only [productHom_apply,map_one,mul_one] using h))
  simp [hM]

private theorem exists_product_of_stabilizes (g : Model K)
    (hg : g∈subspaceStabilizer rho plane) : ∃M N : SL(2,K),productHom (M,N)=g := by
  let a := rho g firstVector
  let b := rho g secondVector
  have ha : a∈plane := (hg firstVector).mpr (subset_span (by simp))
  have hb : b∈plane := (hg secondVector).mpr (subset_span (by simp))
  have ha' := (mem_plane a).mp ha
  have hb' := (mem_plane b).mp hb
  have hpair : form a b=1 := (form_invariant g _ _).trans form_first_second
  let N : SL(2,K) := ⟨!![a 0,b 0;a 5,b 5],by
    simpa [Matrix.det_fin_two,form_apply,ha'.1,ha'.2.1,ha'.2.2.1,ha'.2.2.2,
      sub_eq_add_neg,CharTwo.neg_eq,mul_comm] using hpair⟩
  have h0 : rho (secondHom N) firstVector=a := by
    rw [secondHom_action]
    ext i
    fin_cases i <;> simp [N,firstVector,ha'.1,ha'.2.1,ha'.2.2.1,ha'.2.2.2]
  have h5 : rho (secondHom N) secondVector=b := by
    rw [secondHom_action]
    ext i
    fin_cases i <;> simp [N,secondVector,hb'.1,hb'.2.1,hb'.2.2.1,hb'.2.2.2]
  let k := (secondHom N)⁻¹*g
  have hk0 : rho k firstVector=firstVector := by
    change rho ((secondHom N)⁻¹*g) firstVector=_
    rw [map_mul,Module.End.mul_apply,show rho g firstVector=a from rfl,←h0]
    simp only [← Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  have hk5 : rho k secondVector=secondVector := by
    change rho ((secondHom N)⁻¹*g) secondVector=_
    rw [map_mul,Module.End.mul_apply,show rho g secondVector=b from rfl,←h5]
    simp only [← Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  have hk : k∈PairStabilizer.fixingPair := by
    rw [←pointwise_plane_eq_pair]
    refine ⟨Subgroup.mem_top _,?_⟩
    intro v hv
    obtain ⟨r,s,rfl⟩ := mem_span_pair.mp hv
    simp only [map_add,map_smul,hk0,hk5]
  let M := PairStabilizer.fixingPairEquivSL2 ⟨k,hk⟩
  have hM : PairStabilizer.blockHom M=k :=
    congrArg Subtype.val (PairStabilizer.fixingPairEquivSL2.symm_apply_apply ⟨k,hk⟩)
  refine ⟨M,N,?_⟩
  rw [productHom_apply,(factors_commute M N).eq,hM]
  exact mul_inv_cancel_left _ _

theorem productHom_range : productHom.range=subspaceStabilizer rho plane := by
  apply le_antisymm
  · rintro g ⟨⟨M,N⟩,rfl⟩
    rw [productHom_apply]
    exact (subspaceStabilizer rho plane).mul_mem (first_mem_stabilizer M) (second_mem_stabilizer N)
  · intro g hg
    obtain ⟨M,N,h⟩ := exists_product_of_stabilizes g hg
    exact ⟨(M,N),h⟩

noncomputable def stabilizerEquivProduct : subspaceStabilizer rho plane ≃* (SL(2,K)×SL(2,K)) :=
  (MulEquiv.subgroupCongr productHom_range).symm.trans
    (MonoidHom.ofInjective productHom_injective).symm

theorem stabilizer_equiv_s3_product :
    Nonempty (subspaceStabilizer rho plane ≃* (Equiv.Perm (Fin 3)×Equiv.Perm (Fin 3))) := by
  obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  exact ⟨stabilizerEquivProduct.trans (e.prodCongr e)⟩
end Atlas.G2.Natural.BinaryNondegeneratePlane
