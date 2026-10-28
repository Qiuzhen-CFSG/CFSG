module
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.HigherRecognition.EvenTwisted.Triality.Outer
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.HigherRecognition.EvenTwisted.Triality.Inner.Complete
public import Theory.Representation.Triality.OuterDisplacement.SchurOperator
public import Theory.Representation.CharacteristicTwoIrreducibleRank.InnerInvolutions
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.Representation.Triality.OuterDisplacement.ConcretePairedTensorSource
public import Theory.SpecificGroups.Triality.StandardTwoRank.Derived
/-!
# Full original triality outer-involution bound

The actual component center is killed by faithful irreducibility, giving the
native triality marking. An outer ambient involution induces a noninner native
automorphism. If it centralizes the component commutant, pass its literal
operator to the Schur field and algebraic closure, invoke the genuine native
paired-tensor estimate, and descend the ratio. Otherwise the existing Schur
commutator argument gives the stronger half-dimension estimate.
All source, geometry and representation inputs are discharged.
Source: Guralnick--Malle II, Section 3.5 and Lemma 8.6.
-/

public section
open scoped MonoidAlgebra TensorProduct
open Theory.AlgebraicGroup Representation Subgroup
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.Triality
universe u v
open _root_.Triality.Standard _root_.Triality.OuterDisplacement

variable {H : Type u} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
  [Theory.GroupTheory.IsQuasisimple N]

theorem source_ratio_of_centralizesCommutant (n : ℕ) (hn : 0<n)
    (hmodel : IsTrialityGroupAt (2^n) (N ⧸ center N))
    {E W : Type v} [Field E] [Finite E] [Algebra (ZMod 2) E] [CharP E 2]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (σ : Representation E H W) [IsIrreducible (σ.comp N.subtype)] (hf : Function.Injective σ)
    (t : H) (ht : t∉N) (ht2 : t^2=1) (hc : CentralizesCommutant σ N t) :
    7*Module.finrank E W ≤16*Module.finrank E (LinearMap.range (σ t-LinearMap.id)) := by
  let τ : Representation E N W := σ.comp N.subtype
  have hz := _root_.Triality.InnerDisplacement.center_eq_bot_of_twoGroup τ
    (hf.comp Subtype.val_injective)
    (_root_.Triality.InnerDisplacement.PrimeToTwoCovers.center_isTwoGroup n hn hmodel)
  obtain ⟨e0⟩ := (isTrialityGroupAt_binary_iff _ n hn).mp hmodel
  let e : N ≃* BinaryCarrier n hn :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.trans e0
  let tn : normalizer (N : Set H) := ⟨t, by rw [normalizer_eq_top]; trivial⟩
  let a : MulAut N := N.normalizerMonoidHom tn
  let α := MulAut.congr e a
  have ha : a^2=1 := by
    rw [←map_pow,show tn^2=1 from Subtype.ext ht2,map_one]
  have hα : α^2=1 := by
    change (MulAut.congr e a)^2=1
    rw [←map_pow,ha,map_one]
  have hnon : ¬∃x,α=MulAut.conj x := by
    intro hh
    apply ht
    exact CharacteristicTwoIrreducible.involution_mem_of_inner σ N hf tn ht2
      ((MulAut.congr_inner_iff e a).mp hh)
  let F := Module.End E[N] τ.asModule
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap E F).injective 2
  let : Finite τ.asModule := Module.finite_of_finite E
  let : FiniteDimensional F τ.asModule := Module.Finite.of_finite
  let k := AlgebraicClosure F
  let ρ := (τ.endFieldRep).comp e.symm.toMonoidHom
  let ρk := Representation.extendScalars k ρ
  let T := componentSchurOperator σ N t hc
  have hT : T*T=1 := SchurOperator.linear_square τ (σ t) hc (by
    rw [←map_mul,←pow_two,ht2,map_one])
  have he (g : N) (v : W) : σ t (τ g v)=τ (a g) (σ t v) := by
    change σ t (σ (g : H) v)=σ (t*(g:H)*t⁻¹) (σ t v)
    simp only [←Module.End.mul_apply,←map_mul]
    simp only [mul_assoc,inv_mul_cancel,mul_one]
  have hTS (g : BinaryCarrier n hn) (v : τ.asModule) : T (ρ g v) = ρ (α g) (T v) := by
    have h := SchurOperator.linear_intertwines τ (σ t) hc a he (e.symm g) v
    change T (τ.endFieldRep (e.symm g) v) =
      τ.endFieldRep (e.symm (e (a (e.symm g)))) (T v)
    rw [e.symm_apply_apply]
    exact h
  have hiF : IsAbsolutelyIrreducible τ.endFieldRep := endFieldRep_isAbsolutelyIrreducible τ
  let : IsAbsolutelyIrreducible τ.endFieldRep := hiF
  let : IsIrreducible (Representation.extendScalars k τ.endFieldRep) :=
    IsAbsolutelyIrreducible.irreducible_of_extension τ.endFieldRep k
  have hir : IsIrreducible ρk :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      (Representation.extendScalars k τ.endFieldRep)).mpr inferInstance
  have hfr : Function.Injective ρk := (extendScalars_faithful_iff k ρ).mp
    (((endFieldRep_injective_iff τ).mpr (hf.comp Subtype.val_injective)).comp e.symm.injective)
  apply displacement_ratio_of_absolute_schur σ N t hc k
  let : IsIrreducible ρk := hir
  apply _root_.Triality.OuterDisplacement.ConcretePairedTensorSource.native_outer_involution_ratio
    k n hn ρk hfr α hα (fun hh => hnon (by
      obtain ⟨x,hx⟩ := hh
      exact ⟨x,hx.symm⟩)) (T.baseChange k)
  · rw [←LinearMap.baseChange_mul,hT,LinearMap.baseChange_one]
  · intro g v
    have heq : T * ρ g=ρ (α g)*T := LinearMap.ext (hTS g)
    have hh := congrArg (LinearMap.baseChange k) heq
    rw [LinearMap.baseChange_mul,LinearMap.baseChange_mul] at hh
    exact LinearMap.congr_fun hh v

/-- The full original ambient bound; no additional representation input remains. -/
theorem outerInvolutionBound_source (n : ℕ) (hn : 0<n)
    (hmodel : IsTrialityGroupAt (2^n) (N ⧸ center N)) :
    OuterInvolutionBound.{u,v} H N n := by
  classical
  intro E W _ _ _ _ _ _ _ σ _ hir hf t ht ht2
  let : IsIrreducible (σ.comp N.subtype) := hir
  by_cases hc : CentralizesCommutant σ N t
  · exact displacement_gt_of_ratio N σ hf n hn hmodel t
      (source_ratio_of_centralizesCommutant N n hn hmodel σ hf t ht ht2 hc)
  · exact displacement_gt_of_not_centralizesCommutant N σ hf n hn hmodel t hc

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.Triality
