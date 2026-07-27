import Submission.ZStar.IsotypicLattice
import Submission.ZStar.NagaoPrincipalRange
import Submission.ZStar.NagaoTrace
import Submission.ZStar.CanonicalLocalCoreSupportScratch
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
# The characterwise Nagao bridge

This file combines the denominator-cleared isotypic lattice with the
representation-level Nagao range.  The block-theoretic hypothesis is stated
explicitly as the principal Brauer equality; no local support or section
invariance is assumed.
-/

noncomputable section

open scoped BigOperators

namespace Submission.ZStar
namespace CharacterwiseNagao

open PrincipalBlockConstruction

universe u

attribute [local instance] Fintype.ofFinite

private instance principalPrime_isPrime
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) : d.primeIdeal.IsPrime :=
  d.primeIdeal_maximal.isPrime

private instance principalPrime_isMaximal
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) : d.primeIdeal.IsMaximal :=
  d.primeIdeal_maximal

/-- The regular right-ideal action really is left multiplication by the
corresponding group-algebra element. -/
theorem rightIdealRepresentation_asAlgebraHom_apply
    {R : Type*} {G : Type*} [CommRing R] [Group G]
    (q a : MonoidAlgebra R G)
    (x : CentralIdempotentSupport.rightIdeal R q) :
    ((CentralIdempotentSupport.rightIdealRepresentation R q).asAlgebraHom a x :
        MonoidAlgebra R G) =
      a * (x : MonoidAlgebra R G) := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
      rw [map_add, LinearMap.add_apply]
      change
        ((CentralIdempotentSupport.rightIdealRepresentation R q).asAlgebraHom a x :
            MonoidAlgebra R G) +
          ((CentralIdempotentSupport.rightIdealRepresentation R q).asAlgebraHom b x :
            MonoidAlgebra R G) =
          (a + b) * (x : MonoidAlgebra R G)
      rw [ha, hb, add_mul]
  | single g r =>
      rw [show (MonoidAlgebra.single g r : MonoidAlgebra R G) =
        r • MonoidAlgebra.single g 1 by simp, map_smul,
        Representation.asAlgebraHom_single_one]
      change r • (MonoidAlgebra.of R G g * (x : MonoidAlgebra R G)) =
        (r • MonoidAlgebra.of R G g) * (x : MonoidAlgebra R G)
      exact (Algebra.smul_mul_assoc r _ _).symm

theorem rightIdealRepresentation_asAlgebraHom
    {R : Type*} {G : Type*} [CommRing R] [Group G]
    (q a : MonoidAlgebra R G) :
    (CentralIdempotentSupport.rightIdealRepresentation R q).asAlgebraHom a =
      IsotypicLattice.rightIdealLeftMul q a := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact rightIdealRepresentation_asAlgebraHom_apply q a x

/-- In every representation, the Nagao complement commutes with the action
of every element of the involution centralizer. -/
theorem principalComplement_action_commutes_centralizer
    {G : Type u} {V : Type*} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G)
    [AddCommGroup V] [Module (Localization.AtPrime d.primeIdeal) V]
    (rho : Representation (Localization.AtPrime d.primeIdeal) G V)
    (z : G) (x : Subgroup.centralizer ({z} : Set G)) :
    Commute (rho.asAlgebraHom (NagaoComplement.principalComplement d z))
      (rho (x : G)) := by
  let R := Localization.AtPrime d.primeIdeal
  let H := Subgroup.centralizer ({z} : Set G)
  let e : MonoidAlgebra R G :=
    BlockOrthogonality.localizedPrincipalBlockElement d
  let b : MonoidAlgebra R H :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization d H
  let B : MonoidAlgebra R G := NagaoComplement.centralizerSubtypeMap z b
  let X : MonoidAlgebra R G := MonoidAlgebra.of R G (x : G)
  have he : Commute e X :=
    (Semigroup.mem_center_iff.mp
      (BlockOrthogonality.localizedPrincipalBlockElement_mem_center d) X).symm
  have hb : Commute b (MonoidAlgebra.of R H x) :=
    (Semigroup.mem_center_iff.mp
      (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization_mem_center
        d H) (MonoidAlgebra.of R H x)).symm
  have hB : Commute B X := by
    have hmap := hb.map (NagaoComplement.centralizerSubtypeMap z)
    simpa [B, X, NagaoComplement.centralizerSubtypeMap,
      MonoidAlgebra.of] using hmap
  have hemap := he.map rho.asAlgebraHom
  have hBmap := hB.map rho.asAlgebraHom
  have hemap' : Commute (rho.asAlgebraHom e) (rho (x : G)) := by
    simpa [X, Representation.asAlgebraHom_single_one] using hemap
  have hBmap' : Commute (rho.asAlgebraHom B) (rho (x : G)) := by
    simpa [X, Representation.asAlgebraHom_single_one] using hBmap
  have hresult : Commute
      (rho.asAlgebraHom e - rho.asAlgebraHom e * rho.asAlgebraHom B)
      (rho (x : G)) :=
    hemap'.sub_left (hemap'.mul_left hBmap')
  simpa [NagaoComplement.principalComplement, NagaoComplement.complement,
    e, b, B, map_sub, map_mul] using hresult

set_option maxHeartbeats 800000 in
/-- Conditional characterwise Nagao trace vanishing.  The only block input
is the full equality between the ambient Brauer image and the compatible
local principal selector. -/
theorem trace_principalComplement_comp_eq_zero
    {G : Type u} {V : Type*} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G)
    [AddCommGroup V] [Module (Localization.AtPrime d.primeIdeal) V]
    [Module.Free (Localization.AtPrime d.primeIdeal) V]
    [Module.Finite (Localization.AtPrime d.primeIdeal) V]
    (rho : Representation (Localization.AtPrime d.primeIdeal) G V)
    (z : G) (hzne : z ≠ 1) (hz : z * z = 1)
    (heq :
      BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z =
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)))
    (x : Subgroup.centralizer ({z} : Set G))
    (hxodd : Odd (orderOf (x : G))) :
    LinearMap.trace (Localization.AtPrime d.primeIdeal) V
        ((rho (z * (x : G))).comp
          (rho.asAlgebraHom (NagaoComplement.principalComplement d z))) = 0 := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let R := Localization.AtPrime d.primeIdeal
  letI : IsDiscreteValuationRing R :=
    CyclotomicDVR.cyclotomicOrderAtPrime_isDiscreteValuationRing d
  let P : Subgroup G := Subgroup.zpowers z
  letI : CommGroup P := IsCyclic.commGroup
  let phi : P →* G := P.subtype
  let sigma : Representation R P V := NagaoRange.restrictedRepresentation rho phi
  letI : AddCommGroup sigma.asModule := inferInstanceAs (AddCommGroup V)
  letI : Module R sigma.asModule := inferInstanceAs (Module R V)
  let f : MonoidAlgebra R G := NagaoComplement.principalComplement d z
  let hcomm : ∀ s : P,
      Commute f (MonoidAlgebra.of R G (phi s)) :=
    LeftIdealHigman.commute_zpowers_of_conjugation_fixed
      z hzne hz f (NagaoComplement.conjugation_principalComplement d z)
  let E : Module.End (MonoidAlgebra R P) sigma.asModule :=
    NagaoRange.commutingGroupAlgebraEnd rho phi f hcomm
  have hE_apply (v : sigma.asModule) :
      sigma.asModuleEquiv (E v) =
        rho.asAlgebraHom f (sigma.asModuleEquiv v) := by
    simpa [E, sigma] using
      NagaoRange.commutingGroupAlgebraEnd_apply rho phi f hcomm v
  have hproj : Module.Projective (MonoidAlgebra R P)
      (LinearMap.range E) := by
    simpa [R, P, phi, sigma, f, hcomm, E] using
      NagaoPrincipalRange.projective_range_principalComplement_of_brauer_eq
        d rho z hzne hz heq
  letI : Module.Projective (MonoidAlgebra R P) (LinearMap.range E) := hproj
  letI : Module.Free R sigma.asModule :=
    Module.Free.of_equiv sigma.asModuleEquiv.symm
  letI : Module.Finite R sigma.asModule :=
    Module.Finite.equiv sigma.asModuleEquiv.symm
  have hEidem : IsIdempotentElem E := by
    apply LinearMap.ext
    intro v
    apply sigma.asModuleEquiv.injective
    simp only [Module.End.mul_apply]
    rw [hE_apply, hE_apply]
    simpa only [map_mul, Module.End.mul_apply] using
      LinearMap.congr_fun
        (congrArg rho.asAlgebraHom
          (NagaoComplement.principalComplement_isIdempotent d z))
        (sigma.asModuleEquiv v)
  have hEres : IsIdempotentElem (E.restrictScalars R) := by
    apply LinearMap.ext
    intro v
    simpa only [Module.End.mul_apply, LinearMap.restrictScalars_apply] using
      LinearMap.congr_fun hEidem v
  letI rangeAdd : AddCommGroup (LinearMap.range E) := by
    change AddCommGroup (LinearMap.range (E.restrictScalars R))
    exact @Submodule.addCommGroup R sigma.asModule
      inferInstance inferInstance inferInstance
      (LinearMap.range (E.restrictScalars R))
  letI rangeModR : Module R (LinearMap.range E) := by
    change Module R (LinearMap.range (E.restrictScalars R))
    exact Submodule.module _
  letI rangeModA : Module (MonoidAlgebra R P) (LinearMap.range E) :=
    Submodule.module (LinearMap.range E)
  have hscalarTower :
      IsScalarTower R (MonoidAlgebra R P) (LinearMap.range E) := by
    constructor
    intro r a v
    apply Subtype.ext
    exact smul_assoc r a (v : sigma.asModule)
  letI : IsScalarTower R (MonoidAlgebra R P) (LinearMap.range E) :=
    hscalarTower
  letI rangeResFinite :
      Module.Finite R (LinearMap.range (E.restrictScalars R)) :=
    Module.Finite.range (E.restrictScalars R)
  letI rangeResFree :
      Module.Free R (LinearMap.range (E.restrictScalars R)) :=
    CentralIdempotentSupport.free_range_of_isIdempotentElem_of_isLocalRing
      (R := R) (M := sigma.asModule) (E.restrictScalars R) hEres
  let rangeEquiv :
      LinearMap.range (E.restrictScalars R) ≃ₗ[R] LinearMap.range E :=
    { toFun := fun v => ⟨v.1, by
          rcases v.2 with ⟨w, hw⟩
          exact ⟨w, hw⟩⟩
      invFun := fun v => ⟨v.1, by
          rcases v.2 with ⟨w, hw⟩
          exact ⟨w, hw⟩⟩
      left_inv := by intro v; rfl
      right_inv := by intro v; rfl
      map_add' := by intro v w; rfl
      map_smul' := by intro r v; rfl }
  letI rangeFiniteR : Module.Finite R (LinearMap.range E) :=
    Module.Finite.equiv rangeEquiv
  letI rangeFreeR : Module.Free R (LinearMap.range E) :=
    Module.Free.of_equiv rangeEquiv
  letI : Module.Finite (MonoidAlgebra R P) (LinearMap.range E) :=
    @Module.Finite.of_restrictScalars_finite
      R (MonoidAlgebra R P) (LinearMap.range E)
      inferInstance inferInstance inferInstance
      (inferInstance : Module R (LinearMap.range E))
      (inferInstance : Module (MonoidAlgebra R P) (LinearMap.range E))
      inferInstance hscalarTower
      (inferInstance : Module.Finite R (LinearMap.range E))
  letI rangeCompat :
      LinearMap.CompatibleSMul (LinearMap.range E) (LinearMap.range E)
      R (MonoidAlgebra R P) := by
    constructor
    intro g r v
    rw [← IsScalarTower.algebraMap_smul (MonoidAlgebra R P) r v,
      g.map_smul,
      IsScalarTower.algebraMap_smul (MonoidAlgebra R P) r (g v)]
  have hxz : Commute (x : G) z :=
    Subgroup.mem_centralizer_singleton_iff.mp x.property
  have hxP : ∀ s : P, (x : G) * phi s = phi s * (x : G) := by
    rw [Subgroup.forall_zpowers]
    intro n
    exact (hxz.zpow_right n).eq
  let TxI : sigma.IntertwiningMap sigma :=
    { toLinearMap := rho (x : G)
      isIntertwining' := by
        intro s
        change rho (x : G) * rho (phi s) = rho (phi s) * rho (x : G)
        rw [← map_mul, hxP s, map_mul] }
  let T : Module.End (MonoidAlgebra R P) sigma.asModule :=
    Representation.IntertwiningMap.equivAlgEnd sigma TxI
  have hT_apply (v : sigma.asModule) :
      sigma.asModuleEquiv (T v) = rho (x : G) (sigma.asModuleEquiv v) := rfl
  have hfx : Commute (rho.asAlgebraHom f) (rho (x : G)) := by
    simpa [f] using principalComplement_action_commutes_centralizer d rho z x
  have hET : E * T = T * E := by
    apply LinearMap.ext
    intro v
    apply sigma.asModuleEquiv.injective
    simp only [Module.End.mul_apply]
    rw [hE_apply, hT_apply, hT_apply, hE_apply]
    exact LinearMap.congr_fun hfx.eq (sigma.asModuleEquiv v)
  let Tr : Module.End (MonoidAlgebra R P) (LinearMap.range E) :=
    T.restrict (by
      rintro v ⟨w, rfl⟩
      refine ⟨T w, ?_⟩
      exact LinearMap.congr_fun hET w)
  have hTr_apply (v : LinearMap.range E) :
      ((Tr v : LinearMap.range E) : sigma.asModule) = T (v : sigma.asModule) :=
    rfl
  have hTrpow_apply (k : ℕ) (v : LinearMap.range E) :
      sigma.asModuleEquiv
          (((Tr ^ k) v : LinearMap.range E) : sigma.asModule) =
        ((rho (x : G)) ^ k)
          (sigma.asModuleEquiv (v : sigma.asModule)) := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ', pow_succ']
        change sigma.asModuleEquiv
            ((Tr ((Tr ^ k) v) : LinearMap.range E) : sigma.asModule) = _
        rw [hTr_apply, hT_apply, ih]
        rfl
  have hTrpow : Tr ^ orderOf (x : G) = 1 := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    apply sigma.asModuleEquiv.injective
    rw [hTrpow_apply]
    change ((rho (x : G)) ^ orderOf (x : G))
        (sigma.asModuleEquiv (v : sigma.asModule)) = _
    rw [← map_pow, pow_orderOf_eq_one, map_one]
    rfl
  let c : P := ⟨z, Subgroup.mem_zpowers z⟩
  have hc : c ≠ 1 := by
    intro h
    exact hzne (congrArg Subtype.val h)
  have hc2 : c * c = 1 := by
    apply Subtype.ext
    exact hz
  have hPcard : Nat.card P = 2 := by
    change Nat.card (Subgroup.zpowers z) = 2
    rw [Nat.card_zpowers,
      orderOf_eq_two (by simpa [pow_two] using hz) hzne]
  have htwo : ¬ IsUnit (2 : R) := by
    simpa [R] using BlockOrthogonality.two_not_isUnit_cyclotomicOrderAtPrime d
  have hzero :=
    @NagaoTrace.trace_lsmul_comp_eq_zero_of_projective_odd_order
      R P (LinearMap.range E)
      inferInstance inferInstance inferInstance inferInstance
      rangeAdd rangeModR rangeModA
      hscalarTower hproj
      (inferInstance : Module.Finite (MonoidAlgebra R P) (LinearMap.range E))
      htwo c hc hc2 hPcard Tr (orderOf (x : G)) hxodd hTrpow
  -- The remaining lines identify this range trace with the ambient trace of
  -- `rho(zx)` followed by the represented complement.
  let F : Module.End R sigma.asModule :=
    NagaoRange.transportedEnd sigma (rho (z * (x : G)))
  have hFcomm :
      F.comp (E.restrictScalars R) = (E.restrictScalars R).comp F := by
    apply LinearMap.ext
    intro v
    apply sigma.asModuleEquiv.injective
    simp only [F, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
    rw [NagaoRange.transportedEnd_apply, hE_apply]
    rw [hE_apply, NagaoRange.transportedEnd_apply]
    have hzf : Commute (rho.asAlgebraHom f) (rho z) := by
      have h := (hcomm c).map rho.asAlgebraHom
      simpa [phi, c, Representation.asAlgebraHom_single_one] using h
    have hzx : Commute (rho.asAlgebraHom f) (rho (x : G)) := hfx
    have hzx' : Commute (rho.asAlgebraHom f) (rho (z * (x : G))) := by
      rw [map_mul]
      exact hzf.mul_right hzx
    exact LinearMap.congr_fun hzx'.eq.symm (sigma.asModuleEquiv v)
  have hFmap : ∀ v ∈ LinearMap.range (E.restrictScalars R),
      F v ∈ LinearMap.range (E.restrictScalars R) := by
    rintro v ⟨w, rfl⟩
    refine ⟨F w, ?_⟩
    exact LinearMap.congr_fun hFcomm.symm w
  have hFmapE : ∀ v ∈ LinearMap.range E, F v ∈ LinearMap.range E := by
    rintro v ⟨w, rfl⟩
    refine ⟨F w, ?_⟩
    change E (F w) = F (E w)
    exact LinearMap.congr_fun hFcomm.symm w
  have hFAll : ∀ v : sigma.asModule,
      (F.comp (E.restrictScalars R)) v ∈
        LinearMap.range (E.restrictScalars R) := by
    intro v
    exact hFmap (E v) ⟨v, rfl⟩
  have hFAmap : ∀ v ∈ LinearMap.range (E.restrictScalars R),
      (F.comp (E.restrictScalars R)) v ∈
        LinearMap.range (E.restrictScalars R) := by
    intro v _hv
    exact hFAll v
  have htraceRange :=
    LinearMap.trace_restrict_eq_of_forall_mem
      (LinearMap.range (E.restrictScalars R))
      (F.comp (E.restrictScalars R)) hFAll hFAmap
  let rangeTraceEnd : Module.End R (LinearMap.range E) :=
    { toFun := fun v =>
        ((LinearMap.lsmul (MonoidAlgebra R P) (LinearMap.range E)
          (MonoidAlgebra.of R P c)).comp Tr) v
      map_add' := by
        intro v w
        exact ((LinearMap.lsmul (MonoidAlgebra R P) (LinearMap.range E)
          (MonoidAlgebra.of R P c)).comp Tr).map_add v w
      map_smul' := by
        intro r v
        exact rangeCompat.map_smul
          ((LinearMap.lsmul (MonoidAlgebra R P) (LinearMap.range E)
            (MonoidAlgebra.of R P c)).comp Tr) r v }
  let ARes : Module.End R (LinearMap.range (E.restrictScalars R)) :=
    (F.comp (E.restrictScalars R)).restrict hFAmap
  let FRange : Module.End R (LinearMap.range E) :=
    rangeEquiv.conj ARes
  have htraceRange' :
      LinearMap.trace R sigma.asModule (F.comp (E.restrictScalars R)) =
        LinearMap.trace R (LinearMap.range E) FRange := by
    calc
      LinearMap.trace R sigma.asModule (F.comp (E.restrictScalars R)) =
          LinearMap.trace R (LinearMap.range (E.restrictScalars R)) ARes := by
            simpa [ARes] using htraceRange.symm
      _ = LinearMap.trace R (LinearMap.range E) FRange := by
        symm
        let b := Module.Free.chooseBasis R
          (LinearMap.range (E.restrictScalars R))
        rw [LinearMap.trace_eq_matrix_trace R (b.map rangeEquiv),
          LinearMap.trace_eq_matrix_trace R b]
        congr 1
  have hE_range (v : LinearMap.range E) :
      E (v : sigma.asModule) = (v : sigma.asModule) := by
    rcases v.property with ⟨w, hw⟩
    rw [← hw]
    exact LinearMap.congr_fun hEidem w
  have hFRange_apply (v : LinearMap.range E) :
      ((FRange v : LinearMap.range E) : sigma.asModule) =
        F (v : sigma.asModule) := by
    calc
      ((FRange v : LinearMap.range E) : sigma.asModule) =
          F (E (v : sigma.asModule)) := rfl
      _ = F (v : sigma.asModule) := congrArg F (hE_range v)
  have hrangeTraceEnd_apply (v : LinearMap.range E) :
      ((rangeTraceEnd v : LinearMap.range E) : sigma.asModule) =
        ((MonoidAlgebra.of R P c) • Tr v : LinearMap.range E) := by
    rfl
  have hrangeEq :
      FRange =
        rangeTraceEnd := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    rw [hFRange_apply, hrangeTraceEnd_apply]
    apply sigma.asModuleEquiv.injective
    rw [show sigma.asModuleEquiv (F (v : sigma.asModule)) =
        rho (z * (x : G)) (sigma.asModuleEquiv (v : sigma.asModule)) by
      exact NagaoRange.transportedEnd_apply sigma (rho (z * (x : G))) v]
    change rho (z * (x : G)) (sigma.asModuleEquiv v) =
      sigma.asModuleEquiv
        ((MonoidAlgebra.of R P c) •
          ((Tr v : LinearMap.range E) : sigma.asModule))
    rw [Representation.asModuleEquiv_map_smul, hTr_apply, hT_apply,
      Representation.asAlgebraHom_of]
    change rho (z * (x : G)) (sigma.asModuleEquiv v) =
      rho (phi c) (rho (x : G) (sigma.asModuleEquiv v))
    rw [map_mul]
    rfl
  have hconj : sigma.asModuleEquiv.conj
      (F.comp (E.restrictScalars R)) =
      (rho (z * (x : G))).comp (rho.asAlgebraHom f) := by
    apply LinearMap.ext
    intro v
    simp only [LinearEquiv.conj_apply_apply, LinearMap.comp_apply, F,
      LinearMap.restrictScalars_apply]
    rw [NagaoRange.transportedEnd_apply, hE_apply]
    simp
  have hzero' :
      LinearMap.trace R (LinearMap.range E) rangeTraceEnd = 0 := by
    rw [← hzero]
    congr 1
  calc
    LinearMap.trace R V
        ((rho (z * (x : G))).comp (rho.asAlgebraHom f)) =
        LinearMap.trace R V
          (sigma.asModuleEquiv.conj (F.comp (E.restrictScalars R))) := by
          rw [hconj]
    _ = LinearMap.trace R sigma.asModule
        (F.comp (E.restrictScalars R)) :=
      LinearMap.trace_conj' (F.comp (E.restrictScalars R))
        sigma.asModuleEquiv
    _ = LinearMap.trace R (LinearMap.range E) FRange := htraceRange'
    _ = 0 := by
      rw [hrangeEq]
      exact hzero'

end CharacterwiseNagao
end Submission.ZStar
