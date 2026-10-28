module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourExtraParabolic
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourExtraParabolic
public import Theory.SpecificGroups.GL2.TwoSubgroupNormalizerAction
public import Theory.SpecificGroups.GL2.NoncommutativeCentralizer
public import Theory.SpecificGroups.GL2.PrimeThreeFiveResidual.Coordinates
public import Theory.GroupTheory.CentralQuotientInversionFixedDerived

/-!
# H-star placement of the Hermitian extraspecial radical

Let X be the original extraspecial Xi radical and R its perfect residual
actor. Conjugation by R normalizes the elementary two-group supplied by V.
On the odd Frattini plane, perfectness kills the normalizer action on that
elementary group; the noncommutative residual image then makes its elements
scalar. Their squares are one, so they fix the extraspecial center.

Thus V centralizes the full center preimage modulo O₂(X). It lies in the
two-core of the center-preimage join with T. The genuine Hermitian H-star
core exclusion forces this join into M. Xi irreducibility puts every proper
overgroup of T in XT in that join, proving actual H-star membership.
The companion Chapter 12 module supplies all these hypotheses for the
original chosen module, on both weak-closure branches.

The proof-only import reuses the private Xi intermediate-subgroup lemma;
no existing public boundary is changed. Whole odd-normalizer control and
completion of 8.2.7--13 remain separate source obligations.

Source: Aschbacher--Smith 1.3.1--3, 8.2.2(1) and the radical paragraph of
8.2.7, printed pp.508--509,714,717--718, refs/quasithin.pdf
(1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource

private theorem perfect_elementary_scalar
    {F : Type*} [Field F] [Finite F] (hF : (2 : F) ≠ 0)
    (R A : Subgroup (GL (Fin 2) F)) [Group.IsPerfect R] [IsElementaryAbelian 2 A]
    (hRA : R ≤ normalizer (A : Set (GL (Fin 2) F))) (hne : R ≠ ⊥) :
    A ≤ (Matrix.GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F).range := by
  let f := A.normalizerMonoidHom.rangeRestrict.comp (inclusion hRA)
  have hp := Matrix.GeneralLinearGroup.normalizerAction_isPGroup_of_elementaryAbelian_two hF A
  let : Group.IsNilpotent A.normalizerMonoidHom.range := hp.isNilpotent
  have hf : f = 1 := by
    let : Group.IsPerfect f.range := Group.IsPerfect.range f
    have ht : Subsingleton f.range := by
      by_contra! hn
      exact Group.IsPerfect.not_isSolvable f.range inferInstance
    ext r : 1
    exact congrArg Subtype.val (ht.elim (f.rangeRestrict r) 1)
  have hc : A ≤ centralizer (R : Set (GL (Fin 2) F)) := by
    intro a ha
    apply mem_centralizer_iff.mpr
    intro r hr
    have hh := congrArg (fun g : A.normalizerMonoidHom.range => (g.val ⟨a,ha⟩).val)
      (DFunLike.congr_fun hf (⟨r,hr⟩ : R))
    change r*a*r⁻¹ = a at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh)
  apply hc.trans (Matrix.GeneralLinearGroup.centralizer_le_scalar_of_noncommutative R ?_)
  intro hcomm
  let := hcomm
  let : Subsingleton R := Group.IsPerfect.subsingleton_of_isMulCommutative
  exact hne (Subgroup.eq_bot_of_subsingleton R)

/-- An elementary two-group normalized by a nontrivial perfect plane actor
fixes the center of an extraspecial group of order p³. -/
theorem extraspecial_center_fixed_by_normalized_elementary
    {G P : Type*} [Group G] [Finite G] [Group P] [Finite P]
    {p : ℕ} [Fact p.Prime] [IsExtraspecial p P]
    (hp : Odd p) (hP : Nat.card P = p^3)
    (α : G →* MulAut P) (R V : Subgroup G)
    [Group.IsPerfect R] [IsElementaryAbelian 2 V]
    (hRV : R ≤ normalizer (V : Set G))
    (hne : ((quotientAut (center P)).comp (α.comp R.subtype)) ≠ 1) :
    ∀ v ∈ V, ∀ z ∈ center P, α v z = z := by
  let E := P ⧸ center P
  let : IsElementaryAbelian p E := IsExtraspecial.quotient_elementary_abelian p P
  have hc : Nat.card E = p^2 := by
    have hh := (center P).index_mul_card
    rw [index_eq_card,IsExtraspecial.center_order_p p P,hP] at hh
    exact Nat.mul_right_cancel (by exact (Fact.out : p.Prime).pos)
      (hh.trans (by ring))
  obtain ⟨c,e,he⟩ := Matrix.GeneralLinearGroup.PrimeThreeFiveResidual.exists_plane_coordinates hc
  let β := (quotientAut (center P)).comp α
  let f := e.toMonoidHom.comp β
  let A := V.map f
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map f
  let B := R.map f
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := f.subgroupMap R) (f.subgroupMap_surjective R)
  have hBA : B ≤ normalizer (A : Set (GL (Fin 2) (ZMod p))) :=
    (map_mono hRV).trans (V.le_normalizer_map f)
  have hB : B ≠ ⊥ := by
    intro hz
    apply hne
    ext r : 1
    apply e.injective
    exact (mem_bot.mp (hz ▸ mem_map_of_mem f r.property)).trans (map_one e).symm
  have hp2 : (2 : ZMod p) ≠ 0 := by
    intro hh
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp hh
    have hh := ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
      (Fact.out : p.Prime).ne_one
    subst p
    norm_num at hp
  have hscalar := perfect_elementary_scalar hp2 B A hBA hB
  intro v hv z hz
  have hv2 : v^2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv
  obtain ⟨u,hu⟩ := hscalar (mem_map_of_mem f hv)
  have hu2 : u^2 = 1 := by
    apply Units.ext
    have hh : Matrix.GeneralLinearGroup.scalar (Fin 2) (u^2) = (1 : GL (Fin 2) (ZMod p)) := by
      rw [map_pow,hu,←map_pow,hv2,map_one]
    exact congrArg (fun a : GL (Fin 2) (ZMod p) => a.val 0 0) hh
  have hdet : (f v).det = 1 := by
    rw [←hu,Matrix.GeneralLinearGroup.det_scalar]
    simpa only [Fintype.card_fin] using hu2
  rcases Matrix.GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one
    hp2 (f v) (by rw [←map_pow,hv2,map_one]) hdet with hid | hinv
  · have hb : β v = 1 := e.injective (hid.trans (map_one e).symm)
    exact (MulAut.mem_fixedSubgroup _ _).mp
      ((α v).fixes_commutator_of_quotientCenter_eq_one hb
        ((IsExtraspecial.commutator_eq_center (p := p)).ge hz))
  · have hi : ∀ x : P, α v x * x ∈ center P := by
      intro x
      apply (QuotientGroup.eq_one_iff _).mp
      change (QuotientGroup.mk' (center P)) (α v x * x) = 1
      rw [map_mul]
      have hx : β v (QuotientGroup.mk' (center P) x) =
          (QuotientGroup.mk' (center P) x)⁻¹ := by
        apply c.injective
        rw [←he,show e (β v) = -1 from hinv]
        simp [Matrix.GeneralLinearGroup.PrimeThreeFiveResidual.planeAction]
      change quotientAut (center P) (α v) _ = _ at hx
      rw [quotientAut_apply_mk] at hx
      rw [hx,inv_mul_cancel]
    exact (MulAut.mem_fixedSubgroup _ _).mp
      ((α v).fixes_derived_of_inverts_mod_center
        (IsExtraspecial.commutator_eq_center (p := p)).le hi
        ((IsExtraspecial.commutator_eq_center (p := p)).ge hz))


/-- The original module centralizes the full extraspecial center modulo the
radical two-core. The perfect residual is the actual normalizer actor. -/
theorem radical_center_module_commutator
    {G : Type*} [Group G] [Finite G] {X R V : Subgroup G}
    [Group.IsPerfect R] [IsElementaryAbelian 2 V]
    (hRX : R ≤ normalizer (X : Set G)) (hVX : V ≤ normalizer (X : Set G))
    (hRV : R ≤ normalizer (V : Set G)) (hcomm : ⁅X,R⁆ = X)
    {p : ℕ} [Fact p.Prime] [IsExtraspecial p (Chapter1.XiQuotient X)]
    (hp : Odd p) (hc : Nat.card (Chapter1.XiQuotient X) = p^3) :
    ⁅V,radicalCenterPreimage X⁆ ≤ X.pCoreIn 2 := by
  let N := normalizer (X : Set G)
  let P := Chapter1.XiQuotient X
  let α : N →* MulAut P := (quotientAut (pCore 2 X)).comp X.normalizerMonoidHom
  let A := R.subgroupOf N
  let W := V.subgroupOf N
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hRX).symm.toMonoidHom)
    (subgroupOfEquivOfLe hRX).symm.surjective
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVX
  have hAW : A ≤ normalizer (W : Set N) := by
    apply le_normalizer_iff.mpr
    intro r hr v hv
    exact (mem_normalizer_iff.mp (hRV hr) (v : G)).mp hv
  have hn : (quotientAut (center P)).comp (α.comp A.subtype) ≠ 1 := by
    intro hh
    have hle : ⁅R,X⁆ ≤ radicalCenterPreimage X := by
      apply commutator_le.mpr
      intro r hr x hx
      let r' : A := ⟨⟨r,hRX hr⟩,hr⟩
      let x' : X := ⟨x,hx⟩
      let y := X.normalizerMonoidHom r'.val x'
      have he := congrArg (fun a : MulAut (P ⧸ center P) =>
        a (QuotientGroup.mk' (center P) (QuotientGroup.mk' (pCore 2 X) x')))
        (DFunLike.congr_fun hh r')
      change quotientAut (center P) (quotientAut (pCore 2 X)
        (X.normalizerMonoidHom r'.val)) _ = _ at he
      rw [quotientAut_apply_mk,quotientAut_apply_mk] at he
      have he' : QuotientGroup.mk' (center P) (QuotientGroup.mk' (pCore 2 X) y) =
          QuotientGroup.mk' (center P) (QuotientGroup.mk' (pCore 2 X) x') := he
      refine ⟨y*x'⁻¹,?_,rfl⟩
      change QuotientGroup.mk' (pCore 2 X) (y*x'⁻¹) ∈ center P
      apply (QuotientGroup.eq_one_iff _).mp
      change (QuotientGroup.mk' (center P)) ((QuotientGroup.mk' (pCore 2 X)) (y*x'⁻¹)) = 1
      rw [map_mul,map_inv,map_mul,map_inv,he',mul_inv_cancel]
    rw [commutator_comm,hcomm] at hle
    have htop : center P = ⊤ := by
      apply top_unique
      intro x _
      obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) x
      obtain ⟨z,hz,hzy⟩ := hle y.property
      have he : z = y := Subtype.ext hzy
      exact he ▸ hz
    let : Nontrivial (P ⧸ center P) := IsExtraspecial.quotient_nontrivial p P
    exact QuotientGroup.nontrivial_iff.mp inferInstance htop
  have hfix := extraspecial_center_fixed_by_normalized_elementary hp hc α A W hAW hn
  apply commutator_le.mpr
  rintro v hv z ⟨x,hx,rfl⟩
  let v' : N := ⟨v,hVX hv⟩
  let y := X.normalizerMonoidHom v' x
  refine ⟨y*x⁻¹,?_,rfl⟩
  apply (QuotientGroup.eq_one_iff _).mp
  have hh := hfix v' hv (QuotientGroup.mk' (pCore 2 X) x) hx
  change quotientAut (pCore 2 X) (X.normalizerMonoidHom v') _ = _ at hh
  rw [quotientAut_apply_mk] at hh
  change QuotientGroup.mk' (pCore 2 X) (y*x⁻¹) = 1
  rw [map_mul,map_inv,show QuotientGroup.mk' (pCore 2 X) y = _ from hh,mul_inv_cancel]


private theorem module_le_core_of_center_commutator
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) {X V : Subgroup G}
    (hXT : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hQT : X.pCoreIn 2 ≤ T) (hVT : V ≤ T)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hc : ⁅V,radicalCenterPreimage X⁆ ≤ X.pCoreIn 2) :
    V ≤ (radicalCenterPreimage X ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let Q := X.pCoreIn 2
  let Z := radicalCenterPreimage X
  let B := Z ⊔ (T : Subgroup G)
  let W := V ⊔ Q
  have hNQ : normalizer (X : Set G) ≤ normalizer (Q : Set G) :=
    normalizer_le_normalizer_characteristic_image X (pCore 2 X)
  have hTW : (T : Subgroup G) ≤ normalizer (W : Set G) :=
    (le_inf hTV (hXT.trans hNQ)).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hZQ : Z ≤ normalizer (Q : Set G) := (map_subtype_le _).trans (X.le_normalizer.trans hNQ)
  have hZW : Z ≤ normalizer (W : Set G) := by
    apply le_normalizer_iff.mpr
    intro z hz
    change W ≤ W.comap (MulAut.conj z).toMonoidHom
    apply sup_le
    · intro v hv
      have hcv : ⁅z,v⁆ ∈ Q := by
        apply hc
        rw [commutator_comm]
        exact commutator_mem_commutator hz hv
      have hh := W.mul_mem (show ⁅z,v⁆ ∈ W from mem_sup_right hcv)
        (show v ∈ W from mem_sup_left hv)
      change z*v*z⁻¹ ∈ W
      simpa only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one] using hh
    · intro q hq
      exact mem_sup_right ((mem_normalizer_iff.mp (hZQ hz) q).mp hq)
  have hWT : W ≤ (T : Subgroup G) := sup_le hVT hQT
  exact (show V ≤ W from le_sup_left).trans
    (le_pCoreIn_of_normalizes (T.isPGroup'.to_le hWT)
      (hWT.trans le_sup_right) (sup_le hZW hTW))

/-- A subgroup containing the original Sylow and with V in its two-core
cannot escape M if every actual H-star subgroup excludes V from its core. -/
theorem le_of_module_le_core_of_hstar
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) {V M H : Subgroup G}
    (hn : ∀ J ∈ Chapter3.HStar (T : Subgroup G) M, ¬ V ≤ J.pCoreIn 2)
    (hH : H ∈ Chapter1.HOver G (T : Set G)) (hV : V ≤ H.pCoreIn 2) : H ≤ M := by
  by_contra hout
  obtain ⟨J,hJ,hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun J : Subgroup G => J ≤ H ∧ J ∈ Chapter1.HOver G (T : Set G) ∧ ¬ J ≤ M)
    ⟨H,le_rfl,hH,hout⟩
  have hstar : J ∈ Chapter3.HStar (T : Subgroup G) M := by
    refine ⟨hJ.2,?_⟩
    intro I hI hIJ
    exact hmin ⟨hIJ.trans hJ.1,hI⟩ hIJ
  exact hn J hstar (hV.trans (Chapter3.twoCore_le_of_sylow_le T hJ.2.1.2 hJ.1))



/-- The full extraspecial radical join belongs to the actual H-star family.
Its proper Sylow overgroups lie in the center-preimage join; V is in the
latter's two-core, so the actual H-star core exclusion places it in M. -/
theorem extraspecial_radical_join_HStar
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) {X R V M : Subgroup G}
    (hX : Chapter1.XiMember (T : Subgroup G) X)
    [Group.IsPerfect R] [IsElementaryAbelian 2 V]
    (hRX : R ≤ normalizer (X : Set G))
    (hRV : R ≤ normalizer (V : Set G)) (hcomm : ⁅X,R⁆ = X)
    (hout : ¬ X ≤ M)
    (hVT : V ≤ T) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnot : ∀ J ∈ Chapter3.HStar (T : Subgroup G) M, ¬ V ≤ J.pCoreIn 2)
    {p : ℕ} [Fact p.Prime] [IsExtraspecial p (Chapter1.XiQuotient X)]
    (hp : Odd p) (hc : Nat.card (Chapter1.XiQuotient X) = p^3) :
    X ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) M := by
  have hQT := hX.pCoreIn_le_of_isSylowIn
    (show Chapter1.IsSylowIn 2 (T : Subgroup G) (X ⊔ (T : Subgroup G)) from
      ⟨T.subtype le_sup_right,map_subgroupOf_eq_of_le le_sup_right⟩)
  have hVC := radical_center_module_commutator hRX (hVT.trans hX.invariant) hRV hcomm hp hc
  have hcore := module_le_core_of_center_commutator T hX.invariant hQT hVT hTV hVC
  have hZT : radicalCenterPreimage X ⊔ (T : Subgroup G) ≤ X ⊔ (T : Subgroup G) :=
    sup_le_sup (map_subtype_le _) le_rfl
  have hZM := le_of_module_le_core_of_hstar T hnot
    (Chapter3.mem_HOver_of_sylow_interval T le_sup_right hZT ⟨hX.join_mem_H,fun x hx => mem_sup_right hx⟩) hcore
  refine ⟨⟨⟨hX.join_mem_H,fun x hx => mem_sup_right hx⟩,fun h => hout (le_sup_left.trans h)⟩,?_⟩
  intro J hJ hJH
  rcases xi_intermediate_center_or_full (p := p) hX hQT hJ.1.2 hJH with hz | hx
  · exact (hJ.2 (hz.trans hZM)).elim
  · exact sup_le hx hJ.1.2

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
