module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFiveScalar
public import Theory.Representation.SL2NaturalOffenders.LinearLifts

/-!
# The outer field-action contradiction in source 6.2.7

The original cubic acts as a nonidentity scalar on the natural SL2(4)
moved component. If a Sylow element induced an outer automorphism on
this component, its natural operator would have a nontrivial field
coefficient. Its commutator with the scalar is scalar again. The cubic
normalizes the arranged Sylow, so this commutator has two-power order;
in characteristic two its scalar must be one. A field automorphism of
F4 fixing the original nonidentity scalar is the identity, a contradiction.

Thus every arranged Sylow element acts innerly on the intrinsic component
quotient. The inner-supplement factorization makes the component Sylow
normalizer normalize the arranged Sylow, contradicting its proved escape
from M. The argument restricts the original action to the whole moved
space and preserves its original two-core quotient map and coordinates.

The Chapter12 companion supplies these inputs on the actual natural
layer and proves the one-sided normalization consequence and both clauses
of 6.2.7. The graph escape and order-eight intersection remain for
LocalAnalysis.
Source: Aschbacher--Smith 6.2.7, final paragraph, printed p.684;
the literal Chapter12 application is 12.2.2(3d), printed p.795.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition

private theorem four_field_aut_eq_one {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) (z : F) (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (σ : F ≃+* F) (hz : σ z = z) : σ = RingEquiv.refl F := by
  classical
  let s : Finset F := {0,1,z,1+z}
  have hsum0 : 1+z ≠ 0 := by
    intro he
    apply hz1
    have hh := congrArg (fun x : F => x+1) he
    simpa only [add_assoc,add_comm,add_left_comm,CharTwo.add_self_eq_zero,zero_add,add_zero] using hh
  have hsum1 : 1+z ≠ 1 := by simpa using hz0
  have hsumz : 1+z ≠ z := by simp
  have hs : s.card = 4 := by simp [s,hz0,hz1,hsum0,hsum1,hsumz,Ne.symm]
  have hall : ∀ x : F, x ∈ s := by
    let := Fintype.ofFinite F
    have he : s = Finset.univ := Finset.eq_univ_of_card s (by simpa only [Nat.card_eq_fintype_card] using hs.trans hF.symm)
    simp [he]
  ext x
  have hx := hall x
  simp only [s,Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact σ.map_zero
  · exact σ.map_one
  · exact hz
  · rw [map_add,map_one,hz]; rfl

private theorem scalar_normalizing_two_inner
    {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    (hF : Nat.card F = 4) (ρ : Representation (ZMod 2) X (Fin 2 → F))
    (R : Subgroup X) (hR : IsPGroup 2 R)
    (d : X) (hd : d ∈ normalizer (R : Set X))
    (z : F) (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (hscalar : ∀ v, ρ d v = z • v)
    (r : X) (hr : r ∈ R)
    (a : MulAut (SL(2,F)))
    (he : ∀ g v, ρ r (g.val.mulVec v) = (a g).val.mulVec (ρ r v)) :
    ∃ g, a = MulAut.conj g := by
  by_contra houter
  obtain ⟨σ,hσne,hσ⟩ := SL2NaturalOffenders.outer_intertwiner_semilinear a
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _ (ρ.asGroupHom r)) he houter
  change ∀ c v, ρ r (c • v) = σ c • ρ r v at hσ
  have hdi (v : Fin 2 → F) : ρ d⁻¹ v = z⁻¹ • v := by
    apply (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _ (ρ.asGroupHom d)).injective
    change ρ d (ρ d⁻¹ v) = ρ d (z⁻¹ • v)
    rw [hscalar (z⁻¹ • v),smul_smul,mul_inv_cancel₀ hz0,one_smul]
    simp [←Module.End.mul_apply,←map_mul]
  let c := r*d*r⁻¹*d⁻¹
  have hcR : c ∈ R := by
    simpa only [c,mul_assoc] using R.mul_mem hr ((mem_normalizer_iff.mp hd r⁻¹).mp (R.inv_mem hr))
  have hc (v : Fin 2 → F) : ρ c v = (σ z*z⁻¹) • v := by
    change ρ (r*d*r⁻¹*d⁻¹) v = _
    simp only [map_mul,Module.End.mul_apply]
    rw [hscalar,hσ]
    have hh (w : Fin 2 → F) : ρ r (ρ r⁻¹ w) = w := by
      simp [←Module.End.mul_apply,←map_mul]
    rw [hh,hdi,smul_smul]
  obtain ⟨m,hm⟩ := (isPGroup_iff_pow_pow_eq_one.mp hR) ⟨c,hcR⟩
  have hcp : c^(2^m)=1 := congrArg Subtype.val hm
  have hcpow (n : ℕ) (v : Fin 2 → F) : ρ (c^n) v = (σ z*z⁻¹)^n • v := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ',map_mul,Module.End.mul_apply,ih,hc,smul_smul,pow_succ']
  have hzpow : (σ z*z⁻¹)^(2^m)=1 := by
    have hh := congrFun (hcpow (2^m) (fun _ => 1)) 0
    rw [hcp,map_one] at hh
    simpa using hh.symm
  have hratio : σ z*z⁻¹=1 := by
    simpa only [pow_one] using (ExpChar.pow_prime_pow_mul_eq_one_iff 2 m 1 _).mp (by simpa using hzpow)
  have hfix : σ z=z := (mul_inv_eq_one₀ hz0).mp hratio
  exact hσne (four_field_aut_eq_one hF z hz0 hz1 σ hfix)

private theorem natural_scalar_normalizer_contained
    {X F : Type*} [Group X] [Finite X] [Field F] [Finite F]
    [CharP F 2] [Algebra (ZMod 2) F]
    (hF : Nat.card F = 4) (K R M : Subgroup X) (hR : IsPGroup 2 R)
    (hRK : R ≤ normalizer (K : Set X))
    (e : (K ⧸ pCore 2 K) ≃* SL(2,F))
    (hc : center (K ⧸ pCore 2 K) = ⊥)
    (ρ : Representation (ZMod 2) X (Fin 2 → F))
    (hnat : ∀ (k : K) v, ρ k v = (e (QuotientGroup.mk' (pCore 2 K) k)).val.mulVec v)
    (P : Sylow 2 K) (hPR : (P : Subgroup K).map K.subtype ≤ R)
    (hNM : normalizer (R : Set X) ≤ M)
    (d : X) (hd : d ∈ normalizer (R : Set X))
    (z : F) (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hscalar : ∀ v, ρ d v = z • v) :
    (((pResidual 2 (normalizer (P : Set K))).map
      (normalizer (P : Set K)).subtype).map K.subtype) ≤ M := by
  have hi (r : R) : pCoreJoinAction 2 hRK (inclusion le_sup_right r) ∈
      MulAut.innerSubgroup (K ⧸ pCore 2 K) := by
    let b := pCoreJoinAction 2 hRK (inclusion le_sup_right r)
    let a := MulAut.congr e b
    have he (g : SL(2,F)) (v : Fin 2 → F) :
        ρ r (g.val.mulVec v) = (a g).val.mulVec (ρ r v) := by
      obtain ⟨k,hk⟩ := QuotientGroup.mk'_surjective (pCore 2 K) (e.symm g)
      have hkg : e (QuotientGroup.mk' (pCore 2 K) k) = g := by rw [hk,e.apply_symm_apply]
      let k' := K.normalizerMonoidHom ⟨r,hRK r.property⟩ k
      have hka : e (QuotientGroup.mk' (pCore 2 K) k') = a g := by
        rw [show QuotientGroup.mk' (pCore 2 K) k' = b (QuotientGroup.mk' (pCore 2 K) k) from
          (pCoreJoinAction_mk 2 hRK (inclusion le_sup_right r) k).symm, hk]
        rfl
      rw [←hka,←hnat,←hkg,←hnat]
      change ρ r (ρ k v) = ρ (r.val*k.val*r.val⁻¹) (ρ r v)
      simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]
    obtain ⟨u,hu⟩ := scalar_normalizing_two_inner hF ρ R hR d hd z hz0 hz1 hscalar
      r r.property a he
    refine ⟨e.symm u,?_⟩
    apply MulEquiv.ext
    intro v
    apply e.injective
    have hh := congrArg (fun t : MulAut SL(2,F) => t (e v)) hu
    change e (b (e.symm (e v))) = u * e v * u⁻¹ at hh
    simpa only [e.symm_apply_apply,MulAut.conj_apply,map_mul,map_inv,e.apply_symm_apply] using hh.symm
  have hfactor := sup_core_factor_of_inner_action K R hRK hR hc P hPR hi
  let B := (normalizer (P : Set K)).map K.subtype
  let W := K ⊔ R
  have hcore : W ≤ normalizer (W.pCoreIn 2 : Set X) :=
    W.le_normalizer.trans (normalizer_le_normalizer_characteristic_image W (pCore 2 W))
  have h1 : B ≤ normalizer ((P : Subgroup K).map K.subtype : Set X) :=
    (P : Subgroup K).le_normalizer_map K.subtype
  have h2 : B ≤ normalizer (W.pCoreIn 2 : Set X) :=
    (map_subtype_le _).trans (le_sup_left.trans hcore)
  have hBR : B ≤ normalizer (R : Set X) := by
    rw [hfactor]
    exact (le_inf h1 h2).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact (map_mono (map_subtype_le _)).trans (hBR.trans hNM)

private theorem natural_moved_scalar_extension
    {H X D W : Type*} [Group H] [Group X] [Group D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (j : H →* X) (π : H →* D)
    (ρ : Representation (ZMod 2) D W) (η : Representation (ZMod 2) X W)
    (hr : ∀ k : H, η (j k) = ρ (π k))
    (K : Subgroup H) (J : Subgroup D) (hKJ : K.map π = J)
    [(K.map j).Normal]
    (F : BinaryField)
    (a : ActionEquiv ((invariantSubspace ρ J (moved ρ J)
      (subspaceCommutator_invariant ρ ⊤ J)).toRepresentation) (linearNatural F 2))
    (d : X) (z : F.Carrier)
    (hscalar : ∀ w : moved ρ J, η d w =
      (a.linearEquiv.symm (z • a.linearEquiv w) : W)) :
    ∃ τ : Representation (ZMod 2) X (Fin 2 → F.Carrier),
      (∀ (k : K) v, τ (j k) v =
        (a.groupEquiv ⟨π k,hKJ ▸ mem_map_of_mem π k.property⟩).val.mulVec v) ∧
      ∀ v, τ d v = z • v := by
  let I := moved ρ J
  have hcomp : η.comp j = ρ.comp π := by ext k; exact LinearMap.congr_fun (hr k) _
  have hmov : subspaceCommutator η ⊤ (K.map j) = I := by
    rw [←subspaceCommutator_comp_map,hcomp,subspaceCommutator_comp_map,hKJ]
  have hI : (⊤ : Subgroup X) ≤ subspaceStabilizer η I := by
    rw [←hmov]
    exact subspaceCommutator_invariant_normalizer η
      (le_subspaceStabilizer η ⊤ (by intros; trivial)) le_normalizer_of_normal
  let B : Subrepresentation η := ⟨I,fun x v hv => (hI (mem_top x) v).2 hv⟩
  let e := a.linearEquiv
  let τ : Representation (ZMod 2) X (Fin 2 → F.Carrier) :=
    e.conjRingEquiv.toMonoidHom.comp B.toRepresentation
  refine ⟨τ,?_,?_⟩
  · intro k v
    have hh := a.intertwines ⟨π k,hKJ ▸ mem_map_of_mem π k.property⟩ (e.symm v)
    rw [e.apply_symm_apply] at hh
    change e (B.toRepresentation (j k) (e.symm v)) = _
    refine Eq.trans (congrArg e (Subtype.ext ?_)) hh
    exact LinearMap.congr_fun (hr k) (e.symm v : W)
  · intro v
    apply e.symm.injective
    apply Subtype.ext
    change (e.symm (e (B.toRepresentation d (e.symm v))) : W) = _
    exact (congrArg (fun w : I => (w : W))
      (e.symm_apply_apply (B.toRepresentation d (e.symm v)))).trans
      ((hscalar (e.symm v)).trans (congrArg
        (fun v : Fin 2 → F.Carrier => (e.symm (z • v) : W)) (e.apply_symm_apply v)))

private theorem five_quotient_center {X : Type*} [Group X]
    (e : X ≃* alternatingGroup (Fin 5)) : center X = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  apply e.injective
  have he : e x = 1 := (alternatingGroup.center_eq_bot (by simp)).le
    ((centerCongr e) ⟨x,hx⟩).property
  exact he.trans e.map_one.symm

namespace LocalFieldQuotientAction
/-- The original Sylow-normalizer escape is incompatible with a nonidentity
scalar cubic on the natural moved A5 component. The same quotient map and
whole moved-space coordinates are used throughout. -/
theorem five_scalar_impossible
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L M R U : Subgroup G} {n : ℕ}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfield : IsInvolutoryFieldFixedSpace L M (layer L R) U n)
    (hUc : Nat.card U = 4)
    (J : Subgroup (action (layer L R) U).range)
    (eJ : J ≃* alternatingGroup (Fin 5))
    (K : Subgroup (Centralizer U)) (hK : K.IsCComponent)
    (hKJ : K.map (action (layer L R) U).rangeRestrict = J)
    (eK : (K ⧸ pCore 2 K) ≃* J)
    (heK : ∀ k : K, ((eK (QuotientGroup.mk' (pCore 2 K) k) : J) :
      (action (layer L R) U).range) = (action (layer L R) U).rangeRestrict k)
    (hescape : ∀ S : Sylow 2 K, ¬ ((((pResidual 2 (normalizer (S : Set K))).map
      (normalizer (S : Set K)).subtype).map K.subtype).map
        (Centralizer U).subtype) ≤ M)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (action (layer L R) U).range W)
    (η : Representation (ZMod 2) (Centralizer U ⊔ fieldLocalResidual L U : Subgroup G) W)
    (hr : ∀ k : Centralizer U, η (inclusion le_sup_left k) =
      ρ ((action (layer L R) U).rangeRestrict k))
    (d : G) (hd : d ∈ fieldLocalResidual L U)
    (F : BinaryField) (hF : F.degree = 2)
    (a : ActionEquiv ((invariantSubspace ρ J (moved ρ J)
      (subspaceCommutator_invariant ρ ⊤ J)).toRepresentation) (linearNatural F 2))
    (z : F.Carrier) (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (hscalar : ∀ w : moved ρ J, η ⟨d,mem_sup_right hd⟩ w =
      (a.linearEquiv.symm (z • a.linearEquiv w) : W)) : False := by
  let H := Centralizer U
  let P := H ⊔ fieldLocalResidual L U
  let N := normalizer (U : Set G)
  let j : H →* P := inclusion le_sup_left
  let jN : H →* N := inclusion (Subgroup.centralizer_le_normalizer _)
  have hPN : P ≤ N := sup_le (Subgroup.centralizer_le_normalizer _)
    ((map_subtype_le _).trans inf_le_right)
  let pN : P →* N := inclusion hPN
  let K0 := K.map j
  let f : K ≃* K0 := K.equivMapOfInjective j (inclusion_injective _)
  let eq : (K ⧸ pCore 2 K) ≃* (K0 ⧸ pCore 2 K0) :=
    QuotientGroup.congr _ _ f (pCore_map_iso 2 f)
  have hnat : IsNaturalModule L (layer L R) n := hnatural.1 ▸ hnatural.2.1
  let hKN := local_field_five_component_normalizer h hnat hfield hUc K hK (eK.trans eJ)
  have hKmap : K0.map pN = K.map jN := by rw [map_map]; rfl
  let : K0.Normal := ⟨by
    intro k hk x
    apply (mem_map_iff_mem (show Function.Injective pN from inclusion_injective _)).mp
    have hh := hKN.conj_mem (pN k) (hKmap ▸ mem_map_of_mem pN hk) (pN x)
    rw [←hKmap] at hh
    simpa only [map_mul,map_inv] using hh⟩
  let π := (action (layer L R) U).rangeRestrict
  obtain ⟨τ,hτ,htScalar⟩ := natural_moved_scalar_extension j π ρ η hr K J hKJ
    F a ⟨d,mem_sup_right hd⟩ z hscalar
  let e0 := (eq.symm.trans eK).trans a.groupEquiv
  have ht (k : K0) (v : Fin 2 → F.Carrier) :
      τ k v = (e0 (QuotientGroup.mk' (pCore 2 K0) k)).val.mulVec v := by
    obtain ⟨k,rfl⟩ := f.surjective k
    change τ (j (k : H)) v =
      (a.groupEquiv (eK (eq.symm (eq (QuotientGroup.mk' (pCore 2 K) k))))).val.mulVec v
    rw [eq.symm_apply_apply]
    exact (hτ k v).trans (congrArg
      (fun t : J => (a.groupEquiv t).val.mulVec v) (Subtype.ext (heK k).symm))
  have hc : center (K0 ⧸ pCore 2 K0) = ⊥ :=
    five_quotient_center ((eq.symm.trans eK).trans eJ)
  obtain ⟨S,_,hDS,hSM⟩ := local_field_residual_sylow h hnatural hE hfield hUc
  obtain ⟨Q,hQ⟩ := S.exists_subgroupOf_eq_of_subnormal K hK.subnormal
  let R0 := (S : Subgroup H).map j
  let Q0 := Q.mapSurjective (f := f.toMonoidHom) f.surjective
  have hR : IsPGroup 2 R0 := S.isPGroup'.map j
  have hRK : R0 ≤ normalizer (K0 : Set P) := by rw [K0.normalizer_eq_top]; exact le_top
  have hQR : (Q0 : Subgroup K0).map K0.subtype ≤ R0 := by
    rintro _ ⟨k,hk,rfl⟩
    obtain ⟨l,hl,rfl⟩ := hk
    rw [hQ] at hl
    exact mem_map_of_mem j hl
  have hRmap : R0.map P.subtype = (S : Subgroup H).map H.subtype := by rw [map_map]; rfl
  have hNM : normalizer (R0 : Set P) ≤ M.subgroupOf P := by
    intro x hx
    have hh := R0.le_normalizer_map P.subtype (mem_map_of_mem P.subtype hx)
    rw [hRmap] at hh
    exact hSM hh
  let x : P := ⟨d,mem_sup_right hd⟩
  have hxR : x ∈ normalizer (R0 : Set P) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply map_injective (f := P.subtype) P.subtype_injective
    rw [map_map]
    have he : P.subtype.comp (MulAut.conj x).toMonoidHom =
        (MulAut.conj d).toMonoidHom.comp P.subtype := by ext y; rfl
    change R0.map (P.subtype.comp (MulAut.conj x).toMonoidHom) = R0.map P.subtype
    rw [he,←map_map,hRmap]
    exact mem_normalizer_iff_map_conj_eq.mp (hDS hd)
  have hle := natural_scalar_normalizer_contained (by rw [F.card_eq,hF]; rfl)
    K0 R0 (M.subgroupOf P) hR hRK e0 hc τ ht Q0 hQR hNM x hxR z hz0 hz1 htScalar
  apply hescape Q
  rintro _ ⟨k,hk,rfl⟩
  obtain ⟨l,hl,rfl⟩ := hk
  have hD : (((pResidual 2 (normalizer (Q : Set K))).map
      (normalizer (Q : Set K)).subtype).map f.toMonoidHom) =
      (pResidual 2 (normalizer (Q0 : Set K0))).map
        (normalizer (Q0 : Set K0)).subtype := by
    rw [map_embedded_pResidual,Q.normalizer_map_surjective f.toMonoidHom f.surjective]
    rfl
  exact hle (mem_map_of_mem K0.subtype (hD ▸ mem_map_of_mem f.toMonoidHom hl))

end LocalFieldQuotientAction
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
