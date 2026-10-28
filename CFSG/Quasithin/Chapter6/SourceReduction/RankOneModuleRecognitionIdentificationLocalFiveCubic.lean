module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFiveNormal
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFiveNormalizer
public import Theory.GroupTheory.PCoreQuotientInnerSupplement
public import Theory.SpecificGroups.SymmetricFive.SylowNormalizer

/-!
# Cubic centralization of the lifted A5 component in source 6.2.7

Let R be the arranged Sylow subgroup of C_G(U), and K the normal lifted
A5 component. If R acts innerly on K/O2(K), the inner-supplement theorem
factors R as (R ∩ K)O2(KR). Then the intrinsic Sylow normalizer in K
normalizes R, contradicting its already proved escape from M.

Thus the two-action image of R contains an outer automorphism and a full
inner Sylow four-group: it is Sylow in Aut(A5) = S5. The original cubic
normalizes R and K, hence this image. Sylow two-normalizers in S5 are
two-groups, forcing the cubic action on K/O2(K) to be trivial. The original
component quotient equivalence transfers centralization to its marked
linear action, without changing the field-plane quotient coordinates.

The Chapter12 companion applies this to the same escaping component.
The scalar/field-automorphism contradiction remains for the A5 exclusion.
Source: Aschbacher--Smith, final paragraph of 6.2.7, printed p.684.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition

private noncomputable def fiveAutEquiv {X : Type*} [Group X]
    (e : X ≃* alternatingGroup (Fin 5)) : MulAut X ≃* Equiv.Perm (Fin 5) :=
  (MulAut.congr e).trans (MulEquiv.ofBijective MulAut.conjNormal
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide))).symm

private theorem fiveCenter {X : Type*} [Group X]
    (e : X ≃* alternatingGroup (Fin 5)) : center X = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  apply e.injective
  have he : e x = 1 := (alternatingGroup.center_eq_bot (by simp)).le
    ((centerCongr e) ⟨x,hx⟩).property
  simpa only [map_one] using he

private theorem five_actor_sylow {X : Type*} [Group X] [Finite X]
    (e : X ≃* alternatingGroup (Fin 5)) (P : Sylow 2 X)
    (A : Subgroup (MulAut X)) (hA : IsPGroup 2 A)
    (hPA : (P : Subgroup X).map MulAut.conj ≤ A)
    (hnot : ¬ A ≤ MulAut.innerSubgroup X) :
    ∃ S : Sylow 2 (MulAut X), (S : Subgroup (MulAut X)) = A := by
  classical
  have hX : Nat.card X = 60 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hAut : Nat.card (MulAut X) = 120 := by
    rw [Nat.card_congr (fiveAutEquiv e).toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    norm_num [Nat.factorial]
  have hP : Nat.card P = 4 := by
    rw [P.card_eq_multiplicity,hX]
    decide +kernel
  let I := (P : Subgroup X).map MulAut.conj
  have hI : Nat.card I = 4 := by
    rw [card_map_of_injective (MulAut.conj_injective_of_center_eq_bot (fiveCenter e)),hP]
  have hlt : I < A := lt_of_le_of_ne hPA (by
    intro he
    apply hnot
    rw [←he]
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨x,rfl⟩)
  have hlo : 4 < Nat.card A := by
    by_contra! hn
    exact hlt.ne (eq_of_le_of_card_ge hPA (by rw [hI]; exact hn))
  obtain ⟨S,hAS⟩ := hA.exists_le_sylow
  have hS : Nat.card S = 8 := by
    rw [S.card_eq_multiplicity,hAut]
    decide +kernel
  have hd : Nat.card A ∣ 2^3 := by simpa only [hS,Nat.reducePow] using card_dvd_of_le hAS
  obtain ⟨k,hk,hkc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hc : Nat.card A = 8 := by
    interval_cases k <;> norm_num only [Nat.reducePow] at hkc <;> omega
  exact ⟨S,eq_of_le_of_card_ge hAS (by rw [hS,hc]) |>.symm⟩

private theorem five_cubic_normalizer {X : Type*} [Group X] [Finite X]
    (e : X ≃* alternatingGroup (Fin 5)) (P : Sylow 2 X)
    (A : Subgroup (MulAut X)) (hA : IsPGroup 2 A)
    (hPA : (P : Subgroup X).map MulAut.conj ≤ A)
    (hnot : ¬ A ≤ MulAut.innerSubgroup X)
    (b : MulAut X) (hb : b^3=1) (hbn : b ∈ normalizer (A : Set (MulAut X))) : b=1 := by
  obtain ⟨S,hS⟩ := five_actor_sylow e P A hA hPA hnot
  let E := fiveAutEquiv e
  let S' := S.mapSurjective (f := E.toMonoidHom) E.surjective
  have hself : normalizer (A : Set (MulAut X)) = A := by
    apply map_injective (f := E.toMonoidHom) E.injective
    rw [map_equiv_normalizer_eq,←hS]
    exact Theory.SpecificGroups.SymmetricFive.SylowNormalizer.sylow_normalizer_eq_self S'
  have hbA : b ∈ A := hself ▸ hbn
  have hb1 : (⟨b,hbA⟩ : A)=1 := by
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes
      (hA.orderOf_coprime (by decide : Nat.Coprime 2 3) ⟨b,hbA⟩) dvd_rfl
      (orderOf_dvd_of_pow_eq_one (Subtype.ext hb))
  exact congrArg Subtype.val hb1

private theorem five_cubic_action_eq_one_of_normalizer_escape
    {X : Type*} [Group X] [Finite X]
    (K R M : Subgroup X) (hR : IsPGroup 2 R)
    (hRK : R ≤ normalizer (K : Set X))
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (P : Sylow 2 K) (hPR : (P : Subgroup K).map K.subtype ≤ R)
    (hNM : normalizer (R : Set X) ≤ M)
    (hescape : ¬ (((pResidual 2 (normalizer (P : Set K))).map
      (normalizer (P : Set K)).subtype).map K.subtype) ≤ M)
    (d : X) (hdK : d ∈ normalizer (K : Set X))
    (hdR : d ∈ normalizer (R : Set X)) (hd : d^3=1) :
    quotientAut (pCore 2 K) (K.normalizerMonoidHom ⟨d,hdK⟩) = 1 := by
  let N := normalizer (K : Set X)
  let q := QuotientGroup.mk' (pCore 2 K)
  let f := (quotientAut (pCore 2 K)).comp K.normalizerMonoidHom
  let A := (R.subgroupOf N).map f
  let Q := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hf (k : K) : f ⟨k,K.le_normalizer k.property⟩ = MulAut.conj (q k) := by
    exact pCoreJoinAction_on_component 2 hRK k
  have hA : IsPGroup 2 A := hR.comap_subtype.map f
  have hQA : (Q : Subgroup (K ⧸ pCore 2 K)).map MulAut.conj ≤ A := by
    rintro _ ⟨v,hv,rfl⟩
    obtain ⟨k,hk,rfl⟩ := hv
    exact ⟨⟨k,K.le_normalizer k.property⟩,hPR (mem_map_of_mem K.subtype hk),hf k⟩
  have hnot : ¬ A ≤ MulAut.innerSubgroup (K ⧸ pCore 2 K) := by
    intro hi
    have hfactor := sup_core_factor_of_inner_action K R hRK hR (fiveCenter e) P hPR
      (fun r => hi (mem_map_of_mem f (show (⟨r,hRK r.property⟩ : N) ∈ R.subgroupOf N from r.property)))
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
    exact hescape ((map_mono (map_subtype_le _)).trans (hBR.trans hNM))
  have hdn : (⟨d,hdK⟩ : N) ∈ normalizer (R.subgroupOf N : Set N) := by
    rw [←subgroupOf_normalizer_eq hRK]
    exact hdR
  apply five_cubic_normalizer e Q A hA hQA hnot (f ⟨d,hdK⟩)
  · rw [←map_pow,show (⟨d,hdK⟩ : N)^3=1 from Subtype.ext hd,map_one]
  · exact (R.subgroupOf N).le_normalizer_map f (mem_map_of_mem f hdn)

/-- The original cubic centralizes the intrinsic A5 quotient of the escaping
component, with its ambient conjugation formula retained. -/
theorem local_field_five_component_cubic
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L M R U : Subgroup G} {n : ℕ}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfield : IsInvolutoryFieldFixedSpace L M (layer L R) U n)
    (hUc : Nat.card U=4)
    (K : Subgroup (centralizer (U : Set G))) (hK : K.IsCComponent)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (hescape : ∀ P : Sylow 2 K, ¬ ((((pResidual 2 (normalizer (P : Set K))).map
      (normalizer (P : Set K)).subtype).map K.subtype).map
        (centralizer (U : Set G)).subtype) ≤ M)
    (d : G) (hd : d ∈ fieldLocalResidual L U) (hd3 : d^3=1) :
    ∃ a : MulAut K, quotientAut (pCore 2 K) a = 1 ∧
      ∀ k : K, ((a k : centralizer (U : Set G)) : G) =
        d * ((k : centralizer (U : Set G)) : G) * d⁻¹ := by
  let H := centralizer (U : Set G)
  let N := normalizer (U : Set G)
  let j : H →* N := inclusion (Subgroup.centralizer_le_normalizer _)
  let K0 := K.map j
  let f : K ≃* K0 := K.equivMapOfInjective j (inclusion_injective _)
  let eq : (K ⧸ pCore 2 K) ≃* (K0 ⧸ pCore 2 K0) :=
    QuotientGroup.congr _ _ f (pCore_map_iso 2 f)
  have hnat : IsNaturalModule L (layer L R) n := hnatural.1 ▸ hnatural.2.1
  let : K0.Normal := local_field_five_component_normalizer h hnat hfield hUc K hK e
  obtain ⟨S,_,hDS,hSM⟩ := local_field_residual_sylow h hnatural hE hfield hUc
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_subnormal K hK.subnormal
  let R0 := (S : Subgroup H).map j
  let P0 := P.mapSurjective (f := f.toMonoidHom) f.surjective
  have hR : IsPGroup 2 R0 := S.isPGroup'.map j
  have hRK : R0 ≤ normalizer (K0 : Set N) := by rw [K0.normalizer_eq_top]; exact le_top
  have hPR : (P0 : Subgroup K0).map K0.subtype ≤ R0 := by
    rintro _ ⟨k,hk,rfl⟩
    obtain ⟨l,hl,rfl⟩ := hk
    rw [hP] at hl
    exact mem_map_of_mem j hl
  have hRmap : R0.map N.subtype = (S : Subgroup H).map H.subtype := by
    rw [map_map]
    rfl
  have hNM : normalizer (R0 : Set N) ≤ M.subgroupOf N := by
    intro x hx
    have hh := R0.le_normalizer_map N.subtype (mem_map_of_mem N.subtype hx)
    rw [hRmap] at hh
    exact hSM hh
  have hesc : ¬ (((pResidual 2 (normalizer (P0 : Set K0))).map
      (normalizer (P0 : Set K0)).subtype).map K0.subtype) ≤ M.subgroupOf N := by
    intro hh
    apply hescape P
    rintro _ ⟨k,hk,rfl⟩
    obtain ⟨l,hl,rfl⟩ := hk
    have hD : (((pResidual 2 (normalizer (P : Set K))).map
        (normalizer (P : Set K)).subtype).map f.toMonoidHom) =
        (pResidual 2 (normalizer (P0 : Set K0))).map
          (normalizer (P0 : Set K0)).subtype := by
      rw [map_embedded_pResidual,P.normalizer_map_surjective f.toMonoidHom f.surjective]
      rfl
    exact hh (mem_map_of_mem K0.subtype (hD ▸ mem_map_of_mem f.toMonoidHom hl))
  let x : N := ⟨d,(map_subtype_le _ hd).2⟩
  have hxK : x ∈ normalizer (K0 : Set N) := by rw [K0.normalizer_eq_top]; trivial
  have hxR : x ∈ normalizer (R0 : Set N) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply map_injective (f := N.subtype) N.subtype_injective
    rw [map_map]
    have hc : N.subtype.comp (MulAut.conj x).toMonoidHom =
        (MulAut.conj d).toMonoidHom.comp N.subtype := by
      ext y
      rfl
    change R0.map (N.subtype.comp (MulAut.conj x).toMonoidHom) = R0.map N.subtype
    rw [hc,←map_map,hRmap]
    exact mem_normalizer_iff_map_conj_eq.mp (hDS hd)
  let b := K0.normalizerMonoidHom ⟨x,hxK⟩
  have hb : quotientAut (pCore 2 K0) b = 1 :=
    five_cubic_action_eq_one_of_normalizer_escape K0 R0 (M.subgroupOf N)
      hR hRK (eq.symm.trans e) P0 hPR hNM hesc x hxK hxR (Subtype.ext hd3)
  let a := MulAut.congr f.symm b
  have hf (k : K) : f (a k) = b (f k) := by simp [a]
  refine ⟨a,?_,fun k => congrArg (fun z : K0 => ((z : N) : G)) (hf k)⟩
  apply MulEquiv.ext
  intro z
  obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) z
  rw [quotientAut_apply_mk]
  apply eq.injective
  change QuotientGroup.mk' (pCore 2 K0) (f (a k)) = QuotientGroup.mk' (pCore 2 K0) (f k)
  rw [hf,←quotientAut_apply_mk,hb]
  rfl

namespace LocalFieldQuotientAction
variable {G : Type*} [Group G] [Finite G]
/-- Centralization on every actual A₅ action component, in any extension
of the original faithful-action marking to the field-plane residual. -/
theorem five_component_cubic_commutes
    {T : Sylow 2 G} {L M R U : Subgroup G} {n : ℕ}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfield : IsInvolutoryFieldFixedSpace L M (layer L R) U n)
    (hUc : Nat.card U = 4)
    (J : Subgroup (action (layer L R) U).range)
    (e : J ≃* alternatingGroup (Fin 5))
    (K : Subgroup (Centralizer U)) (hK : K.IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* J)
    (heK : ∀ k : K, ((eK (QuotientGroup.mk' (pCore 2 K) k) : J) :
      (action (layer L R) U).range) = (action (layer L R) U).rangeRestrict k)
    (hescape : ∀ P : Sylow 2 K, ¬ ((((pResidual 2 (normalizer (P : Set K))).map
      (normalizer (P : Set K)).subtype).map K.subtype).map
        (Centralizer U).subtype) ≤ M)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (action (layer L R) U).range W)
    (η : Representation (ZMod 2) (Centralizer U ⊔ fieldLocalResidual L U : Subgroup G) W)
    (hrestrict : ∀ k : Centralizer U, η (inclusion le_sup_left k) =
      ρ ((action (layer L R) U).rangeRestrict k))
    (d : G) (hd : d ∈ fieldLocalResidual L U) (hd3 : d ^ 3 = 1) :
    ∀ j : J, Commute (η.asGroupHom ⟨d,mem_sup_right hd⟩) (ρ.asGroupHom j) := by
  let H := Centralizer U
  let P := H ⊔ fieldLocalResidual L U
  let π := (action (layer L R) U).rangeRestrict
  obtain ⟨a,haq,ha⟩ := local_field_five_component_cubic h hnatural hE hfield hUc
    K hK (eK.trans e) hescape d hd hd3
  let q := QuotientGroup.mk' (pCore 2 K)
  have hπ (k : K) : π (a k) = π k := by
    have hq : q (a k) = q k := by
      have hh := congrArg (fun b : MulAut (K ⧸ pCore 2 K) => b (q k)) haq
      simpa only [q,quotientAut_apply_mk,MulAut.one_apply] using hh
    rw [←heK (a k),←heK k,hq]
  have hr (k : H) : η.asGroupHom (inclusion le_sup_left k) = ρ.asGroupHom (π k) :=
    Units.ext (hrestrict k)
  intro j
  obtain ⟨k,hk⟩ := QuotientGroup.mk'_surjective (pCore 2 K) (eK.symm j)
  have hkj : π k = (j : (action (layer L R) U).range) := by
    rw [←heK k,hk,eK.apply_symm_apply]
  let x : P := ⟨d,mem_sup_right hd⟩
  have hap : inclusion (show H ≤ P from le_sup_left) (a k : H) =
      x * inclusion le_sup_left (k : H) * x⁻¹ := Subtype.ext (ha k)
  have hc : η.asGroupHom x * ρ.asGroupHom (π k) * (η.asGroupHom x)⁻¹ =
      ρ.asGroupHom (π k) := by
    calc
      _ = η.asGroupHom (x * inclusion le_sup_left (k : H) * x⁻¹) := by
        rw [map_mul,map_mul,map_inv,hr]
      _ = ρ.asGroupHom (π (a k)) := by rw [←hap,hr]
      _ = ρ.asGroupHom (π k) := congrArg ρ.asGroupHom (hπ k)
  rw [hkj] at hc
  exact mul_inv_eq_iff_eq_mul.mp hc

/-- The original cubic section, with its marking and noncentrality claim,
augmented by the moved A5 component centralized by that same cubic. -/
@[expose] def CubicFiveSection (L B A U : Subgroup G)
    [IsElementaryAbelian 2 (space B U)] : Prop :=
    let H := LocalFieldQuotientAction.Centralizer U
    let J := conjugateSpanBy B H
    let P := H ⊔ fieldLocalResidual L U
    let W := Additive (LocalFieldQuotientAction.space B U)
    let π := (LocalFieldQuotientAction.action B U).rangeRestrict
    let I := (A.subgroupOf H).map π
    ∃ (ρ : Representation (ZMod 2) (LocalFieldQuotientAction.action B U).range W)
      (c : BinaryConjugationSection H J U (ρ.comp π)),
      Function.Injective ρ ∧ IsOffender ρ I ∧ Nat.card I = 4 ∧
      ∃ (d : G) (hd : d ∈ fieldLocalResidual L U), orderOf d = 3 ∧ ⁅B,zpowers d⁆ = B ∧
        ∃ (η : Representation (ZMod 2) P W) (c' : BinaryConjugationSection P J U η),
          c'.coordinates = c.coordinates ∧
          (∀ a : H, η (inclusion le_sup_left a) = ρ (π a)) ∧
          (∃ hd : d ∈ P, orderOf (η.asGroupHom ⟨d,hd⟩) = 3) ∧
          (∀ K : Subgroup G, A ≤ K → K ≤ H →
            (⁅K,zpowers d⁆.subgroupOf P).map η.asGroupHom = ⊥ →
            c'.imageSpace ⁅⁅J,K⁆,zpowers d⁆ ≠ ⊥) ∧
          (∀ j : J, ∃ hj : (j : G) ∈ H, LocalFieldQuotientAction.projection U ⟨j,hj⟩ =
            ((c'.coordinates j).toAdd.toMul : LocalFieldQuotientAction.Ambient U)) ∧
          ∃ K : Subgroup (LocalFieldQuotientAction.action B U).range,
            IsComponent _ K ∧ ⁅K,I⁆ = K ∧ Nonempty (K ≃* alternatingGroup (Fin 5)) ∧
            ∀ k : K, Commute (η.asGroupHom ⟨d,mem_sup_right hd⟩) (ρ.asGroupHom k)

end LocalFieldQuotientAction
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
