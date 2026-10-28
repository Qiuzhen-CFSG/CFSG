module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourRadicalPlacement
public import Theory.Representation.AbelianAffineDegree.FaithfulRestriction

/-!
# The nilpotent elementary-omega branch at the Hermitian normalizer

In the nilpotent A.3.6 alternative, the component quotient by its full Fitting
subgroup acts faithfully as SL₂(5) on an elementary omega plane. Nontriviality
of that plane's action on the source section makes its restriction faithful.
An order-24 free subgroup in the plane automizer then forces binary degree
at least 24, even when other Fitting primes or higher homocyclic layers remain
in the component-action kernel.

At the actual parameter-one selected Hermitian pair, the source section has
degree at most ten. The resulting contradiction excludes every elementary
radical quotient in the nilpotent alternative. The Chapter 12 consumer proves
radical placement and applies this result on both weak-closure branches.
The extraspecial radical case and 8.2.8--13 remain separate obligations.

Source: Aschbacher--Smith, A.3.6 and 8.2.7, printed pp.43--45,717--718,
refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open Chapter1 Chapter1.Section02 Chapter1.RadicalActions
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
open Normalizer.ComponentExclusion Normalizer.ComponentExclusion.ChiefAction

/-- The elementary omega plane in the nilpotent alternative already forces
binary degree at least 24. The whole component action may have a kernel. -/
theorem nilpotent_omega_plane_degree
    {K W : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (hnil : A36Nilpotent K) (p : ℕ) [Fact p.Prime]
    (hd : p ∣ Nat.card (fittingSubgroup K))
    [IsElementaryAbelian p (omegaCore p K)]
    (τ : K →* MulAut W) (hactive : ¬ omegaCore p K ≤ τ.ker) :
    24 ≤ Module.finrank (ZMod 2) (Additive W) := by
  let N := omegaCore p K
  let : Fact (IsPGroup p N) := ⟨IsElementaryAbelian.isPGroup p N⟩
  let e : (N ⧸ frattini N) ≃* N := frattiniQuotientEquivOfIsElementaryAbelian (p := p)
  have hp : 3 < p := (Chapter1.RadicalStructure.radical_core (Or.inr hnil) hd).2.1
  have ho : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  have hcard : Nat.card N = p^2 :=
    (Nat.card_congr e.toEquiv).symm.trans (Nilpotent.frattini_shape hnil hd).2
  let S : Sylow 2 K := Classical.arbitrary _
  have hi := (CenterFrattiniSource.nilpotent_sylow_actions hnil ho hd S).1
  have heq (g : K) (x : N) :
      omegaFrattiniAction p K g (e.symm x) = e.symm (omegaCoreAction p K g x) := by
    change quotientAut (frattini N) (omegaCoreAction p K g)
      (QuotientGroup.mk' (frattini N) x) = QuotientGroup.mk' _ _
    exact quotientAut_apply_mk _ _ _
  have hf : Function.Injective (τ.comp N.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    let A := (τ.comp N.subtype).ker
    have hstable : ∀ s : S, ∀ x, x ∈ A.map e.symm.toMonoidHom →
        omegaFrattiniAction p K s x ∈ A.map e.symm.toMonoidHom := by
      rintro s x ⟨a,ha,rfl⟩
      refine ⟨omegaCoreAction p K s a,?_,(heq s a).symm⟩
      change τ ((s : K) * (a : K) * (s : K)⁻¹) = 1
      have hh : τ a = 1 := ha
      simp only [map_mul,map_inv,hh,mul_one,mul_inv_cancel]
    rcases hi _ hstable with hb | ht
    · exact (map_eq_bot_iff_of_injective _ e.symm.injective).mp hb
    · exfalso
      apply hactive
      have htop : A = ⊤ := by
        apply map_injective (f := e.symm.toMonoidHom) e.symm.injective
        rw [map_top_of_surjective _ e.symm.surjective]
        exact ht
      intro x hx
      exact show (⟨x,hx⟩ : N) ∈ A from htop ▸ mem_top _
  obtain ⟨q,hq⟩ := CenterFrattiniSource.nilpotent_exists_inverting_quotient hnil ho hd
  let α : SL(2,ZMod 5) →* MulAut N := (MulAut.congr e).toMonoidHom.comp
    ((Nilpotent.quotientAction hnil hd).comp q.symm.toMonoidHom)
  have hα : Function.Injective α := (MulAut.congr e).injective.comp
    ((Nilpotent.quotientAction_injective_of_inversion hnil hd
      (by simp : Nat.card (ZMod 5) = 5) q hq).comp q.symm.injective)
  obtain ⟨C,hC,hfree⟩ := Matrix.SpecialLinearGroup.AffineFreeAction.exists_free_twentyFour_sl25
    hp hcard α hα
  let π := q.toMonoidHom.comp (QuotientGroup.mk' (generalizedFitting K))
  have hconj (g : K) : α (π g) = MulAut.conjNormal (H := N) g := by
    apply MulEquiv.ext
    intro x
    change e (Nilpotent.quotientAction hnil hd
      (q.symm (q (QuotientGroup.mk' _ g))) (e.symm x)) = _
    rw [q.symm_apply_apply,Nilpotent.quotientAction_apply_mk,heq,e.apply_symm_apply]
    rfl
  let : MulDistribMulAction K W := MulDistribMulAction.compHom W τ
  let ρ := Representation.ofElementaryAbelianAction (A := K) (G := W) (p := 2)
  have hρ : Function.Injective (ρ.comp N.subtype) := by
    intro x y hh
    apply hf
    ext w
    exact Additive.ofMul.injective
      (congrArg (fun f : Module.End (ZMod 2) (Additive W) => f (Additive.ofMul w)) hh)
  let : Nontrivial N := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; nlinarith)
  have hodd : Odd (Nat.card N) := by rw [hcard]; exact ho.pow
  have hbound := Representation.card_le_finrank_of_free_quotientAction_of_faithful_restriction
    ρ N hρ (ZMod.natCast_ne_zero_iff_odd.mpr hodd) π
    (q.surjective.comp (QuotientGroup.mk'_surjective _)) α hconj C hfree
  rwa [hC] at hbound


universe u
variable {G : Type u} [Group G] [Finite G]

/-- Nilpotence of the entire generalized Fitting subgroup rules out the
quasisimple alternative, without a center--Frattini assertion. -/
theorem nilpotent_not_quasisimple {A : Type*} [Group A] [Finite A]
    (hnil : A36Nilpotent A) : ¬ IsQuasisimple A := by
  intro hq
  let := hq
  have hf : fittingSubgroup A = ⊤ :=
    hnil.1.symm.trans generalizedFitting_eq_top_of_quasisimple
  let e := (MulEquiv.subgroupCongr hf).trans topEquiv
  let : IsSimpleGroup (A ⧸ center A) := IsQuasisimple.simple
  let : Nontrivial A := Function.Surjective.nontrivial
    (QuotientGroup.mk'_surjective (center A))
  exact Group.IsPerfect.not_isSolvable A
    (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

/-- The nilpotent alternative supplies the actual Xi radical and its odd
quotient, including both elementary and extraspecial possibilities. -/
theorem nilpotent_radical_member {κ : GroupClass.{u}}
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK κ E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
        C.IsCComponent → A36Conclusion C)
    {T K : Subgroup G} (hK : K ∈ Chapter1.L G T)
    (hQ : IsSQTK κ ((K ⊔ T : Subgroup G) ⧸ pCore 2 (K ⊔ T : Subgroup G)))
    (hTK : T ≤ normalizer (K : Set G))
    (p : ℕ) [Fact p.Prime] (hnil : A36Nilpotent (XiQuotient K))
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient K))) :
    3 < p ∧ XiOddQuotient p (XiQuotient (XiP p K)) ∧ XiMember T (XiP p K) := by
  have hp := (Chapter1.RadicalStructure.radical_core (Or.inr hnil) hd).2.1
  have ho : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  have hn := nilpotent_not_quasisimple hnil
  have hq := (XiP_oddQuotient_of_A36 hA36 hK hQ hn ho hd).2
  exact ⟨hp,hq,XiP_isPPerfect p K,XiP_invariant p hTK,XiP_join_mem_H p hK,
    ⟨p,Fact.out,ho,hq⟩,
    RadicalActions.XiP_irreducible_of_A36 hA36 hK hQ hn hTK ho hd⟩

private theorem nilpotent_elementary_quotient_card (p : ℕ) [Fact p.Prime]
    (K : Subgroup G) (hnil : A36Nilpotent (XiQuotient K))
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient K)))
    [IsElementaryAbelian p (XiQuotient (XiP p K))] :
    Nat.card (XiQuotient (XiP p K)) = p^2 := by
  have hp := (Chapter1.RadicalStructure.radical_core (Or.inr hnil) hd).2.1
  have ho : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  let e := xiPQuotientEquivCore ho K
  let : IsElementaryAbelian p (omegaCore p (XiQuotient K)) :=
    IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective
  let : Fact (IsPGroup p (omegaCore p (XiQuotient K))) := ⟨IsElementaryAbelian.isPGroup p _⟩
  let f := frattiniQuotientEquivOfIsElementaryAbelian (R := omegaCore p (XiQuotient K)) (p := p)
  exact (Nat.card_congr e.toEquiv).trans
    ((Nat.card_congr f.toEquiv).symm.trans (Nilpotent.frattini_shape hnil hd).2)

private theorem nilpotent_residual_inverter
    {X H V : Subgroup G} {p : ℕ} [Fact p.Prime]
    [IsElementaryAbelian 2 V] [IsElementaryAbelian p (XiQuotient X)]
    (S : Sylow 2 H) (hmin : ChapterB.IsMinimalParabolicOver S ⊤)
    (hsol : Group.IsSolvable H) (hVH : V ≤ H) (hVS : V.subgroupOf H ≤ S)
    (hSV : (S : Subgroup H) ≤ normalizer (V.subgroupOf H : Set H))
    (hcard : Nat.card ((V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 2)
    (hX : (pResidual 2 H).map H.subtype = X) :
    ∃ v : V, ∀ x ∈ X, (v : G)*x*(v : G)⁻¹*x ∈ H.pCoreIn 2 := by
  let R := pResidual 2 H
  let e : R ≃* X := (R.equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr hX)
  let eq := QuotientGroup.congr (pCore 2 R) (pCore 2 X) e (pCore_map_iso 2 e)
  let : IsElementaryAbelian p (R ⧸ pCore 2 R) :=
    IsElementaryAbelian.of_surjective eq.symm.toMonoidHom eq.symm.surjective
  have hc : pCore 2 R = (pCore 2 H).subgroupOf R :=
    pCore_subnormal_eq_comap 2 (inferInstance : R.Normal).isSubnormal
  let eqc := QuotientGroup.quotientMulEquivOfEq hc
  let : IsElementaryAbelian p (R ⧸ (pCore 2 H).subgroupOf R) :=
    IsElementaryAbelian.of_surjective eqc.toMonoidHom eqc.surjective
  let : Fact (IsPGroup p (R ⧸ (pCore 2 H).subgroupOf R)) :=
    ⟨IsElementaryAbelian.isPGroup p _⟩
  have hf : frattini (R ⧸ (pCore 2 H).subgroupOf R) = ⊥ :=
    frattini_eq_bot_of_isElementaryAbelian (p := p)
  let : IsElementaryAbelian 2 (V.subgroupOf H) := IsElementaryAbelian.subgroupOf hVH
  obtain ⟨v,hv,hi⟩ := DihedralCubic.source_residual_frattini_inverter S hmin hsol
    (V.subgroupOf H) hVS (normal_subgroupOf_of_le_normalizer hSV) hcard
  refine ⟨⟨v,hv⟩,?_⟩
  intro x hx
  obtain ⟨r,hr,hrx⟩ := hX.symm ▸ hx
  have hh := hi ⟨r,hr⟩
  change QuotientGroup.mk' ((pCore 2 H).subgroupOf R)
    ((MulAut.conjNormal v : MulAut R) ⟨r,hr⟩ * ⟨r,hr⟩) ∈
      frattini (R ⧸ (pCore 2 H).subgroupOf R) at hh
  rw [hf,mem_bot] at hh
  have hm := (QuotientGroup.eq_one_iff _).mp hh
  refine ⟨v*r*v⁻¹*r,hm,?_⟩
  change (v : G)*(r : G)*(v : G)⁻¹*(r : G) = _
  change (r : G) = x at hrx
  rw [hrx]

/-- The nilpotent elementary-omega alternative cannot occur at a reselected Hermitian
pair in the radical's actual Sylow join. -/
theorem selected_one_nilpotent_elementary_exclusion
    {κ : GroupClass} {V H M I K : Subgroup G} [IsElementaryAbelian 2 V]
    {T : Sylow 2 G} {i : I} {S : Sylow 2 I}
    (s : Selected H T M V I 1 i S)
    (h28 : HypothesisE28 κ H T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hT : HypothesisE322 V T) (hE : IsEvenCharacteristicAt T)
    (e : Additive V ≃ₗ[ZMod 2] Space 1)
    (j : Automizer V →* binaryNormalizer 1) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction 1 (binaryNormalizer 1) (j a) (e v))
    (p : ℕ) [Fact p.Prime]
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK κ E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
        C.IsCComponent → A36Conclusion C)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hQ : IsSQTK κ ((K ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G)))
    (hjoin : XiP p K ⊔ (T : Subgroup G) = H)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKU : K ≤ normalizer
      (V ⊓ centralizer (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G) : Set G))
    (hnil : A36Nilpotent (XiQuotient K))
    [IsElementaryAbelian p (XiQuotient (XiP p K))]
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient K))) : False := by
  obtain ⟨hp,_,hXi⟩ := nilpotent_radical_member hA36 hK hQ hTK p hnil hd
  let X := XiP p K
  let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2
  let U := V ⊓ centralizer (A : Set G)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ V from inf_le_left)
  have hel : IsElementaryAbelian p (XiQuotient X) := inferInstance
  have hqcard := nilpotent_elementary_quotient_card p K hnil hd
  have ho : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  have hq : XiOddQuotient p (XiQuotient X) := Or.inl ⟨hel,hqcard⟩
  have hres : X = (pResidual 2 H).map H.subtype := by
    rw [←hjoin]
    exact (embedded_pResidual_join_pGroup X T hXi.perfect T.isPGroup' hXi.invariant).symm
  let : Group.IsSolvable X := hXi.isSolvable
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  have hsol : Group.IsSolvable H := hjoin ▸ Group.isSolvable_sup_of_normalizes X T hXi.invariant
  have hTH : (T : Subgroup G) ≤ H := hjoin ▸ le_sup_right
  have hSyl : IsSylowIn 2 (T : Subgroup G) H :=
    ⟨T.subtype hTH,map_subgroupOf_eq_of_le hTH⟩
  have hQT := hXi.pCoreIn_le_of_isSylowIn (hSyl.restrict le_sup_right hjoin.le)
  have hcentric := hXi.mem_He (fun _ hM _ hN hNM hn => lemma_1_1_3_1 hM hN hNM hn)
    (lemma_1_1_4_6 T hE)
  obtain ⟨_,_,_,hu,hUeq,_,hTU,hIC,_,_⟩ := selected_one_fixed_subgroup s hT 1 e j hj he
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  have hUI : U ≤ I := inf_le_left.trans hVI
  have hU2 : IsPGroup 2 U := IsElementaryAbelian.isPGroup 2 U
  have hUP : U ≤ I.pCoreIn 2 := le_pCoreIn_of_normalizes hU2 hUI
    (hIC.trans (Subgroup.centralizer_le_normalizer _))
  have hUB : U ≤ V ⊓ I.pCoreIn 2 := le_inf inf_le_left hUP
  have hHU : H ≤ normalizer (U : Set G) := by
    rw [←hjoin]
    exact sup_le ((XiP_le p K).trans hKU) hTU
  have hP : I.pCoreIn 2 = ⁅I.pCoreIn 2,(pResidual 2 I).map I.subtype⁆ ⊔ U := by
    exact (selected_one_core_residual_product s).trans
      (congrArg (fun Z => ⁅I.pCoreIn 2,(pResidual 2 I).map I.subtype⁆ ⊔ Z) hUeq.symm)
  have hodd : Odd (Nat.card (XiQuotient X)) := by rw [hqcard]; exact ho.pow
  have hcore := pair_core_le I H X U s.family.le_ambient hres hUI hU2 hHU hodd hP
  have hk : (V ⊓ I.pCoreIn 2).relIndex V = 2 := by
    have hr := s.rank_eq
    change rank ((V.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))) = 1 at hr
    rw [quotient_rank_eq_core_corank I V hVI] at hr
    change subgroupCorank V (V ⊓ I.pCoreIn 2) = 1 at hr
    have hh := relIndex_eq_two_pow_quotient_finrank V (V ⊓ I.pCoreIn 2)
    rw [←log_relIndex_eq_quotient_finrank] at hh
    change (V ⊓ I.pCoreIn 2).relIndex V = 2 ^ subgroupCorank V (V ⊓ I.pCoreIn 2) at hh
    simpa only [hr,pow_one] using hh
  obtain ⟨S₂,hS₂,hmin,_⟩ := h28.minimal
  have hVS : V.subgroupOf H ≤ S₂ := by rw [hS₂]; exact comap_mono hT.le_sylow
  have hSV : (S₂ : Subgroup H) ≤ normalizer (V.subgroupOf H : Set H) := by
    rw [hS₂,←subgroupOf_normalizer_eq (hT.le_sylow.trans hTH)]
    exact comap_mono hT.normalizes
  have hVcardH : Nat.card ((V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 2 := by
    rw [←relIndex_ker,QuotientGroup.ker_mk']
    have hQ : (H.pCoreIn 2).subgroupOf H = pCore 2 H := by
      exact comap_map_eq_self_of_injective H.subtype_injective _
    rw [←hQ,relIndex_subgroupOf (hT.le_sylow.trans hTH),←inf_relIndex_right]
    rw [inf_comm (H.pCoreIn 2) V,←pair_core_intersection I H V s.family.le_ambient hVI hcore]
    exact hk
  obtain ⟨v,hinv⟩ := nilpotent_residual_inverter (p := p) S₂ hmin hsol (hT.le_sylow.trans hTH)
    hVS hSV hVcardH hres.symm
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := X)
  let Y := (P : Subgroup X).map X.subtype
  let eY := hXi.ambientSylowQuotientEquiv ho hq P
  let : IsElementaryAbelian p Y := IsElementaryAbelian.of_surjective eY.symm.toMonoidHom eY.symm.surjective
  have hYcard : Nat.card Y = p^2 := (Nat.card_congr eY.toEquiv).trans hqcard
  have hUcard : Nat.card U = 16 := by
    obtain ⟨a,ha⟩ := hU2.exists_card_eq
    change rank U = 4 at hu
    rw [rank,ha,Nat.log_pow Nat.one_lt_two] at hu
    simpa [hu] using ha
  have hVcard : Nat.card V = 512 := by
    change Nat.card (Additive V) = 512
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,e.finrank_eq,finrank_binary]
    norm_num
  obtain ⟨hJR,D,hUD,hDR,hJD,hN,ρ,hρ,helem,hne,hirr,hfull,hactive,_hker,hsmall⟩ :=
    exists_bounded_component_section p hp K U V T Y H I hTK hKU hTU hQT
      (inf_le_left.trans hT.le_sylow) T.isPGroup' (map_subtype_le _) P rfl hYcard
      hq.isPGroup hcentric hres (selected_generates_hstar s hH) hIC
      hVI hT.le_sylow hT.normalizes hUB hk hUcard (Or.inl hVcard) v
      (fun y hy => hinv y ((map_subtype_le _) hy))
  let := hN
  let := helem
  let := hne
  have hKperfect : Group.IsPerfect K := by
    let e : K.subgroupOf (K ⊔ (T : Subgroup G)) ≃* K := subgroupOfEquivOfLe le_sup_left
    let := hK.1.perfect
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let := hKperfect
  let : Group.IsPerfect (XiQuotient K) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (pCore 2 K)) (QuotientGroup.mk'_surjective _)
  let eq := xiPQuotientEquivCore ho K
  let : IsElementaryAbelian p (omegaCore p (XiQuotient K)) :=
    IsElementaryAbelian.of_surjective eq.toMonoidHom eq.surjective
  have hQker := core_killed (K ⊔ (T : Subgroup G)) K ρ (sup_le K.le_normalizer hTK) hirr
  let τ := ExtensionImage.componentQuotientAction (K ⊔ (T : Subgroup G)) K le_sup_left ρ hQker
  have hact := ExtensionImage.omega_active p (K ⊔ (T : Subgroup G)) K Y le_sup_left
    (map_subtype_le _) ρ hQker hactive
  have hlarge := nilpotent_omega_plane_degree hnil p hd τ hact
  omega

/-- After exclusion of elementary omega, the full odd core is extraspecial;
all higher homocyclic exponents are excluded at once. -/
theorem nilpotent_core_extraspecial_of_not_elementary
    {G : Type*} [Group G] [Finite G] (K : Subgroup G)
    (hnil : A36Nilpotent (XiQuotient K)) (p : ℕ) [Fact p.Prime]
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient K)))
    (he : ¬ IsElementaryAbelian p (XiQuotient (XiP p K))) :
    LocalModels.OddExtraspecialThree p (pCore p (XiQuotient K)) ∧
      IsExtraspecial p (XiQuotient (XiP p K)) ∧
      Nat.card (XiQuotient (XiP p K)) = p^3 ∧
      Monoid.exponent (XiQuotient (XiP p K)) = p := by
  have hp := (Chapter1.RadicalStructure.radical_core (Or.inr hnil) hd).2.1
  have ho : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  have hfull : LocalModels.OddExtraspecialThree p (pCore p (XiQuotient K)) := by
    rcases (hnil.2.2.2 p Fact.out (hnil.1.symm ▸ hd)).2 with hx | hh
    · exact hx
    · exfalso
      apply he
      obtain ⟨a,_,⟨e⟩⟩ := hh
      let : IsMulCommutative (pCore p (XiQuotient K)) :=
        IsMulCommutative.of_comm (fun x y => e.injective (by simp only [map_mul,mul_comm]))
      let : IsElementaryAbelian p (omega (pCore p (XiQuotient K)) (p := p) 1) :=
        IsElementaryAbelian.omega₁_of_isMulCommutative _
      let e' := xiPQuotientEquivOmega ho K
      exact IsElementaryAbelian.of_surjective e'.symm.toMonoidHom e'.symm.surjective
  have hq := ((Chapter1.RadicalStructure.core_omega (Or.inr hnil) hd).2).of_mulEquiv
    (xiPQuotientEquivOmega ho K).symm
  exact ⟨hfull,hq.resolve_left (fun hh => he hh.1)⟩

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
