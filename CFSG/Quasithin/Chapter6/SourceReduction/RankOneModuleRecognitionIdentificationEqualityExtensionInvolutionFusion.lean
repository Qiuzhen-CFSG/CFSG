module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionInvolutionLifting
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionFusionQuotient
public import Theory.SpecificGroups.SymmetricFive.EvenInvolutions

/-!
# All transfer-subgroup involutions fuse to z

The canonical conjugate eight E = (V∩P)ᵍ lies in P and meets Q in ⟨z⟩.
Every involution in E is conjugate to z by natural-layer transitivity.
Its image is the outer four-group P Q/Q, so E supplies representatives
for both involution types of S₅. The same marked map identifies LP/V
with S₅. Lift a quotient conjugator into LP, then correct it inside V
using the square-root fixed-space calculation. This fuses every involution
of P(T∩L), in either centralizer alternative, to z.

This is a direct route through the source's inner and outer involution
classes; no abstract group-family tag or splitting is used.
Source: Aschbacher–Smith, proof of 6.2.13, printed p.688.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

private theorem symmetric_five_involution_fusion (s t : Equiv.Perm (Fin 5))
    (hs : s^2=1) (ht : t^2=1) (hs1 : s≠1) (ht1 : t≠1)
    (hparity : (s∈alternatingGroup (Fin 5)) ↔ (t∈alternatingGroup (Fin 5))) : IsConj s t := by
  by_cases he : s∈alternatingGroup (Fin 5)
  · exact Equiv.Perm.even_involutions_five_isConj s t ⟨he,hs,hs1⟩ ⟨hparity.mp he,ht,ht1⟩
  · have ho : ∀ s : Equiv.Perm (Fin 5), s^2=1 → s∉alternatingGroup (Fin 5) →
        s.cycleType = {2} := by
      have h : ∀ s : Equiv.Perm (Fin 5), s^2=1 → Equiv.Perm.sign s≠1 → s.cycleType={2} := by
        decide +kernel
      intro s hs he
      exact h s hs (fun hh => he (Equiv.Perm.mem_alternatingGroup.mpr hh))
    exact Equiv.Perm.isConj_of_cycleType_eq
      ((ho s hs he).trans (ho t ht (fun hh => he (hparity.mpr hh))).symm)

private theorem elementary_eight_representative
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (f : E →* Equiv.Perm (Fin 5)) (h8 : Nat.card E = 8) (hk2 : Nat.card f.ker = 2)
    (hout : ¬ f.range ≤ alternatingGroup (Fin 5))
    (t : Equiv.Perm (Fin 5)) (ht : t^2=1) (ht1 : t≠1) :
    ∃ e : E, orderOf e=2 ∧ IsConj (f e) t := by
  have hsquare (e : E) : e^2=1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 E) e
  have hf2 (e : E) : f e^2=1 := by rw [←map_pow,hsquare,map_one]
  by_cases hte : t∈alternatingGroup (Fin 5)
  · let s := Equiv.Perm.sign.comp f
    have hr : Nat.card s.range ≤ 2 := by
      have hh := Nat.card_le_card_of_injective s.range.subtype s.range.subtype_injective
      have hcard : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card]; decide
      exact hh.trans_eq hcard
    have hex : ∃ x : E, s x=1 ∧ f x≠1 := by
      by_contra! hno
      have he : s.ker=f.ker := by
        apply le_antisymm (fun x hx => hno x hx)
        intro x hx
        change Equiv.Perm.sign (f x)=1
        rw [show f x=1 from hx,map_one]
      have hc := s.ker.card_mul_index
      rw [index_ker,he,hk2,h8] at hc
      omega
    obtain ⟨x,hx,hxn⟩ := hex
    refine ⟨x,orderOf_eq_prime (hsquare x) (fun hh => hxn (hh ▸ map_one f)),?_⟩
    exact symmetric_five_involution_fusion (f x) t (hf2 x) ht hxn ht1
      ⟨fun _ => hte,fun _ => Equiv.Perm.mem_alternatingGroup.mpr hx⟩
  · obtain ⟨_,⟨x,rfl⟩,hx⟩ := SetLike.not_le_iff_exists.mp hout
    have hxn : f x≠1 := fun hh => hx (hh ▸ (alternatingGroup (Fin 5)).one_mem)
    refine ⟨x,orderOf_eq_prime (hsquare x) (fun hh => hxn (hh ▸ map_one f)),?_⟩
    exact symmetric_five_involution_fusion (f x) t (hf2 x) ht hxn ht1
      ⟨fun hh => (hx hh).elim,fun hh => (hte hh).elim⟩

/-- The canonical conjugate eight retains its ambient involution fusion. -/
theorem LocalAnalysis.equality_conjugate_eight_fusion
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    ∃ E : Subgroup G, IsElementaryAbelian 2 E ∧ Nat.card E = 8 ∧
      E ≤ (equalityCore L R z).map (centralizer ({z} : Set G)).subtype ∧
      E ⊓ (L ⊔ (T : Subgroup G)).pCoreIn 2 = zpowers z ∧
      ∀ e ∈ E, orderOf e = 2 → IsConj z e := by
  let H := centralizer ({z} : Set G)
  let P := (equalityCore L R z).map H.subtype
  let V := layer L R
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hp := A.equality_action_pair_data h611 hnatural hz horder hTH hbranch
  obtain ⟨g,hg,_,_,_,_,hi⟩ := hp.pair
  let c := (MulAut.conj g).toMonoidHom
  have hPn : H ≤ normalizer (P : Set G) := by
    have hh := (equalityCore L R z).le_normalizer_map H.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hPm : P.map c = P := (mem_normalizer_iff_map_conj_eq).mp (hPn hg)
  let E := (V ⊓ P).map c
  have hE : E = V.map c ⊓ P := by
    change (V ⊓ P).map c = _
    rw [map_inf _ _ _ (MulAut.conj g).injective,hPm]
  let : IsElementaryAbelian 2 V := h611.layer_elementary
  let : IsElementaryAbelian 2 (V ⊓ P : Subgroup G) := IsElementaryAbelian.of_injective
    (inclusion (show V ⊓ P ≤ V from inf_le_left)) (inclusion_injective _)
  have hc : Nat.card E = 8 := by
    rw [Nat.card_congr ((V ⊓ P).equivMapOfInjective c (MulAut.conj g).injective).toEquiv.symm]
    rw [equality_layer_inf_core h611 hz]
    exact A.layer_core_card
  have hEP : E ≤ P := hE ▸ inf_le_right
  refine ⟨E,IsElementaryAbelian.map c,hc,hEP,?_,?_⟩
  swap
  · rintro e ⟨v,hv,rfl⟩ he
    have hv2 : orderOf v = 2 := ((MulAut.conj g).orderOf_eq v).symm.trans he
    exact (equality_layer_involution_fusion hnatural hz horder hv.1 hv2).trans
      (isConj_iff.mpr ⟨g,rfl⟩)
  have hPQ := A.equality_core_inf_local_core h611 hnatural hz horder hTH hbranch
  change P ⊓ Q = V ⊓ P at hPQ
  have hEQ : E ⊓ Q = E ⊓ V := by
    calc
      E ⊓ Q = E ⊓ (P ⊓ Q) := by rw [←inf_assoc,inf_eq_left.mpr hEP]
      _ = E ⊓ (V ⊓ P) := by rw [hPQ]
      _ = E ⊓ V := by rw [inf_left_comm,inf_eq_left.mpr hEP,inf_comm]
  rw [hEQ,hE,inf_right_comm,inf_comm (V.map c) V]
  change (layer L R ⊓ (layer L R).map (MulAut.conj g).toMonoidHom) ⊓ P = _
  rw [hi,hp.core_center,map_subgroupOf_eq_of_le (zpowers_le.mpr (by
    exact mem_centralizer_singleton_iff.mpr rfl))]
  exact inf_eq_left.mpr ((zpowers_le.mpr hz).trans (by
    have hh := map_mono (f := H.subtype) hp.plane_le_core
    rwa [map_subgroupOf_eq_of_le (h611.ZS_le_T.trans hTH)] at hh))



/-- All involutions in the transfer subgroup are fused to the distinguished z.
The conjugate natural eight supplies both parity classes of the S₅ quotient. -/
theorem LocalAnalysis.equality_transfer_involution_fusion
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R)
    {t : G} (ht : t ∈ equalityTransferSubgroup (T : Subgroup G) L R z)
    (ht2 : orderOf t=2) : IsConj z t := by
  let H := centralizer ({z} : Set G)
  let P := (equalityCore L R z).map H.subtype
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let V := layer L R
  let J := L ⊔ P
  have hPT : P ≤ (T : Subgroup G) := equalityCore_le_sylow hTH
  have hPM : P ≤ M := hPT.trans h611.sylow_le
  have hQM : Q ≤ M := (pCoreIn_le 2 _).trans (sup_le h611.L_le h611.sylow_le)
  have hJM : J ≤ M := sup_le h611.L_le hPM
  have htJ : t ∈ J := (sup_le (show P ≤ J from le_sup_right)
    (show (T : Subgroup G) ⊓ L ≤ J from inf_le_right.trans le_sup_left)) ht
  let tM : M := ⟨t,hJM htJ⟩
  obtain ⟨f,hf,hker,hL,hPE,hPk,hP4,hPout⟩ :=
    A.equality_core_permutation_image h611 hnatural hz horder hTH hbranch
  obtain ⟨hJmap,hJQ⟩ := A.equality_fusion_quotient h611 hnatural hz horder hTH hbranch f hker hL
  change (J.subgroupOf M).map f = ⊤ at hJmap
  change J ⊓ Q = V at hJQ
  have htm2 : f tM^2=1 := by
    rw [←map_pow,show tM^2=1 from Subtype.ext (ht2 ▸ pow_orderOf_eq_one t),map_one]
  by_cases htker : f tM=1
  · have htQ : t ∈ Q := by
      change tM ∈ Q.subgroupOf M
      rw [←hker]
      exact htker
    have htv : t ∈ V := hJQ ▸ (show t ∈ J ⊓ Q from ⟨htJ,htQ⟩)
    exact equality_layer_involution_fusion hnatural hz horder htv ht2
  obtain ⟨E,hE,h8,hEP,hEQ,hEf⟩ :=
    A.equality_conjugate_eight_fusion h611 hnatural hz horder hTH hbranch
  let := hE
  have hEM : E ≤ M := hEP.trans hPM
  let i : E →* M := inclusion hEM
  let F := f.comp i
  have hk : F.ker=Q.subgroupOf E := by
    ext e
    change i e ∈ f.ker ↔ _
    rw [hker]
    rfl
  have hk2 : Nat.card F.ker=2 := by
    rw [hk,←inf_subgroupOf_right Q E,
      Nat.card_congr (subgroupOfEquivOfLe (show Q ⊓ E ≤ E from inf_le_right)).toEquiv,
      inf_comm Q E,hEQ,Nat.card_zpowers,horder]
  have hF4 : Nat.card F.range=4 := by
    have hh := F.ker.card_mul_index
    rw [index_ker,hk2,h8] at hh
    omega
  let j := equalityCoreToMaximal hTH h611.sylow_le (L := L) (R := R)
  have hj : j.range = P.subgroupOf M := by
    ext m
    constructor
    · rintro ⟨p,rfl⟩
      change (j p : G) ∈ P
      rw [show (j p : G) = (p.val : G) from equalityCoreToMaximal_coe hTH h611.sylow_le p]
      exact mem_map_of_mem H.subtype p.property
    · rintro ⟨p,hp,he⟩
      refine ⟨⟨p,hp⟩,Subtype.ext ?_⟩
      exact (equalityCoreToMaximal_coe hTH h611.sylow_le ⟨p,hp⟩).trans he
  have hr : (f.comp j).range = (P.subgroupOf M).map f := by
    rw [MonoidHom.range_comp,hj]
  have hFle : F.range ≤ (f.comp j).range := by
    rw [hr]
    rintro _ ⟨e,rfl⟩
    exact mem_map_of_mem f (show i e ∈ P.subgroupOf M from hEP e.property)
  have hFeq : F.range=(f.comp j).range := eq_of_le_of_card_ge hFle (by
    change Nat.card (f.comp j).range=4 at hP4
    omega)
  have hFout : ¬ F.range ≤ alternatingGroup (Fin 5) := by
    rw [hFeq]
    exact hPout
  obtain ⟨e,he2,heconj⟩ := elementary_eight_representative F h8 hk2 hFout (f tM) htm2 htker
  have heG2 : orderOf (e : G)=2 := (Subgroup.orderOf_coe e).trans he2
  have hze : IsConj z (e : G) := hEf e e.property heG2
  obtain ⟨c,hc⟩ := isConj_iff.mp heconj
  obtain ⟨cM,hcJ,hfc⟩ := (show c ∈ (J.subgroupOf M).map f from hJmap ▸ mem_top c)
  let a : G := (cM : G)*(e : G)*(cM : G)⁻¹
  have haJ : a ∈ J := J.mul_mem (J.mul_mem hcJ (mem_sup_right (hEP e.property))) (J.inv_mem hcJ)
  let aM : M := ⟨a,hJM haJ⟩
  have hfa : f aM=f tM := by
    change f (cM * i e * cM⁻¹)=f tM
    rw [map_mul,map_mul,map_inv,hfc]
    exact hc
  have haQ : a ∉ Q := by
    intro haQ
    have hh : f aM=1 := by
      change aM ∈ f.ker
      rw [hker]
      exact haQ
    exact htker (hfa.symm.trans hh)
  have hea : IsConj (e : G) a := isConj_iff.mpr ⟨cM,rfl⟩
  have ha2 : a^2=1 := by
    change (MulAut.conj (cM : G) (e : G))^2=1
    rw [←map_pow,show (e : G)^2=1 from heG2 ▸ pow_orderOf_eq_one (e : G),map_one]
  have hab : t*a⁻¹ ∈ V := by
    rw [←hJQ]
    refine ⟨J.mul_mem htJ (J.inv_mem haJ),?_⟩
    change tM*aM⁻¹ ∈ Q.subgroupOf M
    rw [←hker]
    change f (tM*aM⁻¹)=1
    rw [map_mul,map_inv,hfa,mul_inv_cancel]
  exact (hze.trans hea).trans (A.equality_involution_coset_fusion h611 hnatural hz horder hTH hbranch
    (hJM haJ) haQ ha2 (ht2 ▸ pow_orderOf_eq_one t) hab)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
