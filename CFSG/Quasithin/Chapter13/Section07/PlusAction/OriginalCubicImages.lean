module
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalTildeMinimal
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalActorImages
public import Theory.GroupTheory.CoprimeCentralizerImage
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
/-!
# The original commuting cubic quotient actor

On the reduced tilde-one module, O₂(L₁) acts trivially and L₁ moves the
whole module. Both the centralizer quotient image of L₁ and its conjugation
image therefore factor through L₁/O₂(L₁), of order three. Coprime splitting
makes the fixed space zero. The nontrivial L₁ image is a normal cubic group;
it commutes with the kernel image modulo O₂(K), and with the image of
O₂(L₁T) by their coprime orders. Its generator is thus the source commuting,
fixed-point-free cubic operator on the literal binary representation.

The final theorem selects the actual minimal reduced tilde-one module,
preserving its original U₂ containment and minimality.

Source: Aschbacher--Smith 13.7.4(1), printed pp.937--938.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
variable {G Y : Type*} [Group G] [Finite G] [Group Y]
omit [Finite G] in
/-- Factoring through the intrinsic cubic quotient bounds an actual image. -/
private theorem cubic_range_card (A : Subgroup G) (f : A →* Y)
    (hk : pCore 2 A ≤ f.ker) (hc : Nat.card (A ⧸ pCore 2 A)=3) :
    Nat.card f.range ∣ 3 := by
  let fbar := QuotientGroup.lift (pCore 2 A) f hk
  have hr : fbar.range=f.range := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 A) x
      exact ⟨a,rfl⟩
    · rintro ⟨a,rfl⟩
      exact ⟨QuotientGroup.mk' (pCore 2 A) a,rfl⟩
  rw [←hr,←hc]
  exact card_range_dvd fbar

/-- Full movement excludes the trivial image; coprime splitting kills fixed points. -/
private theorem cubic_image (U A : Subgroup G) [U.Normal]
    [IsElementaryAbelian 2 U] (q : G →* Y)
    (hker : q.ker=centralizer (U : Set G))
    (hcore : A.pCoreIn 2 ≤ centralizer (U : Set G))
    (hcard : Nat.card (A ⧸ pCore 2 A)=3)
    (hne : U≠⊥) (hm : ⁅U,A⁆=U) :
    Nat.card (A.map q)=3 ∧ U ⊓ centralizer (A : Set G)=⊥ := by
  let f := q.comp A.subtype
  have hk : pCore 2 A ≤ f.ker := by
    intro a ha
    change q a=1
    exact (show (a:G)∈q.ker from hker ▸ hcore (mem_map_of_mem A.subtype ha))
  have hr : f.range=A.map q := by
    ext y
    constructor
    · rintro ⟨a,rfl⟩
      exact mem_map_of_mem q a.property
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a,ha⟩,rfl⟩
  have hdiv : Nat.card (A.map q) ∣ 3 := hr ▸ cubic_range_card A f hk hcard
  have hAcard : Nat.card (A.map q)=3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with he | he
    · have hb := (eq_bot_iff_card (A.map q)).mpr he
      have hc : A ≤ centralizer (U : Set G) :=
        hker ▸ (Subgroup.map_eq_bot_iff A).mp hb
      exact False.elim (hne (hm.symm.trans
        (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc))))
    · exact he
  have hn : A ≤ normalizer (U : Set G) := le_normalizer_of_normal
  let α := U.normalizerMonoidHom.comp (inclusion hn)
  have hαker : pCore 2 A ≤ α.ker := by
    intro a ha
    apply DFunLike.ext
    intro u
    apply Subtype.ext
    change (a:G)*(u:G)*(a:G)⁻¹=(u:G)
    have he := (mem_centralizer_iff.mp (hcore (mem_map_of_mem A.subtype ha))) u u.property
    change (u:G)*(a:G)=(a:G)*(u:G) at he
    rw [←he,mul_inv_cancel_right]
  have hαdiv := cubic_range_card A α hαker hcard
  obtain ⟨n,hncard⟩ := IsPGroup.iff_card.mp (IsElementaryAbelian.isPGroup 2 U)
  have hcop : Nat.Coprime (Nat.card α.range) (Nat.card U) := by
    rw [hncard]
    exact ((by decide : Nat.Coprime 3 2).pow_right n).coprime_dvd_left hαdiv
  have hd := commutator_disjoint_centralizer_of_actionRange_coprime U A hn hcop
  rw [hm] at hd
  exact ⟨hAcard,le_bot_iff.mp ((le_inf inf_le_left le_rfl).trans hd.le_bot)⟩

omit [Finite G] in
/-- Every generator of the cubic image acts without nonzero fixed vectors. -/
private theorem cubic_generator_fixed_free [Finite Y] (U A : Subgroup G) [U.Normal]
    [IsElementaryAbelian 2 U] (q : G →* Y) (hq : Function.Surjective q)
    (hker : q.ker=centralizer (U : Set G))
    (hcard : Nat.card (A.map q)=3)
    (hfixed : U ⊓ centralizer (A : Set G)=⊥) :
    let ρ := Representation.NormalElementaryQuotient.representation U q hq hker
    ∃z∈A.map q,orderOf z=3 ∧ ∀v:Additive U,ρ z v=v → v=0 := by
  let B := A.map q
  let ρ := Representation.NormalElementaryQuotient.representation U q hq hker
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G:=B) 3 (by change 3∣Nat.card (A.map q);rw [hcard])
  have hznot : z≠1 := by
    intro he
    rw [he,orderOf_one] at hz
    omega
  have hgen : zpowers (z:Y)=B := by
    have hh := congrArg (Subgroup.map B.subtype) (zpowers_eq_top_of_prime_card hcard hznot)
    rw [MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  refine ⟨z,z.property,?_,?_⟩
  · exact (orderOf_injective B.subtype B.subtype_injective z).trans hz
  · intro v hv
    have hvfix : v∈Representation.BinaryOffender.fixedSpace ρ B := by
      rw [←hgen]
      exact (Representation.BinaryOffender.mem_fixedSpace_zpowers_iff ρ _ v).mpr hv
    have hc := (Representation.NormalElementaryQuotient.mem_fixedSpace_image U q hq hker A v).mp hvfix
    have hvone : (v.toMul:G)=1 := mem_bot.mp (hfixed ▸ (show (v.toMul:G)∈U⊓centralizer (A:Set G) from ⟨v.toMul.property,hc⟩))
    apply Additive.toMul.injective
    exact Subtype.ext hvone

variable {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The literal reduced quotient supplies the source commuting cubic operator. -/
theorem source_kernel_reduced_cubic_image
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    {K : Subgroup G}
    (hKC : K ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hKn : H ≤ normalizer (K : Set G)) (hp : IsPPerfect 2 K)
    (hcomm : ⁅K,(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁⁆ ≤ K.pCoreIn 2)
    (U : Subgroup ↥(K ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G))))
    (hred : IsPReduced 2 U) (hne : U≠⊥)
    (hm : ⁅U,(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁.subgroupOf
      (K ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G)))⁆=U)
    (hUR : U ≤ (⁅commutatorPreimage
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).UH
      ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁.pCoreIn 2)
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).V₁,K⁆).subgroupOf
      (K ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G)))) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let P := F.L₁ ⊔ (T : Subgroup G)
    let X := K ⊔ P
    letI := hred.normal
    letI := hred.elementary
    let q := QuotientGroup.mk' (centralizer (U : Set X))
    let A := (F.L₁.subgroupOf X).map q
    let E := (K.subgroupOf X).map q ⊔ ((P.pCoreIn 2).subgroupOf X).map q
    let ρ := Representation.NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    A.Normal ∧ Nat.card A=3 ∧ A ≤ centralizer (E : Set (X ⧸ centralizer (U : Set X))) ∧
      ∃z∈A,orderOf z=3 ∧ ∀v:Additive U,ρ z v=v → v=0 := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let P := F.L₁ ⊔ (T : Subgroup G)
  let X := K ⊔ P
  let LX := F.L₁.subgroupOf X
  let KX := K.subgroupOf X
  let W := commutatorPreimage F.UH (F.L₁.pCoreIn 2) F.V₁
  let R := ⁅W,K⁆
  let := hred.normal
  let := hred.elementary
  let q := QuotientGroup.mk' (centralizer (U : Set X))
  let A := LX.map q
  let C := KX.map q
  let B := ((P.pCoreIn 2).subgroupOf X).map q
  let E := C ⊔ B
  have hKH : K ≤ H := hKC.trans (kernel_le_H (D:=F))
  have hXH : X ≤ H := sup_le hKH h.local_le
  have hKX : K ≤ X := le_sup_left
  have hLX : F.L₁ ≤ X := le_sup_left.trans le_sup_right
  have hPX : P ≤ X := le_sup_right
  have hQX : P.pCoreIn 2 ≤ X := (pCoreIn_le 2 P).trans hPX
  have hXL := (source_kernel_mixed_geometry d h hKC hKn hp hcomm).1
  let : LX.Normal := normal_subgroupOf_of_le_normalizer hXL
  let : KX.Normal := normal_subgroupOf_of_le_normalizer (hXH.trans hKn)
  have hAn : A.Normal := (inferInstance : LX.Normal).map q (QuotientGroup.mk'_surjective _)
  let := hAn
  have hcoreR := (source_kernel_tilde_geometry d h hKC hKn hp hcomm).2.2.2.2.2.1
  have hcoremapL : (LX.pCoreIn 2).map X.subtype=F.L₁.pCoreIn 2 := by
    rw [map_pCoreIn_of_ker_isPGroup X.subtype
      (by rw [X.ker_subtype];exact IsPGroup.of_bot),map_subgroupOf_eq_of_le hLX]
  have hcoreL : LX.pCoreIn 2 ≤ centralizer (U : Set X) := by
    intro a ha
    rw [mem_centralizer_iff]
    intro u hu
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (hcoreR (hcoremapL ▸ mem_map_of_mem X.subtype ha))) u.val (hUR hu)
  let eLX := subgroupOfEquivOfLe hLX
  have hcardLX : Nat.card (LX ⧸ pCore 2 LX)=3 := by
    rw [Nat.card_congr (QuotientGroup.congr _ _ eLX (pCore_map_iso 2 eLX)).toEquiv]
    rw [source_local_residual_eq d h]
    exact Section03.Noncentrality.ordinary_point_residual_quotient_card d eL
  obtain ⟨hAcard,hfixed⟩ := cubic_image U LX q (QuotientGroup.ker_mk' _) hcoreL hcardLX hne hm
  have hcoremapK : (KX.pCoreIn 2).map X.subtype=K.pCoreIn 2 := by
    rw [map_pCoreIn_of_ker_isPGroup X.subtype
      (by rw [X.ker_subtype];exact IsPGroup.of_bot),map_subgroupOf_eq_of_le hKX]
  have hcoreK : KX.pCoreIn 2 ≤ centralizer (U : Set X) := by
    have hn : (KX.pCoreIn 2).Normal := ConjAct.normal_of_characteristic_of_normal
    have hl : KX.pCoreIn 2 ≤ pCore 2 X := le_sSup ⟨hn,isPGroup_pCoreIn 2 KX⟩
    exact hl.trans (le_centralizer_iff.mp hred.le_centralizer_pCore)
  have hcommX : ⁅KX,LX⁆ ≤ KX.pCoreIn 2 := by
    apply (map_le_map_iff_of_injective X.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hKX,map_subgroupOf_eq_of_le hLX,hcoremapK]
    exact hcomm
  have hAC : A ≤ centralizer (C : Set (X ⧸ centralizer (U : Set X))) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [←map_commutator,commutator_comm]
    apply le_bot_iff.mp
    exact (map_mono hcommX).trans (by
      rw [(Subgroup.map_eq_bot_iff (KX.pCoreIn 2)).mpr
        (by rw [QuotientGroup.ker_mk'];exact hcoreK)])
  have hLP : F.L₁ ≤ normalizer (P.pCoreIn 2 : Set G) :=
    (le_sup_left.trans P.le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
  have hLB : LX ≤ normalizer ((P.pCoreIn 2).subgroupOf X : Set X) := by
    rw [←subgroupOf_normalizer_eq hQX]
    exact subgroupOf_mono X hLP
  have hAB : A ≤ normalizer (B : Set (X ⧸ centralizer (U : Set X))) :=
    (map_mono hLB).trans (Subgroup.le_normalizer_map (H:=(P.pCoreIn 2).subgroupOf X) q)
  have hpA : IsPGroup 3 A := IsPGroup.of_card (n:=1) (by rw [pow_one];exact hAcard)
  have hpB : IsPGroup 2 B := (isPGroup_pCoreIn 2 P).comap_subtype.map q
  have hd : Disjoint A B := hpA.disjoint_of_coprime hpB (by decide)
  have hABcent : A ≤ centralizer (B : Set (X ⧸ centralizer (U : Set X))) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    exact (le_inf (commutator_le_left A B)
      (le_normalizer_iff_commutator_le_right.mp hAB)).trans hd.le_bot
  have hAE : A ≤ centralizer (E : Set (X ⧸ centralizer (U : Set X))) := by
    apply le_centralizer_iff.mp
    exact sup_le (le_centralizer_iff.mp hAC) (le_centralizer_iff.mp hABcent)
  exact ⟨hAn,hAcard,hAE,cubic_generator_fixed_free U LX q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hAcard hfixed⟩

/-- The actual primitive cubic branch chooses the reduced tilde-one module and
produces its literal commuting, fixed-point-free cubic quotient operator. -/
theorem source_primitive_cubic_minimal_actor_image
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥)
    (J : Subgroup H)
    (hJC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hJn : H ≤ normalizer (J.map H.subtype : Set G))
    (hp : IsPPerfect 2 (J.map H.subtype)) (hout : ¬ J.map H.subtype ≤ M)
    (hcard : Nat.card (J ⧸ pCore 2 J)=3) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let K := J.map H.subtype
    let P := F.L₁ ⊔ (T : Subgroup G)
    let X := K ⊔ P
    let W := commutatorPreimage F.UH (F.L₁.pCoreIn 2) F.V₁
    let R := ⁅W,K⁆
    let D := ⁅R,F.L₁⁆
    let U₂ := ⁅⁅fixedLayer F,F.L₁⁆,K⁆
    ∃U : Subgroup X, U ≤ D.subgroupOf X ∧ U ≤ U₂.subgroupOf X ∧
      ∃hred : IsPReduced 2 U, U≠⊥ ∧ ⁅U,K.subgroupOf X⁆=U ∧ ⁅U,F.L₁.subgroupOf X⁆=U ∧
      (∀B : Subgroup X,B ≤ U → B.Normal → ⁅B,K.subgroupOf X⁆≠⊥ → B=U) ∧
      letI := hred.normal
      letI := hred.elementary
      let q := QuotientGroup.mk' (centralizer (U : Set X))
      let A := (F.L₁.subgroupOf X).map q
      let E := (K.subgroupOf X).map q ⊔ ((P.pCoreIn 2).subgroupOf X).map q
      let ρ := Representation.NormalElementaryQuotient.representation U q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      A.Normal ∧ Nat.card A=3 ∧ A ≤ centralizer (E : Set (X ⧸ centralizer (U : Set X))) ∧
        ∃z∈A,orderOf z=3 ∧ ∀v:Additive U,ρ z v=v → v=0 := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let K := J.map H.subtype
  let P := F.L₁ ⊔ (T : Subgroup G)
  let X := K ⊔ P
  let W := commutatorPreimage F.UH (F.L₁.pCoreIn 2) F.V₁
  let R := ⁅W,K⁆
  let D := ⁅R,F.L₁⁆
  let U₂ := ⁅⁅fixedLayer F,F.L₁⁆,K⁆
  obtain ⟨U,hUD,hUU₂,hred,hne,hUK,hUL,hmin⟩ :=
    source_primitive_cubic_minimal_tilde_module d h1221 h hU eL hm J hJC hJn hp hout hcard
  have hcomm : ⁅K,F.L₁⁆ ≤ K.pCoreIn 2 := source_primitive_cubic_centralized h J hJn hcard
  have hDR : D ≤ R := (source_kernel_tilde_geometry d h hJC hJn hp hcomm).2.2.2.2.2.2.1
  exact ⟨U,hUD,hUU₂,hred,hne,hUK,hUL,hmin,
    source_kernel_reduced_cubic_image d h eL hJC hJn hp hcomm U hred hne hUL
      (hUD.trans (subgroupOf_mono X hDR))⟩
end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
