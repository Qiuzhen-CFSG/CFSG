module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Diagonal.Quotient
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Theory.Representation.ElementaryPerfectSplit
public import Theory.SpecificGroups.Alternating.FiveSylowRadical
public import Theory.GroupTheory.PCoreQuotientInnerSupplement
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.MarkedAlternatingFiveThompson
public import CFSG.Quasithin.Chapter6.Section01.SourceModelKernel
public import Theory.GroupTheory.NormalModuleCore
public import Theory.Representation.BinaryOffender.QuasisimpleRestrictionFitting
public import Theory.Representation.BinaryOffender.MarkedCentralQuotient
public import Theory.Representation.BinaryPermutationNaturalStructure

/-! The ordinary diagonal radical: noncontainment makes the intersection
with the point parabolic a two-group. The actual A5 Sylow action then
makes the point radical inner. Source: Aschbacher--Smith13.3.14, p.893. -/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality.Diagonal
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem normal_le_core_of_cubic_quotient (A : Subgroup G)
    (hp : IsPPerfect 2 A) (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (N : Subgroup A) [N.Normal] (hne : N ≠ ⊤) : N ≤ pCore 2 A := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsSimpleGroup (A ⧸ pCore 2 A) := isSimpleGroup_of_prime_card hc
  let q := QuotientGroup.mk' (pCore 2 A)
  have hn := (inferInstance : N.Normal).map q (QuotientGroup.mk'_surjective _)
  rcases hn.eq_bot_or_eq_top with h | h
  · have hh := (map_eq_bot_iff N).mp h
    simpa only [q,QuotientGroup.ker_mk'] using hh
  · have hs : N ⊔ pCore 2 A = ⊤ := by
      have hh := congrArg (comap q) h
      simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using hh
    exact (hne (hp N inferInstance
      (isPGroup_quotient_of_sup_eq_top N (pCore 2 A) pCore_isPGroup hs))).elim

omit [Finite G] in
/-- A cubic residual which escapes a normalized subgroup has only a two-group
intersection with that subgroup in its Sylow join. -/
theorem intersection_point_join_isPGroup (A K : Subgroup G) (T : Sylow 2 G)
    (hTA : (T : Subgroup G) ≤ normalizer A)
    (hAK : A ≤ normalizer K)
    (hp : IsPPerfect 2 A) (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hout : ¬ A ≤ K) : IsPGroup 2 (K ⊓ (A ⊔ (T : Subgroup G)) : Subgroup G) := by
  let P := A ⊔ (T : Subgroup G)
  let N := K.subgroupOf A
  let : N.Normal := normal_subgroupOf_of_le_normalizer hAK
  have hne : N ≠ ⊤ := by
    intro hh
    apply hout
    intro a ha
    exact show (⟨a,ha⟩ : A) ∈ N from hh.symm ▸ mem_top _
  have hNc := normal_le_core_of_cubic_quotient A hp hc N hne
  have hKA : IsPGroup 2 (A ⊓ K : Subgroup G) := by
    have hh := (pCore_isPGroup.to_le hNc).map A.subtype
    have he : N.map A.subtype = A ⊓ K :=
      (subgroupOf_map_subtype K A).trans (inf_comm K A)
    exact he ▸ hh
  let AP := A.subgroupOf P
  let : AP.Normal := normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hTA)
  have hgen : AP ⊔ (T : Subgroup G).subgroupOf P = ⊤ := by
    rw [←subgroupOf_sup (show A ≤ P from le_sup_left)
      (show (T : Subgroup G) ≤ P from le_sup_right)]
    exact subgroupOf_self P
  have hquot : IsPGroup 2 (P ⧸ AP) :=
    isPGroup_quotient_of_sup_eq_top AP ((T : Subgroup G).subgroupOf P)
      T.isPGroup'.comap_subtype hgen
  let f : (K ⊓ P : Subgroup G) →* P ⧸ AP :=
    (QuotientGroup.mk' AP).comp (inclusion inf_le_right)
  have hk : IsPGroup 2 f.ker := by
    apply (hKA.comap_subtype : IsPGroup 2 ((A ⊓ K).subgroupOf (K ⊓ P))).to_le
    intro x hx
    have ha : inclusion (show K ⊓ P ≤ P from inf_le_right) x ∈ AP :=
      (QuotientGroup.eq_one_iff (N := AP) _).mp hx
    exact ⟨ha,x.property.1⟩
  have ht := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup f hk
  rw [comap_top] at ht
  exact ht.of_equiv topEquiv

/-- In the same configuration the point radical acts by inner automorphisms
on the actual A5 quotient. -/
theorem point_radical_inner (A K : Subgroup G) (T : Sylow 2 G)
    (hTA : (T : Subgroup G) ≤ normalizer A)
    (hAK : A ≤ normalizer K) (hTK : (T : Subgroup G) ≤ normalizer K)
    (hp : IsPPerfect 2 A) (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hout : ¬ A ≤ K) (hgen : ⁅K,A⁆ = K)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) :
    ∀ r : (A ⊔ (T : Subgroup G)).pCoreIn 2,
      quotientAut (pCore 2 K)
        (K.normalizerMonoidHom ⟨r,(sup_le hAK hTK)
          (pCoreIn_le 2 _ r.property)⟩) ∈ MulAut.innerSubgroup (K ⧸ pCore 2 K) := by
  let P := A ⊔ (T : Subgroup G)
  let hPK : P ≤ normalizer K := sup_le hAK hTK
  let q₀ := QuotientGroup.mk' (pCore 2 K)
  let q := eK.toMonoidHom.comp q₀
  let a : P →* MulAut (alternatingGroup (Fin 5)) := (MulAut.congr eK).toMonoidHom.comp
    ((quotientAut (pCore 2 K)).comp (K.normalizerMonoidHom.comp (inclusion hPK)))
  have ha (x : P) (k : K) : a x (q k) =
      q (K.normalizerMonoidHom ⟨x,hPK x.property⟩ k) := by
    change eK ((quotientAut (pCore 2 K) (K.normalizerMonoidHom
      ⟨x,hPK x.property⟩)) (eK.symm (eK (q₀ k)))) = _
    rw [eK.symm_apply_apply,quotientAut_apply_mk]
    rfl
  have hnon : ∃ b : A, a (inclusion (show A ≤ P from le_sup_left) b) ≠ 1 := by
    by_contra hall
    push Not at hall
    have hcomm : ⁅A,K⁆ ≤ K.pCoreIn 2 := by
      apply commutator_le.mpr
      intro l hl k hk
      let n : K := K.normalizerMonoidHom ⟨l,hPK (mem_sup_left hl)⟩ ⟨k,hk⟩
      have hfix : q n = q ⟨k,hk⟩ := by
        have hh := congrArg (fun b : MulAut (alternatingGroup (Fin 5)) => b (q ⟨k,hk⟩))
          (hall ⟨l,hl⟩)
        rw [ha] at hh
        exact hh
      have hfix₀ : q₀ n = q₀ ⟨k,hk⟩ := eK.injective hfix
      have hcore : n * (⟨k,hk⟩ : K)⁻¹ ∈ pCore 2 K := by
        apply (QuotientGroup.eq_one_iff _).mp
        change q₀ (n * (⟨k,hk⟩ : K)⁻¹) = 1
        rw [map_mul,map_inv,hfix₀,mul_inv_cancel]
      exact mem_map_of_mem K.subtype hcore
    rw [commutator_comm,hgen] at hcomm
    have htop : pCore 2 K = ⊤ := by
      apply top_unique
      intro k _
      obtain ⟨x,hx,he⟩ := hcomm k.property
      exact (show x = k from Subtype.ext he) ▸ hx
    have hcard := Nat.card_congr eK.toEquiv
    rw [htop,nat_card_alternatingGroup] at hcard
    have h1 : Nat.card (K ⧸ (⊤ : Subgroup K)) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨QuotientGroup.subsingleton_quotient_top,⟨1⟩⟩
    norm_num [h1,Nat.factorial] at hcard
  have hi := Theory.SpecificGroups.Alternating.FiveSylowRadical.pCore_action_inner
    T K P A hPK le_sup_right
    (intersection_point_join_isPGroup A K T hTA hAK hp hc hout)
    le_sup_left hp q (eK.surjective.comp (QuotientGroup.mk'_surjective _)) a ha hnon
  intro r
  obtain ⟨r₀,hr₀,he⟩ := r.property
  change (r₀ : G) = (r : G) at he
  have hh := hi ⟨r₀,hr₀⟩
  change MulAut.congr eK (quotientAut (pCore 2 K)
    (K.normalizerMonoidHom ⟨r₀,hPK r₀.property⟩)) ∈ _ at hh
  rw [←MulAut.map_innerSubgroup_congr eK,mem_map_equiv] at hh
  simpa only [MulEquiv.symm_apply_apply,he] using hh

omit [Finite G] in
/-- The literal intersection is a normal two-subgroup of the point parabolic. -/
theorem intersection_point_join_le_core (A K : Subgroup G) (T : Sylow 2 G)
    (hTA : (T : Subgroup G) ≤ normalizer A)
    (hAK : A ≤ normalizer K) (hTK : (T : Subgroup G) ≤ normalizer K)
    (hp : IsPPerfect 2 A) (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hout : ¬ A ≤ K) :
    K ⊓ (A ⊔ (T : Subgroup G)) ≤ (A ⊔ (T : Subgroup G)).pCoreIn 2 :=
  le_pCoreIn_of_normalizes
    (intersection_point_join_isPGroup A K T hTA hAK hp hc hout) inf_le_right
    ((le_inf (sup_le hAK hTK) (A ⊔ (T : Subgroup G)).le_normalizer).trans
      inf_normalizer_le_normalizer_inf)

omit [Finite G] in
/-- The component-Sylow join's core lies in the original point radical.
The centralizer kernel is tested on the cubic residual; no centerlessness
of the residual quotient is needed. -/
theorem component_join_core_le_point_radical (A K : Subgroup G) (T : Sylow 2 G)
    (hTA : (T : Subgroup G) ≤ normalizer A)
    (hAK : A ≤ normalizer K) (hTK : (T : Subgroup G) ≤ normalizer K)
    (hp : IsPPerfect 2 A) (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hgen : ⁅K,A⁆ = K)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) :
    (K ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (A ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let P := A ⊔ (T : Subgroup G)
  let C := quotientCentralizer K P (sup_le hAK hTK)
  have hPC : P ≤ normalizer (C : Set G) := by
    have hh := (pCoreJoinAction 2 (sup_le hAK hTK)).ker.le_normalizer_map
      (K ⊔ P).subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
    exact (show P ≤ K ⊔ P from le_sup_right).trans hh
  have hout : ¬ A ≤ C := by
    intro hh
    have hKC : K ≤ K.pCoreIn 2 := by
      conv_lhs => rw [←hgen,commutator_comm]
      exact (commutator_mono hh le_rfl).trans
        (quotientCentralizer_commutator_le_core K P (sup_le hAK hTK))
    have htop : pCore 2 K = ⊤ := by
      apply top_unique
      intro k _
      obtain ⟨x,hx,he⟩ := hKC k.property
      exact (show x = k from Subtype.ext he) ▸ hx
    have hcard := Nat.card_congr eK.toEquiv
    rw [htop,nat_card_alternatingGroup] at hcard
    have h1 : Nat.card (K ⧸ (⊤ : Subgroup K)) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨QuotientGroup.subsingleton_quotient_top,⟨1⟩⟩
    norm_num [h1,Nat.factorial] at hcard
  have hCP := intersection_point_join_le_core A C T hTA
    ((show A ≤ P from le_sup_left).trans hPC)
    ((show (T : Subgroup G) ≤ P from le_sup_right).trans hPC) hp hc hout
  apply le_trans (le_inf ?_ ?_) hCP
  · rintro x ⟨q,hq,rfl⟩
    refine ⟨inclusion (sup_le le_sup_left
      (show (T : Subgroup G) ≤ K ⊔ P from le_sup_right.trans le_sup_right)) q,?_,rfl⟩
    exact pCore_le_pCoreJoinAction_kernel 2 hTK hq
  · have hh := pCoreIn_le_sylow (K ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
    have hQT : (K ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
        (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right)] using hh
    exact hQT.trans le_sup_right

/-- The source's intended radical identity, with both embedded cores literal. -/
theorem point_radical_eq_component_sylow_sup_core (A K : Subgroup G) (T : Sylow 2 G)
    (hTA : (T : Subgroup G) ≤ normalizer A)
    (hAK : A ≤ normalizer K) (hTK : (T : Subgroup G) ≤ normalizer K)
    (hp : IsPPerfect 2 A) (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hout : ¬ A ≤ K) (hgen : ⁅K,A⁆ = K)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) :
    (A ⊔ (T : Subgroup G)).pCoreIn 2 =
      ((T : Subgroup G) ⊓ K) ⊔ (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let P := A ⊔ (T : Subgroup G)
  let R := P.pCoreIn 2
  let X := K ⊔ R
  let KT := K ⊔ (T : Subgroup G)
  have hRT : R ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow P (T.subtype (show (T : Subgroup G) ≤ P from le_sup_right))
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ P from le_sup_right)] using hh
  have hRK : R ≤ normalizer K := hRT.trans hTK
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hh : eK x ∈ center (alternatingGroup (Fin 5)) :=
      (centerCongr eK ⟨x,hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hh
    exact eK.injective (hh.trans eK.map_one.symm)
  obtain ⟨S,hS⟩ := Subgroup.NormalSylowQuotientAction.intersection_sylow T K hTK
  have hSm : (S : Subgroup K).map K.subtype = (T : Subgroup G) ⊓ K := by
    rw [hS,subgroupOf_map_subtype]
  have hSR : (S : Subgroup K).map K.subtype ≤ R := by
    rw [hSm]
    exact (le_inf inf_le_right (inf_le_left.trans le_sup_right)).trans
      (intersection_point_join_le_core A K T hTA hAK hTK hp hc hout)
  have hi := point_radical_inner A K T hTA hAK hTK hp hc hout hgen eK
  have hfactor := sup_core_factor_of_inner_action K R hRK (isPGroup_pCoreIn 2 P)
    hz S hSR hi
  have hQR : KT.pCoreIn 2 ≤ R :=
    component_join_core_le_point_radical A K T hTA hAK hTK hp hc hgen eK
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (show (T : Subgroup G) ≤ P from le_sup_right).trans
      (P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P)))
  have hNX : KT ≤ normalizer (X : Set G) := sup_le
    ((show K ≤ X from le_sup_left).trans X.le_normalizer)
    ((le_inf hTK hTR).trans (normalizer_inf_normalizer_le_normalizer_sup K R))
  have he : X.pCoreIn 2 = KT.pCoreIn 2 := le_antisymm
    (pCoreIn_mono_of_normalizes (sup_le le_sup_left (hRT.trans le_sup_right)) hNX)
    (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 KT) (hQR.trans le_sup_right)
      ((sup_le le_sup_left (hRT.trans le_sup_right)).trans
        (KT.le_normalizer.trans (normalizer_le_normalizer_characteristic_image KT (pCore 2 KT)))))
  rwa [hSm,he] at hfactor

open Representation Representation.BinaryOffender

/-- The two-core of any normalizing overgroup fixes the actual irreducible A5
module. The proof transports the original conjugation representation. -/
theorem core_centralizes_a5_module (K I X : Subgroup G)
    [IsElementaryAbelian 2 I] (hKX : K ≤ X)
    (hXI : X ≤ normalizer (I : Set G))
    (hm : Chapter6.Source.IsConjugationModel K I Chapter6.Source.a5Module) :
    X.pCoreIn 2 ≤ centralizer (I : Set G) := by
  obtain ⟨m,f,hf⟩ := hm
  let ρ := elementaryRepresentation (p := 2)
    (I.normalizerMonoidHom.comp (inclusion hXI))
  let KX := K.subgroupOf X
  let q : KX →* alternatingGroup (Fin 5) := m.toMonoidHom.comp
    ((QuotientGroup.mk' (pCore 2 K)).comp (subgroupOfEquivOfLe hKX).toMonoidHom)
  have hq : Function.Surjective q := m.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (subgroupOfEquivOfLe hKX).surjective)
  let a : Additive I ≃+ BinaryPermutation.natural (Fin 5) :=
    f.toAdditive.trans (AddEquiv.additiveMultiplicative _)
  let e : Additive I ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5) :=
    { a with map_smul' := ZMod.map_smul a }
  have he (k : KX) (v : Additive I) :
      e ((ρ.comp KX.subtype) k v) = Chapter6.Source.a5Module (q k) (e v) := by
    have hh := hf ((subgroupOfEquivOfLe hKX) k) v.toMul
    have hv : f.symm (Multiplicative.ofAdd (Chapter6.Source.a5Module
        (q k) (f v.toMul).toAdd)) = (ρ k.val v).toMul := Subtype.ext hh
    have ht := congrArg (fun u : I => (f u).toAdd) hv
    change (f ((ρ k.val) v).toMul).toAdd =
      Chapter6.Source.a5Module (q k) (f v.toMul).toAdd
    simpa only [f.apply_symm_apply,toAdd_ofAdd] using ht.symm
  have hi := irreducible_of_surjective_equivariant (ρ.comp KX.subtype)
    Chapter6.Source.a5Module q hq e he
    (BinaryPermutation.alternatingNatural_isIrreducible (Ω := Fin 5) (by decide))
  let := irreducible_of_subgroup_restriction ρ KX hi
  have hker := normal_p_subgroup_le_ker ρ (pCore 2 X) pCore_isPGroup
  rintro x ⟨x,hx,rfl⟩ i hi
  have hh := DFunLike.congr_fun (hker hx) (Additive.ofMul (⟨i,hi⟩ : I))
  have hv := congrArg (fun v : Additive I => (v.toMul : G)) hh
  change (x : G) * i * (x : G)⁻¹ = i at hv
  exact (mul_inv_eq_iff_eq_mul.mp hv).symm

/-- The exact radical factorization gives the Baumann equality before any
block recognition or chief-factor bound. -/
theorem baumann_eq_of_a5_radical_factor (K I R : Subgroup G) (T : Sylow 2 G)
    [IsElementaryAbelian 2 I] (hTK : (T : Subgroup G) ≤ normalizer K)
    (hIK : I ≤ K) (hIR : I ≤ R)
    (hXI : K ⊔ (T : Subgroup G) ≤ normalizer (I : Set G))
    (hm : Chapter6.Source.IsConjugationModel K I Chapter6.Source.a5Module)
    (hfactor : R = ((T : Subgroup G) ⊓ K) ⊔ (K ⊔ (T : Subgroup G)).pCoreIn 2) :
    ChapterB.baumann R = ChapterB.baumann ((K ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let X := K ⊔ (T : Subgroup G)
  let Q := X.pCoreIn 2
  have hRX : R ≤ X := by
    rw [hfactor]
    exact sup_le (inf_le_right.trans le_sup_left) (pCoreIn_le 2 X)
  have hQR : Q ≤ R := by rw [hfactor]; exact le_sup_right
  have hQC : Q ≤ centralizer (I : Set G) :=
    core_centralizes_a5_module K I X le_sup_left hXI hm
  have hcentral : X ⊓ centralizer (I : Set G) = Q :=
    ambient_centralizer_eq_core_of_normal_supplement K I T hTK
      (hIK.trans le_sup_left) hXI T.isPGroup' hm.a5_centralizer_eq_core hQC
  have hRC : R ⊓ centralizer (I : Set G) = Q :=
    le_antisymm ((inf_le_inf_right _ hRX).trans hcentral.le) (le_inf hQR hQC)
  have hinner : ∀ r : R, ∃ k : K, ∀ v : I,
      (r : G) * (v : G) * (r : G)⁻¹ = (k : G) * (v : G) * (k : G)⁻¹ := by
    intro r
    have hr : (r : G) ∈ K ⊔ Q := by
      have hh := hfactor.le r.property
      exact (show ((T : Subgroup G) ⊓ K) ⊔ Q ≤ K ⊔ Q from
        sup_le_sup inf_le_right le_rfl) hh
    have hQK : Q ≤ normalizer K := (pCoreIn_le 2 X).trans (sup_le K.le_normalizer hTK)
    have hr' : (r : G) ∈ (K : Set G) * (Q : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left K Q hQK]
      exact hr
    obtain ⟨k,hk,q,hq,he⟩ := hr'
    refine ⟨⟨k,hk⟩,?_⟩
    intro v
    have hqv : q * (v : G) * q⁻¹ = v :=
      mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp (hQC hq)) v v.property).symm
    rw [←he,mul_inv_rev]
    simpa only [mul_assoc] using congrArg (fun z : G => k * z * k⁻¹) hqv
  have hJ := Section07.PlusAction.Original.thompson_centralizes_marked_a5_module
    K I R hIR (hRX.trans hXI) hm hinner
  rw [ChapterB.lemma_B_2_3_5 R I hIR hJ,hRC]

end CFSG.Quasithin.Chapter13.Section03.Noncentrality.Diagonal
