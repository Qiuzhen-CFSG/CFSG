module

public import Theory.GroupTheory.Commutator.PerfectCoreKernel
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.Commutator.FullActorNormalLayer
public import Theory.GroupTheory.ConjugateGenerationPGroupQuotient

/-!
# Subgroup deductions in the normalizer of the canonical fixed space

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), §8.2.2, printed pp.717–721 (PDF pp.734–738).

The actual subgroup L_U is the embedded solvable residual of N_L(U).
Its containing component K_U has quasisimple quotient modulo O₂(K_U) in
8.2.7. Perfectness and the proper action kernel imply the commutator bound
in 8.2.8(2), including the descent from K_U to L_U. Conjugating V by the
source h then gives the actions on I = ⟨V,V^h⟩ and P = O₂(I).

The two-group quotient of H by its relative centralizer of U gives
O²(H) ≤ C_G(U). The two-conjugate generation also gives I = O²(I)V,
which transfers T-normalization of O²(I) to I and VA. Finally the literal
O₂(L) and the full-commutator equality L = [L,A] give [O₂(L),L] ≤ V.

These are conditional source deductions, not the complete Lemmas 8.2.6–10.
In particular the natural marked actions, containing-component recognition,
tensor decomposition, small overgroup and chief-factor exclusions, and covering
arguments remain required. No family tag or conclusion-containing record is
used in place of those arguments. All displayed normality is relative; O₂,
O² and the solvable residual are distinct throughout.
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer
variable {G : Type*} [Group G]

/-- The actual L_U = N_L(U)^∞, embedded in G; the residual is solvable, not the two-residual
or two-core. -/
@[expose] def localResidual (L U : Subgroup G) : Subgroup G :=
  (solvableResidual (L ⊓ normalizer (U : Set G) : Subgroup G)).map
    (L ⊓ normalizer (U : Set G)).subtype

/-- The subgroup L_U lies in the literal relative normalizer N_L(U). -/
theorem localResidual_le (L U : Subgroup G) :
    localResidual L U ≤ L ⊓ normalizer (U : Set G) := map_subtype_le _

/-- The source T normalizes L_U because it normalizes both L and U. -/
theorem normalizes_localResidual (L U T : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G)) (hTU : T ≤ normalizer (U : Set G)) :
    T ≤ normalizer (localResidual L U : Set G) := by
  apply le_trans ?_ (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
  exact (le_inf hTL (hTU.trans (normalizer (U : Set G)).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf

/-- Relative normality in N_M(U), with containment kept explicit. This is the normality part
of the setup for 8.2.6; C-component membership remains separate. -/
theorem localResidual_normal_in_relative_normalizer (L M U : Subgroup G)
    (hLM : L ≤ M) (hML : M ≤ normalizer (L : Set G)) :
    localResidual L U ≤ M ⊓ normalizer (U : Set G) ∧
      ((localResidual L U).subgroupOf (M ⊓ normalizer (U : Set G))).Normal :=
  ⟨(localResidual_le L U).trans (inf_le_inf_right _ hLM),
    normal_subgroupOf_of_le_normalizer (normalizes_localResidual L U _
      (inf_le_left.trans hML) inf_le_right)⟩

/-- The deduction in 8.2.8(2) from the containing perfect component, its quasisimple two-
core quotient (8.2.7), and the nontrivial natural action in 8.2.6. The original Sylow
subgroup contains O₂(K_U) and normalizes L and U. -/
theorem localResidual_centralizer_commutator [Finite G] (L K U T : Subgroup G)
    [Group.IsPerfect K] [Theory.GroupTheory.IsQuasisimple (K ⧸ pCore 2 K)]
    (hRK : localResidual L U ≤ K) (hKN : K ≤ normalizer (U : Set G))
    (hNK : normalizer (U : Set G) ≤ normalizer (K : Set G))
    (hnontriv : ¬ localResidual L U ≤ centralizer (U : Set G))
    (hQT : K.pCoreIn 2 ≤ T) (hTL : T ≤ normalizer (L : Set G))
    (hTU : T ≤ normalizer (U : Set G)) :
    ⁅localResidual L U, centralizer (U : Set G)⁆ ≤ (localResidual L U).pCoreIn 2 := by
  let C := (centralizer (U : Set G)).subgroupOf K
  have hNC : normalizer (U : Set G) ≤ normalizer (centralizer (U : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer _)).mp inferInstance
  let : C.Normal := normal_subgroupOf_of_le_normalizer (hKN.trans hNC)
  have hproper : C ≠ ⊤ := by
    intro he
    apply hnontriv
    intro r hr
    exact (show (⟨r, hRK hr⟩ : K) ∈ C from he ▸ mem_top _)
  have hCm : C.map K.subtype = K ⊓ centralizer (U : Set G) := by
    rw [subgroupOf_map_subtype, inf_comm]
  have hker : ⁅K ⊓ centralizer (U : Set G), K⁆ ≤ K.pCoreIn 2 := by
    have hm := map_mono (f := K.subtype) (normal_kernel_commutator_le_twoCore C hproper)
    simpa only [map_commutator, hCm, ← MonoidHom.range_eq_map, range_subtype, pCoreIn] using hm
  let : Group.IsPerfect (localResidual L U) := Group.IsPerfect.map _
  exact perfect_subgroup_core_commutator _ K _ hRK
    (hQT.trans (normalizes_localResidual L U T hTL hTU))
    (perfect_core_commutator K U hKN hNK hker)

/-- Transport normalization of V across the source conjugator. The book convention V^h = h⁻¹
V h is used literally. -/
theorem normalizes_twoConjugate (J V : Subgroup G) (h : G)
    (hJV : J ≤ normalizer (V : Set G)) (hh : h ∈ normalizer (J : Set G)) :
    J ≤ normalizer ((V ⊔ V.map (MulAut.conj h⁻¹).toMonoidHom : Subgroup G) : Set G) := by
  apply le_trans (le_inf hJV ?_) (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have he : J.map (MulAut.conj h⁻¹).toMonoidHom = J :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (J : Set G)).inv_mem hh)
  rw [← map_equiv_normalizer_eq V (MulAut.conj h⁻¹)]
  simpa only [he] using map_mono (f := (MulAut.conj h⁻¹).toMonoidHom) hJV

/-- An actor on the two-conjugate subgroup also acts on its actual two-core. -/
theorem normalizes_twoConjugate_core (J V : Subgroup G) (h : G)
    (hJV : J ≤ normalizer (V : Set G)) (hh : h ∈ normalizer (J : Set G)) :
    J ≤ normalizer (((V ⊔ V.map (MulAut.conj h⁻¹).toMonoidHom).pCoreIn 2) : Set G) :=
  (normalizes_twoConjugate J V h hJV hh).trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

/-- The group L_U O₂(K_U) acts on the actual I and P = O₂(I), as in the opening of 8.2.8(4).
The input commutator bound is proved above; h belongs to the source I and I centralizes
U by 8.2.5. -/
theorem local_factor_normalizes_pair_and_core (L K U I V T : Subgroup G) (h : G)
    (hh : h ∈ I) (hgen : V ⊔ V.map (MulAut.conj h⁻¹).toMonoidHom = I)
    (hIC : I ≤ centralizer (U : Set G))
    (hNK : normalizer (U : Set G) ≤ normalizer (K : Set G))
    (hQT : K.pCoreIn 2 ≤ T) (hLV : L ≤ normalizer (V : Set G))
    (hTV : T ≤ normalizer (V : Set G))
    (hRC : ⁅localResidual L U, centralizer (U : Set G)⁆ ≤ (localResidual L U).pCoreIn 2) :
    localResidual L U ⊔ K.pCoreIn 2 ≤ normalizer (I : Set G) ∧
      localResidual L U ⊔ K.pCoreIn 2 ≤ normalizer (I.pCoreIn 2 : Set G) := by
  let R := localResidual L U
  let J := R ⊔ K.pCoreIn 2
  have hCR : centralizer (U : Set G) ≤ normalizer (R : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hRC.trans (pCoreIn_le 2 R))
  have hCQ : centralizer (U : Set G) ≤ normalizer (K.pCoreIn 2 : Set G) :=
    ((centralizer_le_normalizer _).trans hNK).trans
      (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  have hCJ : centralizer (U : Set G) ≤ normalizer (J : Set G) :=
    (le_inf hCR hCQ).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hJV : J ≤ normalizer (V : Set G) :=
    sup_le (((localResidual_le L U).trans inf_le_left).trans hLV) (hQT.trans hTV)
  have hJI := normalizes_twoConjugate J V h hJV (hCJ (hIC hh))
  rw [hgen] at hJI
  exact ⟨hJI, hJI.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I))⟩

/-- The opening residual containment in 8.2.9: if H = ⟨I,T⟩, I centralizes U and T
normalizes U, then O²(H) centralizes U. The two-group quotient comes from T; it is not
asserted that O₂(H) centralizes U. -/
theorem residual_centralizes (H I T U : Subgroup G)
    (hgen : I ⊔ T = H) (hT : IsPGroup 2 T)
    (hIC : I ≤ centralizer (U : Set G)) (hTU : T ≤ normalizer (U : Set G)) :
    (pResidual 2 H).map H.subtype ≤ centralizer (U : Set G) := by
  let C := (centralizer (U : Set G)).subgroupOf H
  have hHN : H ≤ normalizer (U : Set G) := by
    rw [← hgen]
    exact sup_le (hIC.trans (centralizer_le_normalizer _)) hTU
  have hNC : normalizer (U : Set G) ≤ normalizer (centralizer (U : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer _)).mp inferInstance
  let : C.Normal := normal_subgroupOf_of_le_normalizer (hHN.trans hNC)
  have hIH : I ≤ H := hgen ▸ le_sup_left
  have hTH : T ≤ H := hgen ▸ le_sup_right
  have hc : C ⊔ T.subgroupOf H = ⊤ := by
    have hIT : I.subgroupOf H ⊔ T.subgroupOf H = ⊤ := by
      apply map_injective H.subtype_injective
      rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hIH, map_subgroupOf_eq_of_le hTH,
        ← MonoidHom.range_eq_map, range_subtype]
      exact hgen
    apply top_unique
    rw [← hIT]
    exact sup_le_sup (fun _ hx => hIC hx) le_rfl
  have hp := isPGroup_quotient_of_sup_eq_top C (T.subgroupOf H) hT.comap_subtype hc
  have hr : pResidual 2 H ≤ C := sInf_le ⟨inferInstance, hp⟩
  rintro _ ⟨x, hx, rfl⟩
  exact hr hx

/-- A group generated by two conjugates of V is O²(G)V. The proof uses the nilpotent
quotient to replace the conjugator by an element of O²(G). -/
theorem twoResidual_sup_of_twoConjugate [Finite G] (V : Subgroup G) (h : G)
    (hgen : V ⊔ V.map (MulAut.conj h⁻¹).toMonoidHom = ⊤) :
    pResidual 2 G ⊔ V = ⊤ := by
  obtain ⟨y, hy, he⟩ := exists_normal_conjugator_of_isPGroup_quotient
    V (pResidual 2 G) (isPGroup_quotient_pResidual 2) h⁻¹ hgen
  apply top_unique
  change ⊤ ≤ pResidual 2 G ⊔ V
  rw [← hgen]
  change V ⊔ V.conjBy h⁻¹ ≤ pResidual 2 G ⊔ V
  rw [← he]
  refine sup_le le_sup_right ?_
  rintro _ ⟨v, hv, rfl⟩
  exact (pResidual 2 G ⊔ V).mul_mem
    ((pResidual 2 G ⊔ V).mul_mem (mem_sup_left hy) (mem_sup_right hv))
    ((pResidual 2 G ⊔ V).inv_mem (mem_sup_left hy))

/-- The source identity I = O²(I)V, with both the residual and the conjugator embedded in
the original ambient group. -/
theorem embedded_twoResidual_sup [Finite G] (I V : Subgroup G) (h : G)
    (hh : h ∈ I) (hgen : V ⊔ V.map (MulAut.conj h⁻¹).toMonoidHom = I) :
    (pResidual 2 I).map I.subtype ⊔ V = I := by
  have hVI : V ≤ I := hgen ▸ le_sup_left
  let x : I := ⟨h, hh⟩
  have hmap : ((V.subgroupOf I).map (MulAut.conj x⁻¹).toMonoidHom).map I.subtype =
      V.map (MulAut.conj h⁻¹).toMonoidHom := by
    rw [map_map]
    have he : I.subtype.comp (MulAut.conj x⁻¹).toMonoidHom =
        (MulAut.conj h⁻¹).toMonoidHom.comp I.subtype := by ext; rfl
    rw [he, ← map_map, map_subgroupOf_eq_of_le hVI]
  have hg : V.subgroupOf I ⊔ (V.subgroupOf I).map (MulAut.conj x⁻¹).toMonoidHom = ⊤ := by
    apply map_injective I.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hVI, hmap,
      ← MonoidHom.range_eq_map, range_subtype]
    exact hgen
  have hm := congrArg (Subgroup.map I.subtype) (twoResidual_sup_of_twoConjugate _ x hg)
  simpa only [Subgroup.map_sup, map_subgroupOf_eq_of_le hVI,
    ← MonoidHom.range_eq_map, range_subtype] using hm

/-- Normalization of V and P = AB gives normalization of VA when B lies in V. -/
theorem product_normalized_of_core_product (T V A P B : Subgroup G)
    (hTV : T ≤ normalizer (V : Set G)) (hTP : T ≤ normalizer (P : Set G))
    (hP : A ⊔ B = P) (hBV : B ≤ V) :
    T ≤ normalizer ((V ⊔ A : Subgroup G) : Set G) := by
  have he : V ⊔ A = V ⊔ P := by
    rw [← hP, ← sup_assoc, sup_eq_left.mpr (hBV.trans le_sup_left)]
  rw [he]
  exact (le_inf hTV hTP).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- The implication from 8.2.9(1) to (2), with P = O₂(I) = A(V ∩ P) and the actual two-
conjugate I. Only T-normalization of O²(I) remains from part (1); the equality I =
O²(I)V is proved here. -/
theorem offender_product_normalized [Finite G] (I V A T : Subgroup G) (h : G)
    (hh : h ∈ I) (hgen : V ⊔ V.map (MulAut.conj h⁻¹).toMonoidHom = I)
    (hTV : T ≤ normalizer (V : Set G))
    (hTR : T ≤ normalizer ((pResidual 2 I).map I.subtype : Set G))
    (hP : A ⊔ (V ⊓ I.pCoreIn 2) = I.pCoreIn 2) :
    T ≤ normalizer (I : Set G) ∧
      T ≤ normalizer ((V ⊔ A : Subgroup G) : Set G) := by
  have hTI : T ≤ normalizer (I : Set G) := by
    rw [← embedded_twoResidual_sup I V h hh hgen]
    exact (le_inf hTR hTV).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hTP := hTI.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  exact ⟨hTI, product_normalized_of_core_product T V A (I.pCoreIn 2) _
    hTV hTP hP inf_le_left⟩

/-- The product-intersection bound in the opening of 8.2.10: a subgroup centralizing V meets
VA only in V when C_A(V) lies in V. -/
theorem core_inter_product_le (Q V A : Subgroup G)
    (hVQ : V ≤ Q) (hQC : Q ≤ centralizer (V : Set G))
    (hAV : A ≤ normalizer (V : Set G))
    (hAC : A ⊓ centralizer (V : Set G) ≤ V) : Q ⊓ (V ⊔ A) ≤ V := by
  rintro x ⟨hxQ, hxVA⟩
  have hx : x ∈ (V : Set G) * (A : Set G) := by
    rwa [← coe_mul_of_right_le_normalizer_left V A hAV]
  obtain ⟨v, hv, a, ha, rfl⟩ := hx
  have haQ : a ∈ Q := by
    simpa using Q.mul_mem (Q.inv_mem (hVQ hv)) hxQ
  exact V.mul_mem hv (hAC ⟨ha, hQC haQ⟩)

/-- Normalization of VA supplies the first commutator bound in 8.2.10. -/
theorem core_commutator_le (Q V A T : Subgroup G)
    (hVQ : V ≤ Q) (hQC : Q ≤ centralizer (V : Set G))
    (hAV : A ≤ normalizer (V : Set G)) (hAQ : A ≤ normalizer (Q : Set G))
    (hAC : A ⊓ centralizer (V : Set G) ≤ V)
    (hQT : Q ≤ T) (hTVA : T ≤ normalizer ((V ⊔ A : Subgroup G) : Set G)) :
    ⁅Q, A⁆ ≤ V := by
  apply le_trans (le_inf ?_ ?_) (core_inter_product_le Q V A hVQ hQC hAV hAC)
  · exact le_normalizer_iff_commutator_le_left.mp hAQ
  · exact (commutator_mono le_rfl (show A ≤ V ⊔ A from le_sup_right)).trans
      (le_normalizer_iff_commutator_le_right.mp (hQT.trans hTVA))

/-- The opening deduction in 8.2.10(1): O₂(L) centralizes L modulo V, from normalization of
VA and L = [L,A]. Normality for the quotient argument is proved inside L A. Recognition
of the block type and all remaining clauses of 8.2.10 are still separate obligations. -/
theorem block_core_commutator_le (L V A T : Subgroup G)
    (hVQ : V ≤ L.pCoreIn 2) (hQC : L.pCoreIn 2 ≤ centralizer (V : Set G))
    (hAT : A ≤ T) (hTL : T ≤ normalizer (L : Set G))
    (hLV : L ≤ normalizer (V : Set G)) (hAV : A ≤ normalizer (V : Set G))
    (hAC : A ⊓ centralizer (V : Set G) ≤ V)
    (hQT : L.pCoreIn 2 ≤ T) (hTVA : T ≤ normalizer ((V ⊔ A : Subgroup G) : Set G))
    (hfull : ⁅L, A⁆ = L) : ⁅L.pCoreIn 2, L⁆ ≤ V := by
  let Q := L.pCoreIn 2
  let D := L ⊔ A
  have hQL : Q ≤ L := pCoreIn_le 2 L
  have hQD : Q ≤ D := hQL.trans le_sup_left
  have hVD : V ≤ D := hVQ.trans hQD
  have hLQ : L ≤ normalizer (Q : Set G) := L.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hAQ : A ≤ normalizer (Q : Set G) := (hAT.trans hTL).trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  let : (Q.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer (sup_le hLQ hAQ)
  let : (V.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer (sup_le hLV hAV)
  have hQA : ⁅Q, A⁆ ≤ V :=
    core_commutator_le Q V A T hVQ hQC hAV hAQ hAC hQT hTVA
  have hQA' : ⁅Q.subgroupOf D, A.subgroupOf D⁆ ≤ V.subgroupOf D := by
    apply (map_le_map_iff_of_injective D.subtype_injective).mp
    rw [map_commutator, map_subgroupOf_eq_of_le hQD,
      map_subgroupOf_eq_of_le (show A ≤ D from le_sup_right),
      map_subgroupOf_eq_of_le hVD]
    exact hQA
  have hfull' : ⁅L.subgroupOf D, A.subgroupOf D⁆ = L.subgroupOf D := by
    apply map_injective D.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le (show L ≤ D from le_sup_left),
      map_subgroupOf_eq_of_le (show A ≤ D from le_sup_right), hfull]
  have hb := commutator_le_of_full_actor (Q.subgroupOf D) (L.subgroupOf D)
    (A.subgroupOf D) (V.subgroupOf D) hQA' hfull'
  have hm := map_mono (f := D.subtype) hb
  simpa only [map_commutator, map_subgroupOf_eq_of_le hQD,
    map_subgroupOf_eq_of_le (show L ≤ D from le_sup_left),
    map_subgroupOf_eq_of_le hVD] using hm

end CFSG.Quasithin.Chapter8.Section02.Normalizer
