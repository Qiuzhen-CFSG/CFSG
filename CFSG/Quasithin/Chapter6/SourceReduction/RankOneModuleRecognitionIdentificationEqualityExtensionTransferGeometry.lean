module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionQuotient
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionFixed
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionCore

/-!
# Weak closure and the transfer index in the equality branch

Write Q=O₂(LT), V=layer L R, P=O₂(⟨Vᴴ⟩), and D=C_H(⟨Vᴴ⟩).
When |D|=4, Q is the unique elementary subgroup of order32 in T,
hence is weakly closed. For an elementary E, a large intersection E∩V
forces E≤Q by the natural-module hyperplane bound. Otherwise its image
in the marked S₅ quotient has order four. The two possible four-groups
are the inner Sylow image and the outer image of P; their fixed subgroups
in Q have order at most four, contradicting |E|=32.

The noncommuting inner and outer four-groups also force P∩L to have
order16. Thus |T∩L|=64 and |P(T∩L)|=128, giving index two in T when
|D|=4. Every subgroup and quotient map is the original source one.
These results discharge the weak-closure and index premises of the
transfer argument. The involution-fusion proof remains with the equality
geometry owner `qt-d-1222-recognition-equality-geometry`.

Source: Aschbacher–Smith, proof of 6.2.13, printed p.688.
-/

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

omit [Finite G] in
private theorem centralizer_image (Q B C : Subgroup G) [IsMulCommutative Q]
    {J : Type*} [Group J] (f : G →* J) (hk : f.ker = Q)
    (he : B.map f = C.map f) :
    Q ⊓ centralizer (B : Set G) = Q ⊓ centralizer (C : Set G) := by
  have hb : B ⊔ Q = C ⊔ Q := by
    have hh := congrArg (Subgroup.comap f) he
    simpa only [comap_map_eq, hk] using hh
  have h (B : Subgroup G) : Q ⊓ centralizer (B : Set G) =
      Q ⊓ centralizer (B ⊔ Q : Subgroup G) := by
    apply le_antisymm
    · intro x hx
      refine ⟨hx.1, ?_⟩
      apply (le_centralizer_iff.mpr (sup_le
        (le_centralizer_iff.mp (zpowers_le.mpr hx.2))
        (le_centralizer_iff.mp (zpowers_le.mpr (Q.le_centralizer hx.1)))))
        (mem_zpowers x)
    · exact inf_le_inf_left _ (centralizer_le (show B ≤ B ⊔ Q from le_sup_left))
  rw [h B, h C, hb]

omit [Finite G] in
private theorem map_intersection_of_kernel_le {J : Type*} [Group J]
    (B C : Subgroup G) (f : G →* J) (hk : f.ker ≤ B) :
    (B ⊓ C).map f = B.map f ⊓ C.map f := by
  apply le_antisymm (map_inf_le B C f)
  rintro x ⟨⟨b,hb,he⟩,c,hc,hf⟩
  have hd : b⁻¹*c ∈ B := hk (by
    change f (b⁻¹*c) = 1
    rw [map_mul,map_inv,he,hf,inv_mul_cancel])
  have hcB : c ∈ B := by simpa only [mul_inv_cancel_left] using B.mul_mem hb hd
  exact ⟨c,⟨hcB,hc⟩,hf⟩

omit [Finite G] in
private theorem map_card_formula {J : Type*} [Group J] [Finite J]
    (B : Subgroup G) (f : G →* J) :
    Nat.card B = Nat.card (B ⊓ f.ker : Subgroup G) * Nat.card (B.map f) := by
  let g := f.comp B.subtype
  have hk : Nat.card g.ker = Nat.card (B ⊓ f.ker : Subgroup G) := by
    change Nat.card (f.ker.subgroupOf B) = _
    rw [← inf_subgroupOf_right f.ker B,
      Nat.card_congr (subgroupOfEquivOfLe (show f.ker ⊓ B ≤ B from inf_le_right)).toEquiv,
      inf_comm]
  have hc := g.ker.card_mul_index
  rw [index_ker,MonoidHom.range_comp,range_subtype,hk] at hc
  exact hc.symm

private theorem eight_even_card :
    Nat.card (Theory.SpecificGroups.SymmetricFive.OuterFourGeometry.eight ⊓
      alternatingGroup (Fin 5) : Subgroup (Equiv.Perm (Fin 5))) = 4 := by
  let B := Theory.SpecificGroups.SymmetricFive.OuterFourGeometry.eight
  have h8 : Nat.card B = 8 := Theory.SpecificGroups.SymmetricFive.OuterFourGeometry.eight_card
  have hn : ¬ B ≤ alternatingGroup (Fin 5) := by
    intro h
    have hd := card_dvd_of_le h
    rw [h8,nat_card_alternatingGroup,Nat.card_fin] at hd
    norm_num [Nat.factorial] at hd
  have hi : (alternatingGroup (Fin 5)).relIndex B = 2 := by
    have hd := (alternatingGroup (Fin 5)).relIndex_dvd_index_of_normal B
    rw [alternatingGroup.index_eq_two] at hd
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left (fun hh => hn (relIndex_eq_one.mp hh))
  have hc := relIndex_mul_relIndex (⊥ : Subgroup (Equiv.Perm (Fin 5)))
    (B ⊓ alternatingGroup (Fin 5)) B bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,hi,h8] at hc
  change Nat.card (B ⊓ alternatingGroup (Fin 5) : Subgroup _) = 4
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < (2 : ℕ)) hc

private theorem four_image_cases (S : Sylow 2 (Equiv.Perm (Fin 5)))
    (B E : Subgroup (Equiv.Perm (Fin 5)))
    [IsElementaryAbelian 2 B] [IsElementaryAbelian 2 E]
    (hB : Nat.card B = 4) (hE : Nat.card E = 4)
    (hBS : B ≤ (S : Subgroup _)) (hES : E ≤ (S : Subgroup _))
    (hout : ¬ B ≤ alternatingGroup (Fin 5)) :
    E = B ∨ E = (S : Subgroup _) ⊓ alternatingGroup (Fin 5) := by
  obtain ⟨e,heS,heB⟩ :=
    Theory.SpecificGroups.SymmetricFive.OuterFourGeometry.exists_marking S B hB hBS hout
  have heAlt : (alternatingGroup (Fin 5)).map e.toMonoidHom = alternatingGroup (Fin 5) :=
    characteristic_iff_map_eq.mp inferInstance e
  let : IsElementaryAbelian 2 (E.map e.toMonoidHom) := IsElementaryAbelian.map e.toMonoidHom
  by_cases hinner : E ≤ alternatingGroup (Fin 5)
  · right
    apply eq_of_le_of_card_ge (le_inf hES hinner)
    have hc : Nat.card ((S : Subgroup _) ⊓ alternatingGroup (Fin 5) : Subgroup _) = 4 := by
      rw [← card_map_of_injective (K := (S : Subgroup _) ⊓ alternatingGroup (Fin 5)) (f := e.toMonoidHom) e.injective,
        map_inf _ _ _ e.injective,heS,heAlt]
      exact eight_even_card
    omega
  · left
    have hm : E.map e.toMonoidHom = B.map e.toMonoidHom := by
      rw [heB]
      apply Theory.SpecificGroups.SymmetricFive.OuterFourGeometry.positioned_four_eq
      · rw [card_map_of_injective e.injective,hE]
      · exact heS ▸ map_mono hES
      · intro hh
        apply hinner
        rw [← heAlt] at hh
        exact (map_le_map_iff_of_injective e.injective).mp hh
    exact (map_injective e.injective) hm


private theorem elementary_order32_unique
    (S Q V B C : Subgroup G) [IsElementaryAbelian 2 Q]
    (f : G →* Equiv.Perm (Fin 5)) (hk : f.ker = Q)
    (S₀ : Sylow 2 (Equiv.Perm (Fin 5))) (hS : S.map f = (S₀ : Subgroup _))
    (hVQ : V ≤ Q) (hQ32 : Nat.card Q = 32) (hV16 : Nat.card V = 16)
    [IsElementaryAbelian 2 (B.map f)]
    (hB4 : Nat.card (B.map f) = 4) (hBS : B ≤ S)
    (hBout : ¬ B.map f ≤ alternatingGroup (Fin 5))
    (hC : C.map f = (S₀ : Subgroup _) ⊓ alternatingGroup (Fin 5))
    (hCB : Nat.card (Q ⊓ centralizer (B : Set G) : Subgroup G) ≤ 4)
    (hCC : Nat.card (Q ⊓ centralizer (C : Set G) : Subgroup G) ≤ 4)
    (hlarge : ∀ E : Subgroup G, IsElementaryAbelian 2 E → E ≤ S →
      8 ≤ Nat.card (E ⊓ V : Subgroup G) → E ≤ Q)
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hES : E ≤ S)
    (hE32 : Nat.card E = 32) : E = Q := by
  by_contra hn
  have hnot : ¬ E ≤ Q := fun hh => hn (eq_of_le_of_card_ge hh (by omega))
  have hEVsmall : Nat.card (E ⊓ V : Subgroup G) < 8 := by
    by_contra hh
    exact hnot (hlarge E inferInstance hES (by omega))
  have hEVdiv : Nat.card (E ⊓ V : Subgroup G) ∣ 16 :=
    hV16 ▸ card_dvd_of_le (show E ⊓ V ≤ V from inf_le_right)
  have hEV4 : Nat.card (E ⊓ V : Subgroup G) ≤ 4 := by
    have : ∀ a : ℕ, a < 8 → a ∣ 16 → a ≤ 4 := by decide +kernel
    exact this _ hEVsmall hEVdiv
  have hk8 : Nat.card (E ⊓ Q : Subgroup G) ≤ 8 := by
    have hnorm : V ≤ normalizer (E ⊓ Q : Subgroup G) := by
      apply (hVQ.trans Q.le_centralizer).trans
      exact (centralizer_le (show E ⊓ Q ≤ Q from inf_le_right)).trans (Subgroup.centralizer_le_normalizer _)
    have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes (E ⊓ Q) V hnorm
    have hinter : (E ⊓ Q) ⊓ V = E ⊓ V := by rw [inf_assoc,inf_eq_right.mpr hVQ]
    have hs := card_le_of_le (sup_le (show E ⊓ Q ≤ Q from inf_le_right) hVQ)
    rw [hinter,hV16] at hc
    rw [hQ32] at hs
    have hbound := Nat.mul_le_mul hEV4 hs
    nlinarith
  let : IsElementaryAbelian 2 (E.map f) := IsElementaryAbelian.map f
  have hE4 : Nat.card (E.map f) ≤ 4 :=
    (primeRank_le_iff_elementary_card_le _).mp
      Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two _ inferInstance
  have hformula := map_card_formula E f
  rw [hk,hE32] at hformula
  have hEq4 : Nat.card (E.map f) = 4 := by
    by_contra hh
    have hbound := Nat.mul_le_mul hk8 (show Nat.card (E.map f) ≤ 3 by omega)
    omega
  have hcases := four_image_cases S₀ (B.map f) (E.map f) hB4 hEq4
    (hS ▸ map_mono hBS) (hS ▸ map_mono hES) hBout
  have hfixed : Nat.card (Q ⊓ centralizer (E : Set G) : Subgroup G) ≤ 4 := by
    rcases hcases with he | he
    · rw [centralizer_image Q E B f hk he]
      exact hCB
    · rw [centralizer_image Q E C f hk (he.trans hC.symm)]
      exact hCC
  have hker : Nat.card (E ⊓ Q : Subgroup G) ≤ 4 :=
    (card_le_of_le (le_inf inf_le_right (inf_le_left.trans E.le_centralizer))).trans hfixed
  rw [hEq4] at hformula
  omega

private theorem large_intersection
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hET : E ≤ (T : Subgroup G))
    (hlarge : 8 ≤ Nat.card (E ⊓ layer L R : Subgroup G)) :
    E ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let V := layer L R
  let B := E ⊓ V
  let := h611.layer_elementary
  have hV16 : Nat.card V = 16 := hnatural.2.1.card
  have hBV : B ≤ V := inf_le_right
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) B V bot_le hBV
  rw [relIndex_bot_left,relIndex_bot_left,hV16] at hc
  have hi : B.relIndex V ≤ 2 := by
    change 8 ≤ Nat.card B at hlarge
    nlinarith
  have hcor : ChapterE.subgroupCorank V B ≤ 1 := by
    unfold ChapterE.subgroupCorank
    interval_cases hh : B.relIndex V <;> decide
  have hEN : E ≤ normalizer (V : Set G) := hET.trans h611.sylow_normalizes_layer
  have hCE : E ≤ centralizer (V : Set G) := by
    apply (ChapterE.inducedAutomizer_eq_bot_iff hEN).mp
    apply eq_bot_iff.mpr
    intro a ha
    by_contra hn
    have hane : a ≠ 1 := by simpa only [mem_bot] using hn
    have hlo := natural_automizer_fixedCodim_ge hnatural.2.1
      (A.normalizer_layer.trans ((normal_subgroupOf_iff_le_normalizer h611.L_le).mp h611.L_normal)) hane
    have hmid := ChapterE.fixedCodim_mono (ChapterE.automizerRepresentation V)
      (zpowers_le.mpr ha)
    have hhi : Representation.BinaryOffender.fixedCodim (ChapterE.automizerRepresentation V)
        (ChapterE.inducedAutomizer V E) ≤ ChapterE.subgroupCorank V B := by
      rw [ChapterE.fixedCodim_inducedAutomizer V E hEN]
      exact ChapterE.Section06.subgroupCorank_antitone
        (le_inf hBV (inf_le_left.trans E.le_centralizer))
    change 2 ≤ Representation.BinaryOffender.fixedCodim (ChapterE.automizerRepresentation V) (zpowers a) at hlo
    omega
  rw [← equality_sylow_centralizer_eq_core h611 hnatural]
  exact le_inf hET hCE

omit [Finite G] in
private theorem subtype_centralizer_map (M B C : Subgroup G) (hB : B ≤ M) (hC : C ≤ M) :
    (B.subgroupOf M ⊓ centralizer (C.subgroupOf M : Set M)).map M.subtype =
      B ⊓ centralizer (C : Set G) := by
  ext x
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨hx.1,?_⟩
    intro c hc
    exact congrArg Subtype.val (hx.2 ⟨c,hC hc⟩ hc)
  · intro hx
    refine ⟨⟨x,hB hx.1⟩,⟨hx.1,?_⟩,rfl⟩
    intro c hc
    exact Subtype.ext (hx.2 c hc)

/-- Under the order-four alternative, the actual local core is the unique
 elementary subgroup of order thirty-two in the chosen Sylow group. -/
theorem LocalAnalysis.equality_elementary_order32_unique
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R)
    (hfour : Nat.card (equalityCentralizer L R z) = 4)
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hET : E ≤ (T : Subgroup G))
    (hE32 : Nat.card E = 32) : E = (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let H := centralizer ({z} : Set G)
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let V := layer L R
  let P := (equalityCore L R z).map H.subtype
  let C := (T : Subgroup G) ⊓ L
  let S := (T : Subgroup G).subgroupOf M
  have hQT : Q ≤ (T : Subgroup G) := by
    rw [show Q = (L ⊔ (T : Subgroup G)).pCoreIn 2 from rfl,
      ←equality_sylow_centralizer_eq_core h611 hnatural]
    exact inf_le_left
  have hQM : Q ≤ M := hQT.trans h611.sylow_le
  have hVM : V ≤ M := h611.layer_le_L.trans h611.L_le
  have hPT : P ≤ (T : Subgroup G) := equalityCore_le_sylow hTH
  have hPM : P ≤ M := hPT.trans h611.sylow_le
  have hCM : C ≤ M := inf_le_left.trans h611.sylow_le
  have hEM : E ≤ M := hET.trans h611.sylow_le
  let := A.equality_local_core_elementary h611 hnatural hz horder hTH hbranch
  let : IsElementaryAbelian 2 (Q.subgroupOf M) := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hQM).toMonoidHom (subgroupOfEquivOfLe hQM).injective
  obtain ⟨f,hf,hker,hL,hPE,hPk,hP4,hPout⟩ :=
    A.equality_core_permutation_image h611 hnatural hz horder hTH hbranch
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
  change IsElementaryAbelian 2 (f.comp j).range at hPE
  change Nat.card (f.comp j).range = 4 at hP4
  change ¬ (f.comp j).range ≤ alternatingGroup (Fin 5) at hPout
  rw [hr] at hPE hP4 hPout
  let := hPE
  let S₀ := (T.subtype h611.sylow_le).mapSurjective hf
  have hS : S.map f = (S₀ : Subgroup _) := rfl
  have hC : (C.subgroupOf M).map f = (S₀ : Subgroup _) ⊓ alternatingGroup (Fin 5) := by
    change (S ⊓ L.subgroupOf M).map f = _
    rw [map_intersection_of_kernel_le S (L.subgroupOf M) f (by
      rw [hker]; exact subgroupOf_mono M hQT),hS,hL]
  have hQ32 : Nat.card Q = 32 := by
    have hh := (A.equality_extension_orders h611 hnatural hz horder hTH hbranch).1
    rw [hfour] at hh
    exact hh
  have hBbound : Nat.card (Q ⊓ centralizer (P : Set G) : Subgroup G) ≤ 4 := by
    have hle : Q ⊓ centralizer (P : Set G) ≤ equalityCentralizer L R z := by
      intro x hx
      let xH : H := ⟨x,hTH (hQT hx.1)⟩
      have hc : xH ∈ centralizer (equalityCore L R z : Set H) := by
        intro p hp
        exact Subtype.ext (hx.2 p (mem_map_of_mem H.subtype hp))
      rw [A.equality_core_centralizer h611 hnatural hz] at hc
      exact mem_map_of_mem H.subtype hc
    exact (card_le_of_le hle).trans_eq hfour
  have hCbound : Nat.card (Q ⊓ centralizer (C : Set G) : Subgroup G) ≤ 4 := by
    rw [show Q ⊓ centralizer (C : Set G) = ZS (T : Subgroup G) L R from
      A.equality_local_core_sylow_fixed h611 hnatural hz horder hTH hbranch,
      (h611.natural_ZS_geometry hnatural).2.1]
  have hc (B : Subgroup G) (hBM : B ≤ M) :
      Nat.card (B.subgroupOf M) = Nat.card B :=
    Nat.card_congr (subgroupOfEquivOfLe hBM).toEquiv
  let : IsElementaryAbelian 2 (E.subgroupOf M) :=
    IsElementaryAbelian.of_injective (subgroupOfEquivOfLe hEM).toMonoidHom
      (subgroupOfEquivOfLe hEM).injective
  have heq := elementary_order32_unique S (Q.subgroupOf M) (V.subgroupOf M)
    (P.subgroupOf M) (C.subgroupOf M) f hker S₀ hS
    (subgroupOf_mono M (h611.layer_le_V.trans (reduced_le_core h611.V_mem)))
    ((hc Q hQM).trans hQ32) ((hc V hVM).trans hnatural.2.1.card)
    hP4 (subgroupOf_mono M hPT) hPout hC
    (by rw [← card_map_of_injective M.subtype_injective,
      subtype_centralizer_map M Q P hQM hPM]; exact hBbound)
    (by rw [← card_map_of_injective M.subtype_injective,
      subtype_centralizer_map M Q C hQM hCM]; exact hCbound)
    (fun B hB hBS hlarge => by
      let := hB
      let : IsElementaryAbelian 2 (B.map M.subtype) := IsElementaryAbelian.map M.subtype
      have hBT : B.map M.subtype ≤ (T : Subgroup G) := by
        have hh := map_mono (f := M.subtype) hBS
        rwa [map_subgroupOf_eq_of_le h611.sylow_le] at hh
      have hbig : 8 ≤ Nat.card (B.map M.subtype ⊓ V : Subgroup G) := by
        rw [← map_subgroupOf_eq_of_le hVM,← map_inf _ _ _ M.subtype_injective,
          card_map_of_injective M.subtype_injective]
        exact hlarge
      have hh := large_intersection A h611 hnatural (B.map M.subtype) hBT hbig
      exact fun b hb => hh (mem_map_of_mem M.subtype hb))
    (E.subgroupOf M) (subgroupOf_mono M hET) ((hc E hEM).trans hE32)
  have hm := congrArg (Subgroup.map M.subtype) heq
  rwa [map_subgroupOf_eq_of_le hEM,map_subgroupOf_eq_of_le hQM] at hm

/-- The order-four local core is weakly closed in the actual Sylow group.
 This discharges the weak-closure premise of the elementary-four transfer. -/
theorem LocalAnalysis.equality_local_core_weakly_closed
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R)
    (hfour : Nat.card (equalityCentralizer L R z) = 4)
    (g : G) (hg : ((L ⊔ (T : Subgroup G)).pCoreIn 2).conjBy g ≤ (T : Subgroup G)) :
    ((L ⊔ (T : Subgroup G)).pCoreIn 2).conjBy g = (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let := A.equality_local_core_elementary h611 hnatural hz horder hTH hbranch
  let : IsElementaryAbelian 2 (Q.conjBy g) := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  apply A.equality_elementary_order32_unique h611 hnatural hz horder hTH hbranch hfour _ hg
  change Nat.card (Q.map (MulAut.conj g).toMonoidHom) = 32
  rw [card_map_of_injective (MulAut.conj g).injective]
  have hh := (A.equality_extension_orders h611 hnatural hz horder hTH hbranch).1
  rw [hfour] at hh
  exact hh

private theorem card_strict {B C : Subgroup G} (h : B < C) : Nat.card B < Nat.card C := by
  apply lt_of_le_of_ne (card_le_of_le h.le)
  intro he
  exact h.ne (eq_of_le_of_card_ge h.le he.ge)

private theorem outer_four_selfcentralizing (S : Sylow 2 (Equiv.Perm (Fin 5)))
    (B : Subgroup (Equiv.Perm (Fin 5))) [IsElementaryAbelian 2 B]
    (hB4 : Nat.card B = 4) (hBS : B ≤ (S : Subgroup _))
    (hout : ¬ B ≤ alternatingGroup (Fin 5)) : centralizer (B : Set _) = B := by
  obtain ⟨e,_,heB⟩ :=
    Theory.SpecificGroups.SymmetricFive.OuterFourGeometry.exists_marking S B hB4 hBS hout
  apply le_antisymm ?_ B.le_centralizer
  apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
  rw [heB,←Theory.SpecificGroups.SymmetricFive.OuterFourGeometry.four_centralizer]
  rintro _ ⟨c,hc,rfl⟩ b hb
  rw [←heB] at hb
  obtain ⟨b,hb,rfl⟩ := hb
  rw [←map_mul,←map_mul]
  exact congrArg e.toMonoidHom (hc b hb)

private theorem sylow_even_four_card (S : Sylow 2 (Equiv.Perm (Fin 5))) :
    Nat.card ((S : Subgroup _) ⊓ alternatingGroup (Fin 5) : Subgroup _) = 4 := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin 5)) S
    Theory.SpecificGroups.SymmetricFive.OuterFourGeometry.standardSylow
  let e := MulAut.conj g
  have hS : (S : Subgroup _).map e.toMonoidHom =
      Theory.SpecificGroups.SymmetricFive.OuterFourGeometry.eight :=
    congrArg (fun Q : Sylow 2 (Equiv.Perm (Fin 5)) => (Q : Subgroup (Equiv.Perm (Fin 5)))) hg
  rw [←card_map_of_injective (K := (S : Subgroup _) ⊓ alternatingGroup (Fin 5))
    (f := e.toMonoidHom) e.injective,map_inf _ _ _ e.injective,hS,
    characteristic_iff_map_eq.mp (inferInstance : (alternatingGroup (Fin 5)).Characteristic) e]
  exact eight_even_card

/-- Orders of the actual local Sylow, its intersection with the canonical
 core, and their transfer join. Both centralizer alternatives are retained. -/
theorem LocalAnalysis.equality_transfer_subgroup_orders
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    Nat.card ((T : Subgroup G) ⊓ L : Subgroup G) = 64 ∧
      Nat.card ((equalityCore L R z).map (centralizer ({z} : Set G)).subtype ⊓ L : Subgroup G) = 16 ∧
      Nat.card (equalityTransferSubgroup (T : Subgroup G) L R z) = 128 := by
  let H := centralizer ({z} : Set G)
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let V := layer L R
  let P := (equalityCore L R z).map H.subtype
  let C := (T : Subgroup G) ⊓ L
  let S := (T : Subgroup G).subgroupOf M
  have hQT : Q ≤ (T : Subgroup G) := by
    rw [show Q = (L ⊔ (T : Subgroup G)).pCoreIn 2 from rfl,
      ←equality_sylow_centralizer_eq_core h611 hnatural]
    exact inf_le_left
  have hQM : Q ≤ M := hQT.trans h611.sylow_le
  have hVM : V ≤ M := h611.layer_le_L.trans h611.L_le
  have hPT : P ≤ (T : Subgroup G) := equalityCore_le_sylow hTH
  have hPM : P ≤ M := hPT.trans h611.sylow_le
  have hCM : C ≤ M := inf_le_left.trans h611.sylow_le
  let := A.equality_local_core_elementary h611 hnatural hz horder hTH hbranch
  let : IsElementaryAbelian 2 (Q.subgroupOf M) := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hQM).toMonoidHom (subgroupOfEquivOfLe hQM).injective
  obtain ⟨f,hf,hker,hL,hPE,hPk,hP4,hPout⟩ :=
    A.equality_core_permutation_image h611 hnatural hz horder hTH hbranch
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
  change IsElementaryAbelian 2 (f.comp j).range at hPE
  change Nat.card (f.comp j).range = 4 at hP4
  change ¬ (f.comp j).range ≤ alternatingGroup (Fin 5) at hPout
  rw [hr] at hPE hP4 hPout
  let := hPE
  let S₀ := (T.subtype h611.sylow_le).mapSurjective hf
  have hS : S.map f = (S₀ : Subgroup _) := rfl
  have hC : (C.subgroupOf M).map f = (S₀ : Subgroup _) ⊓ alternatingGroup (Fin 5) := by
    change (S ⊓ L.subgroupOf M).map f = _
    rw [map_intersection_of_kernel_le S (L.subgroupOf M) f (by
      rw [hker]; exact subgroupOf_mono M hQT),hS,hL]
  have hVQ : V ≤ Q := h611.layer_le_V.trans (reduced_le_core h611.V_mem)
  have hVL : V ≤ L := h611.layer_le_L
  have hLQ : L ⊓ Q = V := by
    rw [show V = L.pCoreIn 2 from A.equality_layer_eq_core h611 hnatural hz horder hTH hbranch]
    apply le_antisymm ?_ (le_inf (pCoreIn_le 2 L) (by
      rw [← A.equality_layer_eq_core h611 hnatural hz horder hTH hbranch]; exact hVQ))
    apply le_pCoreIn_of_normalizes
      ((isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))).to_le inf_le_right) inf_le_left
    have hLN : L ≤ normalizer (Q : Set G) :=
      (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left).trans
        ((L ⊔ (T : Subgroup G)).le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
    intro l hl
    rw [mem_normalizer_iff_map_conj_eq,map_inf _ _ _ (MulAut.conj l).injective,
      mem_normalizer_iff_map_conj_eq.mp (L.le_normalizer hl),
      mem_normalizer_iff_map_conj_eq.mp (hLN hl)]
  have hC4 : Nat.card ((C.subgroupOf M).map f) = 4 := by
    rw [hC]
    exact sylow_even_four_card S₀
  have hCQ : C ⊓ Q = V := by
    change ((T : Subgroup G) ⊓ L) ⊓ Q = V
    rw [inf_assoc,hLQ,inf_eq_right.mpr h611.layer_le_T]
  have hC64 : Nat.card C = 64 := by
    have hh := map_card_formula (C.subgroupOf M) f
    rw [hker,show C.subgroupOf M ⊓ Q.subgroupOf M = (C ⊓ Q).subgroupOf M from rfl,hCQ,
      Nat.card_congr (subgroupOfEquivOfLe hCM).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hVM).toEquiv,hC4] at hh
    have hv : Nat.card V = 16 := hnatural.2.1.card
    rw [hv] at hh
    exact hh
  have hPn : (T : Subgroup G) ≤ normalizer (P : Set G) := by
    have hh := (equalityCore L R z).le_normalizer_map H.subtype
    have hH : H ≤ normalizer (P : Set G) := by
      simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
    exact hTH.trans hH
  have hPLnotQ : ¬ P ⊓ L ≤ Q := by
    intro hPL
    have hcomm : ⁅P,C⁆ ≤ Q := by
      apply (le_inf
        (le_normalizer_iff_commutator_le_left.mp (inf_le_left.trans hPn))
        ?_).trans hPL
      exact (commutator_mono le_rfl (show C ≤ L from inf_le_right)).trans
        (le_normalizer_iff_commutator_le_right.mp (hPT.trans h611.sylow_normalizes_L))
    have hCB : (C.subgroupOf M).map f ≤ centralizer ((P.subgroupOf M).map f : Set _) := by
      rintro _ ⟨c,hc,rfl⟩ _ ⟨p,hp,rfl⟩
      apply commutatorElement_eq_one_iff_mul_comm.mp
      rw [←map_commutatorElement]
      change ⁅p,c⁆ ∈ f.ker
      rw [hker]
      exact hcomm (commutator_mem_commutator hp hc)
    rw [outer_four_selfcentralizing S₀ (P.subgroupOf M |>.map f)
      hP4 (hS ▸ map_mono (subgroupOf_mono M hPT)) hPout] at hCB
    have he := eq_of_le_of_card_ge hCB (show
      Nat.card ((P.subgroupOf M).map f) ≤ Nat.card ((C.subgroupOf M).map f) by omega)
    apply hPout
    rw [←he,hC]
    exact inf_le_right
  have hp := A.equality_action_pair_data h611 hnatural hz horder hTH hbranch
  have hP32 : Nat.card P = 32 := by
    rw [show P = (equalityCore L R z).map H.subtype from rfl,card_map_of_injective H.subtype_injective]
    exact hp.plusType.some.card
  have hPV8 : Nat.card (P ⊓ V : Subgroup G) = 8 := by
    rw [inf_comm,equality_layer_inf_core h611 hz]
    exact A.layer_core_card
  have hPLlt : Nat.card (P ⊓ L : Subgroup G) < 32 := by
    have hproper : P ⊓ L < P := lt_of_le_of_ne inf_le_left (by
      intro he
      apply hPout
      have hPL : P ≤ L := he ▸ inf_le_right
      rw [←hL]
      exact map_mono (subgroupOf_mono M hPL))
    exact (card_strict hproper).trans_eq hP32
  have hPLgt : 8 < Nat.card (P ⊓ L : Subgroup G) := by
    have hproper : P ⊓ V < P ⊓ L := lt_of_le_of_ne (inf_le_inf_left P hVL) (by
      intro he
      exact hPLnotQ (he ▸ inf_le_right.trans hVQ))
    exact hPV8 ▸ card_strict hproper
  have hPL16 : Nat.card (P ⊓ L : Subgroup G) = 16 := by
    have hd : Nat.card (P ⊓ L : Subgroup G) ∣ 32 :=
      hP32 ▸ card_dvd_of_le (show P ⊓ L ≤ P from inf_le_left)
    have harith : ∀ a : ℕ, a < 32 → 8 < a → a ∣ 32 → a = 16 := by decide +kernel
    exact harith _ hPLlt hPLgt hd
  have hPC : P ⊓ C = P ⊓ L := by
    change P ⊓ ((T : Subgroup G) ⊓ L) = _
    rw [←inf_assoc,inf_eq_left.mpr hPT]
  have hPC128 : Nat.card (P ⊔ C : Subgroup G) = 128 := by
    have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes P C (inf_le_left.trans hPn)
    rw [hP32,hC64,hPC,hPL16] at hc
    omega
  exact ⟨hC64,hPL16,hPC128⟩

/-- In the order-four alternative, the literal transfer subgroup P(T∩L)
 has index two in the chosen Sylow group. -/
theorem LocalAnalysis.equality_transfer_subgroup_index
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R)
    (hfour : Nat.card (equalityCentralizer L R z) = 4) :
    (equalityTransferSubgroup (T : Subgroup G) L R z).relIndex (T : Subgroup G) = 2 := by
  let P := (equalityCore L R z).map (centralizer ({z} : Set G)).subtype
  let C := (T : Subgroup G) ⊓ L
  have hPT : P ≤ (T : Subgroup G) := equalityCore_le_sylow hTH
  have hPC128 : Nat.card (P ⊔ C : Subgroup G) = 128 :=
    (A.equality_transfer_subgroup_orders h611 hnatural hz horder hTH hbranch).2.2
  have hT256 : Nat.card T = 256 := by
    have hh := (A.equality_extension_orders h611 hnatural hz horder hTH hbranch).2
    rw [hfour] at hh
    exact hh
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G) (P ⊔ C) (T : Subgroup G)
    bot_le (sup_le hPT inf_le_left)
  rw [relIndex_bot_left,relIndex_bot_left,hPC128,hT256] at hi
  change (P ⊔ C).relIndex (T : Subgroup G) = 2
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
