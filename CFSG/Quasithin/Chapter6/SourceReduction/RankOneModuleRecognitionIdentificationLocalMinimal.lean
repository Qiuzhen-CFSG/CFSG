module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalSymmetric
public import Theory.Representation.AlternatingSevenFiveSeed.Geometry
public import Theory.SpecificGroups.Alternating.FiveSylowMaximal

/-!
# Minimal H-star preimage in the order-four branch

The original layer has image a best offender in the marked A₇ action.
A Sylow-normalized A₅ seed through that offender supplies the unique proper
Sylow overgroup of index five. Its full preimage in L₀ is minimal outside M:
the unique proper overgroup preserves Z_S, whereas a quintic action on U
cannot preserve that plane. The actual elementary layer still maps onto
a full Sylow four-group of this same A₅ seed.

Source: Aschbacher--Smith, 6.2.11, printed p.686. The generation-parameter
contradiction remains separate; no LocalAnalysis or later identification
is assumed.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction
variable {G : Type*} [Group G] [Finite G] {P : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- Realize the original faithful A₇ image as its marked action on U. -/
theorem four_marked_alternating_action
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hNL : normalizer (layer L R : Set G) ≤ normalizer (L : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    letI := four_closure_elementary h hnatural hz ho hP hplane hcard
    ∃ q : fourOvergroup (P : Subgroup G) L z →* alternatingGroup (Fin 7),
      Function.Surjective q ∧
      ∃ ρ : Representation (ZMod 2) (alternatingGroup (Fin 7))
          (Additive (sourceClosure (P : Subgroup G) L R z)),
        Function.Injective ρ ∧
        (∀ (x : fourOvergroup (P : Subgroup G) L z)
          (u : sourceClosure (P : Subgroup G) L R z),
          ((ρ (q x) (Additive.ofMul u)).toMul : G) = (x : G) * u * (x : G)⁻¹) := by
  let U := sourceClosure (P : Subgroup G) L R z
  let := four_closure_elementary h hnatural hz ho hP hplane hcard
  let hn := four_generated_overgroup_normalizes_closure h hnatural hz ho hP hplane hNL hcard
  let f := fourOvergroupAction (P : Subgroup G) L R z hn
  obtain ⟨e⟩ := four_overgroup_action_alternating h hnatural hz ho hP hplane hNL hcard
  let q := e.toMonoidHom.comp f.rangeRestrict
  let ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Additive U) := {
    toFun a := (e.symm a).val.toMonoidHom.toAdditive.toZModLinearMap 2
    map_one' := by ext u; simp
    map_mul' a b := by ext u; simp }
  refine ⟨q, e.surjective.comp f.rangeRestrict_surjective, ρ, ?_, ?_⟩
  · intro a b hab
    apply e.symm.injective
    apply Subtype.ext
    apply MulEquiv.ext
    intro u
    exact congrArg (fun l : Module.End (ZMod 2) (Additive U) => l (Additive.ofMul u)) hab
  · intro x u
    change ((e.symm (e (f.rangeRestrict x))).val u : G) = _
    rw [e.symm_apply_apply]
    rfl

omit [Finite G] in
private theorem marked_kernel {X U : Subgroup G} [IsElementaryAbelian 2 U]
    {D : Type*} [Group D] (q : X →* D)
    (ρ : Representation (ZMod 2) D (Additive U)) (hf : Function.Injective ρ)
    (hρ : ∀ (x : X) (u : U), ((ρ (q x) (Additive.ofMul u)).toMul : G) =
      (x : G) * u * (x : G)⁻¹) : q.ker = (centralizer (U : Set G)).subgroupOf X := by
  ext x
  change q x = 1 ↔ (x : G) ∈ centralizer (U : Set G)
  constructor
  · intro hx u hu
    have hh := hρ x ⟨u,hu⟩
    rw [hx,map_one] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  · intro hx
    apply hf
    rw [map_one]
    apply LinearMap.ext
    intro u
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (hρ x u.toMul).trans (mul_inv_eq_of_eq_mul (hx u.toMul u.toMul.property).symm)

omit [Finite G] in
private theorem marked_fixed_iff {X U A : Subgroup G} [IsElementaryAbelian 2 U]
    {D : Type*} [Group D] (q : X →* D)
    (ρ : Representation (ZMod 2) D (Additive U))
    (hρ : ∀ (x : X) (u : U), ((ρ (q x) (Additive.ofMul u)).toMul : G) =
      (x : G) * u * (x : G)⁻¹) (hAX : A ≤ X) (u : Additive U) :
    u ∈ fixedSpace ρ ((A.subgroupOf X).map q) ↔
      (u.toMul : G) ∈ centralizer (A : Set G) := by
  constructor
  · intro hu a ha
    have hf := congrArg (fun v : Additive U => (v.toMul : G))
      (hu ⟨q ⟨a,hAX ha⟩,mem_map_of_mem q ha⟩)
    change ((ρ (q ⟨a,hAX ha⟩) (Additive.ofMul u.toMul)).toMul : G) = _ at hf
    rw [hρ] at hf
    exact mul_inv_eq_iff_eq_mul.mp hf
  · intro hu a
    obtain ⟨x,hx,he⟩ := a.property
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((ρ a.val u).toMul : G) = (u.toMul : G)
    rw [← he]
    exact (hρ x u.toMul).trans (mul_inv_eq_of_eq_mul (hu x hx))

/-- The original layer maps to a best offender in the marked A₇ action. -/
theorem four_layer_best_in_alternating
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4)
    (q : fourOvergroup (P : Subgroup G) L z →* alternatingGroup (Fin 7)) :
    letI := four_closure_elementary h hnatural hz ho hP hplane hcard
    ∀ (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7))
          (Additive (sourceClosure (P : Subgroup G) L R z))),
      Function.Injective ρ →
      (∀ (x : fourOvergroup (P : Subgroup G) L z)
          (u : sourceClosure (P : Subgroup G) L R z),
          ((ρ (q x) (Additive.ofMul u)).toMul : G) = (x : G) * u * (x : G)⁻¹) →
      IsBestOffender ρ (((layer L R).subgroupOf (fourOvergroup (P : Subgroup G) L z)).map q) := by
  let U := sourceClosure (P : Subgroup G) L R z
  let B := layer L R
  let X := fourOvergroup (P : Subgroup G) L z
  let S := ZS (P : Subgroup G) L R
  let := four_closure_elementary h hnatural hz ho hP hplane hcard
  intro ρ hf hρ
  have hBX : B ≤ X := (layer_le_involution_centralizer h hz).trans le_sup_right
  have hSU : S ≤ U := (ZS_le_sourceClosure_intersection h hz).trans inf_le_left
  let A := (B.subgroupOf X).map q
  let := h.layer_elementary
  let : IsElementaryAbelian 2 (B.subgroupOf X) := IsElementaryAbelian.subgroupOf hBX
  have hAel : IsElementaryAbelian 2 A := IsElementaryAbelian.map q
  have hker := marked_kernel q ρ hf hρ
  have hi : S.relIndex B = 4 := by
    have hh := (S.subgroupOf B).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (show S ≤ B from inf_le_left)).toEquiv,
      (h.natural_ZS_geometry hnatural).2.1, hnatural.2.1.card] at hh
    change 4 * S.relIndex B = 2 ^ (2 * 2) at hh
    omega
  have hcA : Nat.card A = 4 := by
    rw [← relIndex_ker, hker, relIndex_subgroupOf hBX]
    rw [← inf_relIndex_right (centralizer (U : Set G)) B, inf_comm, four_layer_centralizer_closure h hnatural hz ho hP hplane hcard]
    exact hi
  have hfixed (u : Additive U) : u ∈ fixedSpace ρ A ↔ (u.toMul : G) ∈ S := by
    rw [marked_fixed_iff q ρ hρ hBX u]
    exact ⟨fun hu => (four_closure_centralizer_layer h hnatural hz ho hP hplane hcard).le
      ⟨u.toMul.property,hu⟩,fun hu => ((four_closure_centralizer_layer h hnatural hz ho hP hplane hcard).ge hu).2⟩
  let ef : fixedSpace ρ A ≃ S := {
    toFun u := ⟨u.val.toMul,(hfixed u).mp u.property⟩
    invFun s := ⟨Additive.ofMul ⟨s,hSU s.property⟩,(hfixed _).mpr s.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hcF : Nat.card (fixedSpace ρ A) = 4 :=
    (Nat.card_congr ef).trans (h.natural_ZS_geometry hnatural).2.1
  have hd : Module.finrank (ZMod 2) (Additive U) = 4 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive U)
    change Nat.card U = _ at hh
    rw [four_closure_card h hnatural hz ho hP hplane hcard,Nat.card_zmod] at hh
    exact hh.symm
  have hdF : Module.finrank (ZMod 2) (fixedSpace ρ A) = 2 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ A)
    rw [Nat.card_zmod] at hh
    exact hh.symm.trans hcF
  apply (isBestOffender_iff_of_not_strong ρ
    (Representation.BinaryAlternatingSevenControl.no_strong_offender ρ hf hd) A).mpr
  refine ⟨⟨?_,hAel⟩,?_⟩
  · intro he
    rw [he,card_bot] at hcA
    contradiction
  · have hh := fixedCodim_add_finrank ρ A
    rw [rank,hcA]
    norm_num
    change fixedCodim ρ A + Module.finrank (ZMod 2) (fixedSpace ρ A) = Module.finrank (ZMod 2) (Additive U) at hh
    omega

private theorem five_sylow_index (Q : Sylow 2 (alternatingGroup (Fin 5))) :
    (normalizer (Q : Set (alternatingGroup (Fin 5)))).index = 5 := by
  obtain ⟨i,hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer Q
  rw [hi]
  have hc : Nat.card (MulAction.stabilizer (alternatingGroup (Fin 5)) i) = 12 := by
    rw [Nat.card_eq_fintype_card]
    exact (by decide +kernel : ∀ j : Fin 5, Fintype.card (MulAction.stabilizer (alternatingGroup (Fin 5)) j) = 12) i
  have hh := (MulAction.stabilizer (alternatingGroup (Fin 5)) i).card_mul_index
  rw [hc,nat_card_alternatingGroup] at hh
  norm_num [Nat.factorial] at hh
  omega

private theorem five_seed_geometry (B : Subgroup (alternatingGroup (Fin 7)))
    (eB : B ≃* alternatingGroup (Fin 5)) (S : Sylow 2 (alternatingGroup (Fin 7)))
    (hSN : (S : Subgroup _) ≤ normalizer (B : Set (alternatingGroup (Fin 7))))
    (A : Subgroup (alternatingGroup (Fin 7))) (hAS : A ≤ S)
    (Q : Sylow 2 B) (hQ : (Q : Subgroup B).map B.subtype = A) :
    let J := B ⊔ (S : Subgroup _)
    let N := J ⊓ normalizer (A : Set (alternatingGroup (Fin 7)))
    N.relIndex J = 5 ∧ (S : Subgroup _) ≤ N ∧
      (∀ K : Subgroup (alternatingGroup (Fin 7)), (S : Subgroup _) ≤ K → K < J → K ≤ N) := by
  let J := B ⊔ (S : Subgroup _)
  let N := J ⊓ normalizer (A : Set (alternatingGroup (Fin 7)))
  have hAB : A ≤ B := hQ ▸ map_subtype_le (Q : Subgroup B)
  have hQA : A.subgroupOf B = (Q : Subgroup B) := by
    rw [← hQ]
    exact comap_map_eq_self_of_injective B.subtype_injective _
  have hAeq : B ⊓ (S : Subgroup _) = A := by
    have hle : (Q : Subgroup B) ≤ (S : Subgroup _).subgroupOf B := by
      rw [← hQA]
      exact comap_mono hAS
    have he := Q.is_maximal' S.isPGroup'.comap_subtype hle
    have hh := congrArg (Subgroup.map B.subtype) he
    change ((S : Subgroup _).subgroupOf B).map B.subtype = _ at hh
    rw [subgroupOf_map_subtype,hQ,inf_comm] at hh
    exact hh
  have hSA : (S : Subgroup _) ≤ normalizer (A : Set (alternatingGroup (Fin 7))) := by
    rw [← hAeq]
    exact (le_inf hSN S.toSubgroup.le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hSN' : (S : Subgroup _) ≤ N := le_inf le_sup_right hSA
  have huB : Order.HasUniqueMaximalOver (Q : Subgroup B) ⊤ := by
    apply hasUniqueMaximalOver_of_surjective eB.toMonoidHom eB.surjective
      (by rw [eB.toMonoidHom.ker_eq_bot eB.injective]; exact bot_le)
    exact Theory.SpecificGroups.Alternating.FiveSylowMaximal.sylow_unique
      (Q.mapSurjective (f := eB.toMonoidHom) eB.surjective)
  have hu : Order.HasUniqueMaximalOver (S : Subgroup _) J := by
    apply hasUniqueMaximalOver_sup_of_normalizes hSN
    rw [hAeq,← hQ]
    exact hasUniqueMaximalOver_map_subtype huB
  have hiB : (normalizer (A : Set (alternatingGroup (Fin 7)))).relIndex B = 5 := by
    change ((normalizer (A : Set (alternatingGroup (Fin 7)))).subgroupOf B).index = 5
    rw [subgroupOf_normalizer_eq hAB,hQA]
    have hh := five_sylow_index (Q.mapSurjective (f := eB.toMonoidHom) eB.surjective)
    change (normalizer ((Q : Subgroup B).map eB.toMonoidHom : Set (alternatingGroup (Fin 5)))).index = 5 at hh
    rw [← map_equiv_normalizer_eq (Q : Subgroup B) eB, index_map_of_bijective (f := eB.toMonoidHom) eB.bijective] at hh
    exact hh
  have hiNB : N.relIndex B = 5 := by
    change (J ⊓ normalizer (A : Set (alternatingGroup (Fin 7)))).relIndex B = 5
    rw [inf_comm,← relIndex_inf_mul_relIndex]
    have hBJ : B ≤ J := le_sup_left
    rw [inf_of_le_right hBJ,relIndex_eq_one.mpr hBJ,mul_one]
    exact hiB
  have hidx : N.relIndex J = 5 := by
    let B' := B.subgroupOf J
    let N' := N.subgroupOf J
    have hBJ : B ≤ J := le_sup_left
    have hNJ : N ≤ J := inf_le_left
    let : B'.Normal := (normal_subgroupOf_iff_le_normalizer hBJ).mpr (sup_le B.le_normalizer hSN)
    have hJgen : B ⊔ N = J := le_antisymm (sup_le le_sup_left inf_le_left)
      (sup_le le_sup_left (hSN'.trans le_sup_right))
    have hs : B' ⊔ N' = ⊤ := by
      apply (map_injective (f := J.subtype) J.subtype_injective)
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hBJ,map_subgroupOf_eq_of_le hNJ,
        hJgen,← MonoidHom.range_eq_map,range_subtype]
    have hi := relIndex_sup_left N' B'
    rw [hs,relIndex_top_right] at hi
    have ht := relIndex_mul_index (show N' ⊓ B' ≤ N' from inf_le_left)
    have hb := relIndex_mul_index (show N' ⊓ B' ≤ B' from inf_le_right)
    rw [inf_relIndex_right,relIndex_subgroupOf hBJ,hiNB] at hb
    rw [inf_relIndex_left,← hi] at ht
    have hp := Nat.pos_of_ne_zero B'.index_ne_zero_of_finite
    change N'.index = 5
    nlinarith
  exact ⟨hidx,hSN',by
    intro K hSK hK
    obtain ⟨W,hW,_⟩ := hu.2
    have hNW := hu.le_maximal hW hSN' (lt_of_le_of_ne inf_le_left (by
      intro he; rw [he,relIndex_self] at hidx; omega))
    have hwidx : W.relIndex J = 1 ∨ W.relIndex J = 5 := by
      apply (Nat.dvd_prime Nat.prime_five).mp
      rw [← hidx]
      exact relIndex_dvd_of_le_left J hNW
    have he : N = W := by
      rcases hwidx with he | he
      · exact (hW.2.ne (le_antisymm hW.2.le (relIndex_eq_one.mp he))).elim
      · apply eq_of_le_of_card_ge hNW
        have hN := (N.subgroupOf J).card_mul_index
        have hW' := (W.subgroupOf J).card_mul_index
        rw [Nat.card_congr (subgroupOfEquivOfLe (show N ≤ J from inf_le_left)).toEquiv] at hN
        rw [Nat.card_congr (subgroupOfEquivOfLe hW.2.le).toEquiv] at hW'
        change Nat.card N * N.relIndex J = Nat.card J at hN
        change Nat.card W * W.relIndex J = Nat.card J at hW'
        rw [hidx] at hN
        rw [he] at hW'
        omega
    change K ≤ N
    rw [he]
    exact hu.le_maximal hW hSK hK⟩

/-- The original preimage of the five-letter seed has a unique maximal
Sylow overgroup of index five. Its image is the normalizer of the original
layer's action, and it retains an actual A₅ subgroup in the quotient. -/
theorem four_five_seed_preimage
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hNL : normalizer (layer L R : Set G) ≤ normalizer (L : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    ∃ Y N : Subgroup G, (P : Subgroup G) ≤ N ∧ N ≤ Y ∧
      Y ≤ fourOvergroup (P : Subgroup G) L z ∧ N.relIndex Y = 5 ∧
      (∀ K : Subgroup G, (P : Subgroup G) ≤ K → K < Y → K ≤ N) ∧
      ∃ q : fourOvergroup (P : Subgroup G) L z →* alternatingGroup (Fin 7),
        Function.Surjective q ∧
        q.ker = (centralizer (sourceClosure (P : Subgroup G) L R z : Set G)).subgroupOf
          (fourOvergroup (P : Subgroup G) L z) ∧
        (N.subgroupOf (fourOvergroup (P : Subgroup G) L z)).map q ≤
          normalizer ((((layer L R).subgroupOf (fourOvergroup (P : Subgroup G) L z)).map q : Set (alternatingGroup (Fin 7)))) ∧
        ∃ B : Subgroup (alternatingGroup (Fin 7)), Nonempty (B ≃* alternatingGroup (Fin 5)) ∧
          (Y.subgroupOf (fourOvergroup (P : Subgroup G) L z)).map q =
            B ⊔ (((P : Subgroup G).subgroupOf (fourOvergroup (P : Subgroup G) L z)).map q) ∧
          (((P : Subgroup G).subgroupOf (fourOvergroup (P : Subgroup G) L z)).map q) ≤
            normalizer (B : Set (alternatingGroup (Fin 7))) ∧
          ∃ Q : Sylow 2 B, (Q : Subgroup B).map B.subtype =
            ((layer L R).subgroupOf (fourOvergroup (P : Subgroup G) L z)).map q := by
  let X := fourOvergroup (P : Subgroup G) L z
  let U := sourceClosure (P : Subgroup G) L R z
  let := four_closure_elementary h hnatural hz ho hP hplane hcard
  have hPX : (P : Subgroup G) ≤ X := hP.trans le_sup_right
  obtain ⟨q,hq,ρ,hf,hρ⟩ := four_marked_alternating_action h hnatural hz ho hP hplane hNL hcard
  have hker := marked_kernel q ρ hf hρ
  let S := (P.subtype hPX).mapSurjective hq
  let A := ((layer L R).subgroupOf X).map q
  have hAS : A ≤ S := map_mono (comap_mono h.layer_le_T)
  have hd : Module.finrank (ZMod 2) (Additive U) = 4 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive U)
    change Nat.card U = _ at hh
    rw [four_closure_card h hnatural hz ho hP hplane hcard,Nat.card_zmod] at hh
    exact hh.symm
  have hA := four_layer_best_in_alternating h hnatural hz ho hP hplane hcard q ρ hf hρ
  obtain ⟨B,⟨eB⟩,hSN,_hAB,⟨Q,hQ⟩,_⟩ :=
    Representation.AlternatingSevenFiveSeed.exists_five_seed ρ hf hd S A hAS hA
  obtain ⟨hi,hSN',hmax⟩ := five_seed_geometry B eB S hSN A hAS Q hQ
  let J := B ⊔ (S : Subgroup _)
  let C := J ⊓ normalizer (A : Set (alternatingGroup (Fin 7)))
  let Y := (J.comap q).map X.subtype
  let N := (C.comap q).map X.subtype
  have hYX : Y ≤ X := map_subtype_le _
  have hNY : N ≤ Y := map_mono (comap_mono inf_le_left)
  have hPN : (P : Subgroup G) ≤ N := by
    intro p hp
    exact ⟨⟨p,hPX hp⟩,hSN' (mem_map_of_mem q hp),rfl⟩
  have hYeq : Y.subgroupOf X = J.comap q := comap_map_eq_self_of_injective X.subtype_injective _
  have hNeq : N.subgroupOf X = C.comap q := comap_map_eq_self_of_injective X.subtype_injective _
  have hYmap : (Y.subgroupOf X).map q = J := by
    rw [hYeq,map_comap_eq_self_of_surjective hq]
  have hNmap : (N.subgroupOf X).map q = C := by
    rw [hNeq,map_comap_eq_self_of_surjective hq]
  have hidx : N.relIndex Y = 5 := by
    change ((C.comap q).map X.subtype).relIndex ((J.comap q).map X.subtype) = 5
    rw [relIndex_map_map_of_injective _ _ X.subtype_injective,
      relIndex_comap,map_comap_eq_self_of_surjective hq]
    exact hi
  have hkp : IsPGroup 2 q.ker := by
    rw [hker]
    exact (four_closure_centralizer_isPGroup h hnatural hz ho hP hplane hNL hcard).comap_subtype
  have hkP : q.ker ≤ (P : Subgroup G).subgroupOf X :=
    hkp.le_sylow_of_normal (P.subtype hPX)
  refine ⟨Y,N,hPN,hNY,hYX,hidx,?_,q,hq,hker,?_,B,⟨eB⟩,?_,hSN,Q,hQ⟩
  · intro K hPK hKY
    have hKX : K ≤ X := hKY.le.trans hYX
    let D := (K.subgroupOf X).map q
    have hSD : (S : Subgroup _) ≤ D := map_mono (comap_mono hPK)
    have hDJ : D ≤ J := by rw [← hYmap]; exact map_mono (comap_mono hKY.le)
    have hDne : D ≠ J := by
      intro he
      have hh := congrArg (Subgroup.comap q) he
      change ((K.subgroupOf X).map q).comap q = J.comap q at hh
      have heK : ((K.subgroupOf X).map q).comap q = K.subgroupOf X :=
        comap_map_eq_self (hkP.trans (comap_mono hPK))
      rw [heK] at hh
      have hm := congrArg (Subgroup.map X.subtype) hh
      rw [map_subgroupOf_eq_of_le hKX] at hm
      exact hKY.ne hm
    have hDC := hmax D hSD (lt_of_le_of_ne hDJ hDne)
    have hKN : K.subgroupOf X ≤ C.comap q := map_le_iff_le_comap.mp hDC
    rw [← map_subgroupOf_eq_of_le hKX]
    exact map_mono hKN
  · rw [hNmap]
    exact inf_le_right
  · exact hYmap

private theorem no_five_on_marked_plane {E : Type*} [Group E] [Finite E]
    (hE : Nat.card E = 16) (B : Subgroup (MulAut E)) (W : Subgroup E)
    (hW : Nat.card W = 4) (hBW : ∀ b ∈ B, ∀ x, x ∈ W ↔ b x ∈ W) :
    ¬ 5 ∣ Nat.card B := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro hd
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := B) 5 hd
  let A := zpowers b
  have hA : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hb]; decide)
  let : IsInvariant A E W := ⟨fun a x => hBW a.val.val a.val.property x⟩
  have hmW := hA.card_modEq_card_fixedPoints W
  change Nat.card W % 5 = Nat.card (FixedPoints.subgroup A W) % 5 at hmW
  have hleW := (FixedPoints.subgroup A W).card_le_card_group
  rw [hW] at hmW hleW
  have hcW : Nat.card (FixedPoints.subgroup A W) = 4 := by omega
  have htopW : FixedPoints.subgroup A W = ⊤ :=
    eq_top_of_card_eq _ (hcW.trans hW.symm)
  have hWF : W ≤ FixedPoints.subgroup A E := by
    intro x hx a
    have hh : (⟨x,hx⟩ : W) ∈ FixedPoints.subgroup A W := htopW ▸ mem_top _
    exact congrArg Subtype.val (hh a)
  have hlow : 4 ≤ Nat.card (FixedPoints.subgroup A E) := by
    rw [← hW]
    exact Nat.le_of_dvd Nat.card_pos (card_dvd_of_le hWF)
  have hm := hA.card_modEq_card_fixedPoints E
  change Nat.card E % 5 = Nat.card (FixedPoints.subgroup A E) % 5 at hm
  rw [hE] at hm
  have hdiv : Nat.card (FixedPoints.subgroup A E) ∣ 2 ^ 4 := by
    rw [show 2 ^ 4 = 16 by decide, ← hE]
    exact (FixedPoints.subgroup A E).card_subgroup_dvd_card
  obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  have hcard : Nat.card (FixedPoints.subgroup A E) = 16 := by
    interval_cases k <;> norm_num only [Nat.reducePow] at he <;> omega
  have htop : FixedPoints.subgroup A E = ⊤ := eq_top_of_card_eq _ (hcard.trans hE.symm)
  have hb1 : b = 1 := by
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    have hx : x ∈ FixedPoints.subgroup A E := htop ▸ mem_top x
    exact hx ⟨b, mem_zpowers b⟩
  rw [hb1, orderOf_one] at hb
  contradiction

private theorem normalizer_image_fixes_plane
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hNL : normalizer (layer L R : Set G) ≤ normalizer (L : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4)
    (q : fourOvergroup (P : Subgroup G) L z →* alternatingGroup (Fin 7))
    (hq : Function.Surjective q)
    (hk : q.ker = (centralizer (sourceClosure (P : Subgroup G) L R z : Set G)).subgroupOf
      (fourOvergroup (P : Subgroup G) L z))
    (N : Subgroup G) (hNX : N ≤ fourOvergroup (P : Subgroup G) L z)
    (hN : (N.subgroupOf (fourOvergroup (P : Subgroup G) L z)).map q ≤
      normalizer ((((layer L R).subgroupOf (fourOvergroup (P : Subgroup G) L z)).map q : Set (alternatingGroup (Fin 7))))) :
    N ≤ normalizer (ZS (P : Subgroup G) L R : Set G) := by
  let X := fourOvergroup (P : Subgroup G) L z
  let U := sourceClosure (P : Subgroup G) L R z
  let V := layer L R
  let D := V.subgroupOf X ⊔ q.ker
  have hVX : V ≤ X := (layer_le_involution_centralizer h hz).trans le_sup_right
  have hn : N.subgroupOf X ≤ normalizer (D : Set X) := by
    have ht := map_le_iff_le_comap.mp hN
    rw [comap_normalizer_eq_of_le_range (by rw [MonoidHom.range_eq_top.mpr hq]; exact le_top),
      comap_map_eq] at ht
    exact ht
  have hNn : N ≤ normalizer (D.map X.subtype : Set G) := by
    rw [← map_subgroupOf_eq_of_le hNX]
    exact (map_mono hn).trans (D.le_normalizer_map X.subtype)
  have hUD : U ⊓ centralizer (D.map X.subtype : Set G) = ZS (P : Subgroup G) L R := by
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hVX]
    have hK : q.ker.map X.subtype ≤ centralizer (U : Set G) := by
      rw [hk]
      rintro _ ⟨x,hx,rfl⟩
      exact hx
    rw [← four_closure_centralizer_layer h hnatural hz ho hP hplane hcard]
    change U ⊓ centralizer ((V ⊔ q.ker.map X.subtype : Subgroup G) : Set G) = U ⊓ centralizer (V : Set G)
    apply le_antisymm (inf_le_inf_left U (centralizer_le
      (show (V : Set G) ⊆ (V ⊔ q.ker.map X.subtype : Subgroup G) from fun _ hx => (show V ≤ V ⊔ q.ker.map X.subtype from le_sup_left) hx)))
    intro u hu
    refine ⟨hu.1,?_⟩
    apply mem_centralizer_iff.mpr
    intro d hd
    have hle : V ⊔ q.ker.map X.subtype ≤ centralizer ({u} : Set G) :=
      sup_le (fun v hv => mem_centralizer_singleton_iff.mpr (hu.2 v hv))
        (fun k hk => mem_centralizer_singleton_iff.mpr (hK hk u hu.1).symm)
    exact mem_centralizer_singleton_iff.mp (hle hd)
  rw [← hUD]
  exact (le_inf (hNX.trans (four_generated_overgroup_normalizes_closure h hnatural hz ho hP hplane hNL hcard))
    (hNn.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf

/-- The actual subgroup obtained from the original A₇ action is H-star,
with its unique Sylow overgroup equal to its index-five intersection with M. -/
theorem four_exists_hstar_index_five_seed
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hNL : normalizer (layer L R : Set G) ≤ normalizer (L : Set G))
    (hNM : normalizer (L : Set G) ≤ M)
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    ∃ Y : Subgroup G, Y ∈ Chapter3.HStar (P : Subgroup G) M ∧
      Y ≤ fourOvergroup (P : Subgroup G) L z ∧ (Y ⊓ M).relIndex Y = 5 ∧
      ∃ q : fourOvergroup (P : Subgroup G) L z →* alternatingGroup (Fin 7),
        Function.Surjective q ∧
        q.ker = (centralizer (sourceClosure (P : Subgroup G) L R z : Set G)).subgroupOf
          (fourOvergroup (P : Subgroup G) L z) ∧
        ∃ B : Subgroup (alternatingGroup (Fin 7)), Nonempty (B ≃* alternatingGroup (Fin 5)) ∧
          (Y.subgroupOf (fourOvergroup (P : Subgroup G) L z)).map q =
            B ⊔ (((P : Subgroup G).subgroupOf (fourOvergroup (P : Subgroup G) L z)).map q) ∧
          (((P : Subgroup G).subgroupOf (fourOvergroup (P : Subgroup G) L z)).map q) ≤
            normalizer (B : Set (alternatingGroup (Fin 7))) ∧
          ∃ Q : Sylow 2 B, (Q : Subgroup B).map B.subtype =
            ((layer L R).subgroupOf (fourOvergroup (P : Subgroup G) L z)).map q := by
  classical
  let X := fourOvergroup (P : Subgroup G) L z
  let U := sourceClosure (P : Subgroup G) L R z
  obtain ⟨Y,N,hPN,hNY,hYX,hi,hmax,q,hq,hk,hN,B,⟨eB⟩,hJ,hSN,Q,hQ⟩ :=
    four_five_seed_preimage h hnatural hz ho hP hplane hNL hcard
  have hPY : (P : Subgroup G) ≤ Y := hPN.trans hNY
  have hNM' : N ≤ M := (normalizer_image_fixes_plane h hnatural hz ho hP hplane hNL hcard
    q hq hk N (hNY.trans hYX) hN).trans (hplane.trans (hNL.trans hNM))
  have hYU : Y ≤ normalizer (U : Set G) := hYX.trans
    (four_generated_overgroup_normalizes_closure h hnatural hz ho hP hplane hNL hcard)
  have hSU : ZS (P : Subgroup G) L R ≤ U := (ZS_le_sourceClosure_intersection h hz).trans inf_le_left
  have hnot : ¬ Y ≤ M := by
    intro hYM
    let b : Y →* MulAut U := U.normalizerMonoidHom.comp (inclusion hYU)
    let c : Y →* alternatingGroup (Fin 7) := q.comp (inclusion hYX)
    have hker : b.ker = c.ker := by
      have hcKer : c.ker = (centralizer (U : Set G)).subgroupOf Y := by
        ext y
        change q (inclusion hYX y) = 1 ↔ (y : G) ∈ centralizer (U : Set G)
        rw [← MonoidHom.mem_ker,hk]
        rfl
      rw [hcKer]
      ext y
      change U.normalizerMonoidHom (inclusion hYU y) = 1 ↔ (y : G) ∈ centralizer (U : Set G)
      rw [← MonoidHom.mem_ker,normalizerMonoidHom_ker]
      rfl
    have hrange : c.range = (Y.subgroupOf X).map q := by
      ext a
      constructor
      · rintro ⟨y,rfl⟩
        exact ⟨inclusion hYX y,y.property,rfl⟩
      · rintro ⟨x,hx,rfl⟩
        exact ⟨⟨x,hx⟩,rfl⟩
    have h5 : 5 ∣ Nat.card b.range := by
      have hh := congrArg Subgroup.index hker
      rw [index_ker,index_ker,hrange] at hh
      rw [hh]
      have hcB : Nat.card B = 60 := by
        rw [Nat.card_congr eB.toEquiv,nat_card_alternatingGroup]
        norm_num [Nat.factorial]
      exact dvd_trans (hcB ▸ (by decide : 5 ∣ 60)) (card_dvd_of_le (show B ≤ (Y.subgroupOf X).map q from hJ.symm ▸ le_sup_left))
    let W := (ZS (P : Subgroup G) L R).subgroupOf U
    have hYW := (le_inf hYM hYX).trans
      (four_maximal_intersection_normalizes_plane h hnatural hz ho hP hplane hNL hcard)
    have hBW : ∀ a ∈ b.range, ∀ u : U, u ∈ W ↔ a u ∈ W := by
      rintro a ⟨y,rfl⟩ u
      exact mem_normalizer_iff.mp (hYW y.property) u.val
    exact no_five_on_marked_plane (four_closure_card h hnatural hz ho hP hplane hcard)
      b.range W ((Nat.card_congr (subgroupOfEquivOfLe hSU).toEquiv).trans
        (h.natural_ZS_geometry hnatural).2.1) hBW h5
  have hUY : U ≤ Y := by
    have hc := pCoreIn_le_sylow (Centralizer z) (P.subtype hP)
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hP] at hc
    exact ((local_closure_core h hnatural hz ho hP).1.trans hc).trans hPY
  have hYH : Y ∈ Chapter1.HOver G (P : Set G) := by
    refine ⟨?_,hPY⟩
    change Y.pCoreIn 2 ≠ ⊥
    have huc : U ≤ Y.pCoreIn 2 := le_pCoreIn_of_normalizes
      (by let := four_closure_elementary h hnatural hz ho hP hplane hcard
          exact IsElementaryAbelian.isPGroup 2 U) hUY hYU
    intro he
    have hzU := bot_unique (he ▸ huc)
    have hc := four_closure_card h hnatural hz ho hP hplane hcard
    change Nat.card U = 16 at hc
    rw [hzU,card_bot] at hc
    contradiction
  have hstar : Y ∈ Chapter3.HStar (P : Subgroup G) M := by
    refine ⟨⟨hYH,hnot⟩,?_⟩
    intro K hK hKY
    by_contra hn
    exact hK.2 ((hmax K hK.1.2 (lt_iff_le_not_ge.mpr ⟨hKY,hn⟩)).trans hNM')
  have hmeet : Y ⊓ M = N := by
    apply le_antisymm _ (le_inf hNY hNM')
    apply hmax _ (le_inf hPY h.sylow_le)
    exact lt_of_le_of_ne inf_le_left (by intro he; exact hnot (he.symm ▸ inf_le_right))
  exact ⟨Y,hstar,hYX,(by rw [hmeet]; exact hi),q,hq,hk,B,⟨eB⟩,hJ,hSN,Q,hQ⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction
