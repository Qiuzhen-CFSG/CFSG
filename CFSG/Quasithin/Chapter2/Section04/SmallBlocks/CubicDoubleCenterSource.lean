module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.CubicGlobalSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.SourceRecognition
public import Theory.SpecificGroups.CyclicTwoSymmetricFourSylow
public import Theory.SpecificGroups.CyclicTwoDihedralFourAlignment
public import Theory.SpecificGroups.CyclicTwoDihedralFourExtension
public import Theory.SpecificGroups.AffineEight.SimpleSylowExclusion
public import Theory.GroupTheory.SymmetricFourModelCoreData

/-!
# Excluding the double-center model in the original single cubic branch

For the actual minimal block setup, the C.6 alternative puts the selected
C₂ × D₈ Sylow subgroup at index two in the ambient Sylow group when
H ≅ C₂ × S₄. Source 2.4.4, applied to the central involution line and to
O₂(H), identifies its involution centralizer and elementary-eight
normalizer. Aligning these two subgroups with the standard coordinates
allows the proved index-two extension theorem to identify the ambient
Sylow group with the affine group of the cyclic group of order eight.
Its transfer obstruction contradicts nonabelian simplicity.

The final theorem applies the complete small-Sylow recognition result to
the remaining S₄ alternative. All subgroups and maps are those of the
original setup; no assumption identifying the core with the chosen block
is needed.

Source: Aschbacher–Smith, 2.4.26, printed p.543, using 2.4.4 and C.6.1.
The two-transfer exclusion on p.543 is replaced by the already proved
intrinsic affine-eight Sylow transfer obstruction.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
private abbrev C2D8 := Multiplicative (ZMod 2) × DihedralGroup 4
private abbrev C2S4 := Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)
private abbrev c : C2D8 := (Multiplicative.ofAdd 1, 1)
private abbrev b : C2D8 := (1, DihedralGroup.sr 0)

omit [Finite G] in
private theorem c2s4_card (e : G ≃* C2S4) : Nat.card G = 48 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_prod]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

private theorem affine_of_original_cubic_index
    (d : MinimalBlockSetup M) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex (T : Subgroup G) = 2)
    (eH : d.H ≃* C2S4) : Nonempty (T ≃* AffineEight.Model) := by
  classical
  let aH : d.H := eH.symm (Multiplicative.ofAdd 1, 1)
  have haHcenter : aH ∈ center d.H := by
    apply mem_center_iff.mpr
    intro x
    apply eH.injective
    simp only [map_mul, aH, eH.apply_symm_apply]
    exact Prod.ext (mul_comm _ _) (by simp)
  have haHns (x : d.H) : x ^ 2 ≠ aH := by
    intro hx
    have he := congrArg (fun y : C2S4 => y.1) (congrArg eH hx)
    simp only [map_pow, aH, eH.apply_symm_apply] at he
    have hz : ∀ z : Multiplicative (ZMod 2), z ^ 2 ≠ Multiplicative.ofAdd 1 := by decide
    exact hz _ he
  have haHorder : orderOf aH = 2 := by
    rw [← eH.orderOf_eq aH]
    change orderOf (eH (eH.symm (Multiplicative.ofAdd 1, 1))) = 2
    rw [eH.apply_symm_apply]
    exact orderOf_eq_prime (by decide) (by decide)
  let W : Subgroup d.H := zpowers aH
  let : W.Normal := by
    constructor
    intro g hg x
    have hc := mem_center_iff.mp ((zpowers_le.mpr haHcenter) hg) x
    rw [hc, mul_inv_cancel_right]
    exact hg
  have hW2 : IsPGroup 2 W := IsPGroup.of_card (n := 1) (by
    simpa only [W, Nat.card_zpowers, pow_one] using haHorder)
  have hWS : W ≤ (d.S : Subgroup d.H) := hW2.le_sylow_of_normal d.S
  have haS : aH ∈ (d.S : Subgroup d.H) := hWS (mem_zpowers aH)
  let aS : d.S := ⟨aH, haS⟩
  have hWne : W.map d.H.subtype ≠ ⊥ := by
    intro he
    have hm : (aH : G) ∈ W.map d.H.subtype := mem_map_of_mem _ (mem_zpowers aH)
    rw [he, mem_bot] at hm
    have ha : aH = 1 := Subtype.ext hm
    simp [ha] at haHorder
  have hWN : ((W.map d.H.subtype).subgroupOf d.H).Normal := by
    rw [subgroupOf, comap_map_eq_self_of_injective d.H.subtype_injective]
    infer_instance
  have hbarrierW := lemma_2_4_4 d.mem_gammaEvenZero.1 d.full_pair d.S le_rfl T hST
    (W.map d.H.subtype) hWne (map_mono hWS) hWN
  let j : d.S →* T := (d.H.subtype.comp (d.S : Subgroup d.H).subtype).codRestrict _
    (fun x => hST (mem_map_of_mem d.H.subtype x.property))
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : T => (z : G)) h
  have hjG : (T : Subgroup G).subtype.comp j =
      d.H.subtype.comp (d.S : Subgroup d.H).subtype := rfl
  have hjrange : j.range = ((d.S : Subgroup d.H).map d.H.subtype).subgroupOf
      (T : Subgroup G) := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact mem_map_of_mem _ y.property
    · rintro ⟨y,hy,he⟩
      exact ⟨⟨y,hy⟩, Subtype.ext he⟩
  have hjC : centralizer ({j aS} : Set T) = j.range := by
    apply le_antisymm
    · intro x hx
      rw [hjrange]
      change (x : G) ∈ (d.S : Subgroup d.H).map d.H.subtype
      rw [← hbarrierW]
      refine ⟨x.property, ?_⟩
      apply Subgroup.centralizer_le_normalizer
      change (x : G) ∈ centralizer ((zpowers aH).map d.H.subtype : Set G)
      rw [MonoidHom.map_zpowers, zpowers_eq_closure, centralizer_closure,
        mem_centralizer_singleton_iff]
      exact congrArg (fun z : T => (z : G)) (mem_centralizer_singleton_iff.mp hx)
    · rintro x ⟨y,rfl⟩
      rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      apply congrArg j
      exact Subtype.ext (mem_center_iff.mp haHcenter y.val)
  have hcoreS : pCore 2 d.H ≤ (d.S : Subgroup d.H) := pCore_isPGroup.le_sylow_of_normal d.S
  obtain ⟨hcoreE,hcorecard⟩ := symmetric_four_model_twoCore_data (Or.inr ⟨eH⟩)
  have hHcard := c2s4_card eH
  have hc8 : Nat.card (pCore 2 d.H) = 8 := by rcases hcorecard with h | h <;> omega
  let D : Subgroup d.S := (pCore 2 d.H).subgroupOf (d.S : Subgroup d.H)
  let : IsElementaryAbelian 2 (pCore 2 d.H) := hcoreE
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.subgroupOf hcoreS
  have hDcard : Nat.card D = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hcoreS).toEquiv).trans hc8
  obtain ⟨eS⟩ := CyclicTwoSymmetricFour.sylow_two_equiv ⟨eH⟩ d.S
  let E := D.map eS.toMonoidHom
  have hE : IsElementaryAbelian 2 E := IsElementaryAbelian.map eS.toMonoidHom
  have hEcard : Nat.card E = 8 := (card_map_of_injective eS.injective).trans hDcard
  have haSC : aS ∈ center d.S := by
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (mem_center_iff.mp haHcenter x.val)
  have htmod : eS aS ∈ center C2D8 := (centerCongr eS ⟨aS,haSC⟩).property
  have htns (x : C2D8) : x ^ 2 ≠ eS aS := by
    intro h
    apply haHns (eS.symm x).val
    have hh : (eS.symm x) ^ 2 = aS := by
      apply eS.injective
      simpa only [map_pow, eS.apply_symm_apply] using h
    exact congrArg (fun z : d.S => (z : d.H)) hh
  obtain ⟨u,huc,huE⟩ := CyclicTwoDihedralFour.exists_alignment E hE hEcard (eS aS) htmod htns
  let k : C2D8 ≃* d.S := u.trans eS.symm
  have hkc : k c = aS := by
    change eS.symm (u c) = aS
    rw [huc,eS.symm_apply_apply]
  have hkD : (centralizer ({b} : Set C2D8)).map k.toMonoidHom = D := by
    change (centralizer ({b} : Set C2D8)).map (eS.symm.toMonoidHom.comp u.toMonoidHom) = D
    rw [← map_map, huE]
    change (D.map eS.toMonoidHom).map eS.symm.toMonoidHom = D
    rw [map_map]
    have hid : eS.symm.toMonoidHom.comp eS.toMonoidHom = MonoidHom.id d.S := by ext x; simp
    rw [hid,map_id]
  let i := j.comp k.toMonoidHom
  have hi : Function.Injective i := hj.comp k.injective
  have hirange : i.range = j.range := by
    apply le_antisymm
    · rintro x ⟨y,rfl⟩
      exact ⟨k y,rfl⟩
    · rintro x ⟨y,rfl⟩
      exact ⟨k.symm y,congrArg j (k.apply_symm_apply y)⟩
  have hic : i c = j aS := by change j (k c) = j aS; rw [hkc]
  let A := (centralizer ({b} : Set C2D8)).map i
  have hA : A = D.map j := by
    change (centralizer ({b} : Set C2D8)).map (j.comp k.toMonoidHom) = _
    rw [← map_map,hkD]
  have hAG : A.map (T : Subgroup G).subtype = twoCore d.H := by
    rw [hA,map_map,hjG,← map_map,map_subgroupOf_eq_of_le hcoreS]
    rfl
  have hQne : twoCore d.H ≠ ⊥ := by
    intro he
    have hc := card_map_of_injective (K := pCore 2 d.H) d.H.subtype_injective
    change Nat.card (twoCore d.H) = Nat.card (pCore 2 d.H) at hc
    rw [he,Subgroup.card_bot,hc8] at hc
    omega
  have hQN : ((twoCore d.H).subgroupOf d.H).Normal := by
    change (((pCore 2 d.H).map d.H.subtype).comap d.H.subtype).Normal
    rw [comap_map_eq_self_of_injective d.H.subtype_injective]
    infer_instance
  have hbarrierQ := lemma_2_4_4 d.mem_gammaEvenZero.1 d.full_pair d.S le_rfl T hST
    (twoCore d.H) hQne (map_mono hcoreS) hQN
  have hNinternal : normalizer (A : Set T) = i.range := by
    have hN := subgroupOf_normalizer_eq (map_subtype_le A)
    have hback : (A.map (T : Subgroup G).subtype).subgroupOf (T : Subgroup G) = A :=
      comap_map_eq_self_of_injective (T : Subgroup G).subtype_injective A
    rw [hback,hAG] at hN
    rw [← hN,hirange,hjrange,← hbarrierQ,inf_subgroupOf_left]
  have hiindex : i.range.index = 2 := by rw [hirange,hjrange]; exact hindex
  obtain ⟨e,_⟩ := CyclicTwoDihedralFour.exists_mulEquiv_affineEight i hi hiindex
    (by rw [hic,hjC,hirange]) hNinternal
  exact ⟨e⟩

/-- The original single cubic setup excludes the C₂ × S₄ alternative of C.6.1. -/
theorem MinimalBlockSetup.single_cubic_double_center_false
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hK : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 3)
    (eH : d.H ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) : False := by
  have hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex (T : Subgroup G) = 2 := by
    rcases (d.single_cubic_global_source hG T hST hsingle hK).2.2.2.2.2 with h | h
    · exact h.1
    · obtain ⟨e⟩ := h.1
      have hc : Nat.card d.H = 24 := by
        rw [Nat.card_congr e.toEquiv]
        norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
      have hc48 := c2s4_card eH
      omega
  obtain ⟨e⟩ := affine_of_original_cubic_index d T hST.le hindex eH
  let : IsSimpleGroup G := hG.simple
  have hbot : _root_.commutator G = ⊥ :=
    (inferInstance : (_root_.commutator G).Normal).eq_bot_or_eq_top.resolve_right
      (AffineEight.not_perfect_of_sylow_equiv T e)
  exact hG.nonabelian ((commutator_eq_bot_iff G).mp hbot)

/-- The entire original single A₃ branch of 2.4.26, with both C.6 alternatives discharged. -/
theorem MinimalBlockSetup.single_cubic_classification
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hK : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 3)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty) : IsTheorem241Model G := by
  rcases (d.single_cubic_global_source hG T hST hsingle hK).2.2.2.2.2 with h | h
  · obtain ⟨e⟩ := h.2.2
    exact (d.single_cubic_double_center_false hG T hST hsingle hK e).elim
  · exact SmallBlocks.source_small_sylow_recognition_complete hG T M hM hu hdelta h.2
end CFSG.Quasithin.Chapter2
