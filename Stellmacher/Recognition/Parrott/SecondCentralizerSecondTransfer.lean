module

public import Stellmacher.Recognition.Parrott.SecondCentralizerWeakClosure
public import Stellmacher.Recognition.Parrott.SecondCentralizerTransferSetup
public import Stellmacher.Recognition.Parrott.SecondCentralizerNormalizerCharacter
public import Stellmacher.Recognition.Parrott.SecondCentralizerTransferKernelGeometry
public import Theory.GroupTheory.WeakCenterTransfer
public import Mathlib.Data.ZMod.Basic

/-!
# The second transfer in the second involution centralizer

Write N=N_G(F), K=O₂(N), W=Ω₁(K), and C=C_G(v). The compatible
cyclic root b belongs to W. The first transfer supplies M of index two
in C, with Sylow image W. Weak closure of Z(W) then permits transfer of
a binary character of its normalizer in M. A character detecting b gives
L of index two in M, excluding b, with Sylow image Y=W∩L of order 128.

The local normalizer character and the invariant-subgroup geometry discharge
the inputs to the final existence theorem. It retains the supplied fixed
involution, the compatible cyclic root, and all actual Sylow embeddings,
independently of ambient containment.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§4, pp.682–683. The source's U and X are our W and L respectively.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The second transfer, with only its local normalizer character supplied.
The output retains the concrete ambient intersection and actual Sylow subgroup. -/
public theorem second_transfer_of_normalizer_character
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v)
    (hCD : let N := normalizer (d.F : Set G)
      let X := (pCore 2 N).map N.subtype
      let D := (commutator X).map X.subtype
      let A := (Q : Subgroup N).map N.subtype
      X ⊓ centralizer (A : Set G) ≤ D) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let i := N.subtype.comp K.subtype
    let W := U.map i
    let ZW := (center U).map (i.comp U.subtype)
    let C := centralizer ({v} : Set G)
    let P := (d.sylow : Subgroup G) ⊓ C
    ∀ (M : Subgroup C), M.Normal → M.map C.subtype ⊓ P = W →
    ∀ (R : Sylow 2 M), (R : Subgroup M).map (C.subtype.comp M.subtype) = W →
    ∀ b ∈ W,
      let j := C.subtype.comp M.subtype
      let ZM := ZW.comap j
      (∃ φ : normalizer (ZM : Set M) →* Multiplicative (ZMod 2),
        ∀ x : normalizer (ZM : Set M), j x = b → φ x ≠ 1) →
      ∃ L : Subgroup M, L.Normal ∧ L.index = 2 ∧ b ∉ L.map j ∧
        Nat.card (W ⊓ L.map j : Subgroup G) = 128 ∧
        ∃ S : Sylow 2 L, (S : Subgroup L).map (j.comp L.subtype) = W ⊓ L.map j := by
  intro N K U i W ZW C P M hMn hinter R hR b hb j ZM hchar
  have hj : Function.Injective j := C.subtype_injective.comp M.subtype_injective
  have hWrange : W ≤ j.range := by
    rw [MonoidHom.range_comp, range_subtype, ← hinter]
    exact inf_le_left
  have hB : (R : Subgroup M) = W.comap j := by
    apply map_injective hj
    rw [hR, map_comap_eq_self hWrange]
  have hZR : (center R).map (R : Subgroup M).subtype = ZM := by
    rw [hB]
    exact (d.first_transfer_omega_center_images v M hinter).2.2.2
  have hZS : ZM ≤ (R : Subgroup M) := by
    rw [← hZR]
    exact map_subtype_le _
  have hRC : (R : Subgroup M) ≤ centralizer (ZM : Set M) := by
    intro x hx t ht
    rw [← hZR] at ht
    obtain ⟨tR, htR, rfl⟩ := ht
    exact (congrArg (R : Subgroup M).subtype (mem_center_iff.mp htR ⟨x, hx⟩)).symm
  have hweak : ∀ m : M, ZM.map (MulAut.conj m).toMonoidHom ≤ (R : Subgroup M) →
      ZM.map (MulAut.conj m).toMonoidHom = ZM := by
    rw [hB]
    exact (d.first_transfer_omega_center_weakly_closed h hN hproper Q v hv hfix
      hCD M hMn hinter).2
  obtain ⟨φ, hφ⟩ := hchar
  obtain ⟨bM, hbR, heb⟩ := hR.symm ▸ hb
  let bR : R := ⟨bM, hbR⟩
  obtain ⟨L, hLn, hLi, hbL, hrest⟩ :=
    R.exists_normal_index_two_of_weakly_closed_normalizer ZM hZS hRC hweak φ
      (by simp) bR (hφ _ heb)
  let := hLn
  have hbLG : b ∉ L.map j := by
    rintro ⟨x, hx, he⟩
    have hexb : x = bM := hj (he.trans heb.symm)
    exact hbL (hexb ▸ hx : bM ∈ L)
  have hnot : ¬ (R : Subgroup M) ≤ L := fun hh => hbL (hh hbR)
  obtain ⟨hcard, S, hS⟩ := R.image_inf_normal_index_two j hj L hLi hnot
  rw [hR] at hcard hS
  have hWcard : Nat.card W = 256 :=
    (card_map_of_injective (f := i) (N.subtype_injective.comp K.subtype_injective)).trans
      (d.normalizer_core_omega_structure h hN hproper).1
  rw [hWcard] at hcard
  exact ⟨L, hLn, hLi, hbLG, by omega, S, hS⟩

/-- Complete assembly of the requested second-transfer interface from the two
local inputs: a normalizer character detecting the compatible root, and the
omega/center geometry of its invariant index-two Sylow intersection. -/
public theorem second_centralizer_second_transfer_of_local_inputs
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let X0 := K.map N.subtype
    let D := (commutator X0).map X0.subtype
    let A := (Q : Subgroup N).map N.subtype
    X0 ⊓ centralizer (A : Set G) ≤ D →
    ∀ v : G, orderOf v = 2 → d.F ⊓ centralizer (A : Set G) = zpowers v →
    let U := omega₁ K (p := 2)
    let W := U.map (N.subtype.comp K.subtype)
    let ZW := (center U).map ((N.subtype.comp K.subtype).comp U.subtype)
    let C := centralizer ({v} : Set G)
    let P := (d.sylow : Subgroup G) ⊓ C
    (∀ M : Subgroup C, M.Normal → M.index = 2 → M.map C.subtype ⊓ P = W →
      ∀ b ∈ X0, orderOf b = 4 → b ^ 2 = v →
        X0 ⊓ centralizer (A : Set G) = zpowers b →
        let j := C.subtype.comp M.subtype
        let ZM := ZW.comap j
        ∃ φ : normalizer (ZM : Set M) →* Multiplicative (ZMod 2),
          ∀ x : normalizer (ZM : Set M), j x = b → φ x ≠ 1) →
    (∀ b ∈ X0, orderOf b = 4 → b ^ 2 = v →
      X0 ⊓ centralizer (A : Set G) = zpowers b →
      ∀ Y : Subgroup G, Y ≤ W → Nat.card Y = 128 →
        A ≤ normalizer (Y : Set G) → b ∉ Y →
        (omega₁ Y (p := 2)).map Y.subtype = d.F ∧
        (center Y).map Y.subtype = ZW) →
    ∃ (M : Subgroup C) (L : Subgroup M) (b : G),
      M.Normal ∧ M.index = 2 ∧ M.map C.subtype ⊓ P = W ∧
      L.Normal ∧ L.index = 2 ∧
      let LG := L.map (C.subtype.comp M.subtype)
      let Y := W ⊓ LG
      b ∈ X0 ∧ orderOf b = 4 ∧ b ^ 2 = v ∧
      X0 ⊓ centralizer (A : Set G) = zpowers b ∧ b ∉ LG ∧
      Nat.card Y = 128 ∧ (omega₁ Y (p := 2)).map Y.subtype = d.F ∧
      (center Y).map Y.subtype = ZW ∧
      ∃ S : Sylow 2 L,
        (S : Subgroup L).map (C.subtype.comp (M.subtype.comp L.subtype)) = Y := by
  intro N K X0 D A hCD v hv hfix U W ZW C P hchar hgeometry
  obtain ⟨b, hbX, hb4, hb2, hbgen⟩ :=
    d.exists_normalizer_three_cyclic_generator_of_local_data h hN hproper Q hCD v hv hfix
  have hbW : b ∈ W := d.normalizer_fixed_root_mem_omega h hN hproper Q v hv hfix b hbX hb2
  obtain ⟨M, hMn, hMi, hinter, R, hR⟩ :=
    d.second_centralizer_index_two h hN hproper Q hCD v hv hfix
  obtain ⟨L, hLn, hLi, hbL, hYcard, S, hS⟩ :=
    d.second_transfer_of_normalizer_character h hN hproper Q v hv hfix hCD
      M hMn hinter R hR b hbW (hchar M hMn hMi hinter b hbX hb4 hb2 hbgen)
  have hAY := d.second_transfer_intersection_three_normalized h hN hproper Q v hfix
    M hMn hMi L hLn
  obtain ⟨hYo, hYz⟩ := hgeometry b hbX hb4 hb2 hbgen
    (W ⊓ L.map (C.subtype.comp M.subtype)) inf_le_left hYcard hAY
    (fun hh => hbL hh.2)
  exact ⟨M, L, b, hMn, hMi, hinter, hLn, hLi,
    hbX, hb4, hb2, hbgen, hbL, hYcard, hYo, hYz, S, hS⟩

/-- The second transfer in C_G(v): nested normal index-two subgroups with
an order-128 Sylow image, omega F, and center Z(W). The excluded order-four
root is compatible with the supplied fixed involution and Sylow three subgroup. -/
public theorem second_centralizer_second_transfer
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let X0 := K.map N.subtype
    let D := (commutator X0).map X0.subtype
    let A := (Q : Subgroup N).map N.subtype
    X0 ⊓ centralizer (A : Set G) ≤ D →
    ∀ v : G, orderOf v = 2 → d.F ⊓ centralizer (A : Set G) = zpowers v →
    let U := omega₁ K (p := 2)
    let W := U.map (N.subtype.comp K.subtype)
    let ZW := (center U).map ((N.subtype.comp K.subtype).comp U.subtype)
    let C := centralizer ({v} : Set G)
    let P := (d.sylow : Subgroup G) ⊓ C
    ∃ (M : Subgroup C) (L : Subgroup M) (b : G),
      M.Normal ∧ M.index = 2 ∧ M.map C.subtype ⊓ P = W ∧
      L.Normal ∧ L.index = 2 ∧
      let LG := L.map (C.subtype.comp M.subtype)
      let Y := W ⊓ LG
      b ∈ X0 ∧ orderOf b = 4 ∧ b ^ 2 = v ∧
      X0 ⊓ centralizer (A : Set G) = zpowers b ∧ b ∉ LG ∧
      Nat.card Y = 128 ∧ (omega₁ Y (p := 2)).map Y.subtype = d.F ∧
      (center Y).map Y.subtype = ZW ∧
      ∃ S : Sylow 2 L,
        (S : Subgroup L).map (C.subtype.comp (M.subtype.comp L.subtype)) = Y := by
  intro N K X0 D A hCD v hv hfix
  exact d.second_centralizer_second_transfer_of_local_inputs h hN hproper Q hCD v hv hfix
    (d.second_centralizer_normalizer_character h hN hproper Q hCD v hv hfix)
    (d.second_transfer_invariant_subgroup_geometry h hN hproper Q hCD v hv hfix)

end Stellmacher.Recognition.ParrottSecondElementaryData
