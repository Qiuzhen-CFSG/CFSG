module

public import Stellmacher.Recognition.Parrott.SecondCentralizerFirstTransfer
public import Stellmacher.Recognition.Parrott.OmegaInvolutionCentralizerDerived
public import Theory.GroupTheory.CenterWeakClosureByDerivedLines

/-!
# The omega-center weak-closure argument for the second transfer

Write N=N_G(F), K=O₂(N), W=Ω₁(K), C=C_G(v), and P=T∩C.
For any normal subgroup M of C with M∩P=W, every nonidentity element
of Z(K) has centralizer W in M. The supplied Sylow three-subgroup acts
transitively on these three elements; it fixes v, normalizes W and M,
and transports the known equality C_M(z)=W.

The remaining local input is stated explicitly: for each noncentral
involution l of W, the derived group of C_W(l) is an involution line
in Z(K). The general normalizer argument then proves weak closure of
Z(W) in W with respect to M. Both ambient subgroup images and the
corresponding subgroups of M are exported, preserving the supplied v.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§4, Lemma 8, p.682, between the first and second transfers.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The supplied three-group is transitive on the nonidentity core-center elements. -/
public theorem normalizer_three_core_center_fusion
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let Z := (center K).map (N.subtype.comp K.subtype)
    let A := (Q : Subgroup N).map N.subtype
    ∀ u ∈ Z, u ≠ 1 → ∃ a : A, (a : G) * z * (a : G)⁻¹ = u := by
  intro N K Z A
  have hAN : A ≤ N := map_subtype_le _
  let _ := conjMulDistribMulActionOfLeNormalizer A Z
    (hAN.trans d.normalizer_core_centers_normalized.1)
  let zZ : Z := ⟨z, d.z_mem_normalizer_core_center⟩
  have hz1 : zZ ≠ 1 := by
    intro he
    have hh := congrArg Z.subtype he
    have ho := h.involution
    change z = 1 at hh
    simp [hh] at ho
  have hAcard : Nat.card A = 3 :=
    (card_map_of_injective N.subtype_injective).trans (d.normalizer_three_card h hN hproper Q)
  have hdis : A ⊓ (d.sylow : Subgroup G) = ⊥ :=
    (disjoint_of_coprime_natCard (by rw [hAcard, d.sylow_card h]; decide)).eq_bot
  have hstab : MulAction.stabilizer A zZ = ⊥ := by
    apply bot_unique
    intro a ha
    have haC : (a : G) ∈ centralizer ({z} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp (congrArg Z.subtype ha))
    have haT : (a : G) ∈ (d.sylow : Subgroup G) :=
      d.normalizer_inf_centralizer h ▸ ⟨hAN a.property, haC⟩
    have ha1 : (a : G) ∈ (⊥ : Subgroup G) := hdis ▸ ⟨a.property, haT⟩
    exact Subtype.ext ha1
  have hcount : Nat.card (MulAction.orbit A zZ) *
      Nat.card (MulAction.stabilizer A zZ) = Nat.card A := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup A zZ)
  rw [hstab, card_bot, mul_one, hAcard] at hcount
  have hsub : MulAction.orbit A zZ ⊆ ({1} : Set Z)ᶜ := by
    rintro y ⟨a, rfl⟩ he
    exact hz1 ((MulDistribMulAction.toMulAut A Z a).injective
      (he.trans (map_one _).symm))
  have hZcard : Nat.card Z = 4 :=
    (card_map_of_injective (K := center K) (f := N.subtype.comp K.subtype)
      (N.subtype_injective.comp K.subtype_injective)).trans
      (d.normalizer_core_order h hN hproper).2.2.2
  have horbit : MulAction.orbit A zZ = ({1} : Set Z)ᶜ := by
    apply Set.eq_of_subset_of_ncard_le hsub
    rw [Set.ncard_compl, Set.ncard_singleton, hZcard]
    change 4 - 1 ≤ Nat.card (MulAction.orbit A zZ)
    omega
  intro u hu hu1
  have huO : (⟨u, hu⟩ : Z) ∈ MulAction.orbit A zZ := by
    rw [horbit]
    exact fun he => hu1 (congrArg Z.subtype he)
  obtain ⟨a, ha⟩ := huO
  exact ⟨a, congrArg Z.subtype ha⟩

/-- Every nonidentity core-center involution has centralizer W in the first transfer kernel. -/
public theorem first_transfer_core_center_centralizer
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let W := U.map (N.subtype.comp K.subtype)
    let ZK := (center K).map (N.subtype.comp K.subtype)
    let C := centralizer ({v} : Set G)
    let P := (d.sylow : Subgroup G) ⊓ C
    ∀ M : Subgroup C, M.Normal → M.map C.subtype ⊓ P = W →
      ∀ u ∈ ZK, u ≠ 1 → M.map C.subtype ⊓ centralizer ({u} : Set G) = W := by
  intro N K U W ZK C P M hMn hinter
  let := hMn
  let MG := M.map C.subtype
  have hWM : W ≤ MG := by rw [← hinter]; exact inf_le_left
  have hHC : centralizer ({z} : Set G) ⊓ C = P := by
    symm
    apply eq_of_le_of_card_ge (inf_le_inf_right _ d.sylow_le_centralizer)
    rw [d.normalizer_fixed_sylow_card h hN hproper Q v hv hfix,
      d.supplied_fixed_original_centralizer_card h hN hproper Q v hv hfix]
  have hMz : MG ⊓ centralizer ({z} : Set G) = W := by
    rw [← hinter]
    change MG ⊓ _ = MG ⊓ P
    rw [← hHC]
    ext x
    exact ⟨fun hx => ⟨hx.1, hx.2, map_subtype_le M hx.1⟩,
      fun hx => ⟨hx.1, hx.2.1⟩⟩
  have hNW : N ≤ normalizer (W : Set G) := by
    let B := U.map K.subtype
    let : U.Characteristic := omega₁_characteristic K
    let : B.Normal := ConjAct.normal_of_characteristic_of_normal
    have hh := le_normalizer_map (H := B) N.subtype
    rw [normalizer_eq_top] at hh
    simpa only [← MonoidHom.range_eq_map, range_subtype, B, W, map_map] using hh
  have hCM : C ≤ normalizer (MG : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      M.le_normalizer_map C.subtype
  let A := (Q : Subgroup N).map N.subtype
  have hAC : A ≤ C := by
    have hvC : v ∈ centralizer (A : Set G) := (hfix.symm ▸ mem_zpowers v).2
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (hvC a ha)
  intro u hu hu1
  obtain ⟨a, ha⟩ := d.normalizer_three_core_center_fusion h hN hproper Q u hu hu1
  have haN : (a : G) ∈ N := map_subtype_le _ a.property
  have haM : (a : G) ∈ normalizer (MG : Set G) := hCM (hAC a.property)
  let f := MulAut.conj (a : G)
  have hfz : f z = u := ha
  apply le_antisymm
  · intro x hx
    have hyM : f.symm x ∈ MG :=
      (mem_normalizer_iff.mp haM (f.symm x)).mpr (by
        change f (f.symm x) ∈ MG
        rw [f.apply_symm_apply]
        exact hx.1)
    have hyz : f.symm x ∈ centralizer ({z} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      apply f.injective
      simpa only [map_mul, f.apply_symm_apply, hfz] using
        mem_centralizer_singleton_iff.mp hx.2
    have hyW : f.symm x ∈ W := hMz ▸ ⟨hyM, hyz⟩
    have hh := (mem_normalizer_iff.mp (hNW haN) (f.symm x)).mp hyW
    change f (f.symm x) ∈ W at hh
    rwa [f.apply_symm_apply] at hh
  · intro x hx
    refine ⟨hWM hx, ?_⟩
    have huZ := d.normalizer_core_omega_inclusions.2.1 hu
    obtain ⟨uU, huU, heu⟩ := huZ
    obtain ⟨xK, hxK, rfl⟩ := hx
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg ((N.subtype.comp K.subtype).comp U.subtype)
      (mem_center_iff.mp huU ⟨xK, hxK⟩)
    change (N.subtype.comp K.subtype) xK *
      ((N.subtype.comp K.subtype).comp U.subtype) uU =
      ((N.subtype.comp K.subtype).comp U.subtype) uU * (N.subtype.comp K.subtype) xK at hh
    rwa [heu] at hh
end Stellmacher.Recognition.ParrottSecondElementaryData

namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Ambient and internal weak-closure interfaces, conditional only on the local derived lines. -/
public theorem first_transfer_omega_center_weakly_closed_of_derived_lines
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let i := N.subtype.comp K.subtype
    let W := U.map i
    let ZK := (center K).map i
    let ZW := (center U).map (i.comp U.subtype)
    (∀ l ∈ W, orderOf l = 2 → l ∉ ZW →
      let B := W ⊓ centralizer ({l} : Set G)
      ∃ u ∈ ZK, orderOf u = 2 ∧ (commutator B).map B.subtype = zpowers u) →
    let C := centralizer ({v} : Set G)
    let P := (d.sylow : Subgroup G) ⊓ C
    ∀ M : Subgroup C, M.Normal → M.map C.subtype ⊓ P = W →
      let j := C.subtype.comp M.subtype
      (∀ m : M, ZW.map (MulAut.conj (j m)).toMonoidHom ≤ W →
        ZW.map (MulAut.conj (j m)).toMonoidHom = ZW) ∧
      (∀ m : M, (ZW.comap j).map (MulAut.conj m).toMonoidHom ≤ W.comap j →
        (ZW.comap j).map (MulAut.conj m).toMonoidHom = ZW.comap j) := by
  intro N K U i W ZK ZW hlines C P M hMn hinter j
  have hi : Function.Injective i := N.subtype_injective.comp K.subtype_injective
  have hZW : (center W).map W.subtype = ZW := map_center_image_of_injective U i hi
  have hW : IsPGroup 2 W := (pCore_isPGroup.to_subgroup U).map i
  have hWM : W ≤ M.map C.subtype := by rw [← hinter]; exact inf_le_left
  let : IsElementaryAbelian 2 (center U) := d.normalizer_core_omega_center_elementary
  let : IsElementaryAbelian 2 ZW := IsElementaryAbelian.map (i.comp U.subtype)
  let : IsElementaryAbelian 2 (center W) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Subtype.ext
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (x.val : G)
        (hZW ▸ mem_map_of_mem W.subtype x.property)) }
  have hweak : ∀ m : M, ZW.map (MulAut.conj (j m)).toMonoidHom ≤ W →
      ZW.map (MulAut.conj (j m)).toMonoidHom = ZW := by
    intro m hm
    rw [← hZW] at hm ⊢
    apply center_weakly_closed_of_centralizer_derived_lines (M.map C.subtype) W hW hWM
      ?_ (⟨j m, mem_map_of_mem C.subtype m.property⟩ : M.map C.subtype) hm
    intro l hl hl2 hlZ
    rw [hZW] at hlZ
    obtain ⟨u, hu, hu2, hline⟩ := hlines l hl hl2 hlZ
    refine ⟨u, hu2, hline, ?_⟩
    exact (d.first_transfer_core_center_centralizer h hN hproper Q v hv hfix
      M hMn hinter u hu (by intro he; simp [he] at hu2)).le
  refine ⟨hweak, weakly_closed_comap_of_injective j
    (C.subtype_injective.comp M.subtype_injective) ZW W ?_ ?_ hweak⟩
  · have hZWle : ZW ≤ W := by rw [← hZW]; exact map_subtype_le _
    rw [MonoidHom.range_comp, range_subtype]
    exact hZWle.trans hWM
  · rw [MonoidHom.range_comp, range_subtype]
    exact hWM
end Stellmacher.Recognition.ParrottSecondElementaryData

namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The omega-center weak-closure statement with Parrott's derived-line input
discharged by the local involution-centralizer calculation. -/
public theorem first_transfer_omega_center_weakly_closed
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
    ∀ M : Subgroup C, M.Normal → M.map C.subtype ⊓ P = W →
      let j := C.subtype.comp M.subtype
      (∀ m : M, ZW.map (MulAut.conj (j m)).toMonoidHom ≤ W →
        ZW.map (MulAut.conj (j m)).toMonoidHom = ZW) ∧
      (∀ m : M, (ZW.comap j).map (MulAut.conj m).toMonoidHom ≤ W.comap j →
        (ZW.comap j).map (MulAut.conj m).toMonoidHom = ZW.comap j) := by
  intro N K U i W ZW C P
  apply first_transfer_omega_center_weakly_closed_of_derived_lines
    d h hN hproper Q v hv hfix
  intro l hl hl2 hlZ
  exact omega_involution_centralizer_derived_line d h hN hproper Q hCD l hl hl2 hlZ
end Stellmacher.Recognition.ParrottSecondElementaryData

namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] {z : G}
/-- The ambient and internal centers agree under the actual first-transfer embedding. -/
public theorem first_transfer_omega_center_images
    (d : ParrottSecondElementaryData z) (v : G) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let i := N.subtype.comp K.subtype
    let W := U.map i
    let ZW := (center U).map (i.comp U.subtype)
    let C := centralizer ({v} : Set G)
    let P := (d.sylow : Subgroup G) ⊓ C
    ∀ M : Subgroup C, M.map C.subtype ⊓ P = W →
      let j := C.subtype.comp M.subtype
      let B := W.comap j
      B.map j = W ∧ (center W).map W.subtype = ZW ∧
        ((center B).map B.subtype).map j = ZW ∧
        (center B).map B.subtype = ZW.comap j := by
  intro N K U i W ZW C P M hinter j B
  have hi : Function.Injective i := N.subtype_injective.comp K.subtype_injective
  have hj : Function.Injective j := C.subtype_injective.comp M.subtype_injective
  have hWrange : W ≤ j.range := by
    rw [MonoidHom.range_comp, range_subtype, ← hinter]
    exact inf_le_left
  have hB : B.map j = W := map_comap_eq_self hWrange
  have hZW : (center W).map W.subtype = ZW := map_center_image_of_injective U i hi
  have hZB : ((center B).map B.subtype).map j = ZW := by
    rw [map_map, ← map_center_image_of_injective B j hj, hB, hZW]
  refine ⟨hB, hZW, hZB, ?_⟩
  apply map_injective hj
  rw [hZB, map_comap_eq_self (show ZW ≤ j.range from ?_)]
  rw [← hZW]
  exact (map_subtype_le _).trans hWrange
end Stellmacher.Recognition.ParrottSecondElementaryData
