module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalOvergroupAction
public import Theory.LinearAlgebra.BinaryFourAlternatingEight
public import Theory.GroupAction.BinaryFixedLineQuotient
public import Theory.SpecificGroups.PSL3Two.Cardinality

/-!
# The faithful A₇ image of the original four-space overgroup

The action of C_G(z) on U has the same kernel as its previously marked
GL₃(2) action on U/⟨z⟩, so its faithful image has order 168. In the original
overgroup L₀ = ⟨N_L(T∩L), C_G(z)⟩ this is exactly the stabilizer of z.
Transitivity on the fifteen nonidentity elements of U gives image order 2520.

The actual GL₄(2) ≃ A₈ comparison makes this image an index-eight subgroup.
Its faithful coset action, restricted to the seven cosets other than itself,
identifies it with A₇. The resulting epimorphism retains L₀ and has kernel
exactly C_{L₀}(U). No LocalAnalysis or later M₂₂ identification is used.

Source: Aschbacher--Smith, 6.2.11, printed p.686, the L₀ paragraph. The
S₅ preimage with generation parameter two remains to be constructed.
The exceptional linear comparison retains its ATLAS attribution and license
through `Theory.LinearAlgebra.BinaryFourAlternatingEight`.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction
variable {G : Type*} [Group G] [Finite G] {P : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The actual overgroup used in source 6.2.11. -/
def fourOvergroup (T L : Subgroup G) (z : G) : Subgroup G :=
  (L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G)) ⊔ Centralizer z

/-- Its conjugation action on the original closure. -/
def fourOvergroupAction (T L R : Subgroup G) (z : G)
    (hN : fourOvergroup T L z ≤ normalizer (sourceClosure T L R z : Set G)) :
    fourOvergroup T L z →* MulAut (sourceClosure T L R z) :=
  (sourceClosure T L R z).normalizerMonoidHom.comp (inclusion hN)

private theorem index_eight_alternating (H : Subgroup (alternatingGroup (Fin 8)))
    (hi : H.index = 8) : Nonempty (H ≃* alternatingGroup (Fin 7)) := by
  classical
  let A8 := alternatingGroup (Fin 8)
  let : IsSimpleGroup A8 := alternatingGroup.isSimpleGroup (by simp)
  have hnt : H ≠ ⊤ := by intro he; simp [he] at hi
  let f := MulAction.toPermHom A8 (A8 ⧸ H)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    rw [← H.normalCore_eq_ker]
    rcases H.normalCore_normal.eq_bot_or_eq_top with he | he
    · exact he
    · exact (hnt (top_le_iff.mp (he ▸ H.normalCore_le))).elim
  let e : (A8 ⧸ H) ≃ Fin 8 := (Finite.equivFin (A8 ⧸ H)).trans (finCongr hi)
  let p : H →* Equiv.Perm (Fin 8) := e.permCongrHom.toMonoidHom.comp (f.comp H.subtype)
  have hp : Function.Injective p := e.permCongrHom.injective.comp (hf.comp H.subtype_injective)
  let i := e (QuotientGroup.mk (1 : A8))
  have hfix (g : H) : p g i = i := by
    change e (g.val • e.symm (e (QuotientGroup.mk (1 : A8)))) = _
    rw [e.symm_apply_apply]
    apply e.injective.eq_iff.mpr
    change QuotientGroup.mk (g.val * 1) = QuotientGroup.mk (1 : A8)
    simp [QuotientGroup.eq, g.property]
  let r : H →* Equiv.Perm {j : Fin 8 // j ≠ i} := {
    toFun g := (p g).subtypePerm (fun j => by
      simpa only [hfix g] using (p g).injective.ne_iff (x := j) (y := i))
    map_one' := by
      apply Equiv.ext
      intro j
      apply Subtype.ext
      exact congrArg (fun t : Equiv.Perm (Fin 8) => t j.val) p.map_one
    map_mul' := by
      intro g h
      apply Equiv.ext
      intro j
      apply Subtype.ext
      exact congrArg (fun t : Equiv.Perm (Fin 8) => t j.val) (p.map_mul g h) }
  have hr : Function.Injective r := by
    intro g h he
    apply hp
    apply Equiv.ext
    intro j
    by_cases hj : j = i
    · subst j; exact (hfix g).trans (hfix h).symm
    · exact congrArg (fun t : Equiv.Perm {j : Fin 8 // j ≠ i} => (t ⟨j, hj⟩).val) he
  let q := (finSuccAboveEquiv i).symm.permCongrHom.toMonoidHom.comp r
  have hq : Function.Injective q := (finSuccAboveEquiv i).symm.permCongrHom.injective.comp hr
  have hc : Nat.card H = 2520 := by
    have hh := H.card_mul_index
    rw [hi, nat_card_alternatingGroup] at hh
    norm_num [Nat.factorial] at hh
    rw [Nat.card_eq_fintype_card]
    omega
  have hqcard : Nat.card q.range = 2520 :=
    (Nat.card_congr (MonoidHom.ofInjective hq).toEquiv).symm.trans hc
  have hqi : q.range.index = 2 := by
    have hh := q.range.card_mul_index
    rw [hqcard, Nat.card_perm, Nat.card_fin] at hh
    norm_num [Nat.factorial] at hh
    omega
  exact ⟨(MonoidHom.ofInjective hq).trans
    (MulEquiv.subgroupCongr (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hqi))⟩

/-- The original centralizer has faithful image of order 168 on U itself.
The equality of kernels transports the already marked quotient action. -/
theorem four_centralizer_action_card
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    Nat.card ((sourceClosure (P : Subgroup G) L R z).normalizerMonoidHom.comp
      (inclusion (closure_normalized (P : Subgroup G) L R z))).range = 168 := by
  let := (reduced_space h hnatural hz ho hP).elementary
  let U := sourceClosure (P : Subgroup G) L R z
  let b := U.normalizerMonoidHom.comp (inclusion (closure_normalized (P : Subgroup G) L R z))
  let a := linearAction (P : Subgroup G) L R z
  have hk : b.ker = a.ker := by
    rw [show a.ker = (action (P : Subgroup G) L R z).ker from
      MonoidHom.ker_comp_of_injective _ _ (linearize _ _ _ _).injective,
      action_ker, four_kernel_eq_centralizer h hnatural hz ho hP hplane hcard]
    ext x
    change U.normalizerMonoidHom (inclusion (closure_normalized _ _ _ _) x) = 1 ↔
      (x : G) ∈ Centralizer z ⊓ centralizer (U : Set G)
    rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
    exact ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩
  have he := congrArg Subgroup.index hk
  rw [index_ker, index_ker] at he
  rw [he]
  obtain ⟨hfull, hd, _⟩ := four_image_three_space h hnatural hz ho hP hplane hcard
  change Nat.card (linearAction (P : Subgroup G) L R z).range = 168
  rw [hfull, card_top]
  let W := Additive (space (P : Subgroup G) L R z)
  let e : W ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) := LinearEquiv.ofFinrankEq _ _ (by simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] using hd)
  let eGL : (W ≃ₗ[ZMod 2] W) ≃* BinaryLinear.OuterCyclic.LinearGroup 3 :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).symm.trans
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv e).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 3 → ZMod 2)))
  rw [Nat.card_congr eGL.toEquiv,
    ← Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear 3).toEquiv,
    Matrix.PSL3Two.card_SL]

/-- Orbit--stabilizer for the actual ambient action gives its order. -/
theorem four_overgroup_action_card
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hNL : normalizer (layer L R : Set G) ≤ normalizer (L : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    Nat.card (fourOvergroupAction (P : Subgroup G) L R z
      (four_generated_overgroup_normalizes_closure h hnatural hz ho hP hplane hNL hcard)).range = 2520 := by
  classical
  let U := sourceClosure (P : Subgroup G) L R z
  let X := fourOvergroup (P : Subgroup G) L z
  let hn := four_generated_overgroup_normalizes_closure h hnatural hz ho hP hplane hNL hcard
  let f := fourOvergroupAction (P : Subgroup G) L R z hn
  let b := U.normalizerMonoidHom.comp (inclusion (closure_normalized (P : Subgroup G) L R z))
  let A := f.range
  have hzU : z ∈ U := (ZS_le_sourceClosure_intersection h hz).trans inf_le_left hz
  let zU : U := ⟨z, hzU⟩
  have hz1 : zU ≠ 1 := by
    intro he
    have hh : z = 1 := congrArg Subtype.val he
    rw [hh, orderOf_one] at ho
    contradiction
  have hstab : (MulAction.stabilizer A zU).map A.subtype = b.range := by
    ext a
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨g, hg⟩ := a.property
      have hfix : a.val zU = zU := ha
      have hh : (g : G) * z * (g : G)⁻¹ = z := by
        have hh := congrArg Subtype.val hfix
        rw [← hg] at hh
        exact hh
      have hgz : (g : G) ∈ Centralizer z := mem_centralizer_singleton_iff.mpr
        ((mul_inv_eq_iff_eq_mul.mp hh) : (g : G) * z = z * (g : G))
      exact ⟨⟨g.val, hgz⟩, hg⟩
    · rintro ⟨g, rfl⟩
      let gX : X := ⟨g.val, mem_sup_right g.property⟩
      refine ⟨f.rangeRestrict gX, ?_, rfl⟩
      change f gX zU = zU
      apply Subtype.ext
      change (g : G) * z * (g : G)⁻¹ = z
      exact (mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp g.property))
  have hstabcard : Nat.card (MulAction.stabilizer A zU) = 168 := by
    rw [← card_map_of_injective (K := MulAction.stabilizer A zU) A.subtype_injective, hstab]
    exact four_centralizer_action_card h hnatural hz ho hP hplane hcard
  have horbit : MulAction.orbit A zU = {u : U | u ≠ 1} := by
    ext u
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨a, rfl⟩
      change a.val zU ≠ 1
      simpa only [map_one] using a.val.injective.ne_iff.mpr hz1
    · intro hu
      have hu1 : (u : G) ≠ 1 := fun he => hu (Subtype.ext he)
      obtain ⟨g, hg, he⟩ := four_generated_overgroup_transitive h hnatural hz ho hP hplane hcard u.property hu1
      exact ⟨f.rangeRestrict ⟨g, hg⟩, Subtype.ext he⟩
  have horbitcard : Nat.card (MulAction.orbit A zU) = 15 := by
    rw [Nat.card_congr (Equiv.setCongr horbit)]
    let := Fintype.ofFinite U
    rw [Nat.card_eq_fintype_card]
    change Fintype.card {u : U // ¬u = 1} = 15
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    rw [← Nat.card_eq_fintype_card, four_closure_card h hnatural hz ho hP hplane hcard]
  have hc : Nat.card (MulAction.orbit A zU) * Nat.card (MulAction.stabilizer A zU) = Nat.card A := by
    rw [← Nat.card_prod, Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup A zU)]
  rw [horbitcard, hstabcard] at hc
  exact hc.symm

/-- The faithful image of the original overgroup is actually A₇. -/
theorem four_overgroup_action_alternating
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hNL : normalizer (layer L R : Set G) ≤ normalizer (L : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    Nonempty ((fourOvergroupAction (P : Subgroup G) L R z
      (four_generated_overgroup_normalizes_closure h hnatural hz ho hP hplane hNL hcard)).range ≃*
        alternatingGroup (Fin 7)) := by
  let U := sourceClosure (P : Subgroup G) L R z
  let := four_closure_elementary h hnatural hz ho hP hplane hcard
  let hn := four_generated_overgroup_normalizes_closure h hnatural hz ho hP hplane hNL hcard
  let A := (fourOvergroupAction (P : Subgroup G) L R z hn).range
  have hd : Module.finrank (ZMod 2) (Additive U) = 4 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive U)
    change Nat.card U = _ at hh
    rw [four_closure_card h hnatural hz ho hP hplane hcard, Nat.card_zmod] at hh
    exact hh.symm
  let e : MulAut U ≃* alternatingGroup (Fin 8) :=
    BinaryFixedLine.linearAutEquiv.trans (BinaryFourAlternatingEight.linearEquivAlternatingEight hd)
  let B := A.map e.toMonoidHom
  have hc : Nat.card B = 2520 := by
    rw [card_map_of_injective e.injective]
    exact four_overgroup_action_card h hnatural hz ho hP hplane hNL hcard
  have hi : B.index = 8 := by
    have hh := B.card_mul_index
    rw [hc, nat_card_alternatingGroup] at hh
    norm_num [Nat.factorial] at hh
    omega
  obtain ⟨eB⟩ := index_eight_alternating B hi
  exact ⟨(e.subgroupMap A).trans eB⟩

/-- The map to A₇ has exactly the centralizer of the original U as kernel.
This gives a quotient of the original ambient subgroup for the H-star step. -/
theorem four_overgroup_alternating_quotient
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hNL : normalizer (layer L R : Set G) ≤ normalizer (L : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    ∃ q : fourOvergroup (P : Subgroup G) L z →* alternatingGroup (Fin 7),
      Function.Surjective q ∧ q.ker =
        (centralizer (sourceClosure (P : Subgroup G) L R z : Set G)).subgroupOf
          (fourOvergroup (P : Subgroup G) L z) := by
  let hn := four_generated_overgroup_normalizes_closure h hnatural hz ho hP hplane hNL hcard
  let f := fourOvergroupAction (P : Subgroup G) L R z hn
  obtain ⟨e⟩ := four_overgroup_action_alternating h hnatural hz ho hP hplane hNL hcard
  refine ⟨e.toMonoidHom.comp f.rangeRestrict, e.surjective.comp f.rangeRestrict_surjective, ?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ e.injective, MonoidHom.ker_rangeRestrict]
  ext x
  change (sourceClosure (P : Subgroup G) L R z).normalizerMonoidHom (inclusion hn x) = 1 ↔ _
  rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
  rfl

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction
