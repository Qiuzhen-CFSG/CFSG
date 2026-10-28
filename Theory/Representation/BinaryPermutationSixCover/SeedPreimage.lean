module
public import Theory.Representation.BinaryPermutationSixCover.PlanePreimage
public import Theory.Representation.BinaryPermutation.SixCoreOrbits

/-!
# Eight-element submodules of the six-letter augmentation core

A coordinate permutation fixing a natural-quotient vector fixes its core lift:
the other lift is its complement, whose weight differs in six even coordinates.
For an invariant plane a two-perfect actor has odd action image, so its two-core
fixes the plane and hence its complete core preimage. In particular it fixes
any invariant eight-element subspace containing the constant line.

Source application: Aschbacher--Smith, 13.3.14(g), printed p.893.
-/

public section
open Subgroup Representation
namespace BinaryPermutation.SixCover

private theorem complement_weight_ne (v : core (Fin 6)) :
    wordWeight (v.val + allOne (Fin 6)) ≠ wordWeight v.val := by
  have h : ∀ w : Fin 6 → ZMod 2, (∑ i, w i) = 0 →
      wordWeight (w + allOne (Fin 6)) ≠ wordWeight w := by decide +kernel
  exact h v.val v.property

/-- Passing to the constant-line quotient creates no fixed core lifts in degree six. -/
theorem six_core_fixed_of_natural_fixed (g : Equiv.Perm (Fin 6))
    (v : core (Fin 6))
    (hv : naturalRepresentation (Fin 6) g (coreToNatural (Fin 6) v) =
      coreToNatural (Fin 6) v) : coreRepresentation (Fin 6) g v = v := by
  have hc : representation (Fin 6) g v.val - v.val ∈ constants (Fin 6) :=
    (Submodule.Quotient.eq _).mp (congrArg Subtype.val hv)
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hc
  have hc' : representation (Fin 6) g v.val = c • allOne (Fin 6) + v.val :=
    sub_eq_iff_eq_add.mp hc.symm
  have hc2 : c = 0 ∨ c = 1 := (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c
  rcases hc2 with rfl | rfl
  · apply Subtype.ext
    simpa using hc'
  · have hw := wordWeight_permute g v.val
    rw [hc'] at hw
    simp only [one_smul] at hw
    exact (complement_weight_ne v (by simpa [add_comm] using hw)).elim

private theorem twoCore_le_ker_permThree {D : Type*} [Group D] [Finite D]
    (hD : IsPPerfect 2 D) (f : D →* Equiv.Perm (Fin 3)) : pCore 2 D ≤ f.ker := by
  have hres : f.range ≤ pResidual 2 (Equiv.Perm (Fin 3)) := by
    have h := map_pResidual_le 2 f
    rw [(pResidual_eq_top_iff 2 D).mpr hD] at h
    rintro x ⟨g,rfl⟩
    exact h ⟨g,trivial,rfl⟩
  have halt : pResidual 2 (Equiv.Perm (Fin 3)) ≤ alternatingGroup (Fin 3) := by
    apply sInf_le
    refine ⟨inferInstance, IsPGroup.of_card (n := 1) ?_⟩
    change (alternatingGroup (Fin 3)).index = 2 ^ 1
    simp
  let P := (pCore 2 D).map f
  have hP : P ≤ alternatingGroup (Fin 3) := (map_le_range _ _).trans (hres.trans halt)
  have hp : IsPGroup 2 P := pCore_isPGroup.map f
  have hc : Nat.card P ∣ 3 := by
    have h := card_dvd_of_le hP
    have hthree : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]; rfl
    rwa [hthree] at h
  have hbot : P = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rcases hp.card_eq_or_dvd with he | he
    · exact he
    · have := he.trans hc
      norm_num at this
  exact (Subgroup.map_eq_bot_iff _).mp hbot

private theorem twoCore_fixes_card_four {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (hD : IsPPerfect 2 D) (ρ : Representation (ZMod 2) D W)
    (hc : Nat.card W = 4) (g : D) (hg : g ∈ pCore 2 D) (v : W) : ρ g v = v := by
  classical
  let _ := Fintype.ofFinite W
  let Q := {v : W // v ≠ 0}
  have hQ : Nat.card Q = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp [← Nat.card_eq_fintype_card, hc]
  let e : Q ≃ Fin 3 := (Finite.equivFin Q).trans (finCongr hQ)
  let p : D →* Equiv.Perm W := {
    toFun g := {
      toFun := ρ g
      invFun := ρ g⁻¹
      left_inv v := by simp [← Module.End.mul_apply, ← map_mul]
      right_inv v := by simp [← Module.End.mul_apply, ← map_mul] }
    map_one' := by ext v; simp
    map_mul' g h := by ext v; simp }
  let q : D →* Equiv.Perm Q := {
    toFun g := Equiv.Perm.subtypePerm (p g) (fun v => by
      change ρ g v ≠ 0 ↔ v ≠ 0
      exact not_congr (by
        constructor
        · intro hv
          have hh := congrArg (ρ g⁻¹) hv
          simpa [← Module.End.mul_apply, ← map_mul] using hh
        · intro hv; simp [hv]))
    map_one' := by ext v; change ρ 1 v.val = v.val; simp
    map_mul' g h := by ext v; change ρ (g*h) v.val = ρ g (ρ h v.val); simp }
  let f := e.permCongrHom.toMonoidHom.comp q
  have hfg : f g = 1 := twoCore_le_ker_permThree hD f hg
  have hqg : q g = 1 := e.permCongrHom.injective (hfg.trans (map_one e.permCongrHom.toMonoidHom).symm)
  by_cases hv : v = 0
  · simp [hv]
  exact congrArg Subtype.val (Equiv.congr_fun hqg (⟨v,hv⟩ : Q))

/-- The actor need not have A4 image: two-perfectness alone suffices. -/
theorem core_plane_preimage_twoCore_fixed {D : Type*} [Group D] [Finite D]
    (hD : IsPPerfect 2 D) (f : D →* alternatingGroup (Fin 6))
    (E : Submodule (ZMod 2) (natural (Fin 6))) (hE : Nat.card E = 4)
    (hinv : ∀ g : D, ∀ v ∈ E, alternatingNaturalRepresentation (Fin 6) (f g) v ∈ E)
    (g : D) (hg : g ∈ pCore 2 D)
    (v : core (Fin 6)) (hv : coreToNatural (Fin 6) v ∈ E) :
    alternatingCoreRepresentation (Fin 6) (f g) v = v := by
  let σ := (alternatingNaturalRepresentation (Fin 6)).comp f
  let q : D →* BinaryOffender.subspaceStabilizer σ E :=
    (MonoidHom.id D).codRestrict _ (fun g =>
      BinaryOffender.le_subspaceStabilizer σ E
        (A := ⊤) (fun a _ v hv => hinv a v hv) (mem_top g))
  let τ := (BinaryOffender.stabilizerRepresentation σ E).comp q
  have hfix := twoCore_fixes_card_four hD τ hE g hg
    (⟨coreToNatural (Fin 6) v,hv⟩ : E)
  exact six_core_fixed_of_natural_fixed (f g).val v (congrArg Subtype.val hfix)

/-- An eight-element core subspace containing the fixed line maps onto a plane. -/
theorem core_seed_natural_image_card (U : Submodule (ZMod 2) (core (Fin 6)))
    (hU : Nat.card U = 8) (hz : sixCoreConstant ∈ U) :
    Nat.card (U.map (coreToNatural (Fin 6))) = 4 := by
  have hk : (coreToNatural (Fin 6)).ker = coreConstants := by
    ext v
    change coreToNatural (Fin 6) v = 0 ↔ v.val ∈ constants (Fin 6)
    rw [← Subtype.val_inj]
    exact Submodule.Quotient.mk_eq_zero _
  have hku : (coreToNatural (Fin 6)).ker ≤ U := by
    rw [hk]
    intro v hv
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hv
    have he : c • sixCoreConstant = v := Subtype.ext hc
    rw [←he]
    exact U.smul_mem c hz
  have hkd : Module.finrank (ZMod 2) ((coreToNatural (Fin 6)).ker) = 1 := by
    have hc := card_coreConstants (Ω := Fin 6) (by decide)
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
    rw [hk]
    exact Nat.pow_right_injective (by decide : 1 < 2) (by simpa using hc)
  have hud : Module.finrank (ZMod 2) U = 3 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hU
    exact Nat.pow_right_injective (by decide : 1 < 2) hU
  have hd := ((coreToNatural (Fin 6)).domRestrict U).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
    (Submodule.comapSubtypeEquivOfLe hku).finrank_eq, hkd, hud] at hd
  have he : Module.finrank (ZMod 2) (U.map (coreToNatural (Fin 6))) = 2 := by omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,he]
  rfl

/-- The two-core fixes any invariant eight-element subspace containing the constant line. -/
theorem core_seed_twoCore_fixed {D : Type*} [Group D] [Finite D]
    (hD : IsPPerfect 2 D) (f : D →* alternatingGroup (Fin 6))
    (U : Submodule (ZMod 2) (core (Fin 6))) (hU : Nat.card U = 8)
    (hz : sixCoreConstant ∈ U)
    (hinv : ∀ g : D, ∀ v ∈ U, alternatingCoreRepresentation (Fin 6) (f g) v ∈ U)
    (g : D) (hg : g ∈ pCore 2 D) (v : core (Fin 6)) (hv : v ∈ U) :
    alternatingCoreRepresentation (Fin 6) (f g) v = v := by
  apply core_plane_preimage_twoCore_fixed hD f (U.map (coreToNatural (Fin 6)))
    (core_seed_natural_image_card U hU hz) _ g hg v ⟨v,hv,rfl⟩
  rintro a _ ⟨w,hw,rfl⟩
  exact ⟨_,hinv a w hw,coreToNatural_equivariant (f a).val w⟩

end BinaryPermutation.SixCover
