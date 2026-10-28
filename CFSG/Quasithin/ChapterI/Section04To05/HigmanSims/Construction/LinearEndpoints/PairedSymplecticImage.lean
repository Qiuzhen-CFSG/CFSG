module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.PairedRadicalAction
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SixteenSymplecticNormalizer
public import Theory.SpecificGroups.SymplecticFour.Binary.MarkedAlternatingFive.RankTwo

/-!
# The literal paired radical in the marked symplectic quotient

The original quotient map sends the second radical to a four-group. Its
exact fixed plane is the image of the literal common plane under the
original form isometry. The commutator bound supplies displacement in
that plane, so the native symplectic geometry is obtained without an
assumed natural four-group marking.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- The second literal radical has order-four image and the transported
common plane as every nonidentity element's exact fixed space. -/
theorem TypeAt.paired_radical_symplectic_image (h : TypeAt z V)
    (A B W : Subgroup G) [IsElementaryAbelian 2 A]
    (hA16 : Nat.card A = 16) (hCA : centralizer (A : Set G) = A)
    (hpureA : ∀ x ∈ A, x ≠ 1 → IsConj x z)
    (hpointsA : ∀ x ∈ A, x ≠ 1 →
      Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8)
    (hB16 : Nat.card B = 16) (hW4 : Nat.card W = 4) (hWA : W ≤ A)
    (hBA : B ≤ normalizer (A : Set G)) (hi : A ⊓ B = W)
    (hcomm : ⁅A, B⁆ ≤ W)
    (hfixed : ∀ b ∈ B, b ∉ W → A ⊓ involutionCentralizer b = W) :
    ∃ β : LinearMap.BilinForm (ZMod 2) (Additive A), β.IsAlt ∧ β.Nondegenerate ∧
      (∀ (x : A) (_hx : x ≠ 1) (y : A),
        β (Additive.ofMul x) (Additive.ofMul y) = 0 ↔
          (y : G) ∈ (involutionCentralizer (x : G)).pCoreIn 2) ∧
      ∃ e : β.IsometryEquiv (Matrix.PSp4Three.form (n := 2) (F := ZMod 2)),
        ∃ φ : (normalizer (A : Set G) ⧸ A.subgroupOf (normalizer (A : Set G))) ≃*
            Matrix.PSp4Three.Sp 2 (ZMod 2),
          (∀ (g : normalizer (A : Set G)) (x : A),
            (φ (QuotientGroup.mk g)).val *ᵥ (e (Additive.ofMul x)) =
              e (Additive.ofMul (A.normalizerMonoidHom g x))) ∧
          let q := φ.toMonoidHom.comp (QuotientGroup.mk' (A.subgroupOf (normalizer (A : Set G))))
          let R := (q.comp (Subgroup.inclusion hBA)).range
          let Wbar := (((W.subgroupOf A).toAddSubgroup.toZModSubmodule 2).map e.toLinearMap)
          Nat.card R = 4 ∧ Module.finrank (ZMod 2) Wbar = 2 ∧
          (∀ x ∈ Wbar, ∀ y ∈ Wbar, form (ZMod 2) x y = 0) ∧
          (∀ r ∈ R, r ≠ 1 → ∀ v : Vector (ZMod 2), r • v = v ↔ v ∈ Wbar) := by
  obtain ⟨β, hAlt, hN, hker, e, φ, hact⟩ :=
    h.sixteen_symplectic_normalizer A hA16 hCA hpureA hpointsA
  refine ⟨β, hAlt, hN, hker, e, φ, hact, ?_⟩
  let N := normalizer (A : Set G)
  let q := φ.toMonoidHom.comp (QuotientGroup.mk' (A.subgroupOf N))
  let f := q.comp (Subgroup.inclusion hBA)
  let R := f.range
  let W0 := (W.subgroupOf A).toAddSubgroup.toZModSubmodule 2
  let Wbar := W0.map e.toLinearMap
  change Nat.card R = 4 ∧ Module.finrank (ZMod 2) Wbar = 2 ∧
    (∀ x ∈ Wbar, ∀ y ∈ Wbar, form (ZMod 2) x y = 0) ∧
    (∀ r ∈ R, r ≠ 1 → ∀ v : Vector (ZMod 2), r • v = v ↔ v ∈ Wbar)
  have hWB : W ≤ B := hi ▸ (show A ⊓ B ≤ B from inf_le_right)
  have hq1 (g : N) : q g = 1 ↔ (g : G) ∈ A := by
    change φ (QuotientGroup.mk g) = 1 ↔ _
    rw [φ.map_eq_one_iff, QuotientGroup.eq_one_iff]
    rfl
  have hk : f.ker = W.subgroupOf B := by
    ext b
    change q (Subgroup.inclusion hBA b) = 1 ↔ (b : G) ∈ W
    rw [hq1]
    constructor
    · intro hb
      exact hi ▸ (show (b : G) ∈ A ⊓ B from ⟨hb,b.property⟩)
    · exact fun hh => hWA hh
  have hR4 : Nat.card R = 4 := by
    have hh := f.ker.card_mul_index
    rw [Subgroup.index_ker, hk,
      Nat.card_congr (subgroupOfEquivOfLe hWB).toEquiv, hW4, hB16] at hh
    change 4 * Nat.card R = 16 at hh
    omega
  have hWmem (x : A) : e (Additive.ofMul x) ∈ Wbar ↔ (x : G) ∈ W := by
    constructor
    · rintro ⟨y,hy,he⟩
      have hey : y = Additive.ofMul x := e.injective he
      subst y
      exact hy
    · intro hx
      exact ⟨Additive.ofMul x,hx,rfl⟩
  let wEquiv : W0 ≃ W :=
    { toFun := fun x => ⟨x.val.toMul, x.property⟩
      invFun := fun w => ⟨Additive.ofMul ⟨w, hWA w.property⟩, w.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hWc : Nat.card Wbar = 4 :=
    (Nat.card_congr (Submodule.equivMapOfInjective e.toLinearMap e.injective W0).toEquiv).symm.trans
      ((Nat.card_congr wEquiv).trans hW4)
  have hWdim : Module.finrank (ZMod 2) Wbar = 2 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Wbar)
    rw [Nat.card_zmod, hWc] at hc
    exact Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hc.symm
  have hf (b : B) (x : A) : f b • e (Additive.ofMul x) =
      e (Additive.ofMul (A.normalizerMonoidHom (Subgroup.inclusion hBA b) x)) :=
    hact (Subgroup.inclusion hBA b) x
  have hfixR : ∀ r ∈ R, r ≠ 1 → ∀ v : Vector (ZMod 2), r • v = v ↔ v ∈ Wbar := by
    rintro r ⟨b,rfl⟩ hr1 v
    obtain ⟨x,rfl⟩ := e.surjective v
    have hbW : (b : G) ∉ W := by
      intro hbW
      apply hr1
      exact (hq1 (Subgroup.inclusion hBA b)).mpr (hWA hbW)
    change f b • e (Additive.ofMul x.toMul) = e (Additive.ofMul x.toMul) ↔ _
    rw [hf]
    change e (Additive.ofMul (A.normalizerMonoidHom (Subgroup.inclusion hBA b) x.toMul)) =
      e (Additive.ofMul x.toMul) ↔ e (Additive.ofMul x.toMul) ∈ Wbar
    rw [show (e (Additive.ofMul (A.normalizerMonoidHom (Subgroup.inclusion hBA b) x.toMul)) =
      e (Additive.ofMul x.toMul)) ↔
      Additive.ofMul (A.normalizerMonoidHom (Subgroup.inclusion hBA b) x.toMul) =
        Additive.ofMul x.toMul from e.injective.eq_iff, hWmem]
    constructor
    · intro he
      have heG := congrArg (fun y : Additive A => (y.toMul : G)) he
      have hxC : (x.toMul : G) ∈ involutionCentralizer (b : G) :=
        mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp heG).symm
      exact hfixed b b.property hbW ▸ (show (x.toMul : G) ∈ A ⊓ involutionCentralizer (b : G)
        from ⟨x.toMul.property,hxC⟩)
    · intro hxW
      have hxC : (x.toMul : G) ∈ involutionCentralizer (b : G) :=
        (hfixed b b.property hbW).symm ▸ hxW |>.2
      apply Additive.toMul.injective
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hxC).symm
  have hmove : ∀ r ∈ R, ∀ v : Vector (ZMod 2), r • v - v ∈ Wbar := by
    rintro r ⟨b,rfl⟩ v
    obtain ⟨x,rfl⟩ := e.surjective v
    change f b • e (Additive.ofMul x.toMul) - e (Additive.ofMul x.toMul) ∈ Wbar
    rw [hf]
    have hemap : e (Additive.ofMul (A.normalizerMonoidHom (Subgroup.inclusion hBA b) x.toMul) -
        Additive.ofMul x.toMul) =
      e (Additive.ofMul (A.normalizerMonoidHom (Subgroup.inclusion hBA b) x.toMul)) -
        e (Additive.ofMul x.toMul) := e.toLinearEquiv.map_sub _ _
    rw [← hemap]
    apply (hWmem _).mpr
    change ((b : G) * (x.toMul : G) * (b : G)⁻¹) / (x.toMul : G) ∈ W
    rw [div_eq_mul_inv]
    change ⁅(b : G),(x.toMul : G)⁆ ∈ W
    rw [← commutatorElement_inv]
    exact W.inv_mem (hcomm (commutator_mem_commutator x.toMul.property b.property))
  exact ⟨hR4,hWdim,
    Theory.SpecificGroups.SymplecticFour.Binary.MarkedAlternatingFive.isotropic_of_exact_fixed_plane
      R Wbar hR4 hWdim hfixR hmove, hfixR⟩

/-- Original HS data retain the paired radicals and their exact image and
fixed plane in the original marked symplectic normalizer quotient. -/
theorem TypeAt.exists_paired_symplectic_image (h : TypeAt z V) :
    ∃ (W A B : Subgroup G) (p : G) (hAe : IsElementaryAbelian 2 A)
      (_hBe : IsElementaryAbelian 2 B) (hBA : B ≤ normalizer (A : Set G)), letI := hAe
      W ≤ V ∧ Nat.card W = 4 ∧ Nat.card A = 16 ∧ Nat.card B = 16 ∧
      p ∈ (normalizer (V : Set G)).pCoreIn 2 ∧ p ^ 2 ∉ W ∧
      B = A.map (MulAut.conj p).toMonoidHom ∧
      A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W ∧
      B ⊓ (normalizer (V : Set G)).pCoreIn 2 = W ∧
      centralizer (A : Set G) = A ∧ centralizer (B : Set G) = B ∧
      A ⊓ B = W ∧ ⁅A, B⁆ ≤ W ∧
      A ≤ normalizer (B : Set G) ∧
      Nat.card (A ⊔ B : Subgroup G) = 64 ∧
      A ⊔ B ≤ centralizer (W : Set G) ∧
      (∀ x ∈ A, x ≠ 1 → IsConj x z) ∧
      (∀ x ∈ B, x ≠ 1 → IsConj x z) ∧
      (∀ x ∈ A, x ≠ 1 → Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8) ∧
      (∀ x ∈ B, x ≠ 1 → Nat.card (B ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8) ∧
      normalizer (A : Set G) ⊓ normalizer (B : Set G) =
        normalizer (A : Set G) ⊓ normalizer (W : Set G) ∧
      (∀ b ∈ B, b ∉ W → A ⊓ involutionCentralizer b = W) ∧
    ∃ β : LinearMap.BilinForm (ZMod 2) (Additive A), β.IsAlt ∧ β.Nondegenerate ∧
      (∀ (x : A) (_hx : x ≠ 1) (y : A),
        β (Additive.ofMul x) (Additive.ofMul y) = 0 ↔
          (y : G) ∈ (involutionCentralizer (x : G)).pCoreIn 2) ∧
      ∃ e : β.IsometryEquiv (Matrix.PSp4Three.form (n := 2) (F := ZMod 2)),
        ∃ φ : (normalizer (A : Set G) ⧸ A.subgroupOf (normalizer (A : Set G))) ≃*
            Matrix.PSp4Three.Sp 2 (ZMod 2),
          (∀ (g : normalizer (A : Set G)) (x : A),
            (φ (QuotientGroup.mk g)).val *ᵥ (e (Additive.ofMul x)) =
              e (Additive.ofMul (A.normalizerMonoidHom g x))) ∧
          let q := φ.toMonoidHom.comp (QuotientGroup.mk' (A.subgroupOf (normalizer (A : Set G))))
          let R := (q.comp (Subgroup.inclusion hBA)).range
          let Wbar := (((W.subgroupOf A).toAddSubgroup.toZModSubmodule 2).map e.toLinearMap)
          Nat.card R = 4 ∧ Module.finrank (ZMod 2) Wbar = 2 ∧
          (∀ x ∈ Wbar, ∀ y ∈ Wbar, form (ZMod 2) x y = 0) ∧
          (∀ r ∈ R, r ≠ 1 → ∀ v : Vector (ZMod 2), r • v = v ↔ v ∈ Wbar) := by
  obtain ⟨W,A,B,p,hWV,hW4,hAe,hA16,hBe,hB16,hp,hpW,hBconj,hAP,hBP,hCA,hCB,
    hi,hcomm,hAB,hBA,h64,hC,hpureA,hpureB,hpointsA,hpointsB,hpairN,hfixed⟩ :=
      h.exists_rank_two_paired_plane_radicals
  let := hAe
  have hWA : W ≤ A := hi ▸ (show A ⊓ B ≤ A from inf_le_left)
  exact ⟨W,A,B,p,hAe,hBe,hBA,hWV,hW4,hA16,hB16,hp,hpW,hBconj,hAP,hBP,hCA,hCB,
    hi,hcomm,hAB,h64,hC,hpureA,hpureB,hpointsA,hpointsB,hpairN,hfixed,
    h.paired_radical_symplectic_image A B W hA16 hCA hpureA hpointsA hB16 hW4 hWA
      hBA hi hcomm hfixed⟩

end CFSG.Quasithin.HigmanSims
