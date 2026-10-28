module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.CommonBorel
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.PairedSymplecticImage
public import Theory.SpecificGroups.SymplecticFour.Binary.MarkedAlternatingFive.Cubic

/-!
# The original paired radicals and their actual common cubic

The exact fixed-space image of the second radical determines a literal
natural SL₂(4) in the first radical's symplectic quotient. Its canonical
cubic is lifted by the actual elementary-kernel calculation. The resulting
order192 subgroup retains the original radicals, their point-core markings,
the exact root image, and the full natural action.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
open Theory.SpecificGroups.SymplecticFour
open Representation.SL2FourNatural.BorelFactors
open Representation.SL2FourNatural.PointCommutator
local notation "SL" => Representation.SL2FourNatural.SL
local notation "FVec" => Representation.SL2FourNatural.V
local notation "cubic" => Representation.SL2FourNatural.PointCommutator.cubic
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- Original HS data construct the same marked radical pair, an actual
common cubic, and a literal common subgroup of order192. The cubic belongs
to the specified natural SL₂(4) containing the exact opposite-root image. -/
theorem TypeAt.exists_marked_common_borel (h : TypeAt z V) :
    ∃ (W A B : Subgroup G) (p : G) (hAE : IsElementaryAbelian 2 A)
      (hBE : IsElementaryAbelian 2 B)
      (_hAB : A ≤ normalizer (B : Set G)) (hBA : B ≤ normalizer (A : Set G)),
      let := hAE
      let := hBE
      W ≤ V ∧ Nat.card W = 4 ∧ Nat.card A = 16 ∧ Nat.card B = 16 ∧
      p ∈ (normalizer (V : Set G)).pCoreIn 2 ∧ p ^ 2 ∉ W ∧
      B = A.map (MulAut.conj p).toMonoidHom ∧
      A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W ∧
      B ⊓ (normalizer (V : Set G)).pCoreIn 2 = W ∧
      centralizer (A : Set G) = A ∧ centralizer (B : Set G) = B ∧
      A ⊓ B = W ∧ ⁅A, B⁆ ≤ W ∧ Nat.card (A ⊔ B : Subgroup G) = 64 ∧
      A ⊔ B ≤ centralizer (W : Set G) ∧
      (∀ x ∈ A, x ≠ 1 → IsConj x z) ∧ (∀ x ∈ B, x ≠ 1 → IsConj x z) ∧
      (∀ x ∈ A, x ≠ 1 → Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8) ∧
      (∀ x ∈ B, x ≠ 1 → Nat.card (B ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8) ∧
      (∀ b ∈ B, b ∉ W → A ⊓ involutionCentralizer b = W) ∧
      ∃ (e : Additive A ≃ₗ[ZMod 2] Matrix.PSp4Three.Vector 2 (ZMod 2))
        (φ : (normalizer (A : Set G) ⧸ A.subgroupOf (normalizer (A : Set G))) ≃*
          Matrix.PSp4Three.Sp 2 (ZMod 2)),
        (∀ (g : normalizer (A : Set G)) (x : A),
          (φ (QuotientGroup.mk g)).val *ᵥ e (Additive.ofMul x) =
            e (Additive.ofMul (A.normalizerMonoidHom g x))) ∧
        ∃ (v : FVec ≃ₗ[ZMod 2] Matrix.PSp4Three.Vector 2 (ZMod 2))
          (ι : SL →* Matrix.PSp4Three.Sp 2 (ZMod 2)), Function.Injective ι ∧
          (∀ g w, (ι g).val *ᵥ v w = v (Representation.SL2FourNatural.action g w)) ∧
          U0.map ι = ((φ.toMonoidHom.comp (QuotientGroup.mk'
            (A.subgroupOf (normalizer (A : Set G))))).comp (inclusion hBA)).range ∧
          Representation.SL2FourNatural.upperFixed.map v.toLinearMap =
            (((W.subgroupOf A).toAddSubgroup.toZModSubmodule 2).map e.toLinearMap) ∧
          ∃ t : normalizer (A : Set G), orderOf (t : G) = 3 ∧
            φ (QuotientGroup.mk t) = ι cubic ∧
            (t : G) ∈ normalizer (B : Set G) ∧ (t : G) ∈ normalizer (W : Set G) ∧
            Disjoint (A ⊔ B) (zpowers (t : G)) ∧
            (A ⊔ B) ⊔ zpowers (t : G) ≤ normalizer (A : Set G) ⊓ normalizer (B : Set G) ∧
            Nat.card ((A ⊔ B) ⊔ zpowers (t : G) : Subgroup G) = 192 := by
  obtain ⟨W,A,B,p,hWV,hW4,hAE,hA16,hBE,hB16,hp,hpW,hB,hAP,hBP,hCA,hCB,
    hi,hcomm,hAB,hBA,h64,hC,hpureA,hpureB,hpointsA,hpointsB,_,hfixed⟩ :=
    h.exists_rank_two_paired_plane_radicals
  let := hAE
  let := hBE
  have hWA : W ≤ A := hi ▸ (show A ⊓ B ≤ A from inf_le_left)
  have hAC : A ≤ centralizer (W : Set G) := le_sup_left.trans hC
  obtain ⟨β,_,_,_,e,φ,hφ,himage⟩ := h.paired_radical_symplectic_image A B W
    hA16 hCA hpureA hpointsA hB16 hW4 hWA hBA hi hcomm hfixed
  let q := φ.toMonoidHom.comp (QuotientGroup.mk' (A.subgroupOf (normalizer (A : Set G))))
  let R := (q.comp (inclusion hBA)).range
  let Wbar := (((W.subgroupOf A).toAddSubgroup.toZModSubmodule 2).map e.toLinearMap)
  change Nat.card R = 4 ∧ Module.finrank (ZMod 2) Wbar = 2 ∧
    (∀ x ∈ Wbar, ∀ y ∈ Wbar, form (ZMod 2) x y = 0) ∧
    (∀ r ∈ R, r ≠ 1 → ∀ w : Vector (ZMod 2), r • w = w ↔ w ∈ Wbar) at himage
  obtain ⟨v,ι,hι,hv,hR,hW,hτ,_,_,hτW,_⟩ :=
    Theory.SpecificGroups.SymplecticFour.Binary.MarkedAlternatingFive.exists_marked_embedding_with_cubic
      R Wbar himage.1 himage.2.1 himage.2.2.1 himage.2.2.2
  have hplane : ∀ x : A, (x : G) ∈ W → ∃ y : A, (y : G) ∈ W ∧
      (ι cubic).val *ᵥ e (Additive.ofMul x) = e (Additive.ofMul y) := by
    intro x hx
    have hxbar : e (Additive.ofMul x) ∈ Wbar := ⟨Additive.ofMul x, hx, rfl⟩
    obtain ⟨y,hy,he⟩ := hτW _ hxbar
    exact ⟨y.toMul,hy,he.symm⟩
  obtain ⟨t,ht3,htφ,htB,htW,_,hdis,hJ,h192⟩ :=
    h.paired_radicals_common_cubic W A hWV hW4 hA16 hWA hAC hAP p hp hpW
      e.toLinearEquiv φ hφ (ι cubic) hτ hplane
  rw [← hB] at htB hdis hJ h192
  exact ⟨W,A,B,p,hAE,hBE,hAB,hBA,hWV,hW4,hA16,hB16,hp,hpW,hB,hAP,hBP,hCA,hCB,
    hi,hcomm,h64,hC,hpureA,hpureB,hpointsA,hpointsB,hfixed,e.toLinearEquiv,φ,hφ,
    v,ι,hι,hv,hR,hW,t,ht3,htφ,htB,htW,hdis,hJ,h192⟩

end CFSG.Quasithin.HigmanSims
