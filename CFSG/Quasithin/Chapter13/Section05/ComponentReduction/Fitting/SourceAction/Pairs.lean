module

public import CFSG.Quasithin.Chapter13.Section05.LocalGeometry.NonabelianClosure
public import Mathlib.Data.Fintype.Perm
/-!
# The F.9.5 conjugate-pair input to 13.5.20

The universal S₃ conclusion retains every hypothesis of F.9.5(5) and
(6.i). The earlier plane transport and centralizer facts give applicability
through NonabelianClosure. Every conjugator in H/O₂(H) lifts to H;
inverting the representative matches the book's right-conjugate convention.
Mapping the original join gives the literal pair in H/O₂(H). We retain its
S₃ isomorphism before computing its order.

This is a conditional source specialization. F.9.5 is owned by
qt-f09-rank-one/qt-f-09; the original F.9.1 application and plane geometry
by qt-13-05-f9-application and qt-13-05-local-geometry. Final discharge of
these source inputs remains with qt-13-05.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
F.9.5(5),(6.i), printed p.319; 13.5.13/20, printed pp.919/923.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction
open Section08.Source
variable {G : Type*} [Group G] [Finite G]

/-- The universal S₃ projection of F.9.5(6.i), including the hypotheses of (5).
Rank four is expressed as order sixteen for the elementary abelian V.
Right conjugates agree literally with Chapter G's convention. -/
def F95Six : Prop :=
  ∀ (D : ChapterF.Section09.Setup G), D.Hypothesis → D.Vplus.relIndex D.V = 2 →
    starImage D.H D.V ≠ ⊥ →
    (∀ g ∈ D.H, D.V₁ < D.V ⊓ ChapterG.Section02.Setup.conjugate D.V g →
      IsPGroup 2 (D.V ⊔ ChapterG.Section02.Setup.conjugate D.V g : Subgroup G)) →
    ⁅D.V, D.H ⊓ centralizer (D.Vplus : Set G)⁆ ≤ D.V₁ →
    Nat.card D.V = 16 → ∀ g ∈ D.H,
    ¬ IsPGroup 2 (starImage D.H (D.V ⊔ ChapterG.Section02.Setup.conjugate D.V g)) →
    Nonempty (starImage D.H (D.V ⊔ ChapterG.Section02.Setup.conjugate D.V g) ≃*
      Equiv.Perm (Fin 3))

omit [Finite G] in
theorem star_conjugate (H A : Subgroup G) (ha : A ≤ H) (x : H) :
    starImage H (A.map (MulAut.conj (x : G)).toMonoidHom) =
      (starImage H A).map (MulAut.conj (QuotientGroup.mk' (pCore 2 H) x)).toMonoidHom := by
  let q := QuotientGroup.mk' (pCore 2 H)
  apply le_antisymm
  · rintro _ ⟨b, hb, rfl⟩
    obtain ⟨a, ha', he⟩ := hb
    let aH : H := ⟨a, ha ha'⟩
    refine mem_map.mpr ⟨q aH, mem_map_of_mem _ ha', ?_⟩
    change q x * q aH * (q x)⁻¹ = q b
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg q (Subtype.ext he)
  · rintro _ ⟨_, ⟨a, ha', rfl⟩, rfl⟩
    refine mem_map.mpr ⟨x * a * x⁻¹, mem_map.mpr ⟨a, ha', rfl⟩, ?_⟩
    change q (x * a * x⁻¹) = q x * q a * (q x)⁻¹
    simp only [map_mul, map_inv]

omit [Finite G] in
theorem lift_pair (H A : Subgroup G) (ha : A ≤ H) (x : Hstar H) :
    ∃ (g : G) (hg : g ∈ H), QuotientGroup.mk' (pCore 2 H) ⟨g⁻¹, H.inv_mem hg⟩ = x ∧
      starImage H (A ⊔ ChapterG.Section02.Setup.conjugate A g) =
        starImage H A ⊔ (starImage H A).map (MulAut.conj x).toMonoidHom := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) x
  refine ⟨(y : G)⁻¹, H.inv_mem y.property, ?_, ?_⟩
  · simp
  · have hc : ChapterG.Section02.Setup.conjugate A (y : G)⁻¹ =
        A.map (MulAut.conj (y : G)).toMonoidHom := by
      simp [ChapterG.Section02.Setup.conjugate]
    rw [hc]
    have hb : A.map (MulAut.conj (y : G)).toMonoidHom ≤ H := by
      have he := mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer y.property)
      exact (map_mono ha).trans_eq he
    change ((A ⊔ A.map (MulAut.conj (y : G)).toMonoidHom).subgroupOf H).map _ = _
    rw [subgroupOf_sup ha hb, Subgroup.map_sup]
    exact congrArg (fun B => starImage H A ⊔ B) (star_conjugate H A ha y)

variable {D : ChapterF.Section09.Setup G}
theorem pairs_symmetric_three (hsource : F95Six (G := G)) (h : D.Hypothesis)
    (V₂ M : Subgroup G) (hindex : D.Vplus.relIndex D.V = 2)
    (hU : ¬ IsMulCommutative D.UH) (hcard : Nat.card D.V = 16)
    (hmove : ∀ W : Subgroup G, D.V₁ < W → W ≤ D.Vplus →
      ∃ l ∈ D.L₁, V₂ ≤ W.map (MulAut.conj l).toMonoidHom)
    (hplane : ∀ k ∈ D.H, V₂ ≤ D.V ⊓ D.V.map (MulAut.conj k).toMonoidHom →
      ⁅D.V, D.V.map (MulAut.conj k).toMonoidHom⁆ = ⊥ ∨
      D.V.map (MulAut.conj k).toMonoidHom ≤ M ⊓ normalizer (D.V : Set G))
    (hbound : normalizer (D.V₁ : Set G) ⊓ normalizer (D.Vplus : Set G) ≤ M)
    (hc : ⁅D.V, M ⊓ centralizer (D.Vplus : Set G)⁆ ≤ D.V₁)
    (x : Hstar D.H)
    (hnot : ¬ IsPGroup 2 (starImage D.H D.V ⊔
      (starImage D.H D.V).map (MulAut.conj x).toMonoidHom : Subgroup (Hstar D.H))) :
    Nonempty ((starImage D.H D.V ⊔
      (starImage D.H D.V).map (MulAut.conj x).toMonoidHom : Subgroup (Hstar D.H)) ≃*
      Equiv.Perm (Fin 3)) := by
  obtain ⟨hne, hp, hcentral⟩ := LocalGeometry.f95_applicability_of_plane_control
    h V₂ M hindex hU hmove hplane hbound hc
  obtain ⟨g, hg, _, he⟩ := lift_pair D.H D.V h.V_le_H x
  have hs := hsource D h hindex hne hp hcentral hcard g hg (he.symm ▸ hnot)
  exact he ▸ hs

theorem pair_card_of_symmetric_three {J : Type*} [Group J]
    (hs : Nonempty (J ≃* Equiv.Perm (Fin 3))) : Nat.card J = 6 := by
  obtain ⟨e⟩ := hs
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
  decide
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction
