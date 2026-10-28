module

public import CFSG.Quasithin.ChapterG.Section02.Intersection
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.BinaryCore

/-!
# The almost-special intersection in the marked binary parabolic

The preceding 12.8.8 generation identity makes the G.2 seed precisely V₂.
The rank-one intersection theorem then identifies E=W∩Wᵍ with U∩Uᵍ,
and proves its elementary abelianness, relative normality and commutator
bound. All maps and conjugates are the original marked ones of Section 12.8.

The Frattini bound is supplied by 12.8.4(2), the V₂-generation by
12.8.8(6), and the generation and centralizer/core identities by 12.8.9(1).
Their discharge and the stronger equality [E,I₂]=V₂ stay with those source
owners. This application is separate from the Section02 entry module to
avoid a dependency from the general source theorem to its later consumer.

Source: Aschbacher–Smith, G.2.3(4–5) applied in 12.8.9(2),
combined manuscript of 1 March 2004, printed pp.333 and 852–853.
-/

open Subgroup

namespace CFSG.Quasithin.ChapterG.Section02.Applications
open CFSG.Quasithin.Chapter12.Section08

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The literal E in the marked parabolic is the normal elementary
intersection supplied by G.2.3. Earlier source inputs remain explicit. -/
public theorem parabolic_intersection_layer (F : InvariantFlag T V n)
    (hn : 2 ≤ n) (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hp : IsPGroup 2 F.U)
    (hf : (frattini F.U).map F.U.subtype ≤ F.Vi 1)
    (hspan : conjugateSpanBy (F.Vi 2) F.H = F.U)
    (hgen : F.U ⊔ conjugate F.U g = F.I₂ L)
    (hcore : F.I₂ L ⊓ centralizer (F.Vi 2 : Set G) = (F.I₂ L).pCoreIn 2) :
    F.E g = F.U ⊓ conjugate F.U g ∧
    F.Vi 2 ≤ F.E g ∧ F.E g ≤ (F.I₂ L).pCoreIn 2 ∧
    ((F.E g).subgroupOf (F.I₂ L)).Normal ∧
    ⁅F.E g, F.I₂ L⁆ ≤ F.Vi 2 ∧ IsElementaryAbelian 2 (F.E g) := by
  have hgG := F.P_le_G₂ hn L hL hgP
  have hUI := F.U_le_G₂_of_commutator (derived_le_of_frattini_image_le hp hf)
  have hIV : F.I₂ L ≤ F.Gi 2 := by
    rw [← hgen]
    exact sup_le hUI (conjugate_le_of_normalizes hUI g ((F.Gi 2).le_normalizer hgG))
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by omega)
  have hcg : Nat.card (conjugate (F.Vi 1) g) = 2 := by
    rw [conjugate, card_map_of_injective (MulAut.conj g⁻¹).injective, hc]
  have hne : F.Vi 1 ≠ conjugate (F.Vi 1) g := by
    intro he
    exact hgH ((conjugate_eq_iff (F.Vi 1) g).mp he.symm)
  have hdis : Disjoint (F.Vi 1) (conjugate (F.Vi 1) g) :=
    disjoint_iff.mpr (inf_eq_bot_of_card_two_of_ne _ _ hc hcg hne)
  let D : Setup G :=
    { V := F.Vi 2, V₁ := F.Vi 1, L := (pResidual 2 (F.P L)).map (F.P L).subtype,
      T := T, H := F.H }
  have hDU : D.U = F.U := hspan
  have hDI : D.I g = F.I₂ L := by
    change D.U ⊔ conjugate D.U g = F.I₂ L
    rw [hDU]
    exact hgen
  have hDE : D.S₂ g = F.U ⊓ conjugate F.U g := by
    change D.U ⊓ conjugate D.U g = _
    rw [hDU]
  have hDS : D.S g = (F.I₂ L).pCoreIn 2 := by
    change (D.I g).pCoreIn 2 = _
    rw [hDI]
  have hpD : IsPGroup 2 D.U := by rw [hDU]; exact hp
  have hfD : (frattini D.U).map D.U.subtype ≤ D.V₁ := by
    change (frattini D.U).map D.U.subtype ≤ F.Vi 1
    rw [hDU]
    exact hf
  have hnormD : D.I g ≤ normalizer (D.V : Set G) := by
    change D.I g ≤ F.Gi 2
    rw [hDI]
    exact hIV
  have h := D.rank_one_intersection_layer g hpD hfD
    (F.monotone (by omega)) hnormD hgG hdis
  rw [hDE, hDS, hDI] at h
  have hW : F.W = F.U ⊓ (F.I₂ L).pCoreIn 2 := by
    rw [← hcore, ← inf_assoc, inf_eq_left.mpr (le_sup_left.trans hgen.le)]
    rfl
  have hSg : conjugate ((F.I₂ L).pCoreIn 2) g = (F.I₂ L).pCoreIn 2 :=
    (conjugate_eq_iff _ _).mpr
      (normalizer_le_normalizer_characteristic_image (F.I₂ L) (pCore 2 (F.I₂ L))
        (le_normalizer_conjugateSpanBy F.U (F.P L) hgP))
  have hE : F.E g = F.U ⊓ conjugate F.U g := by
    change F.W ⊓ conjugate F.W g = _
    rw [hW, conjugate_inf, hSg]
    apply le_antisymm
    · exact inf_le_inf inf_le_left inf_le_left
    · intro x hx
      exact ⟨⟨hx.1, h.2.1 hx⟩, ⟨hx.2, h.2.1 hx⟩⟩
  refine ⟨hE, ?_⟩
  rw [hE]
  exact h

end CFSG.Quasithin.ChapterG.Section02.Applications
