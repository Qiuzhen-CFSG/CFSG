module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.Intersection
public import CFSG.Quasithin.ChapterG.Section02.Binary.Core

/-!
# The literal partner core in source 15.3.56

For the rank-one group J, its centralizer kernel on V₀ is its two-core.
The old U∩O₂(J) definition of W is then exactly F=U∩Hʸ. The binary
conjugate-kernel theorem gives O₂(J)=F Fʸ, retaining the original y.
The symmetric-three quotient and its centralizer-kernel identification
are the independent finite-action recognition inputs to this adapter.

Source: Aschbacher–Smith, 15.3.56, printed p.1147, using the group
argument of G.2.3(3).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
variable {G : Type*} [Group G] (Z ZS : Subgroup G)

/-- The actual centralizer intersection F equals the core intersection W. -/
theorem intersectionF_eq_pairW (V₀ : Subgroup G) (y : G)
    (hZS : ZS ≤ centralizerH Z)
    (hplane : V₀ = Z ⊔ rightConjugate Z y)
    (hcore : pairP Z ZS y = pairI Z ZS y ⊓ centralizer (V₀ : Set G)) :
    intersectionF Z ZS y = pairW Z ZS y := by
  rw [intersectionF, rightConjugate_centralizer, pairW, hcore]
  have hU : closureU Z ZS ≤ centralizerH Z := closureU_le_H hZS
  apply le_antisymm
  · intro x hx
    refine ⟨hx.1, (show closureU Z ZS ≤ pairI Z ZS y from le_sup_left) hx.1, ?_⟩
    have hcZ : Z ≤ centralizer ({x} : Set G) := fun z hz =>
      mem_centralizer_singleton_iff.mpr (hU hx.1 z hz)
    have hcZy : rightConjugate Z y ≤ centralizer ({x} : Set G) := fun z hz =>
      mem_centralizer_singleton_iff.mpr (hx.2 z hz)
    have hv : V₀ ≤ centralizer ({x} : Set G) := by
      rw [hplane]
      exact sup_le hcZ hcZy
    exact fun z hz => mem_centralizer_singleton_iff.mp (hv hz)
  · intro x hx
    refine ⟨hx.1, ?_⟩
    exact centralizer_le (show rightConjugate Z y ≤ V₀ by rw [hplane]; exact le_sup_right) hx.2.2

/-- The G.2.3 kernel calculation gives the literal J-core field required by
Partner.EarlierGeometry. No binary hypothesis on the exchanged factor is used. -/
theorem partner_core_product [Finite G] (V₀ Y₁ T : Subgroup G) (y : G)
    (hZS : ZS ≤ centralizerH Z)
    (hplane : V₀ = Z ⊔ rightConjugate Z y)
    (hcore : pairP Z ZS y = pairI Z ZS y ⊓ centralizer (V₀ : Set G))
    (hy : y ∈ pairI Z ZS y)
    (e : (pairI Z ZS y ⧸ pCore 2 (pairI Z ZS y)) ≃* Equiv.Perm (Fin 3))
    (hindex : (intersectionF Z ZS y).relIndex (closureU Z ZS) = 2) :
    pairP Z ZS y = intersectionF Z ZS y ⊔ partnerX Z ZS y := by
  let D : CFSG.Quasithin.ChapterG.Section02.Setup G := ⟨ZS, Z, Y₁, T, centralizerH Z⟩
  have hF : intersectionF Z ZS y = pairW Z ZS y :=
    intersectionF_eq_pairW Z ZS V₀ y hZS hplane hcore
  have hnorm : pairP Z ZS y ≤ normalizer (closureU Z ZS : Set G) := by
    rw [hcore]
    exact (inf_le_right.trans
      (centralizer_le (show Z ≤ V₀ by rw [hplane]; exact le_sup_left))).trans
        (H_normalizes_closureU Z ZS)
  have hi : (D.W y).relIndex D.U = 2 := by
    change (pairW Z ZS y).relIndex (closureU Z ZS) = 2
    rw [← hF]
    exact hindex
  have hh := D.binary_core_factorization y hy e hnorm hi
  change pairP Z ZS y = pairW Z ZS y ⊔ rightConjugate (pairW Z ZS y) y at hh
  rw [← hF] at hh
  exact hh

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
