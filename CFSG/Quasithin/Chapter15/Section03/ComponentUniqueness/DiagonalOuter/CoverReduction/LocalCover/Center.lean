module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.Algebra

/-!
# Deducing the center and both local centralizers

For Q=S∩L, A=Y_L and D=Y_D, the core order comparison first proves Q^t=Q.
The local central-omega argument kills C_S(Y) before the center calculation.
Thus the center has no D-fixed points, and the root centralizer modulo the
center lifts to C_Q(D)=V₂. Conjugating C_Q(A)=Z(L) identifies the compatible
other plane as V₁=Z(L).

Conjugation makes C_S(A) and C_S(D) have the same order. Their intersection
is trivial, while the matrix inclusion bounds their join by V₂ C_S(L).
The subgroup product formula forces C_S(L)=V₁. Inside C_I(L), this is a
central Sylow two-subgroup. Trivial odd core and Burnside transfer then give
C_I(L)=V₁. Normality is relative to I throughout.

The theorem retains the explicit local fixed-point inclusions and residual
product as hypotheses. Supplying them from the source setup is still required
for the local-cover assembly; it is not a proof of all of 15.3.38.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
proof of 15.3.38, printed p.1136.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
variable {G : Type*} [Group G] [Finite G]

/-- The central-cover deduction. All fixed-point assumptions are inclusions
modulo the central kernel, and neither center nor centralizer equality is assumed. -/
theorem center_and_centralizers
    (I L Y S V A D W₁ W₂ : Subgroup G)
    (hLI : L ≤ I) (hL : IsComponent I (L.subgroupOf I))
    (hIL : I ≤ normalizer (L : Set G))
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hodd : pPrimeCore 2 I = ⊥)
    (hSY : S ≤ normalizer (Y : Set G)) (hΩ : centralOmegaIn S ≤ V)
    (hVY : V ⊓ centralizer (Y : Set G) = ⊥) (hY : Y = A ⊔ D)
    (t : G) (hSt : S.map (MulAut.conj t).toMonoidHom = S)
    (hAD : A.map (MulAut.conj t).toMonoidHom = D)
    (hDA : D.map (MulAut.conj t).toMonoidHom = A)
    (hWt : W₂.map (MulAut.conj t).toMonoidHom = W₁)
    (hAQ : A.pCoreIn 2 = S ⊓ L)
    (hQD : S ⊓ L ≤ normalizer (D : Set G))
    (hDQ : D ≤ normalizer (S ⊓ L : Subgroup G))
    (hcomm : ⁅S ⊓ L, D⁆ = S ⊓ L)
    (hSA : S ⊓ centralizer (A : Set G) = S ⊓ centralizer (L : Set G))
    (hWQ : W₂ ≤ S ⊓ L) (hDW : D ≤ centralizer (W₂ : Set G))
    (hQfix : (S ⊓ L) ⊓ centralizer (D : Set G) ≤ W₂ ⊔ centerImage L)
    (hSfix : S ⊓ centralizer (D : Set G) ≤ W₂ ⊔ (S ⊓ centralizer (L : Set G))) :
    center L = pCore 2 L ∧ centerImage L = W₁ ∧
      S ⊓ centralizer (L : Set G) = W₁ ∧
      I ⊓ centralizer (L : Set G) = W₁ ∧
      D.pCoreIn 2 = S ⊓ L ∧
      (S ⊓ L).map (MulAut.conj t).toMonoidHom = S ⊓ L := by
  let e := MulAut.conj t
  have hSI : S ≤ I := hP ▸ map_subtype_le _
  have hS : IsPGroup 2 S := hP ▸ P.isPGroup'.map I.subtype
  have hZ := center_eq_twoCore_in hLI hL hodd
  have hZS : centerImage L ≤ S := by
    have he : centerImage L = L.pCoreIn 2 := congrArg (Subgroup.map L.subtype) hZ
    rw [he]
    exact (pCoreIn_mono_of_normalizes hLI hIL).trans (hP ▸ pCoreIn_le_sylow I P)
  have hZA : (S ⊓ L) ⊓ centralizer (A : Set G) = centerImage L := by
    calc
      (S ⊓ L) ⊓ centralizer (A : Set G) = L ⊓ (S ⊓ centralizer (A : Set G)) := by ac_rfl
      _ = S ⊓ (L ⊓ centralizer (L : Set G)) := by rw [hSA]; ac_rfl
      _ = centerImage L := by rw [← centerImage_eq_inf, inf_eq_right.mpr hZS]
  have hCY := sylow_centralizer_eq_bot S Y V hS hSY hΩ hVY
  have hZfixed : centerImage L ⊓ centralizer (D : Set G) = ⊥ := by
    apply le_bot_iff.mp
    intro z hz
    apply hCY.le
    refine ⟨hZS hz.1, ?_⟩
    rw [hY, centralizer_join]
    exact ⟨(hZA.ge hz.1).2, hz.2⟩
  have hQDcore : S ⊓ L ≤ D.pCoreIn 2 := by
    rw [← hcomm]
    exact commutator_le_twoCore (hS.to_le inf_le_left) hQD hDQ
  obtain ⟨hDcore, hQt⟩ := core_eq_and_invariant e hAD hAQ hQDcore
  have hWfix : (S ⊓ L) ⊓ centralizer (D : Set G) = W₂ :=
    fixed_eq_of_central_kernel (le_inf hWQ (le_centralizer_iff.mp hDW)) hQfix
      ((centerImage_centralizes L).trans (centralizer_le (hWQ.trans inf_le_right))) hZfixed
  have hZW : centerImage L = W₁ := center_eq_of_interchange e hQt hDA hWt hZA hWfix
  have hCmap : (S ⊓ centralizer (L : Set G)).map e.toMonoidHom =
      S ⊓ centralizer (D : Set G) := by
    rw [← hSA, map_inf _ _ _ e.injective, Theory.Quasithin.map_centralizer, hSt, hAD]
  have hCcard : Nat.card (S ⊓ centralizer (D : Set G) : Subgroup G) =
      Nat.card (S ⊓ centralizer (L : Set G) : Subgroup G) := by
    rw [← hCmap]
    exact (Nat.card_congr (e.subgroupMap _).toEquiv).symm
  have hCdis : (S ⊓ centralizer (L : Set G)) ⊓
      (S ⊓ centralizer (D : Set G)) = ⊥ := by
    rw [← hSA]
    have he : (S ⊓ centralizer (A : Set G)) ⊓ (S ⊓ centralizer (D : Set G)) =
        S ⊓ centralizer (Y : Set G) := by
      rw [hY, centralizer_join]
      simp only [inf_assoc, inf_left_comm, inf_left_idem]
    exact he.trans hCY
  have hWcard : Nat.card W₁ = Nat.card W₂ := by
    rw [← hWt]
    exact (Nat.card_congr (e.subgroupMap W₂).toEquiv).symm
  have hCS : S ⊓ centralizer (L : Set G) = W₁ :=
    centralizer_eq_plane rfl (hSI.trans hIL) inf_le_left (hWQ.trans inf_le_left)
      hSfix hCdis hCcard (hZW ▸ le_inf hZS (centerImage_centralizes L)) hWcard
  have hCI : I ⊓ centralizer (L : Set G) = W₁ :=
    (centralizer_eq_sylow_centralizer I L S hLI hIL P hP hodd
      (hCS ▸ hZW ▸ centerImage_le L)).trans hCS
  exact ⟨hZ, hZW, hCS, hCI, hDcore, hQt⟩

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
