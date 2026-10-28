module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.Lifting.Defs
public import Theory.SpecificGroups.SymmetricFiveInvolutions
public import Theory.SpecificGroups.SymmetricTwoResidual
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# The actual alternating subgroup under the H/Q marking

The preceding J.2.2(1) containment Q ≤ R₁ gives Q ≤ K, since R₁ ≤ L₁
and functoriality of the two-residual gives L₁ ≤ K. Surjective transport of
the residual then identifies K with the inverse image of A₅. Consequently
every outer involution maps to a transposition. Quotient conjugators lift
along the actual Ru2 map, and one seed supplies every transposition fiber.

The containment Q ≤ R₁ remains an earlier-source premise, produced by
`qt-j12-parabolic-structure`. It is not built into the type-Ru hypotheses.

Source: Aschbacher–Smith, J.2.2(1) and J.2.6, printed pp.432 and 435
(PDF pp.443 and 446).
-/

public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterJ.Fusion.Outer
variable {G : Type*} [Group G] [Finite G]

theorem L₁_le_K (d : TypeRuSetup G) : d.L₁ ≤ d.K := by
  let f : (d.L ⊓ d.H : Subgroup G) →* d.H := inclusion inf_le_right
  rintro x ⟨a, ha, rfl⟩
  exact ⟨f a, map_pResidual_le 2 f (mem_map_of_mem f ha), rfl⟩

theorem Q_le_K_of_le_R₁ (d : TypeRuSetup G) (hQR : d.Q ≤ d.R₁) : d.Q ≤ d.K :=
  hQR.trans ((pCoreIn_le 2 d.L₁).trans (L₁_le_K d))

theorem mem_K_iff_quotient_even (d : TypeRuSetup G) (hQR : d.Q ≤ d.R₁) (x : d.H) :
    (x : G) ∈ d.K ↔ d.ru2.quotientMap x ∈ alternatingGroup (Fin 5) := by
  have hmem (y : d.H) : (y : G) ∈ d.K ↔ y ∈ pResidual 2 d.H := by
    change (y : G) ∈ (pResidual 2 d.H).map d.H.subtype ↔ _
    exact mem_map_iff_mem d.H.subtype_injective
  have hker : d.ru2.quotientMap.ker ≤ pResidual 2 d.H := by
    intro y hy
    apply (hmem y).mp
    apply Q_le_K_of_le_R₁ d hQR
    rw [d.ru2.quotient_kernel] at hy
    exact hy
  have himage : (pResidual 2 d.H).map d.ru2.quotientMap = alternatingGroup (Fin 5) :=
    (map_pResidual_of_surjective 2 _ d.ru2.quotient_surjective).trans
      (Equiv.Perm.twoResidual_eq_alternating (Fin 5))
  rw [hmem, ← himage]
  change x ∈ pResidual 2 d.H ↔ x ∈ ((pResidual 2 d.H).map d.ru2.quotientMap).comap _
  rw [comap_map_eq, sup_eq_left.mpr hker]

/-- The quotient involution belongs to the actual ten-element transposition class. -/
theorem quotient_isSwap (d : TypeRuSetup G) (hQR : d.Q ≤ d.R₁)
    (i : d.H) (hiK : (i : G) ∉ d.K) (hi : orderOf (i : G) = 2) :
    (d.ru2.quotientMap i).IsSwap := by
  have hout : d.ru2.quotientMap i ∉ alternatingGroup (Fin 5) :=
    fun h => hiK ((mem_K_iff_quotient_even d hQR i).mpr h)
  apply Equiv.Perm.five_isSwap_of_outer_involution _ _ hout
  apply orderOf_eq_prime
  · rw [← map_pow]
    have hi2 : i ^ 2 = 1 := Subtype.ext (hi ▸ pow_orderOf_eq_one (i : G))
    rw [hi2, map_one]
  · intro he
    exact hout (he ▸ (alternatingGroup (Fin 5)).one_mem)

/-- Conjugacy in S₅ is lifted along the literal quotient map. -/
theorem exists_conjugator_quotient (d : TypeRuSetup G) (hQR : d.Q ≤ d.R₁)
    (i x : d.H) (hiK : (i : G) ∉ d.K) (hi : orderOf (i : G) = 2)
    (hxK : (x : G) ∉ d.K) (hx : orderOf (x : G) = 2) :
    ∃ h : d.H, d.ru2.quotientMap (h * x * h⁻¹) = d.ru2.quotientMap i := by
  have hc : IsConj (d.ru2.quotientMap x) (d.ru2.quotientMap i) :=
    Equiv.Perm.isConj_of_cycleType_eq
      ((Equiv.Perm.isSwap_iff_cycleType.mp (quotient_isSwap d hQR x hxK hx)).trans
        (Equiv.Perm.isSwap_iff_cycleType.mp (quotient_isSwap d hQR i hiK hi)).symm)
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  obtain ⟨h, hh⟩ := d.ru2.quotient_surjective g
  exact ⟨h, by simpa only [map_mul, map_inv, hh] using hg⟩

/-- A seed involution supplies a lift above every transposition. -/
theorem involutionFiber_nonempty_of_seed (d : TypeRuSetup G) (hQR : d.Q ≤ d.R₁)
    (i : d.H) (hiK : (i : G) ∉ d.K) (hi : orderOf (i : G) = 2)
    (t : S5) (ht : t.IsSwap) : (involutionFiber d t).Nonempty := by
  have hc : IsConj (d.ru2.quotientMap i) t :=
    Equiv.Perm.isConj_of_cycleType_eq
      ((Equiv.Perm.isSwap_iff_cycleType.mp (quotient_isSwap d hQR i hiK hi)).trans
        (Equiv.Perm.isSwap_iff_cycleType.mp ht).symm)
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  obtain ⟨h, hh⟩ := d.ru2.quotient_surjective g
  refine ⟨h * i * h⁻¹, ?_, ?_⟩
  · exact ((MulAut.conj (h : G)).orderOf_eq (i : G)).trans hi
  · simpa only [map_mul, map_inv, hh] using hg

end CFSG.Quasithin.ChapterJ.Fusion.Outer
