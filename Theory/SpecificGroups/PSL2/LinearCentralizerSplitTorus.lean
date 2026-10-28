module

public import Theory.SpecificGroups.PSL2.SplitTorusSemilinearSquares
/-!
# Linear actors fixing fourth powers of the full torus

In the actual dihedral split-involution centralizer, a reflection
inverts all rotations. Fixing their fourth powers would force the full
unit group to have exponent dividing eight, impossible for fields of
order greater than nine. The actor thus lies in the torus itself.
Source application: Aschbacher–Smith E.2.7, printed pp.218–219.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2
 theorem linear_centralizer_mem_split_torus_of_fourth_fixed
    {F : Type*} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (hlarge : 9 < Nat.card F)
    (x : PGammaL2 F) (hf : x.right = 1)
    (hx : Commute x (SemidirectProduct.inl (pGammaL2FullSplitTorus F (-1))))
    (hfix : ∀ a : Fˣ, Commute x ((SemidirectProduct.inl (pGammaL2FullSplitTorus F a) : PGammaL2 F) ^ 4)) :
    x ∈ ((SemidirectProduct.inl : PGL2 F →* PGammaL2 F).comp (pGammaL2FullSplitTorus F)).range := by
  have hleft : x.left ∈ centralizer ({pGammaL2FullSplitTorus F (-1)} : Set (PGL2 F)) := by
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg SemidirectProduct.left hx.eq
    simpa only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, hf, map_one, MulAut.one_apply] using hh
  obtain ⟨w, _, _, _, _, hw, hw2, hwi, hc, _⟩ := pgl2_fullSplitTorus_centralizer_data F hF
  rw [hc] at hleft
  obtain ⟨u, hu, he | he⟩ := (mem_sup_zpowers_of_involution_inverts hw hw2 hwi).mp hleft
  · obtain ⟨a, ha⟩ := hu
    refine ⟨a, ?_⟩
    apply SemidirectProduct.ext
    · exact ha.trans he.symm
    · exact hf.symm
  · exfalso
    obtain ⟨a, ha⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic Fˣ)
    have hcomm : Commute x.left (pGammaL2FullSplitTorus F (a ^ 4)) := by
      have hh : Commute x (SemidirectProduct.inl (pGammaL2FullSplitTorus F (a ^ 4))) := by
        simpa only [map_pow] using hfix a
      have hh' := congrArg SemidirectProduct.left hh.eq
      change x.left * (pGammaL2FullSplitTorus F (a ^ 4)) = _
      simpa only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
        SemidirectProduct.right_inl, hf, map_one, MulAut.one_apply] using hh'
    have hinv : x.left * pGammaL2FullSplitTorus F (a ^ 4) * x.left⁻¹ =
        (pGammaL2FullSplitTorus F (a ^ 4))⁻¹ := by
      rw [he]
      calc
        (u * w) * pGammaL2FullSplitTorus F (a ^ 4) * (u * w)⁻¹ =
            u * (w * pGammaL2FullSplitTorus F (a ^ 4) * w⁻¹) * u⁻¹ := by group
        _ = u * (pGammaL2FullSplitTorus F (a ^ 4))⁻¹ * u⁻¹ := by rw [hwi _ ⟨_, rfl⟩]
        _ = _ := by
          obtain ⟨b, rfl⟩ := hu
          simp only [← map_inv, ← map_mul]
          congr 1
          simp [mul_comm, mul_left_comm]
    have heq : pGammaL2FullSplitTorus F (a ^ 4) = (pGammaL2FullSplitTorus F (a ^ 4))⁻¹ := by
      simpa only [hcomm.eq, mul_inv_cancel_right] using hinv
    have heq' : a ^ 4 = (a ^ 4)⁻¹ :=
      pGammaL2FullSplitTorus_injective F (by simpa only [map_inv] using heq)
    have height : a ^ 8 = 1 := by
      calc
        a ^ 8 = a ^ 4 * a ^ 4 := by rw [← pow_add]
        _ = (a ^ 4)⁻¹ * a ^ 4 := by rw [← heq']
        _ = 1 := inv_mul_cancel _
    have hd := orderOf_dvd_of_pow_eq_one height
    rw [ha, Nat.card_units] at hd
    have hb := Nat.le_of_dvd (by decide : 0 < 8) hd
    omega
end Theory.PSL2
