module
public import GorensteinWalter.PGammaL2PureFieldComplement

/-!
# The actual linear layer and pure field complement

Let A be a subgroup of PGammaL2 over a finite field of odd order, containing
the canonical PSL2 layer and having odd field-automorphism image. Its actual
linear kernel is normal and isomorphic to PSL2 or PGL2. It has a cyclic
odd-order complement whose image is exactly the corresponding pure
coefficient-automorphism subgroup.

The model theorem identifies the same kernel appearing in the proved
pure-field complement theorem. Combining them preserves both the concrete
subgroup and the field action, as required in Alperin--Brauer--Gorenstein,
II.3 Proposition 4(i)–(iii), article p28. No additional condition on the
field order excludes three or nine. Sylow centralization is a separate
input in the source assembly.
-/

namespace GorensteinWalter
universe u

public theorem pGammaL2_linear_decomposition (K : Type u) [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (A : Subgroup (PGammaL2 K)) [Finite A]
    (hPSL : pGammaL2PSLRange K ≤ A)
    (hodd : Odd (Nat.card (pGammaL2FieldProjection K A).range)) :
    (pGammaL2LinearKernel K A).Normal ∧
      (Nonempty (pGammaL2LinearKernel K A ≃* PSL2 K) ∨
        Nonempty (pGammaL2LinearKernel K A ≃* PGL2 K)) ∧
      ∃ E : Subgroup A, (pGammaL2LinearKernel K A).IsComplement' E ∧
        IsCyclic E ∧ Odd (Nat.card E) ∧
        E.map A.subtype = (pGammaL2FieldProjection K A).range.map
          (SemidirectProduct.inr : (K ≃+* K) →* PGammaL2 K) := by
  exact ⟨inferInstance, pGammaL2_linear_kernel_model K hK A hPSL, pGammaL2_exists_pure_field_complement K hK A hPSL hodd⟩

end GorensteinWalter

