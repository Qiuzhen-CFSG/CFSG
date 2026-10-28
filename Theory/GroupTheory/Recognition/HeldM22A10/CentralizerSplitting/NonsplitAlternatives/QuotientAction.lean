module

public import Theory.GroupTheory.Recognition.HeldM22A10.LocalStructure
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.BinaryReduction

/-!
# The quotient action before splitting the Held centralizer

Conjugation on the normal elementary kernel F factors through the actual
quotient H/F, giving an S4-action on F and, after choosing a basis, on binary
four-space. No complement is used. The image of the chosen local Sylow group
has precisely two fixed vectors, the identity and the distinguished central
involution. Both are fixed by the whole quotient as well.

The fixed-point argument lifts a fixed kernel element into the cyclic center
of the original Sylow group. A nonidentity such element has order two, so
uniqueness of its involution identifies it with the specified one. This is
an unconditional reduction of the extension problem, not a classification of
the action or of the group extension.

Source: Huppert--Blackburn, *Finite Groups III*, XII.1.18(b), printed p.314.
The cited Held (1968) splitting theorem is still to be proved. Binary basis
coordinates are reused from the independent `BinaryReduction` definition;
none of its theorems requiring a complement is invoked here.
-/

open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.HeldM22A10
namespace LocalData
universe u
variable {G : Type u} [Group G] (D : LocalData G)

/-- The actual projection of the centralizer onto its specified symmetric quotient. -/
@[expose] public noncomputable def extensionQuotient : D.centralizer →* LocalModelDichotomy.SymmetricFour := by
  let := D.kernel_normal
  exact D.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' D.kernel)

/-- The actual quotient projection is surjective. -/
public theorem extensionQuotient_surjective : Function.Surjective D.extensionQuotient := by
  let := D.kernel_normal
  exact D.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective D.kernel)

/-- The kernel of the specified quotient projection is precisely F. -/
public theorem extensionQuotient_ker : D.extensionQuotient.ker = D.kernel := by
  let := D.kernel_normal
  ext h
  change D.quotientEquiv (QuotientGroup.mk' D.kernel h) = 1 ↔ h ∈ D.kernel
  rw [EmbeddingLike.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff h

/-- Conjugation by the full centralizer on its normal elementary kernel. -/
@[expose] public def extensionConjugation : D.centralizer →* MulAut D.kernel := by
  let := D.kernel_normal
  exact MulAut.conjNormal

/-- The kernel action is the original conjugation inside the centralizer. -/
public theorem extensionConjugation_apply (h : D.centralizer) (f : D.kernel) :
    (D.extensionConjugation h f : D.centralizer) = h * f * h⁻¹ := rfl

private theorem kernel_le_extensionConjugation_ker : D.kernel ≤ D.extensionConjugation.ker := by
  let := D.kernel_elementary
  intro f hf
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change f * x * f⁻¹ = x
  have hcomm : f * (x : D.centralizer) = x * f :=
    congrArg Subtype.val (mul_comm (⟨f, hf⟩ : D.kernel) x)
  rw [hcomm, mul_inv_cancel_right]

/-- The S4-action obtained by descending conjugation through the abelian kernel. -/
@[expose] public noncomputable def quotientKernelAction : LocalModelDichotomy.SymmetricFour →* MulAut D.kernel := by
  let := D.kernel_normal
  exact (QuotientGroup.lift D.kernel D.extensionConjugation
    (by exact D.kernel_le_extensionConjugation_ker)).comp D.quotientEquiv.symm.toMonoidHom

/-- The descended action agrees with conjugation by every lift. -/
public theorem quotientKernelAction_quotient (h : D.centralizer) :
    D.quotientKernelAction (D.extensionQuotient h) = D.extensionConjugation h := by
  let := D.kernel_normal
  change QuotientGroup.lift D.kernel D.extensionConjugation D.kernel_le_extensionConjugation_ker
    (D.quotientEquiv.symm (D.quotientEquiv (QuotientGroup.mk' D.kernel h))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The quotient action transported to binary four-space without a complement. -/
@[expose] public noncomputable def quotientBinaryAction [Finite G] :
    LocalModelDichotomy.SymmetricFour →* MulAut LocalModelDichotomy.BinaryFour :=
  (MulAut.congr D.kernelBinaryEquiv).toMonoidHom.comp D.quotientKernelAction

/-- Binary coordinates intertwine the two quotient actions. -/
public theorem quotientBinaryAction_apply [Finite G]
    (s : LocalModelDichotomy.SymmetricFour) (f : D.kernel) :
    D.quotientBinaryAction s (D.kernelBinaryEquiv f) =
      D.kernelBinaryEquiv (D.quotientKernelAction s f) := by
  change D.kernelBinaryEquiv (D.quotientKernelAction s
    (D.kernelBinaryEquiv.symm (D.kernelBinaryEquiv f))) = _
  rw [MulEquiv.symm_apply_apply]

/-- The binary action of a quotient element is conjugation by its lift. -/
public theorem quotientBinaryAction_quotient [Finite G] (h : D.centralizer) (f : D.kernel) :
    D.quotientBinaryAction (D.extensionQuotient h) (D.kernelBinaryEquiv f) =
      D.kernelBinaryEquiv (D.extensionConjugation h f) := by
  change D.kernelBinaryEquiv
    (D.quotientKernelAction (D.extensionQuotient h)
      (D.kernelBinaryEquiv.symm (D.kernelBinaryEquiv f))) = _
  rw [MulEquiv.symm_apply_apply, D.quotientKernelAction_quotient]

/-- The Sylow two-subgroup obtained by projecting the given local Sylow subgroup. -/
@[expose] public noncomputable def quotientSylow [Finite G] : Sylow 2 LocalModelDichotomy.SymmetricFour :=
  D.localSylow.mapSurjective D.extensionQuotient_surjective

/-- The specified central involution viewed inside the elementary kernel. -/
@[expose] public def kernelInvolution : D.kernel := ⟨D.centralInvolution, D.centralInvolution_mem_kernel⟩

/-- The distinguished kernel element is nonidentity. -/
public theorem kernelInvolution_ne_one : D.kernelInvolution ≠ 1 := by
  intro h
  exact D.z_ne_one (congrArg (fun x : D.kernel => ((x : D.centralizer) : G)) h)

/-- Every quotient element fixes the distinguished kernel involution. -/
public theorem quotientKernelAction_fix_involution (s : LocalModelDichotomy.SymmetricFour) :
    D.quotientKernelAction s D.kernelInvolution = D.kernelInvolution := by
  obtain ⟨h, rfl⟩ := D.extensionQuotient_surjective s
  rw [D.quotientKernelAction_quotient]
  apply Subtype.ext
  rw [D.extensionConjugation_apply]
  change h * D.centralInvolution * h⁻¹ = D.centralInvolution
  rw [mem_center_iff.mp D.centralInvolution_mem_center h, mul_inv_cancel_right]

/-- The quotient Sylow group fixes exactly the two elements on the central line. -/
public theorem quotientSylow_fixed_iff [Finite G] (f : D.kernel) :
    (∀ s : D.quotientSylow, D.quotientKernelAction s f = f) ↔
      f = 1 ∨ f = D.kernelInvolution := by
  constructor
  · intro hf
    by_cases hf1 : f = 1
    · exact Or.inl hf1
    · right
      have hfT : ((f : D.centralizer) : G) ∈ D.sylow :=
        D.kernel_le_localSylow f.property
      let fT : D.sylow := ⟨f, hfT⟩
      have hfZ : fT ∈ center D.sylow := by
        apply mem_center_iff.mpr
        intro t
        let tH : D.centralizer := ⟨t, D.sylow_le_centralizer t.property⟩
        have htP : D.extensionQuotient tH ∈ D.quotientSylow :=
          mem_map.mpr ⟨tH, t.property, rfl⟩
        have h := hf ⟨D.extensionQuotient tH, htP⟩
        rw [D.quotientKernelAction_quotient] at h
        have hc := congrArg (fun x : D.kernel => (x : D.centralizer)) h
        rw [D.extensionConjugation_apply] at hc
        have hc' : tH * (f : D.centralizer) = f * tH := mul_inv_eq_iff_eq_mul.mp hc
        exact Subtype.ext (congrArg (fun x : D.centralizer => (x : G)) hc')
      have hf2 : orderOf f = 2 := by
        let := D.kernel_elementary
        exact orderOf_eq_prime
          (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p 2 D.kernel) f) hf1
      have hfZ2 : orderOf (⟨fT, hfZ⟩ : center D.sylow) = 2 := by
        simpa only [Subgroup.orderOf_mk, fT, Subgroup.orderOf_coe] using hf2
      have he := D.involution_unique ⟨fT, hfZ⟩ hfZ2
      apply Subtype.ext
      exact Subtype.ext (congrArg (fun x : center D.sylow => ((x : D.sylow) : G)) he)
  · rintro (rfl | rfl) s
    · exact map_one _
    · exact D.quotientKernelAction_fix_involution s

/-- In binary coordinates, the Sylow fixed vectors form the distinguished line. -/
public theorem quotientBinaryAction_fixed_iff [Finite G] (v : LocalModelDichotomy.BinaryFour) :
    (∀ s : D.quotientSylow, D.quotientBinaryAction s v = v) ↔
      v = 1 ∨ v = D.kernelBinaryEquiv D.kernelInvolution := by
  obtain ⟨f, rfl⟩ := D.kernelBinaryEquiv.surjective v
  simp only [D.quotientBinaryAction_apply, D.kernelBinaryEquiv.injective.eq_iff,
    EmbeddingLike.map_eq_one_iff]
  exact D.quotientSylow_fixed_iff f

/-- The fixed space of the quotient Sylow group has order two. -/
public theorem quotientBinaryAction_fixed_card [Finite G] :
    Nat.card {v : LocalModelDichotomy.BinaryFour //
      ∀ s : D.quotientSylow, D.quotientBinaryAction s v = v} = 2 := by
  let oneFixed : {v : LocalModelDichotomy.BinaryFour //
      ∀ s : D.quotientSylow, D.quotientBinaryAction s v = v} := ⟨1, fun _ => map_one _⟩
  apply (Nat.card_eq_two_iff' oneFixed).mpr
  let zFixed : {v : LocalModelDichotomy.BinaryFour //
      ∀ s : D.quotientSylow, D.quotientBinaryAction s v = v} :=
    ⟨D.kernelBinaryEquiv D.kernelInvolution,
      (D.quotientBinaryAction_fixed_iff _).mpr (Or.inr rfl)⟩
  have hz : zFixed ≠ oneFixed := by
    intro h
    have he : D.kernelBinaryEquiv D.kernelInvolution = 1 := congrArg Subtype.val h
    exact D.kernelInvolution_ne_one (D.kernelBinaryEquiv.injective (he.trans D.kernelBinaryEquiv.map_one.symm))
  refine ⟨zFixed, hz, ?_⟩
  intro y hy
  rcases (D.quotientBinaryAction_fixed_iff y.val).mp y.property with h | h
  · exact (hy (Subtype.ext h)).elim
  · exact Subtype.ext h

/-- The entire quotient has the same fixed line as its chosen Sylow subgroup. -/
public theorem quotientBinaryAction_fixed_all_iff [Finite G] (v : LocalModelDichotomy.BinaryFour) :
    (∀ s : LocalModelDichotomy.SymmetricFour, D.quotientBinaryAction s v = v) ↔
      v = 1 ∨ v = D.kernelBinaryEquiv D.kernelInvolution := by
  constructor
  · intro hv
    exact (D.quotientBinaryAction_fixed_iff v).mp (fun s => hv s)
  · rintro (rfl | rfl) s
    · exact map_one _
    · change D.kernelBinaryEquiv (D.quotientKernelAction s
        (D.kernelBinaryEquiv.symm (D.kernelBinaryEquiv D.kernelInvolution))) = _
      rw [MulEquiv.symm_apply_apply, D.quotientKernelAction_fix_involution]

/-- The fixed space of the entire symmetric quotient has order two. -/
public theorem quotientBinaryAction_fixed_all_card [Finite G] :
    Nat.card {v : LocalModelDichotomy.BinaryFour //
      ∀ s : LocalModelDichotomy.SymmetricFour, D.quotientBinaryAction s v = v} = 2 := by
  let e : {v : LocalModelDichotomy.BinaryFour //
      ∀ s : LocalModelDichotomy.SymmetricFour, D.quotientBinaryAction s v = v} ≃
      {v : LocalModelDichotomy.BinaryFour //
      ∀ s : D.quotientSylow, D.quotientBinaryAction s v = v} :=
    Equiv.subtypeEquivRight (fun v => by
      rw [D.quotientBinaryAction_fixed_all_iff, D.quotientBinaryAction_fixed_iff])
  exact (Nat.card_congr e).trans D.quotientBinaryAction_fixed_card

end LocalData
end Theory.GroupTheory.HeldM22A10
