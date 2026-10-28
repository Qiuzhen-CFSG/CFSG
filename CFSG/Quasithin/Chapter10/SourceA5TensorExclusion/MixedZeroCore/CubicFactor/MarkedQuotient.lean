module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.MixedZeroCore.CubicFactor.QuotientCharacters
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.MixedZeroCore.CubicFactor.Exchange

/-!
# The original Cartan marking and mixed cubic factor

Both cubic characters have been constructed on the literal Cartan–Sylow
join with kernel its actual two-core. Equal coordinate signs would make
conjugation a scalar power on the image torus. The original factor-exchange
calculation rules this out for every t outside N_G(L), completing the
CartanPairMarking without a marking or field–swap assumption.

The existing factor-lifting theorem now gives MixedCubicFactorInput under
its full original contract. Its literal 9.3.1 application centralizes the
tensor line conditional only on MixedSizeInput. That remaining bound is
owned by qt-d-tensor-mixed-size-bound; final line-centralization assembly
stays with qt-d-tensor-mixed-zero-core.
Source: Aschbacher–Smith, original 9.3.1–2, printed pp.732–733.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

/-- Factor exchange forces opposite signs in every faithful marking of the two cubic directions. -/
theorem cartan_pair_exchange_sign (A : Subgroup G)
    (hAB : A ≤ sourceOrbitBorel T L) (hA9 : Nat.card A = 9)
    (q : (A ⊔ (T : Subgroup G) : Subgroup G) →*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (hk : q.ker = pCore 2 (A ⊔ (T : Subgroup G) : Subgroup G))
    (hA : (A.subgroupOf (A ⊔ (T : Subgroup G))).map q =
      (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3)))
    (t : T) (htn : (t : G) ∉ normalizer (L : Set G)) :
    Equiv.Perm.sign (q (inclusion le_sup_right t)).1 ≠
      Equiv.Perm.sign (q (inclusion le_sup_right t)).2 := by
  intro he
  obtain ⟨n,hn⟩ := CubicPairCharacters.equal_signs_common_power
    (q (inclusion le_sup_right t)).1 (q (inclusion le_sup_right t)).2 he
  apply m.cartan_exchange_not_scalar A hAB hA9 t htn n
  intro a
  apply QuotientGroup.eq_iff_div_mem.mpr
  rw [←hk,MonoidHom.mem_ker,map_div,map_mul,map_mul,map_inv,map_pow]
  apply div_eq_one.mpr
  have hqa : q (inclusion le_sup_left a) ∈
      (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3)) :=
    hA ▸ mem_map_of_mem q a.property
  exact hn _ hqa

/-- The actual source hypotheses construct the Cartan marking, including
its field-exchange signs; no quotient or factor witness is assumed. -/
theorem mixedCartanPairInput : m.MixedCartanPairInput := by
  intro H hH _ _ A B hAB hA9 hAe hBA _ hB3 _ hBC _ hmove
  obtain ⟨q,hk,hA,hB,hline⟩ := m.exists_cartan_pair_characters
    hH A B hAB hA9 hAe hBA hB3 hBC hmove
  exact ⟨{
    quotient := q
    kernel_eq := hk
    cartan_image := hA
    hall_image := hB
    line_kernel := hline
    exchange_sign := m.cartan_pair_exchange_sign A hAB hA9 q hk hA }⟩

/-- Original 9.3.1's cubic factor is now constructed from the source setup. -/
theorem mixedCubicFactorInput : m.MixedCubicFactorInput :=
  m.mixedCubicFactorInput_of_cartanPairInput m.mixedCartanPairInput

/-- The exact line-centralization consumer now retains only the separately
owned mixed A₅/S₃ size theorem. Its final discharge remains with this task. -/
theorem old_residual_centralizes_tensorLine_of_mixed_size
    (size : MixedZeroCore.MixedSizeInput G)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < ChapterE.generationParameter H) :
    (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G) :=
  m.old_residual_centralizes_tensorLine_of_mixed_inputs size m.mixedCubicFactorInput hH hlarge

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
