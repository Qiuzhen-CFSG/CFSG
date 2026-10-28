module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Transfer.Model
public import Theory.GroupTheory.FourGroupCentralizerOddCore

/-!
# Local fusion input to Held's transfer calculation

`TransferFusion` records an actual order-32 Sylow subgroup, an isomorphism
from C2 × C2 × D8, and the conjugacy information about p on printed p.233.
The two known reflection classes occur; only the final pair zlm,pzlm is
left undecided. The centralizer is the actual ambient C_K(p).

The source application must construct this data in Q = C_G(mu)/<mu> from
D,e and nonfusion, including the permitted lambda and xi changes. This
interface makes no existence assertion and assumes no transfer kernel.

The known fused four-group already proves that the odd core of K is trivial.
Source: Held, Illinois J. Math. 13 (1969), 224--240, pp.233--234,
DOI 10.1215/ijm/1256053756, proof of Lemma 4.2.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
universe u
open TransferModel (Model l z t m R m_conj_lt)

public structure TransferFusion (K : Type u) [Group K] (p : K) where
  sylow : Sylow 2 K
  coordinates : Model ≃* sylow
  mark_p : (coordinates TransferModel.p : K) = p
  centralizer_eq : centralizer ({p} : Set K) = (sylow : Subgroup K)
  conj_lt : IsConj p (coordinates (l * t) : K)
  conj_zm : IsConj p (coordinates (z * m) : K)
  class_bound : ∀ x : Model, IsConj p (coordinates x : K) →
    x = TransferModel.p ∨ x = l * t ∨ x = TransferModel.p * (l * t) ∨
    x = z * m ∨ x = TransferModel.p * (z * m) ∨
    x = z * l * m ∨ x = TransferModel.p * (z * l * m)

namespace TransferFusion
variable {K : Type u} [Group K] {p : K} (F : TransferFusion K p)

@[expose] public def into : Model →* K := (F.sylow : Subgroup K).subtype.comp F.coordinates.toMonoidHom

public theorem into_injective : Function.Injective F.into :=
  Subtype.val_injective.comp F.coordinates.injective

public theorem into_p : F.into TransferModel.p = p := F.mark_p

include F

public theorem p_order : orderOf p = 2 := by
  rw [← F.into_p, orderOf_injective F.into F.into_injective, TransferModel.p_order]

public theorem oddCore [Finite K] : pPrimeCore 2 K = ⊥ := by
  have hc : IsPGroup 2 (centralizer ({p} : Set K)) := by
    rw [F.centralizer_eq]
    exact F.sylow.isPGroup'
  apply pPrimeCore_eq_bot_of_fused_involutions p (F.into (l * t)) F.p_order F.conj_lt _ hc
  apply F.conj_lt.trans
  refine isConj_iff.mpr ⟨F.into m, ?_⟩
  change F.into m * F.into (l * t) * (F.into m)⁻¹ = p * F.into (l * t)
  rw [← map_inv, ← map_mul, ← map_mul, m_conj_lt, map_mul, F.into_p]

end TransferFusion
end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
