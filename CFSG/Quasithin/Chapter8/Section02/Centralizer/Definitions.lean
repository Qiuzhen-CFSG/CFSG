module

public import CFSG.Quasithin.Chapter8.Section02.NormalClosure
public import Theory.GroupTheory.SolvableResidual

/-!
# The literal subgroups in the involution-centralizer calculation

We form L_z as the perfect residual of L ∩ C_G(z), take its intrinsic
two-core, and form V_z=[V,O₂(L_z)]. The closure E is taken inside C_G(z).
Abelianness and normalization of V justify the subgroup restrictions and
ambient maps. The crossing argument then uses relative normality to force
E outside Q_M when V_z has a conjugate in A crossing A∩Q_M=U.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), §8.2,
Lemmas 8.2.11–12, printed p.722 (PDF p.739). These are constructions and
conditional deductions; their source local-action premises remain to be proved.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter8.Section02.Centralizer
open Subgroup
noncomputable section

variable {G : Type*} [Group G]

/-- The source L_z = C_L(z)^∞, mapped back to the ambient group. -/
def localResidual (L : Subgroup G) (z : G) : Subgroup G :=
  (solvableResidual (L ⊓ centralizer ({z} : Set G) : Subgroup G)).map
    (L ⊓ centralizer ({z} : Set G)).subtype

/-- The intrinsic two-core of L_z, with its original ambient embedding. -/
def localTwoCore (L : Subgroup G) (z : G) : Subgroup G :=
  (pCore 2 (localResidual L z)).map (localResidual L z).subtype

/-- The source commutator V_z = [V,O₂(L_z)]. -/
def commutatorSpace (L V : Subgroup G) (z : G) : Subgroup G :=
  ⁅V, localTwoCore L z⁆

/-- The source E is formed inside C_G(z), never as a normal closure in G. -/
def sourceClosure (L V : Subgroup G) (z : G) :
    Subgroup (centralizer ({z} : Set G)) :=
  centralizerClosure z ((commutatorSpace L V z).subgroupOf (centralizer ({z} : Set G)))

/-- Normality is relative to the literal involution centralizer. -/
instance sourceClosure_normal (L V : Subgroup G) (z : G) :
    (sourceClosure L V z).Normal := by
  change (centralizerClosure z _).Normal
  infer_instance

theorem localResidual_le (L : Subgroup G) (z : G) :
    localResidual L z ≤ L ⊓ centralizer ({z} : Set G) := by
  rintro x ⟨y, hy, rfl⟩
  exact y.property

theorem localTwoCore_le (L : Subgroup G) (z : G) :
    localTwoCore L z ≤ localResidual L z := by
  rintro x ⟨y, hy, rfl⟩
  exact y.property

theorem commutatorSpace_le (L V : Subgroup G) (z : G)
    (hn : L ≤ normalizer (V : Set G)) : commutatorSpace L V z ≤ V := by
  exact le_normalizer_iff_commutator_le_left.mp
    (((localTwoCore_le L z).trans ((localResidual_le L z).trans inf_le_left)).trans hn)

theorem commutatorSpace_le_centralizer (L V : Subgroup G) [IsMulCommutative V]
    (z : G) (hz : z ∈ V) (hn : L ≤ normalizer (V : Set G)) :
    commutatorSpace L V z ≤ centralizer ({z} : Set G) := by
  intro x hx
  exact mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mul_comm' (⟨x, commutatorSpace_le L V z hn hx⟩ : V) ⟨z, hz⟩))

/-- Every literal commutator lies in the ambient image of E. This discharges
the subgroup-transport step needed by the final fusion application. -/
theorem commutatorSpace_le_sourceClosure (L V : Subgroup G) [IsMulCommutative V]
    (z : G) (hz : z ∈ V) (hn : L ≤ normalizer (V : Set G)) :
    commutatorSpace L V z ≤ (sourceClosure L V z).map (centralizer ({z} : Set G)).subtype := by
  intro x hx
  refine ⟨⟨x, commutatorSpace_le_centralizer L V z hz hn hx⟩, ?_, rfl⟩
  exact le_normalClosure hx

/-- The crossing argument in the second paragraph of 8.2.12. A conjugate of
V_z lying in A but not in U=A∩Q_M forces E to escape Q_M. Relative normality
is used only inside C_G(z); the conjugator centralizes the source U. -/
theorem sourceClosure_not_le_of_crossing
    (L V U A QM : Subgroup G) [IsMulCommutative V]
    (z h : G) (hzV : z ∈ V) (hzU : z ∈ U)
    (hn : L ≤ normalizer (V : Set G))
    (hh : h ∈ centralizer (U : Set G)) (hcap : A ⊓ QM = U)
    (hconj : (commutatorSpace L V z).map (MulAut.conj h).toMonoidHom ≤ A)
    (hnot : ¬ commutatorSpace L V z ≤ U) :
    ¬ (sourceClosure L V z).map (centralizer ({z} : Set G)).subtype ≤ QM := by
  intro hEQ
  apply hnot
  intro v hv
  let hc : centralizer ({z} : Set G) :=
    ⟨h, mem_centralizer_singleton_iff.mpr (hh z hzU).symm⟩
  let vc : centralizer ({z} : Set G) :=
    ⟨v, commutatorSpace_le_centralizer L V z hzV hn hv⟩
  have hvE : vc ∈ sourceClosure L V z := le_normalClosure hv
  have hgE : hc * vc * hc⁻¹ ∈ sourceClosure L V z :=
    (inferInstance : (sourceClosure L V z).Normal).conj_mem vc hvE hc
  have hgQ : h * v * h⁻¹ ∈ QM := hEQ ⟨hc * vc * hc⁻¹, hgE, rfl⟩
  have hgA : h * v * h⁻¹ ∈ A := hconj (mem_map_of_mem _ hv)
  have hgU : h * v * h⁻¹ ∈ U := hcap ▸ (show h * v * h⁻¹ ∈ A ⊓ QM from ⟨hgA, hgQ⟩)
  exact ((centralizer_le_normalizer (U : Set G) hh) v).mpr hgU

end
end CFSG.Quasithin.Chapter8.Section02.Centralizer
