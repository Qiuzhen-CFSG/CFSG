module

public import CFSG.Quasithin.ChapterE.Section03.Parameters
public import Theory.GroupTheory.Commutator.NormalClosure

/-!
# The terminal Case-II critical-pair contradiction

For the literal conjugates V and W = Vᵍ, the source critical pair gives
hyperplanes A = V ∩ Qγ and B = W ∩ QH which centralize one another.
The bound s(G,V) > 1 makes E.3.6 apply first to A and then to B; hence
all of V and W centralize one another, contradicting the selected pair.
The layer-bound consumer obtains the hyperplane commutator from the two
15.2.28 bounds and the trivial intersection of the endpoint centers.

These are the final deductions on printed p.1120 of Aschbacher--Smith,
*The Classification of Quasithin Groups*, combined manuscript (1 March
2004). The original critical-pair construction, the corank-one bounds,
and the earlier 15.2.26--28 source inputs remain with the source assembly.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterE

variable {G : Type*} [Group G] [Finite G]

/-- The last two E.3.6 applications in the original Case-II argument. -/
theorem source_critical_pair_false
    (V QH : Subgroup G) [IsElementaryAbelian 2 V] (g : G)
    (hs : 1 < globalS V)
    (hfirst : subgroupCorank V (V ⊓ QH.map (MulAut.conj g).toMonoidHom) ≤ 1)
    (hsecond : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom ⊓ QH) ≤ 1)
    (hcomm : ⁅V ⊓ QH.map (MulAut.conj g).toMonoidHom,
      V.map (MulAut.conj g).toMonoidHom ⊓ QH⁆ = ⊥)
    (hmove : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) : False := by
  let W := V.map (MulAut.conj g).toMonoidHom
  let A := V ⊓ QH.map (MulAut.conj g).toMonoidHom
  let B := W ⊓ QH
  let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hA : (subgroupCorank V A : ℕ∞) < globalS V :=
    (show (subgroupCorank V A : ℕ∞) ≤ 1 by exact_mod_cast hfirst).trans_lt hs
  have hB : (subgroupCorank W B : ℕ∞) < globalS W := by
    rw [globalS_map_equiv]
    exact (show (subgroupCorank W B : ℕ∞) ≤ 1 by exact_mod_cast hsecond).trans_lt hs
  have hBA : B ≤ centralizer (A : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have heqB := centralizer_inf_eq_of_corank_lt_globalS
    (V := V) (B := A) (E := B) inf_le_left hA
    (IsElementaryAbelian.isPGroup 2 W).to_inf_left
  have hBV : B ≤ centralizer (V : Set G) := by
    have he : B ⊓ centralizer (V : Set G) = B :=
      heqB.symm.trans (inf_eq_left.mpr hBA)
    exact inf_eq_left.mp he
  have heqV := centralizer_inf_eq_of_corank_lt_globalS
    (V := W) (B := B) (E := V) inf_le_left hB
    (IsElementaryAbelian.isPGroup 2 V)
  have hVB : V ≤ centralizer (B : Set G) := le_centralizer_iff.mpr hBV
  have hVW : V ≤ centralizer (W : Set G) := by
    have he : V ⊓ centralizer (W : Set G) = V :=
      heqV.symm.trans (inf_eq_left.mpr hVB)
    exact inf_eq_left.mp he
  exact hmove (commutator_eq_bot_iff_le_centralizer.mpr hVW)

/-- Apply the terminal contradiction to the literal normal-closure layers.
The two 15.2.28 bounds and the disjoint endpoint centers discharge the
commuting-hyperplanes input. -/
theorem source_critical_pair_false_of_layer_bounds
    (V QH UH ZS : Subgroup G) [IsElementaryAbelian 2 V] (g : G)
    (hs : 1 < globalS V) (hVU : V ≤ UH)
    (hfirst : subgroupCorank V (V ⊓ QH.map (MulAut.conj g).toMonoidHom) ≤ 1)
    (hsecond : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom ⊓ QH) ≤ 1)
    (hleft : ⁅UH, UH.map (MulAut.conj g).toMonoidHom ⊓ QH⁆ ≤ ZS)
    (hright : ⁅UH.map (MulAut.conj g).toMonoidHom,
      UH ⊓ QH.map (MulAut.conj g).toMonoidHom⁆ ≤
      ZS.map (MulAut.conj g).toMonoidHom)
    (hcenters : ZS ⊓ ZS.map (MulAut.conj g).toMonoidHom = ⊥)
    (hmove : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) : False := by
  apply source_critical_pair_false V QH g hs hfirst hsecond ?_ hmove
  apply bot_unique
  rw [← hcenters]
  refine le_inf ((commutator_mono (inf_le_left.trans hVU)
    (inf_le_inf_right QH (Subgroup.map_mono hVU))).trans hleft) ?_
  rw [commutator_comm]
  exact (commutator_mono (inf_le_left.trans (Subgroup.map_mono hVU))
    (inf_le_inf_right _ hVU)).trans hright

end CFSG.Quasithin.Chapter15.Section02
