module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.ModelTransport
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.QuotientObstructions
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.Levi

/-!
# The two dimension-five contradictions in 13.8.25

For a marked single node, add a nonadjacent node and use its constructed
S₃ × S₃ quotient. The solvable lift lies in M by 13.8.13. Its second cubic
factor contradicts the theta identity for L₁.

For the marked pair, transport the source normalizer restriction. The
intrinsic normalizer calculation chooses a strictly larger two-space or
three-space stabilizer. Its lift belongs to Hz, and its S₃ × PSL₃(2)
quotient retains L₁,+ outside the simple factor, contradicting uniform
13.8.21(1). All overgroups and quotient maps in these deductions are
constructed from the given whole-group model and source node markings.

Source: Aschbacher–Smith 13.8.25, printed pp.959–960 (PDF pp.976–977),
combined manuscript of 1 March 2004. Identifying the actual L₁, L₀ and
L₁,+ with these nodes, proving H ∩ M = L₁T, and deriving the starred
normalizer restriction are still obligations of source assembly. These
conditional deductions do not assert the complete parabolic reduction.
-/

public section

open Subgroup BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

variable {G : Type*} [Group G] [Finite G]

/-- The single-node source case is impossible in dimension five. The strict
solvable overgroup, its S₃ × S₃ quotient, and its marked residual images are
constructed; only identification of the source single node is an input. -/
theorem exclude_five_single_node (L₁ T G₁ M H : Subgroup G)
    (hH : H ∈ Source.Hz L₁ T G₁ M)
    (e : Source.Hstar H ≃* LinearGroup 5) (b : FiveBasis) (i : Fin 4)
    (hbase : (Source.starImage H (L₁ ⊔ T)).map e.toMonoidHom = fiveParabolic b {i})
    (hresidual : (Source.starImage H L₁).map e.toMonoidHom = fiveNodeResidual b i)
    (htheta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (h13 : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M) : False := by
  obtain ⟨j, _, hlt, hsol, a, hfirst, _⟩ := five_single_node_levi_overgroup b i
  let P := fiveParabolic b {i, j}
  have hbaseY : L₁ ⊔ T ≤ modelLift H e P := by
    apply (le_modelLift_iff H _ hH.1.2 e P).mpr
    rw [hbase]
    exact hlt.le
  let := hsol
  apply exclude_solvable_marked_product L₁ T G₁ M H (modelLift H e P) hH
    (modelLift_le H e P) hbaseY htheta h13 (modelLift_solvable H e P)
    ((modelLiftQuotientEquiv H e P).trans a)
  rw [modelLiftQuotientEquiv_image H L₁ e P a (le_sup_left.trans hbaseY), hresidual]
  exact hfirst.le.trans (Subgroup.prod_mono le_top le_rfl)

/-- The ordered marked two-node source case is impossible in dimension five.
The normalizer calculation selects the two-space or three-space stabilizer;
its full inverse image is in Hz and has the constructed S₃ × PSL₃(2)
quotient. The marked L₁,+ image violates uniform 13.8.21(1). -/
theorem exclude_five_marked_pair (L₁ L₀ L₁plus T G₁ M H : Subgroup G)
    (hH : H ∈ Source.Hz L₁ T G₁ M)
    (e : Source.Hstar H ≃* LinearGroup 5) (b : FiveBasis) (beta delta : Fin 4)
    (hgap : beta.val + 1 < delta.val ∨ delta.val + 1 < beta.val)
    (hbase : (Source.starImage H (L₁ ⊔ T)).map e.toMonoidHom =
      fiveParabolic b {beta, delta})
    (hzero : (Source.starImage H L₀).map e.toMonoidHom = fiveNodeResidual b beta)
    (hplus : (Source.starImage H L₁plus).map e.toMonoidHom = fiveNodeResidual b delta)
    (hplusL : L₁plus ≤ L₁)
    (hn : normalizer (Source.starImage H L₀ : Set (Source.Hstar H)) ≤
      normalizer (Source.starImage H L₁plus : Set (Source.Hstar H)))
    (hinter : H ⊓ M = L₁ ⊔ T) (hcore : Source.QH H ≤ T)
    (h21 : ∀ (Y D : Subgroup G), Y ∈ Source.Hz L₁ T G₁ M → D ≤ Y →
      (D.subgroupOf Y).IsCComponent → L₁ ≤ D) : False := by
  have hn' := model_normalizer_le H e _ _ _ _ hzero hplus hn
  obtain ⟨k, _, hlt, _, a, hnot⟩ := five_normalizer_levi_overgroup b beta delta hgap hn'
  let Q := flagStabilizer b {k}
  have hbaseQ : (Source.starImage H (L₁ ⊔ T)).map e.toMonoidHom ≤ Q := by
    rw [hbase]
    exact hlt.le
  have hbaseY : L₁ ⊔ T ≤ modelLift H e Q :=
    (le_modelLift_iff H _ hH.1.2 e Q).mpr hbaseQ
  have hoverlap : modelLift H e (fiveParabolic b {beta, delta}) = H ⊓ M := by
    rw [hinter]
    exact modelLift_eq_of_image H _ hH.1.2 e _ hbase (hcore.trans le_sup_right)
  have hY := modelLift_mem_Hz L₁ T G₁ M H hH e _ Q hbaseQ hoverlap hlt
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  let : Group.IsPerfect (LinearGroup 3) := BinaryLinear.linearGroup_isPerfect 3 (by decide)
  let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Group.IsPerfect.ofSurjective (f := SmallParabolicLevi.linearThreeEquivProjective.toMonoidHom)
      SmallParabolicLevi.linearThreeEquivProjective.surjective
  apply exclude_Hz_of_marked_product_quotient L₁ T G₁ M (modelLift H e Q) hY h21
    ((modelLiftQuotientEquiv H e Q).trans a)
  intro hle
  apply hnot
  have hp := (map_mono (f := ((modelLiftQuotientEquiv H e Q).trans a).toMonoidHom.comp
      (QuotientGroup.mk' _)) (subgroupOf_mono (modelLift H e Q) hplusL)).trans hle
  rw [modelLiftQuotientEquiv_image H L₁plus e Q a
    (hplusL.trans (le_sup_left.trans hbaseY)), hplus] at hp
  exact hp

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

end
