module

public import Stellmacher.MainDefs
public import CFSG.Quasithin.Chapter14.Section01.BaumannReduction

/-!
# Chapter 14, §14.1: legacy conditional interfaces

The declarations below are retained for public API compatibility. They are
lattice consequences of supplied data, not proofs of the source-numbered
results. In particular, `LocalData.hS` assumes `S ≤ E`, whereas the actual
Baumann subgroup is `C_T(E)` and contains `E`. Membership in `R₂(H)` means
being a two-reduced normal elementary abelian subgroup, not having rank two;
`H∞` is the solvable residual, not the derived subgroup.

`EmptyLfHypothesis` assumes the centralization assertion that source 14.1.3
must prove. `TerminalCertificate` assumes its conclusions and substitutes `V`
for the source factor `C_M(V)`. Its equality `Y = V` is absent from 14.1.18.
Likewise, `normalizer_decomposition` uses `V` where source 14.1.11 uses
`C_M(V(M))`. None of these legacy declarations establishes the book theorem.

The genuine terminal construction is developed separately in
`Section01.SourcePreliminaries`: `R_c = O₂(M ∩ M_c)` and
`Y = O²(⟨R_c^M⟩)`. Its explicit preceding inputs still require discharge
from the QTKE and local-family hypotheses before final source assembly.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
§14.1, pp. 975--980 (1 March 2004 manuscript).
-/

namespace CFSG.Quasithin.Chapter14

universe u

variable {G : Type u} [Group G] [Finite G]

/-- Legacy subgroup data. No field identifies `S` as a Baumann subgroup,
`V` as a member of `R₂(M)`, or `C₂` as a characteristic subgroup.
In particular `hS : S ≤ E` is not the source Baumann containment.
These hypotheses are preserved only for compatibility. -/
public structure LocalData (G : Type u) [Group G] [Finite G] where
  T : Sylow 2 G
  Z : Subgroup G
  E : Subgroup G
  S : Subgroup G
  M : Subgroup G
  Mc : Subgroup G
  V : Subgroup G
  C₂ : Subgroup G
  hZ : Z ≤ (T : Subgroup G)
  hE : E ≤ (T : Subgroup G)
  hS : S ≤ E
  hV : V ≤ S
  hC₂ : C₂ ≤ S

namespace LocalDataAPI

variable {D : LocalData G}

/-- A lattice consequence of the legacy inclusions, not source 14.1.2(1). -/
public theorem v_le_E (D : LocalData G) : D.V ≤ D.E :=
  D.hV.trans D.hS

public theorem s_le_T (D : LocalData G) : D.S ≤ (D.T : Subgroup G) :=
  D.hS.trans D.hE

public theorem v_le_T (D : LocalData G) : D.V ≤ (D.T : Subgroup G) :=
  (v_le_E D).trans D.hE

public theorem c₂_le_E (D : LocalData G) : D.C₂ ≤ D.E :=
  D.hC₂.trans D.hS

end LocalDataAPI

/-- Legacy centralization certificate. `Residual` and `rankTwo` are arbitrary
parameters: they do not define the solvable residual or the source family
`R₂(H)`. The final field assumes the desired centralizer containment and is
not an encoding of `L_f(G,T) = ∅`. -/
public structure EmptyLfHypothesis (D : LocalData G) where
  Residual : Subgroup G → Subgroup G
  rankTwo : Subgroup G → Subgroup G → Prop
  residual_le_centralizer : ∀ (H U : Subgroup G), rankTwo H U →
    Residual H ≤ Subgroup.centralizer (U : Set G)

/-- Projection of the legacy certificate; not a proof of Lemma 14.1.3. -/
public theorem residual_centralizes_rankTwo
    {D : LocalData G} (h : EmptyLfHypothesis D)
    {H U : Subgroup G} (hU : h.rankTwo H U) :
    h.Residual H ≤ Subgroup.centralizer (U : Set G) :=
  h.residual_le_centralizer H U hU

/- Historical numbered aliases. Their names do not certify source fidelity. -/
public theorem lemma_14_1_2_v_le_E (D : LocalData G) : D.V ≤ D.E :=
  LocalDataAPI.v_le_E D

public theorem lemma_14_1_2_s_le_T (D : LocalData G) : D.S ≤ (D.T : Subgroup G) :=
  LocalDataAPI.s_le_T D

public theorem lemma_14_1_3
    {D : LocalData G} (h : EmptyLfHypothesis D)
    {H U : Subgroup G} (hU : h.rankTwo H U) :
    h.Residual H ≤ Subgroup.centralizer (U : Set G) :=
  residual_centralizes_rankTwo h hU

/-- Legacy abstract relation and equality certificate. It does not construct
the source ordering on `M(T)` or prove uniqueness of a maximal member. -/
public structure MaximalLocalOrder (D : LocalData G) where
  le : Subgroup G → Subgroup G → Prop
  top : Subgroup G
  top_eq : top = D.M
  top_mem : le D.M top
  maximal : ∀ {X}, le X top → le top X → X = top

/-- Equality from the supplied legacy relation certificate.
This is not the uniqueness assertion in Lemma 14.1.4 or 14.1.9. -/
public theorem eq_of_comparable_to_maximal
    {D : LocalData G} (O : MaximalLocalOrder D)
    {X : Subgroup G} (hXM : O.le X D.M) (hMX : O.le D.M X) : X = D.M := by
  rw [← O.top_eq] at hXM hMX ⊢
  exact O.maximal hXM hMX

public theorem lemma_14_1_4
    {D : LocalData G} (O : MaximalLocalOrder D)
    {X : Subgroup G} (hXM : O.le X D.M) (hMX : O.le D.M X) : X = D.M :=
  eq_of_comparable_to_maximal O hXM hMX

/-- Projection of a legacy containment. It supplies neither nontriviality nor
characteristicness, both required for source `C₂(T)`. -/
public theorem c₂_le_baumann {D : LocalData G} : D.C₂ ≤ D.S :=
  D.hC₂

/-- Legacy join equality from inclusions. This is not 14.1.11: its source
factor is `C_M(V(M))`, not `V`, and its difficult inclusion is assumed here. -/
public theorem normalizer_decomposition
    {D : LocalData G} {N : Subgroup G}
    (h : D.M ≤ D.V ⊔ N) (hV : D.V ≤ D.M) (hN : N ≤ D.M) :
    D.M = D.V ⊔ N := by
  exact le_antisymm h (sup_le hV hN)

/-- Transitivity of supplied centralizer containments. -/
public theorem centralizer_le_maximal
    {D : LocalData G} {X : Subgroup G}
    (hX : X ≤ Subgroup.centralizer (D.Z : Set G))
    (hmax : Subgroup.centralizer (D.Z : Set G) ≤ D.Mc) : X ≤ D.Mc :=
  hX.trans hmax

/-- Legacy certificate assuming three equalities via pairs of inclusions.
It does not construct `Rc = O₂(M ∩ Mc)` or `Y = O²(⟨Rc^M⟩)`. The factor `V`
in the intersection formula should be `C_M(V)` in the source, and `Y = V`
is not a source conclusion. Do not use this certificate to prove 14.1.18. -/
public structure TerminalCertificate (D : LocalData G) where
  Rc : Subgroup G
  R : Subgroup G
  Y : Subgroup G
  Rc_le_T : Rc ≤ (D.T : Subgroup G)
  R_le_T : R ≤ (D.T : Subgroup G)
  T_le_RcR : (D.T : Subgroup G) ≤ Rc ⊔ R
  intersection_le : D.M ⊓ D.Mc ≤ D.V ⊔ Rc
  join_le_intersection : D.V ⊔ Rc ≤ D.M ⊓ D.Mc
  quotient_odd : Y ≤ D.V
  V_le_quotient : D.V ≤ Y

public theorem terminal_preliminary
    {D : LocalData G} (c : TerminalCertificate D) :
    c.Rc ⊔ c.R = (D.T : Subgroup G) ∧
      D.M ⊓ D.Mc = D.V ⊔ c.Rc ∧
      c.Y = D.V := by
  refine ⟨?_, ?_, ?_⟩
  · exact le_antisymm (sup_le c.Rc_le_T c.R_le_T) c.T_le_RcR
  · exact le_antisymm c.intersection_le c.join_le_intersection
  · exact le_antisymm c.quotient_odd c.V_le_quotient

public theorem lemma_14_1_18
    {D : LocalData G} (c : TerminalCertificate D) :
    c.Rc ⊔ c.R = (D.T : Subgroup G) ∧
      D.M ⊓ D.Mc = D.V ⊔ c.Rc ∧
      c.Y = D.V :=
  terminal_preliminary c

end CFSG.Quasithin.Chapter14
