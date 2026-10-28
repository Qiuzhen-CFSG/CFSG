module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry.FixedPlane.Transport

/-!
# The strict span in 15.3.49(m)

Write V = V(M), Q_H = O₂(H), S = N_T(V₁), and Z_S = C_V(S), using
the actual source subgroups. The commutator bound of 15.3.48(2) gives
[⟨Z_S^H⟩,Q_H] ≤ Z ≤ V. Local normalization gives [V,Q_H] ≤ V, while
the local equality [Z_S,Q_H] = Z proved on p.1142 makes the Q_H action
nontrivial. The numbered clause 15.3.49(2) is its specialization to M_c;
the input below retains the local equality for the actual H.
The transported dihedral calculation then proves Z_S ≤ [V,Q_H], and
the invariant quadratic form makes Z_S not totally singular.

If ⟨V^H⟩ were ⟨Z_S^H⟩V, its commutator with Q_H would thus be a
subgroup of V that is not totally singular and is normalized by H. The earlier 15.3.46(2)
normalizer bound would force H ≤ M, a contradiction. This supplies all
local commutator and fixed-plane premises of localSpan_sup_lt.

The cited earlier commutator conclusions, the normalizer bound, and
15.3.49(d)'s abelianness remain explicit inputs. Their source assembly,
and the subsequent geometric offender argument, belong to the parent task.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.49(m), printed p.1144; see also pp.1121–1122 and 1141–1142.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry.FixedPlane
variable {G : Type*} [Group G] [Finite G]

/-- Step (m), with the source's actual V, Q_H, S and Z_S. The earlier inputs
are 15.3.46(2), 15.3.48(2), the local equality proved just before the
specialization in 15.3.49(2), and 15.3.49(d). The order of Z is 15.3.2(2).
In particular fixed-plane containment and nonsingularity are proved. -/
theorem localSpan_fixedPlane_sup_lt
    (T : Sylow 2 G) (M H : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hTH : (T : Subgroup G) ≤ H) (hout : ¬ H ≤ M)
    (d : Section03.NaturalOrthogonalAction M (localModule T M))
    [IsElementaryAbelian 2 (localModule T M)]
    (o : FusionCore.NaturalOrthogonalAction M (localModule T M))
    (i : OrthogonalPlaneIndex)
    [IsMulCommutative (localSpan (localModule T M) H)]
    (hZcard : Nat.card (centralInvolutions T) = 2)
    (h48 : ⁅localSpan (fixedPlane (localModule T M) (planeStabilizer T (d.plane i))) H,
      localTwoCore H⁆ ≤ centralInvolutions T)
    (h49 : ⁅fixedPlane (localModule T M) (planeStabilizer T (d.plane i)),
      localTwoCore H⁆ = centralInvolutions T)
    (hnormalizer : ∀ W : Subgroup G, W ≤ localModule T M →
      ¬ IsTotallySingular o.form W → normalizer (W : Set G) ≤ M) :
    localSpan (fixedPlane (localModule T M) (planeStabilizer T (d.plane i))) H ⊔
      localModule T M < localSpan (localModule T M) H := by
  have hZV : centralInvolutions T ≤ localModule T M := le_conjugateSpanBy _ _
  have hnon : ⁅localModule T M, localTwoCore H⁆ ≠ ⊥ := by
    intro hb
    have hz : centralInvolutions T = ⊥ := le_bot_iff.mp (by
      rw [← h49]
      exact (commutator_mono inf_le_left le_rfl).trans hb.le)
    have hzn : centralInvolutions T ≠ ⊥ :=
      (one_lt_card_iff_ne_bot _).mp (by omega)
    exact hzn hz
  have hc := core_control d T H hTM hTH
  exact ExtraspecialElimination.localSpan_sup_lt H M (localModule T M)
    (fixedPlane (localModule T M) (planeStabilizer T (d.plane i))) (localTwoCore H)
    o.form inf_le_left (fixedPlane_not_totallySingular d o T hTM i)
    hc.1 hout (h48.trans hZV) hc.2.2
    (fixedPlane_le_commutator d T H hTM hTH i hnon) hnormalizer

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry.FixedPlane
