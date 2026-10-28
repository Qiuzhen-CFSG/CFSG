module

public import CFSG.Quasithin.Chapter13.Section09.CentralizerStructure.CentralClosure
public import Theory.GroupTheory.QuaternionCentralProductIntrinsic

/-!
# The marked input Q for the independent branches of 13.9.8

The input retains Q as a subgroup of the original G, its two quaternion
factors, the original central involution z, and the actual quotient map.
Its Thompson and elementary clauses are 13.9.6. The factor presentation
specifies the plus-type extraspecial group, rather than an order-only tag.

The local-geometry owner constructs this data from the marked wreath
model. Normality in C_G(z), its quotient recognition, and BQ=O₂(C_G(z))
are deliberately separate proof obligations.

Source: Aschbacher–Smith, setup and Lemma 13.9.6, printed p.971
(PDF p.988), and the quaternion factors used on printed p.972.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section09.CentralizerStructure
open Subgroup
variable {G : Type*} [Group G] [Finite G] {d : Configuration G}

/-- Earlier marked local geometry, with no normality assertion in C_G(z). -/
structure CoreData (m : PairData d) where
  Q : Subgroup G
  le_T : Q ≤ (d.T : Subgroup G)
  t_mem : m.t ∈ Q
  factors : QuaternionCentralProductData Q
  center_eq : (center Q).map Q.subtype = m.Z
  tilde_thompson : m.tilde Q = Stellmacher.elementaryAbelianMaxJ (m.tilde d.T)
  tilde_elementary : IsElementaryAbelian 2 (m.tilde Q)
  tilde_card : Nat.card (m.tilde Q) = 16

namespace CoreData
variable {m : PairData d} (q : CoreData m)

theorem le_C : q.Q ≤ m.C := q.le_T.trans m.z_central

theorem Z_le : m.Z ≤ q.Q := q.center_eq ▸ map_subtype_le (center q.Q)

theorem isPGroup : IsPGroup 2 q.Q := d.T.isPGroup'.to_le q.le_T

theorem card : Nat.card q.Q = 32 := q.factors.card

end CoreData
end CFSG.Quasithin.Chapter13.Section09.CentralizerStructure
