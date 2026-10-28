module
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.WeakClosure.SylowChoice
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# The marked centralizer configuration and its assembly targets

E and T_E are defined as actual subgroups of G. The intersection setup proves
E elementary of order four, and the normalizer-adapted Sylow choice makes
T_E Sylow in C_G(E).

`CentralizerGeometry` specifies the still-required model-to-ambient geometry:
V = Ω₁(T_E), an actual E₈ equivalence, the two T_E alternatives, the center
of T, and the reflection moving r to rv. `SymmetricTransvections` specifies
the actual elements and conjugation equations needed by the endgame, including
their fixed axes and commutator centers. These are output specifications;
this module does not construct them or assert weak closure or symmetry.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 16.4.6, printed pp.1184–1185. Conjugation is left conjugation.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.WeakClosure
open Subgroup
variable {G : Type*} [Group G]

/-- The actual subgroup E of the source. -/
def involutionPair (z r : G) : Subgroup G := zpowers r ⊔ zpowers z

/-- T_E is an intersection in G, not an abstract isomorphic carrier. -/
def commonCentralizer (T : Subgroup G) (z r : G) : Subgroup G :=
  T ⊓ centralizer (involutionPair z r : Set G)

/-- The marked eight, whose equality with Ω₁(T_E) remains to be proved. -/
def markedEight (z r v : G) : Subgroup G := (zpowers v ⊔ zpowers z) ⊔ zpowers r

/-- The center of a subgroup, embedded in the original ambient group. -/
def embeddedCenter (T : Subgroup G) : Subgroup G := T ⊓ centralizer (T : Set G)

/-- Elementwise weak closure in the center; no fusion conclusion is built in. -/
def WeaklyClosedInCenter (T : Subgroup G) (z : G) : Prop :=
  z ∈ embeddedCenter T ∧ ∀ x ∈ embeddedCenter T, IsConj z x → x = z

abbrev ElementaryEight := Multiplicative (Fin 3 → ZMod 2)
abbrev FourTimesCyclicFour := Multiplicative (Fin 2 → ZMod 2) × Multiplicative (ZMod 4)

/-- The geometric conclusion to be constructed from the intrinsic model facts.
This record is only an interface for that separate proof, not a source hypothesis. -/
structure CentralizerGeometry (T : Sylow 2 G) (z : G) (L : Subgroup G) (r v : G) : Prop where
  v_order : orderOf v = 2
  v_mem : v ∈ componentSylow T L
  component_fixed : componentSylow T L ⊓ involutionCentralizer r = zpowers v
  center_eq : embeddedCenter (T : Subgroup G) = zpowers z ⊔ zpowers v
  intersection_eq : commonCentralizer (T : Subgroup G) z r ⊓
    ((L ⊔ centralizer (L : Set G)) ⊔ zpowers r) = markedEight z r v
  omega_eq : omegaOneAmbient (commonCentralizer (T : Subgroup G) z r) = markedEight z r v
  eight_equiv : Nonempty (markedEight z r v ≃* ElementaryEight)
  alternatives : commonCentralizer (T : Subgroup G) z r = markedEight z r v ∨
    Nonempty (commonCentralizer (T : Subgroup G) z r ≃* FourTimesCyclicFour)
  reflection : ∃ t ∈ componentSylow T L ⊓
    normalizer (commonCentralizer (T : Subgroup G) z r : Set G),
    MulAut.conj t r = r * v

variable [Finite G] {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

theorem involutionPair_le_sylow (h : IntersectionSetup T z L g R) (hr : r ∈ R) :
    involutionPair z r ≤ (T : Subgroup G) :=
  sup_le (zpowers_le.mpr (h.le_sylow hr)) (zpowers_le.mpr h.mem_sylow)

theorem involutionPair_elementary (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) : IsElementaryAbelian 2 (involutionPair z r) := by
  let : IsElementaryAbelian 2 (zpowers r) := IsElementaryAbelian.zpowers_of_pow_eq_one
    (hr2 ▸ pow_orderOf_eq_one r)
  let : IsElementaryAbelian 2 (zpowers z) := IsElementaryAbelian.zpowers_of_pow_eq_one
    (h.involution ▸ pow_orderOf_eq_one z)
  apply IsElementaryAbelian.sup_of_le_centralizer
  rw [zpowers_eq_closure r, centralizer_closure]
  apply zpowers_le.mpr
  exact mem_centralizer_singleton_iff.mpr
    ((mem_centralizer_singleton_iff.mp (h.sylow_centralizes (h.le_sylow hr))).symm)

theorem involutionPair_card (h : IntersectionSetup T z L g R) (hr : r ∈ R)
    (hr2 : orderOf r = 2) :
    Nat.card (involutionPair z r) = 4 := by
  have hzout : z ∉ zpowers r := by
    intro hz
    have hRz : z ∈ R := (zpowers_le.mpr hr) hz
    have he : z = 1 := by
      have hm : z ∈ R ⊓ centralizer (L : Set G) :=
        ⟨hRz, h.toStandardSetup.z_mem_commutingSylow.2⟩
      simpa only [h.normalizer_structure.2.2.2, mem_bot] using hm
    have hh := h.involution
    simp [he] at hh
  have hzC : z ∈ centralizer (zpowers r : Set G) := by
    rw [zpowers_eq_closure r, centralizer_closure]
    exact mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_singleton_iff.mp (h.sylow_centralizes (h.le_sylow hr))).symm)
  rw [involutionPair, card_sup_zpowers_of_normalizing_involution (zpowers r) z
    (h.involution ▸ pow_orderOf_eq_one z) hzout (centralizer_le_normalizer _ hzC),
    Nat.card_zpowers, hr2]

theorem commonCentralizer_sylow (h : IntersectionSetup T z L g R)
    (hR : R = zpowers r)
    (hn : SylowIn ((T : Subgroup G) ⊓ normalizer (R : Set G))
      (normalizer (L : Set G) ⊓ normalizer (R : Set G))) :
    SylowIn (commonCentralizer (T : Subgroup G) z r)
      (centralizer (involutionPair z r : Set G)) := by
  unfold commonCentralizer involutionPair
  rw [← hR]
  exact h.centralizer_sylow hn

/-- Actual ambient equations and fixed axes, exported for the E₈ endgame.
This is a target specification, not a premise for the weak-closure proof. -/
structure SymmetricTransvections (T : Sylow 2 G) (z r : G) (L : Subgroup G)
    (g v u s t : G) : Prop where
  weak_z : WeaklyClosedInCenter (T : Subgroup G) z
  weak_r : WeaklyClosedInCenter ((T : Subgroup G).conjBy g) r
  v_not_mem : v ∉ L.conjBy g
  u_order : orderOf u = 2
  intersection_eq : markedEight z r v ⊓ L.conjBy g = zpowers u
  lines_ne : zpowers u ≠ zpowers v
  opposite_center_eq : embeddedCenter ((T : Subgroup G).conjBy g) = zpowers r ⊔ zpowers u
  t_mem : t ∈ componentSylow T L ⊓
    normalizer (commonCentralizer (T : Subgroup G) z r : Set G)
  s_mem : s ∈ (T : Subgroup G).conjBy g ⊓
    normalizer (commonCentralizer (T : Subgroup G) z r : Set G)
  t_r : MulAut.conj t r = r * v
  t_z : MulAut.conj t z = z
  t_v : MulAut.conj t v = v
  s_z : MulAut.conj s z = z * u
  s_r : MulAut.conj s r = r
  s_u : MulAut.conj s u = u
  t_axis : markedEight z r v ⊓ involutionCentralizer t = zpowers z ⊔ zpowers v
  s_axis : markedEight z r v ⊓ involutionCentralizer s = zpowers r ⊔ zpowers u
  t_center : ⁅markedEight z r v, zpowers t⁆ = zpowers v
  s_center : ⁅markedEight z r v, zpowers s⁆ = zpowers u

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.WeakClosure
