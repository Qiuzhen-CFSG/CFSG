module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.ModelData
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.Centerless
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!+# Identifying the opposite graph-field action

Write D = O²(C_L(r)) and L′ = L.conjBy g. The earlier placement D ≤ L′,
together with L ≤ C_G(z), puts the two-perfect group D in O²(C_L′(z)).
The empty-family detector proves that z is outer on L′. The field and
graph rows of 16.1.4 have residuals PSL₃(2) and PSL₂(4), respectively;
their orders 168 and 60 cannot be divisible by |D| = 9. The remaining
graph-field row has residual E₉, so containment is equality.

The three outer rows of the earlier involution table remain an explicit
input, with actual quotient actions and residual isomorphisms. This module
proves the opposite identification from that table; it does not prove the
table or construct either quaternion normalizer. In particular, it does
not assume an opposite graph-field action, equality of residuals, or a
conjugator interchanging both marks. The argument needs neither a new
fusion restriction nor the additional nontrivial-cover assumptions.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.4(4)–(6), printed p.1171, and the proof of 16.4.9(2), pp.1190–1191.
The group-order formula is reused from the attributed ATLAS port in
`Theory.AtlasPort.ExceptionalIsomorphisms.Support`.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections.GraphField.Cover.OppositeMarking

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- The specified ambient actor induces the specified automorphism on the
actual two-core quotient, through a multiplicative equivalence. -/
def QuotientAction (J : Subgroup G) (s : G) (a : MulAut Matrix.PSL3Four.PSL) : Prop :=
  ∃ hs : s ∈ normalizer (J : Set G),
    ∃ e : (J ⧸ pCore 2 J) ≃* Matrix.PSL3Four.PSL,
      ∀ x : J,
        e (QuotientGroup.mk' (pCore 2 J) (J.normalizerMonoidHom ⟨s, hs⟩ x)) =
          a (e (QuotientGroup.mk' (pCore 2 J) x))

/-- The outer PSL₃(4) slice of source 16.1.4(4)–(6), for a fixed component.
This is an explicit earlier source input, not an assertion that the table has
been proved. Each row retains its action and the actual O²(C_J(s)) model.
No opposite marking, residual placement, or empty-family condition occurs
in this table contract. -/
def OuterInvolutionTable (J : Subgroup G) : Prop :=
  Nonempty ((J ⧸ pCore 2 J) ≃* Matrix.PSL3Four.PSL) →
  ∀ s : G, orderOf s = 2 → s ∈ normalizer (J : Set G) →
    s ∉ centralizer (J : Set G) ⊔ J →
    (QuotientAction J s Matrix.PSL3Four.pslFrobenius ∧
      Nonempty (residual J s ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))) ∨
    (QuotientAction J s (Matrix.PSL3.OuterSolvable.graph Matrix.PSL3Four.F) ∧
      Nonempty (residual J s ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) Matrix.PSL3Four.F)) ∨
    (IsL3FourGraphField J s ∧
      Nonempty (residual J s ≃* Multiplicative (Fin 2 → ZMod 3)))

/-- The precise 16.4.8 placement puts the original two-perfect residual inside
the opposite fixed-point residual. Elementary abelianness is not needed. -/
theorem residual_le_opposite_residual (h : IntersectionSetup T z L g R)
    (hplace : residual L r ≤ L.conjBy g) :
    residual L r ≤ residual (L.conjBy g) z := by
  let C := L.conjBy g ⊓ centralizer ({z} : Set G)
  have hDC : residual L r ≤ C := le_inf hplace
    ((residual_le_centralizer L r).trans (inf_le_left.trans h.component.1))
  have hp : IsPPerfect 2 (residual L r) :=
    isPPerfect_embedded_pResidual 2 (L ⊓ centralizer ({r} : Set G))
  have hpC : IsPPerfect 2 ((residual L r).subgroupOf C) :=
    hp.of_surjective (subgroupOfEquivOfLe hDC).symm.toMonoidHom
      (subgroupOfEquivOfLe hDC).symm.surjective
  have hh := map_mono (f := C.subtype)
    (le_pResidual_of_isPPerfect ((residual L r).subgroupOf C) hpC)
  rwa [map_subgroupOf_eq_of_le hDC] at hh

private theorem field_card :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  have hh := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 3
  norm_num [Fin.prod_univ_succ] at hh
  rw [Nat.card_eq_fintype_card]
  exact hh

private theorem graph_card :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) Matrix.PSL3Four.F) = 60 := by
  have hh := Atlas.ExceptionalSupport.card_psl_mul (F := Matrix.PSL3Four.F) 2
  norm_num [Matrix.PSL3Four.card_F, Fin.prod_univ_succ] at hh
  omega

private theorem nine_card : Nat.card (Multiplicative (Fin 2 → ZMod 3)) = 9 := by
  simp

/-- A subgroup of order nine in the actual residual excludes both the field
and graph rows. The graph-field row then identifies the embedded residual
with that subgroup, rather than merely giving an abstract isomorphism. -/
theorem graphField_and_residual_eq_of_table {J D : Subgroup G} {s : G}
    (htable : OuterInvolutionTable J)
    (hq : Nonempty ((J ⧸ pCore 2 J) ≃* Matrix.PSL3Four.PSL))
    (hs2 : orderOf s = 2) (hsN : s ∈ normalizer (J : Set G))
    (hout : s ∉ centralizer (J : Set G) ⊔ J)
    (hD : D ≤ residual J s) (h9 : Nat.card D = 9) :
    IsL3FourGraphField J s ∧ residual J s = D := by
  have hdiv := card_dvd_of_le hD
  rw [h9] at hdiv
  rcases htable hq s hs2 hsN hout with ⟨_, ⟨e⟩⟩ | ⟨_, ⟨e⟩⟩ | ⟨ha, ⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv, field_card] at hdiv
    norm_num at hdiv
  · rw [Nat.card_congr e.toEquiv, graph_card] at hdiv
    norm_num at hdiv
  · have hcard : Nat.card (residual J s) = 9 :=
      (Nat.card_congr e.toEquiv).trans nine_card
    exact ⟨ha, (eq_of_le_of_card_ge hD (by rw [hcard, h9])).symm⟩

/-- The opposite graph-field identification and equality of actual residuals
needed by the cover argument. Outerness is derived from the empty-family
detector. Only the permitted earlier 16.1.4 table and 16.4.8 placement remain
explicit; the quaternion-normalizer constructor is a separate obligation. -/
theorem opposite_graphField_and_residual (h : IntersectionSetup T z L g R)
    (hsmall : OrderTwoOutsideDeltaZero L) (hempty : ¬ (deltaZero L).Nonempty)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hmodel : IsL3FourGraphField L r)
    (h9 : Nat.card (residual L r) = 9)
    (hplace : residual L r ≤ L.conjBy g)
    (htable : OuterInvolutionTable (L.conjBy g)) :
    IsL3FourGraphField (L.conjBy g) z ∧ residual (L.conjBy g) z = residual L r := by
  obtain ⟨_, e, _⟩ := hmodel
  let c := (MulAut.conj g).subgroupMap L
  let q := QuotientGroup.congr (pCore 2 L) (pCore 2 (L.conjBy g)) c
    (pCore_map_iso 2 c)
  have hq : Nonempty (((L.conjBy g) ⧸ pCore 2 (L.conjBy g)) ≃* Matrix.PSL3Four.PSL) :=
    ⟨q.symm.trans e⟩
  have hzN : z ∈ normalizer (L.conjBy g : Set G) :=
    fourGroup_le_conjugate_normalizer h hr hr2 (mem_sup_right (mem_zpowers z))
  exact graphField_and_residual_eq_of_table htable hq h.involution hzN
    (Centerless.z_outside_conjugate_product h hsmall hempty hr hr2 hout)
    (residual_le_opposite_residual h hplace) h9

end CFSG.Quasithin.Chapter16.Intersections.GraphField.Cover.OppositeMarking
