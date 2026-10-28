module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Consequences.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Splitting.Local

/-!
# Elementary radius groups and displacement modulo U

The supplied initial escape facts give b ≥ 6. Every pair of M-vertices in
a radius-two ball is then closer than the critical distance, so their
Z-groups commute. Their elementary generators make the whole radius group
V elementary abelian.

At a critical pair, [Z_a,Z_a'] lies in U_a because Z_a' normalizes Z_a.
Its order is two, whereas [V_a,Z_a'] has order at most four. Thus the
actual endpoint displacement modulo U_a has order at most two. This is the
extra geometric bound needed to exclude a central extension in Vcirc/U.
Source: Meierfrankenfeld--Stellmacher (1993), (4.3.1)(i),(ii),(v),
pp.882--883, and the quotient assertion in (4.3.2)(3), p.884.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree.Kernel
open Initial Initial.Consequences Initial.Natural.Splitting
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

theorem radius_elementary (a : Vertex R) (ha : color R a = false)
    (hsix : 6 ≤ geometry.b R) : IsElementaryAbelian 2 (V R a) := by
  have hc : V R a ≤ centralizer (V R a : Set (FreeAmalgam R)) := by
    apply V_le_of_m_ball ha
    intro d hd hda
    apply le_centralizer_iff.mpr
    exact (V_le_Q_of_distance ha (by rw [SimpleGraph.dist_comm]; omega)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes d hd)))
  let : IsMulCommutative (V R a) :=
    commutator_self_eq_bot_iff.mp (commutator_eq_bot_iff_le_centralizer.mpr hc)
  let I := {d : Vertex R // color R d = false ∧ (cosetGraph R).dist d a ≤ 2}
  let A : I → Subgroup (FreeAmalgam R) := fun d => Z R d.val
  have hV : V R a = ⨆ d, A d := by
    apply le_antisymm
    · apply V_le_of_m_ball ha
      intro d hd hda
      exact le_iSup A ⟨d, hd, hda⟩
    · apply iSup_le
      intro d
      exact le_iSup_of_le d.val (le_iSup_of_le d.property.2 le_rfl)
  refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  apply Subtype.ext
  change (x : FreeAmalgam R) ^ 2 = 1
  suffices hp : ∀ y ∈ (⨆ d, A d), y ^ 2 = 1 by
    exact hp x (hV ▸ x.property)
  intro y hy
  induction hy using iSup_induction' with
  | hp d x hx =>
    let := geometry.Z_elementary (by omega) d.val d.property.1
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  | h1 => simp
  | hmul x y hx hy hxp hyp =>
    have hxy : Commute x y := mem_centralizer_iff.mp (hc (hV.symm ▸ hy)) x (hV.symm ▸ hx)
    rw [hxy.mul_pow, hxp, hyp, one_mul]

variable [Finite M]

theorem radius_mod_U_index (source : LocalSource L R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (p : Counterexample geometry) :
    (U R p.a).relIndex (radiusCommutator p.a p.a') ≤ 2 := by
  let := p.radius_finite
  let D := radiusCommutator p.a p.a'
  let C := (U R p.a).subgroupOf D
  let : Finite ↥(U R p.a ⊓ D) := Finite.of_injective
    (inclusion (show U R p.a ⊓ D ≤ D from inf_le_right)) (inclusion_injective _)
  have hCU : criticalCommutator p.a p.a' ≤ U R p.a := by
    exact (commutator_mono le_rfl
      (source.critical_Z_le_stabilizer geometry p.a p.color_a p.a' p.critical).2).trans
        (Z_commutator_stabilizer source p.a p.color_a).le
  have hC : 2 ≤ Nat.card C := by
    have hh := card_le_of_le
      (show criticalCommutator p.a p.a' ≤ U R p.a ⊓ D from
        le_inf hCU (commutator_mono (Z_le_VBall R p.a 2) le_rfl))
    rw [p.critical_card source hb modules] at hh
    rwa [← Nat.card_congr (subgroupOfEquivOfLe
      (show U R p.a ⊓ D ≤ D from inf_le_right)).toEquiv, inf_subgroupOf_right] at hh
  have hprod := C.index_mul_card
  have hsmall := radius_card_le_four p source hb modules
  change C.index ≤ 2
  change Nat.card D ≤ 4 at hsmall
  nlinarith
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree.Kernel
