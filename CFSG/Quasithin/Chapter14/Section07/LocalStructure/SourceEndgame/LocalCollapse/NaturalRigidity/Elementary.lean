module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.Setup
public import Theory.Frattini.BinarySquares

/-!
# Elementary structure of the canonical fixed preimage

The cubic paragraph of 14.7.74 needs Φ(QC) ≤ C_Q(L). This follows directly
from its central elementary displacements: for x ∈ QC and l ∈ L, the
commutator [l,x] lies in V ≤ Z(QC), so conjugation by l fixes x². Squares
generate the Frattini subgroup of this finite two-group. Consequently
C_Q(L)=1 makes QC itself elementary abelian.

All groups are the canonical constructions from LocalCollapse.Setup. No
splitting or vanishing assertion is added to Prior. The later module
construction consumes the elementary conclusion.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
proof of 14.7.74, printed p.1077 (PDF p.1094).
-/

@[expose] public section

open Subgroup Representation
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.NaturalRigidity
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (a : Prior d)

include a in
/-- The original natural subgroup lies in the canonical fixed preimage. -/
theorem V_le_QC : V ≤ QC T L V := by
  have hVQ : V ≤ Q T L := a.steinberg.kernel_le.trans
    (a.core.le.trans (pCoreIn_mono_of_normalizes le_sup_left
      (sup_le L.le_normalizer a.sylow_normalizes)))
  exact le_commutatorPreimage hVQ
    (le_normalizer_iff_commutator_le_left.mp d.natural.chosen.normalizes)

include a in
/-- The centralizer identity for LT makes the natural layer central in QC. -/
theorem QC_centralizes_V : QC T L V ≤ centralizer (V : Set G) :=
  (commutatorPreimage_le _ _ _).trans (a.centralizer_LT.symm.le.trans inf_le_right)

include a in
/-- Every square in QC is fixed by L: its displacement is central of exponent two. -/
theorem square_mem_QL (x : G) (hx : x ∈ QC T L V) : x ^ 2 ∈ QL T L := by
  refine ⟨(Q T L).pow_mem ((commutatorPreimage_le _ _ _) hx) 2, ?_⟩
  intro l hl
  have hc : ⁅l,x⁆ ∈ V := by
    have h := QC_commutator_le (F := F) (L := L)
    rw [commutator_comm] at h
    exact commutator_le.mp h l hl x hx
  have hcs : ⁅l,x⁆ ^ 2 = 1 := by
    let := d.natural.chosen.elementary
    exact elemPow_eq_one_of_isElementaryAbelian _ hc
  have hcx : Commute ⁅l,x⁆ x := QC_centralizes_V d a hx _ hc
  have he : l * x * l⁻¹ = ⁅l,x⁆ * x := by
    simp only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one]
  have hs : l * x ^ 2 * l⁻¹ = x ^ 2 := by
    calc
      l * x ^ 2 * l⁻¹ = (l * x * l⁻¹) ^ 2 := map_pow (MulAut.conj l) x 2
      _ = (⁅l,x⁆ * x) ^ 2 := congrArg (fun t : G => t ^ 2) he
      _ = x ^ 2 := by rw [hcx.mul_pow, hcs, one_mul]
  exact mul_inv_eq_iff_eq_mul.mp hs

include a in
/-- The Frattini subgroup of the actual QC is fixed pointwise by L. -/
theorem frattini_le_QL : (frattini (QC T L V)).map (QC T L V).subtype ≤ QL T L := by
  have hp : IsPGroup 2 (QC T L V) :=
    (isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))).to_le (commutatorPreimage_le _ _ _)
  apply map_le_iff_le_comap.mpr
  rw [hp.frattini_eq_closure_squares]
  apply (closure_le _).mpr
  rintro _ ⟨x,rfl⟩
  exact square_mem_QL d a x x.property

include a in
/-- Once the original fixed subgroup vanishes, the actual QC is elementary abelian. -/
theorem QC_elementary (hQL : QL T L = ⊥) : IsElementaryAbelian 2 (QC T L V) := by
  have hs (x : QC T L V) : x ^ 2 = 1 := by
    apply Subtype.ext
    have h := square_mem_QL d a x x.property
    rwa [hQL, mem_bot] at h
  exact {
    is_comm := ⟨fun x y => (Commute.of_orderOf_dvd_two
      (fun z => orderOf_dvd_of_pow_eq_one (hs z)) x y).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }

include a in
/-- The Frattini conclusion of the cubic paragraph, from the same source hypotheses. -/
theorem QC_frattini (hQL : QL T L = ⊥) : frattini (QC T L V) = ⊥ := by
  let := QC_elementary d a hQL
  let : Fact (IsPGroup 2 (QC T L V)) := ⟨IsElementaryAbelian.isPGroup 2 _⟩
  exact frattini_eq_bot_of_isElementaryAbelian (p := 2)


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.NaturalRigidity
