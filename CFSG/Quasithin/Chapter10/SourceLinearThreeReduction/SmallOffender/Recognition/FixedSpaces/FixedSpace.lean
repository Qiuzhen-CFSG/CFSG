module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.Inputs
public import CFSG.Quasithin.Chapter10.SourceA5OffenderFixedGeometry

/-!
# The normalizing offender fixes every nonfixed point's fixed space

For P=Wˣ and B=P∩M∩N_G(W), point-centralizer control puts C_W(b) in
N_G(P). Thus [B,C_W(b)] lies in W∩P. The earlier outside-conjugate
intersection theorem makes it trivial. This argument has no model premise.
Source: Aschbacher--Smith 10.2.9(3), 10.2.10(1), 10.2.12, pp.750--754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition.FixedSpaces
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The normalizing part of the offender fixes the fixed space of every
nonfixed point in the conjugate moved factor. -/
theorem normalizer_fixed_space
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L} (c : Context D) {g : G}
    (hinter : ⁅D.fullModule,L⁆ ⊓
      (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⊥)
    {b : G} (hb : b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom)
    (hbn : b ∉ centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)) :
    ⁅D.fullModule,L⁆ ⊓ centralizer ({b} : Set G) ≤ centralizer
      (((⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal ⊓
        normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp c.nonnormal
  let W := ⁅D.fullModule,L⁆
  let P := W.map (MulAut.conj g).toMonoidHom
  let X := W ⊓ centralizer ({b} : Set G)
  let B := P ⊓ D.maximalLocal ⊓ normalizer (W : Set G)
  have hXN : X ≤ normalizer (P : Set G) := inf_le_right.trans
    ((source_nonnormal_conjugate_point_centralizer_normalizes D c.nonnormal ht htn
      (c.crossed t ht htn) c.pointCentralizers hb hbn).trans inf_le_right)
  have hcomm : ⁅B,X⁆ ≤ W ⊓ P := le_inf
    ((commutator_mono le_rfl (show X ≤ W from inf_le_left)).trans
      (le_normalizer_iff_commutator_le_right.mp (show B ≤ normalizer (W : Set G) from inf_le_right)))
    ((commutator_mono (show B ≤ P from inf_le_left.trans inf_le_left) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hXN))
  have he : ⁅B,X⁆ = ⊥ := eq_bot_iff.mpr (hcomm.trans_eq hinter)
  exact le_centralizer_iff.mpr (commutator_eq_bot_iff_le_centralizer.mp he)


end CFSG.Quasithin.Chapter10.SmallOffender.Recognition.FixedSpaces
