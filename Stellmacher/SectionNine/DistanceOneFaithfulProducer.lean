module

public import Stellmacher.SectionNine.DistanceOneFaithfulSetup
public import Stellmacher.SectionNine.DistanceOneReduction
public import Stellmacher.SectionOne.NineCoreSixteenWreath

/-!
# The faithful initial action at critical distance one

The initial center has order sixteen, and the initial stabilizer modulo its
centralizer of that center is the literal SL₂(2) wreath C₂ model.

Construct the actual distance-one extraction and a faithful quotient-module
witness on the original center. The proved setup supplies the order-sixteen
module, order-nine odd core, Sylow supplement with a unique maximal overgroup,
and elementary subgroup of order four. The proved nine-core recognition theorem
identifies the entire witness group, not just its relative double-SL₂ subgroup.
Compose that equivalence with the witness projection to retain the exact kernel.

Source: Stellmacher (9.1), relation (8), printed p.47 of
`refs/files/stellmacher-n-group.pdf`. The graph remains in G and the ambient
hypothesis remains in H. No initial-core equality or faithful conclusion is
assumed, and no admitted numbered result is used.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem distance_one_faithful_conclusion
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) :
    DistanceOneFaithfulConclusion ctx.toLocalContext := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a
  let Za := ZAt Γ cp.a
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let _ : IsElementaryAbelian 2 Za :=
    z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hfirst
  have hZaP : Za ≤ P := by
    change z Γ cp.a ≤ stabilizer Γ cp.a
    rw [z, Γ.zAt_def]
    apply sSup_le
    rintro center ⟨sylow, rfl⟩
    exact (omegaOneCenter_le_centerAmbient _).trans
      ((Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _))
  obtain ⟨data⟩ := distance_one_initial_geometry ctx hb
  obtain ⟨w⟩ := exists_quotientModuleWitness P Za hZaP (stabilizer_le_normalizer_z Γ cp.a)
  let _ := w.groupX
  let _ := w.finiteX
  let _ := MulDistribMulAction.compHom Za w.action
  obtain ⟨hsetup, hcard, hodd, ⟨R, hgen, huniq⟩, X, hX, hXcard⟩ :=
    distance_one_faithful_recognition_setup ctx hb data w
  obtain ⟨equiv⟩ := SectionOne.nineCore_sixteen_wreath
    hsetup R hgen huniq hcard hodd X hX hXcard
  change Nat.card Za = 2 ^ 4 ∧
    QuotientIsModel P (P ⊓ Subgroup.centralizer (Za : Set G)) SL2TwoWreathC2
  refine ⟨hcard, equiv.toMonoidHom.comp w.projection,
    equiv.surjective.comp w.surjective, ?_⟩
  rw [MonoidHom.ker_comp_of_injective w.projection equiv.toMonoidHom equiv.injective]
  exact w.kernel_eq

end Stellmacher.SectionNine
