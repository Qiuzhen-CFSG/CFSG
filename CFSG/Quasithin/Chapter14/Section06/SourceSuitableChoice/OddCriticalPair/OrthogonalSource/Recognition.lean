module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Alternatives.Dimensions
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.OrthogonalSource.MarkedWreath
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.OrthogonalSource.MovedQuotient
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.OrthogonalSource.PlanePermutation

/-!
# Recognition of the marked rank-four moved action

The two exchanged moved summands have dimension two, and the actor has order
72. Their permutation and faithfulness on the moved space give the full matrix
wreath action, with its first plane marked. Lifting through the actual map from
[U,H] to U/Z gives the original orthogonal action, both exact kernels, and the
literal first-factor covering plane.

The source consumer retains the rank-four condition. Its discharge and the
critical endpoint conjugator belong to the assembly of original 14.6.13.
Source: Aschbacher--Smith, printed pp.1031--1032.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.OrthogonalSource
open OddNormalizer SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
variable {H U Z : Subgroup G} [IsElementaryAbelian 2 U]

/-- A summand viewed as a subgroup of the actual moved space. -/
def restrictedPlane (a : LocalQuotientAction H U Z)
    (A : Submodule (ZMod 2) (Additive (U ⧸ Z.subgroupOf U))) :
    Subgroup (Multiplicative (movedSpace a)) :=
  Representation.BinaryGroupAction.submoduleEquivSubgroup (A.comap (movedSpace a).subtype)

omit [Finite G] in
private theorem restrictedPlane_map (a : LocalQuotientAction H U Z)
    (A B : Submodule (ZMod 2) (Additive (U ⧸ Z.subgroupOf U))) (hA : A ≤ movedSpace a)
    (g : H ⧸ pCore 2 H) (he : A.map (a.representation g) = B) :
    let := movedAction a
    (restrictedPlane a A).map
      (MulDistribMulAction.toMulAut (H ⧸ pCore 2 H) (Multiplicative (movedSpace a)) g).toMonoidHom =
      restrictedPlane a B := by
  let := movedAction a
  ext v
  constructor
  · rintro ⟨w,hw,rfl⟩
    change a.representation g w.toAdd.val ∈ B
    rw [← he]
    exact ⟨w.toAdd.val,hw,rfl⟩
  · intro hv
    change v.toAdd.val ∈ B at hv
    rw [← he] at hv
    obtain ⟨w,hw,hwv⟩ := hv
    exact ⟨Multiplicative.ofAdd ⟨w,hA hw⟩,hw,Subtype.ext hwv⟩

/-- Recognition on the moved space, retaining the literal first-factor marking.
The source consumer below supplies the moved-space faithfulness premise. -/
theorem exchanged_four_coordinates (a : LocalQuotientAction H U Z)
    (T : Subgroup G) (hTH : T ≤ H) (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a T p H0 H1 H2)
    (hdim : Module.finrank (ZMod 2) (movedSpace a) = 4)
    (hf : ∀ g : H ⧸ pCore 2 H,
      (∀ v ∈ movedSpace a, a.representation g v = v) → g = 1) :
    p = 3 ∧ ∃ eG : (H ⧸ pCore 2 H) ≃* OrthogonalActor,
      ∃ eV : Multiplicative (movedSpace a) ≃* OrthogonalVector,
      (letI := movedAction a; letI := orthogonalAction
        ∀ g v, eV (g • v) = eG g • eV v) ∧
      (∀ v, eV v ∈ orthogonalCoordinatePlane 1 ↔
        v.toAdd.val ∈ subspaceCommutator a.representation ⊤ (actorImage H H1)) := by
  have hp : p = 3 := by
    have h := exchanged_moved_dimension a T hTH p H0 H1 H2 d
    change (p = 3 ∧ Module.finrank (ZMod 2) (movedSpace a) = 4) ∨
      Module.finrank (ZMod 2) (movedSpace a) = 8 at h
    omega
  let A := subspaceCommutator a.representation ⊤ (actorImage H H1)
  let B := subspaceCommutator a.representation ⊤ (actorImage H H2)
  have hAW : A ≤ movedSpace a := le_sup_left.trans d.split.le
  have hBW : B ≤ movedSpace a := le_sup_right.trans d.split.le
  have heq : Module.finrank (ZMod 2) A = Module.finrank (ZMod 2) B :=
    exchanged_dimensions_eq a T hTH p H0 H1 H2 d
  have hd := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [d.split,d.disjoint.eq_bot,finrank_bot,add_zero,hdim] at hd
  have hA : Module.finrank (ZMod 2) A = 2 := by omega
  have hB : Module.finrank (ZMod 2) B = 2 := by omega
  have hc : IsCompl (A.comap (movedSpace a).subtype) (B.comap (movedSpace a).subtype) := by
    constructor
    · apply Submodule.disjoint_def.mpr
      intro v ha hb
      apply Subtype.ext
      exact Submodule.disjoint_def.mp d.disjoint v.val ha hb
    · apply codisjoint_iff.mpr
      apply top_unique
      intro v _
      have hv : v.val ∈ A ⊔ B := d.split.symm ▸ v.property
      obtain ⟨x,hx,y,hy,hxy⟩ := Submodule.mem_sup.mp hv
      exact Submodule.mem_sup.mpr ⟨⟨x,hAW hx⟩,hx,⟨y,hBW hy⟩,hy,Subtype.ext hxy⟩
  have hcompl : IsCompl (restrictedPlane a A) (restrictedPlane a B) :=
    Representation.BinaryGroupAction.submoduleEquivSubgroup.isCompl_iff.mp hc
  have hcard (C : Submodule (ZMod 2) (Additive (U ⧸ Z.subgroupOf U)))
      (hCW : C ≤ movedSpace a) (hdC : Module.finrank (ZMod 2) C = 2) :
      Nat.card (restrictedPlane a C) = 4 := by
    rw [restrictedPlane, Representation.BinaryGroupAction.card_submoduleEquivSubgroup,
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      (Submodule.comapSubtypeEquivOfLe hCW).finrank_eq,hdC]
    norm_num
  let := movedAction a
  let : IsElementaryAbelian 2 (Multiplicative (movedSpace a)) :=
    Representation.BinaryGroupAction.elementary
  have hfaithful : fixingSubgroup (H ⧸ pCore 2 H)
      (Set.univ : Set (Multiplicative (movedSpace a))) = ⊥ := by
    apply bot_unique
    intro g hg
    apply Subgroup.mem_bot.mpr
    apply hf g
    intro v hv
    have h := (mem_fixingSubgroup_iff _).mp hg (Multiplicative.ofAdd ⟨v,hv⟩) (Set.mem_univ _)
    exact congrArg (fun w => w.toAdd.val) h
  have h72 : Nat.card (H ⧸ pCore 2 H) = 72 := by
    rw [exchanged_actor_card a T p H0 H1 H2 d,hp]
    norm_num
  have hperm (g : H ⧸ pCore 2 H) := exchanged_spaces_permuted a T hTH p H0 H1 H2 d g
  obtain ⟨eG,eV,he,hmark⟩ := equiv_marked_wreath_of_complementary_four
    (restrictedPlane a A) (restrictedPlane a B) hcompl (hcard A hAW hA) (hcard B hBW hB)
    hfaithful h72 (fun g => by
      rcases hperm g with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact Or.inl ⟨restrictedPlane_map a A A hAW g h1,restrictedPlane_map a B B hBW g h2⟩
      · exact Or.inr ⟨restrictedPlane_map a A B hAW g h1,restrictedPlane_map a B A hBW g h2⟩)
  refine ⟨hp,eG,eV,?_,hmark⟩
  intro g v
  funext i
  exact he g v i

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.OrthogonalSource

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
open OddNormalizer OrthogonalSource SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]

/-- Original 14.6.13(1)'s action recognition, conditional only on dimension four
and the unchanged earlier-source exchanged factors. The endpoint is separate. -/
theorem source_rankFour_orthogonal_action
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hdim : Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⊤) = 4) :
    p = 3 ∧ ∃ o : SourceOrthogonalFourAction H (conjugateSpanBy (localModule T M) H)
      (centralInvolutions T) (H.pCoreIn 2),
      ∃ i : OrthogonalPlaneIndex, o.plane i = firstSupport a H1 := by
  have hf (g : H ⧸ pCore 2 H)
      (hfix : ∀ v ∈ movedSpace a, a.representation g v = v) : g = 1 := by
    apply source_rankTwo_residual_moved_faithful
      hG T hempty hM hunique hmany hcard e hab H hH a g
    rw [← source_rankTwo_whole_moved_eq_residual hG T hempty hM hunique hmany hcard e hab H hH a]
    exact hfix
  obtain ⟨hp,eG,eV,he,hmark⟩ := exchanged_four_coordinates a (T : Subgroup G)
    hH.1.2 p H0 H1 H2 d hdim hf
  have hZ : centralInvolutions T ≤ ⁅conjugateSpanBy (localModule T M) H,H⁆ :=
    d.point_first.trans (commutator_mono le_rfl ((residual_le H1).trans (d.first_le.trans d.zero_le)))
  refine ⟨hp,liftAction a hZ eG eV he,1,?_⟩
  exact liftAction_plane a hZ eG eV he _ (le_sup_left.trans d.split.le) 1 hmark

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
