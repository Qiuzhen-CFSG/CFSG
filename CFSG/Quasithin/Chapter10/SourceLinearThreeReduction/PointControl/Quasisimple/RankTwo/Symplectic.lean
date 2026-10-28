module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Symplectic
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Preparation
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Symplectic

/-!
# The actual symplectic containing-component branch

The proper local image at the full restricted Sylow is conjugate to a
point or plane parabolic residual. Compose that conjugation with the
given central-quotient equivalence to mark the literal image of L.
The prime-scalar obstruction then excludes the original escaping component.
Neither an A₅ quotient nor irreducibility of the chosen module is required.

Source: Aschbacher--Smith A.3.12(2) and 10.2.9, pp.47--48,750--751.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.RankTwo
open Chapter3.Section02 ChapterA.Section03 Theory.SpecificGroups.SymplecticFour
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c

/-- The full point Sylow supplies an actual symplectic marking of the
original local image, over the field in the given model. -/
theorem symplectic_placement [Group.IsPerfect I]
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (eI : (I ⧸ center I) ≃* Sp F) :
    ∃ f : (I ⧸ center I) ≃* Sp F,
      (L.subgroupOf I).map
        (f.toMonoidHom.comp (QuotientGroup.mk' (center I))) = pointLocal ∨
      (L.subgroupOf I).map
        (f.toMonoidHom.comp (QuotientGroup.mk' (center I))) = planeLocal := by
  obtain ⟨S,_,hB,_,_,hproper,_⟩ := center_quotient_data D c
  let q := QuotientGroup.mk' (center I)
  let B := (L.subgroupOf I).map q
  let R := S.mapSurjective (QuotientGroup.mk'_surjective (center I))
  let A := B.map eI.toMonoidHom
  let : Group.IsSolvable eI.toMonoidHom.ker := by
    rw [eI.toMonoidHom.ker_eq_bot_iff.mpr eI.injective]
    infer_instance
  have hA : A ∈ localCComponents (R.mapSurjective (f := eI.toMonoidHom) eI.surjective) :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hB eI.toMonoidHom
  have hp : A ≠ ⊤ := by
    intro ht
    apply hproper
    apply map_injective (f := eI.toMonoidHom) eI.injective
    rw [map_top_of_surjective _ eI.surjective]
    exact ht
  obtain ⟨g,hg⟩ := SourceEmbeddings.FiveLocalFF.symplectic_local_placement
    hF hn (R.mapSurjective (f := eI.toMonoidHom) eI.surjective) A hA hp
  refine ⟨eI.trans (MulAut.conj g), ?_⟩
  have he : (eI.trans (MulAut.conj g)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp eI.toMonoidHom := by ext; rfl
  simpa only [A,B,q,map_map,he,MonoidHom.comp_assoc] using hg

/-- The original scalar contradiction discharges the symplectic row of
the actual rank-two catalogue, including its subgroup-marking premise. -/
theorem not_symplectic [Group.IsPerfect I] {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSp (I ⧸ center I) 2 (2 ^ n)) : False := by
  obtain ⟨F,_,_,hF,⟨eP⟩⟩ := hm
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  let eI := eP.trans (EvenProjective.equiv (F := F)).symm
  obtain ⟨f,hf⟩ := symplectic_placement D c hF (by omega) eI
  exact symplectic_marking_impossible D c hF (by omega) f hf

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.RankTwo
