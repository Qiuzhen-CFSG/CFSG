module
public import CFSG.Quasithin.Chapter10.SourceA5PointFFModels.Symplectic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SpecialLinearThree
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2Image
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.BinaryLinear.Source

/-!
# Local-section sieve in the actual point-component FF action

The original subgroup L is carried through its specified action quotient,
retaining its A₅ marking and its possibly nontrivial two-core. Linear-three
and G₂ images lie in field-four parabolic residuals; the higher binary linear
and binary derived G₂ rows cannot contain this local section. These outputs
feed the actual representation movement and original-group lifting steps.

Source: Aschbacher–Smith, 10.2.9, printed pp.751–752.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings.FiveLocalFF
noncomputable section
variable {G : Type*} [Group G] [Finite G] {L I : Subgroup G}

private def restrictedFive (hLI : L ≤ I)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    ((L.subgroupOf I) ⧸ pCore 2 (L.subgroupOf I)) ≃* alternatingGroup (Fin 5) :=
  (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLI)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hLI))).trans e

theorem source_a5_point_linear_ff_placement
    (hLI : L ≤ I) (S : Sylow 2 I)
    (hlocal : L.subgroupOf I ∈ localCComponents S)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (f : I →* SL(3,F)) (hf : Function.Surjective f)
    (hks : Group.IsSolvable f.ker)
    (hk : IsPGroup 2 (f.subgroupMap (L.subgroupOf I)).ker)
    (hproper : (L.subgroupOf I).map f ≠ ⊤)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    Nat.card F = 4 ∧ ∃ g : SL(3,F),
      ((L.subgroupOf I).map f).map (MulAut.conj g).toMonoidHom = Matrix.PSL3.LinearThree.pointLocalSL F ∨
      ((L.subgroupOf I).map f).map (MulAut.conj g).toMonoidHom = Matrix.PSL3.LinearThree.lineLocalSL F :=
  special_linear_three_five_section_image hF f hf hks S (L.subgroupOf I) hlocal hk
    hproper (restrictedFive hLI e)

theorem source_a5_point_g2_ff_placement
    (hLI : L ≤ I) (S : Sylow 2 I)
    (hlocal : L.subgroupOf I ∈ localCComponents S)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (f : I →* Atlas.G2.Model F) (hf : Function.Surjective f)
    (hks : Group.IsSolvable f.ker)
    (hk : IsPGroup 2 (f.subgroupMap (L.subgroupOf I)).ker)
    (hproper : (L.subgroupOf I).map f ≠ ⊤)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    Nat.card F = 4 ∧ ∃ g : Atlas.G2.Model F,
      ((L.subgroupOf I).map f).map (MulAut.conj g).toMonoidHom = Atlas.G2.LieParabolicSetup.local₁ ∨
      ((L.subgroupOf I).map f).map (MulAut.conj g).toMonoidHom = Atlas.G2.LieParabolicSetup.local₂ :=
  G2.five_section_image hF f hf hks S (L.subgroupOf I) hlocal hk
    hproper (restrictedFive hLI e)

theorem source_a5_point_higher_binary_ff_excluded
    (hLI : L ≤ I) (S : Sylow 2 I)
    (hlocal : L.subgroupOf I ∈ localCComponents S)
    {M : Type*} [Group M] [Finite M]
    (f : I →* M) (hf : Function.Surjective f)
    (hks : Group.IsSolvable f.ker)
    (hk : IsPGroup 2 (f.subgroupMap (L.subgroupOf I)).ker)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {d : ℕ} (hd : d = 4 ∨ d = 5) (hm : ClassicalGroup.IsPSL M d 2) : False :=
  BinaryLinear.image_excluded f hf hks S (L.subgroupOf I) hlocal hk
    (restrictedFive hLI e) hd hm

theorem source_a5_point_binary_g2_ff_excluded
    (hLI : L ≤ I)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    (f : I →* commutator (Atlas.G2.Model F))
    (hk : IsPGroup 2 (f.subgroupMap (L.subgroupOf I)).ker)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) : False :=
  G2.binary_derived_image_excluded hF f (L.subgroupOf I) hk (restrictedFive hLI e)
end
end CFSG.Quasithin.Chapter10
