module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellSelection.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.BlockRecognition.Source
/-!
# Uniform C.1.18 selection with the block alternative discharged

The actual residual commutator bound yields the named L₂ or A₃ block by
BlockRecognition. Substituting this theorem in the maximal-family selection
leaves exactly the independently proved Campbell Theorem A commutator input.
The pair is chosen before every finite overgroup and every marking, and the
last theorem performs the literal center restriction in C.1.19.

Source: Campbell II.8, printed pp.36–38; Aschbacher–Smith C.1.18–19.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
universe u v
variable {B : Type u} [Group B] [Finite B] [Nontrivial B]

theorem exists_universal_pair_of_campbell_theoremA
    (hp : IsPGroup 2 B) (hB : IsBaumannFixed B)
    (hA : ∀ (H : Type v) [Group H] [Finite H] (e : B →* H), InLocalClass e →
      (∀ a : MulAut B, ((Campbell.V H).comap e |>.map a.toMonoidHom).map e ≤ pCore 2 H) →
      ∀ a : MulAut B,
        ⁅Campbell.J (⊤ : Subgroup H),((Campbell.F H).comap e |>.map a.toMonoidHom).map e⁆ ≤ Campbell.F H) :
    ∃ D : CharacteristicPair B, D.Universal.{u,v} :=
  exists_universal_pair_of_campbell_inputs hp hB hA
    (fun _ _ _ _ h hc => h.blockAlternative_of_residual_commutator_le hB hc)

theorem exists_reducedPair_of_campbell_theoremA
    {S : Type u} [Group S] [Finite S]
    (hp : IsPGroup 2 S) (B : Subgroup S) [B.Characteristic] [Nontrivial B]
    (hB : IsBaumannFixed B)
    (hA : ∀ (H : Type v) [Group H] [Finite H] (e : B →* H), InLocalClass e →
      (∀ a : MulAut B, ((Campbell.V H).comap e |>.map a.toMonoidHom).map e ≤ pCore 2 H) →
      ∀ a : MulAut B,
        ⁅Campbell.J (⊤ : Subgroup H),((Campbell.F H).comap e |>.map a.toMonoidHom).map e⁆ ≤ Campbell.F H) :
    ∃ C : RankOneCharacteristicPair B,
      ∀ (H : Type v) [Group H] [Finite H] (e : B →* H),
        InLocalClass e → Alternatives (C.first.subgroupOf B) C.second e :=
  exists_reducedPair_of_campbell_inputs hp B hB hA
    (fun _ _ _ _ h hc => h.blockAlternative_of_residual_commutator_le hB hc)
end CFSG.Quasithin.ChapterC.GlaubermanNiles
