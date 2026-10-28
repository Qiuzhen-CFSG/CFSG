module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.TheoremA.OriginalEmbedding
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellSelection.Source

/-!
# The uniform Glauberman–Niles characteristic pair

Campbell Theorem A is proved for every original marking and every actual
Sylow automorphism. Substituting it into the maximal-family selector proves
C.1.18 with one intrinsic pair chosen before every finite overgroup and every
marking. The residual-layer block alternative has already been recognized
from the actual natural module. The second theorem performs C.1.19's literal
center restriction; neither theorem retains a selection or control premise.

Source: Campbell, Pushing up in Finite Groups, II.6–8, pp.31–38;
Aschbacher–Smith, The Classification of Quasithin Groups, C.1.18–19,
printed pp.126–127.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
universe u v

/-- One characteristic pair works for every original local-class embedding. -/
theorem exists_universal_characteristicPair
    {B : Type u} [Group B] [Finite B] [Nontrivial B]
    (hp : IsPGroup 2 B) (hB : IsBaumannFixed B) :
    ∃ D : CharacteristicPair B, D.Universal.{u,v} :=
  exists_universal_pair_of_campbell_theoremA hp hB
    (fun _ _ _ _ h hAll => h.campbell_theoremA_original hB hAll)

/-- The same single-pair choice after the original C.1.19 center restriction. -/
theorem exists_universal_reducedPair
    {S : Type u} [Group S] [Finite S]
    (hp : IsPGroup 2 S) (B : Subgroup S) [B.Characteristic] [Nontrivial B]
    (hB : IsBaumannFixed B) :
    ∃ C : RankOneCharacteristicPair B,
      ∀ (H : Type v) [Group H] [Finite H] (e : B →* H),
        InLocalClass e → Alternatives (C.first.subgroupOf B) C.second e :=
  exists_reducedPair_of_campbell_theoremA hp B hB
    (fun _ _ _ _ h hAll => h.campbell_theoremA_original hB hAll)
end CFSG.Quasithin.ChapterC.GlaubermanNiles
