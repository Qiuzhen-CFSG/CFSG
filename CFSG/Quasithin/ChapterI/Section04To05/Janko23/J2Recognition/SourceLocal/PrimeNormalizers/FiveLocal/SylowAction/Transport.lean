module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction.Reduction

/-!
# Transport of the two five-families along the literal action

Conjugation preserves each five-family. Mapping a line from P to G commutes
with the normalizer's actual conjugation homomorphism, so an orbit in its
image remains in the same ambient family. The separation supplied by the
two-central branch therefore prevents fusion of the two marked lines.

Source: Aschbacher, *Sporadic Groups* (1994), 47.2, printed p.261.
-/

@[expose] public section

open Subgroup
open scoped Pointwise

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem fiveCentralizing_conjugate {t : G} {E : Subgroup G}
    (hE : FiveCentralizing t E) (g : G) :
    FiveCentralizing t (E.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hcard, u, htu, hEu⟩ := hE
  refine ⟨?_, (MulAut.conj g) u, htu.trans (isConj_iff.mpr ⟨g, rfl⟩), ?_⟩
  · rw [card_map_of_injective (MulAut.conj g).injective, hcard]
  · rintro _ ⟨x, hx, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg (MulAut.conj g) (mem_centralizer_singleton_iff.mp (hEu hx))
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using he

omit [Finite G] in
theorem lineImage_action (P : Sylow 5 G) (L : Subgroup P)
    (g : normalizer (P : Set G)) :
    lineImage P (L.map ((P : Subgroup G).normalizerMonoidHom g).toMonoidHom) =
      (lineImage P L).map (MulAut.conj (g : G)).toMonoidHom := by
  unfold lineImage
  rw [map_map, map_map]
  rfl

omit [Finite G] in
theorem fiveCentralizing_of_lineOrbit (P : Sylow 5 G) {t : G} {A L : Subgroup P}
    (hA : FiveCentralizing t (lineImage P A))
    (hL : InLineOrbit (automizer P) A L) :
    FiveCentralizing t (lineImage P L) := by
  obtain ⟨a, ha⟩ := hL
  obtain ⟨g, hg⟩ := a.property
  have hAL : A.map ((P : Subgroup G).normalizerMonoidHom g).toMonoidHom = L := by
    rw [hg]
    exact ha
  rw [← hAL, lineImage_action]
  exact fiveCentralizing_conjugate hA g

/-- The source separation assertion forbids fusion in the actual automizer. -/
theorem nonfusion_of_markings {D : Seed G} {t : G}
    (hB : TwoCentralFiveFamily D t) (P : Sylow 5 G) (A B : Subgroup P)
    (hA : FiveCentralizing t (lineImage P A))
    (hBline : FiveCentralizing D.z (lineImage P B)) :
    ¬ InLineOrbit (automizer P) A B := by
  intro h
  exact hB.separated _ (fiveCentralizing_of_lineOrbit P hA h) hBline

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction
