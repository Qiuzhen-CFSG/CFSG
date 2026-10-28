module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.Local
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.Quotient

/-!
# Comparing the two quotients in the natural L₂ block branch

The block model has centerless quotient by O₂(L). The quasisimplicity already
supplied by the component witness therefore makes this quotient simple.
Relative normality and the common Sylow subgroup then identify it with the
actual star image. The resulting matrix quotient takes the actual M ∩ L to
the marked Borel, on the same lifts as the original local action map.

This comparison is needed before using the natural block representation in
the centralizer argument of Aschbacher–Smith 15.3.30, printed pp.1131–1132.
It uses the genuine block definition C.1.12, printed p.124.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo

variable {G : Type*} [Group G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I} {m n : ℕ}

/-- No simplicity classification is needed: the known quasisimple quotient
has trivial center in the block's actual characteristic-two matrix model. -/
theorem block_coreQuotient_simple (hblock : ChapterC.IsL2EvenBlock c.L m) :
    IsSimpleGroup (c.L ⧸ pCore 2 c.L) := by
  obtain ⟨_, _, E, _, _, hE, _, hmodel⟩ := hblock
  let := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hE)
  obtain ⟨e⟩ := hmodel.quotient_iso
  have hz : center (c.L ⧸ pCore 2 c.L) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have he : e x ∈ center (Matrix.SpecialLinearGroup (Fin 2) E) :=
      (centerCongr e ⟨x, hx⟩).property
    rw [Theory.PSL2.sl2_center_eq_bot E, mem_bot] at he
    exact e.injective (he.trans e.map_one.symm)
  let := c.core_quotient_quasisimple
  exact (MulEquiv.isSimpleGroup_congr
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot)).mp
      Theory.GroupTheory.IsQuasisimple.simple

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The block's core quotient and the marked linear star model agree through
the canonical map induced by conjugation on U_I. -/
noncomputable def BorelIdentification.coreLinear
    (b : BorelIdentification d I c n F) (h : Earlier d I c)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hblock : ChapterC.IsL2EvenBlock c.L m) :
    (c.L ⧸ pCore 2 c.L) ≃* Matrix.SpecialLinearGroup (Fin 2) F := by
  let := block_coreQuotient_simple hblock
  exact (SmallExtension.coreQuotientEquivStar d c h.component_normal P hP).trans b.linear

/-- The quotient comparison preserves the original component lifts. -/
theorem BorelIdentification.coreLinear_apply
    (b : BorelIdentification d I c n F) (h : Earlier d I c)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hblock : ChapterC.IsL2EvenBlock c.L m) (l : c.L) :
    b.coreLinear h P hP hblock (QuotientGroup.mk' (pCore 2 c.L) l) =
      b.linear (SmallExtension.componentMap d c l) := rfl

private theorem intersection_componentMap :
    (d.M.subgroupOf c.L).map (SmallExtension.componentMap d c) =
      (d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L) := by
  apply le_antisymm
  · rintro _ ⟨l, hl, rfl⟩
    exact ⟨⟨l, component_le c l.property⟩, ⟨hl, l.property⟩, rfl⟩
  · rintro ⟨x, hx⟩ ⟨l, hl, he⟩
    exact ⟨⟨l, hl.2⟩, hl.1, Subtype.ext he⟩

/-- The marked Borel is the image of the actual intersection under the
core quotient, not merely under an unrelated isomorphism of simple groups. -/
theorem BorelIdentification.coreLinear_borel
    (b : BorelIdentification d I c n F) (h : Earlier d I c)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hblock : ChapterC.IsL2EvenBlock c.L m) :
    (d.M.subgroupOf c.L).map
      ((b.coreLinear h P hP hblock).toMonoidHom.comp
        (QuotientGroup.mk' (pCore 2 c.L))) =
      Matrix.SpecialLinearGroup.rankOneBorel F := by
  have he : (b.coreLinear h P hP hblock).toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 c.L)) =
      b.linear.toMonoidHom.comp (SmallExtension.componentMap d c) := rfl
  rw [he, ← map_map, intersection_componentMap]
  exact b.linear_borel

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo

end
