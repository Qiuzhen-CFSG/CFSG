module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentReduction
/-!
# The actual component catalogue input in F.6.15–18

For the original SQTK cover, Theorem A gives strong quasithinness on the
literal central quotient of every component of the target quotient. The
K-group condition follows through the same section maps. Theorem C then
applies to this nonabelian simple quotient, retaining its actual models.
The cyclic consumer constructs and orients the component before applying
that catalogue. The A/C premises are the earlier source results owned by
the simultaneous A.2 assembly, not F.6.18 output assumptions.

The arithmetic consumer also checks the prime-field refinement in rows
(3)–(5): a power of degree at most two that is 3 or 5 modulo 8 must have
degree one. The original model and the mod-24 constraints are preserved.

Source: Aschbacher–Smith, Remark F.6.15 and the first two paragraphs of
F.6.18, printed pp.308–310.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
    {κ : GroupClass.{u}} {K : Subgroup G}

/-- The simple quotient of a component is an SQTK section of the original cover. -/
theorem component_central_quotient_sqtk
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (f : H →* G) (hf : Function.Surjective f) (hK : IsComponent G K) :
    IsSQTK κ (K ⧸ center K) := by
  let : IsQuasisimple K := hK.2
  let Q := K ⧸ center K
  let : IsSimpleGroup Q := IsQuasisimple.simple
  let : Group.IsPerfect Q := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center K))
  have hna : ¬ IsMulCommutative Q := Group.IsPerfect.not_isMulCommutative Q
  have hZ : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with hz | hz
    · exact hz
    · exact (hna (center_eq_top_iff.mp hz)).elim
  let : IsQuasisimple Q := { simple :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hsem : ChapterA.Section02.IsSemisimple Q := by
    apply top_unique
    exact le_sSup (show IsComponent Q ⊤ from
      ⟨.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩)
  have hsection : ChapterA.Section02.IsSectionOf Q H :=
    (ChapterA.Section02.IsSectionOf.quotient_subgroup K (center K)).ambient_surjective f hf
  exact ⟨hA.stronglyQuasithin_section hH.stronglyQuasithin hH.isKGroup hsection hsem,
    hsection.isKGroup hH.isKGroup⟩

/-- Remark F.6.15's actual model invocation uses Theorem C on K/Z(K),
with all rank and K-group hypotheses supplied by its original covering group. -/
theorem component_central_quotient_model
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ChapterA.Section02.TheoremC κ (K ⧸ center K))
    (hH : IsSQTK κ H) (f : H →* G) (hf : Function.Surjective f)
    (hK : IsComponent G K) : ChapterA.Section02.IsTheoremCModel (K ⧸ center K) := by
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center K))
  have hs := component_central_quotient_sqtk hA hH f hf hK
  exact hC inferInstance (Group.IsPerfect.not_isMulCommutative _) hs.stronglyQuasithin hs.isKGroup

variable {G₁ G₂ : Subgroup G}
/-- The actual normal component and its central quotient model in the cyclic branch.
Only the earlier simultaneous A/C results remain; the component, its orientation,
and the source rank/K hypotheses are constructed here. -/
theorem cyclic_component_model
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (S : Type u) [Group S] [Finite S], ChapterA.Section02.TheoremC κ S)
    (hH : IsSQTK κ H) (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (h : IsGoldschmidtTriple G₁ G₂) (hc : IsCyclic (pCore 3 G)) :
    ∃ K : Subgroup G, IsComponent G K ∧ K.Normal ∧
      ChapterA.Section02.IsTheoremCModel (K ⧸ center K) ∧
      (((pResidual 2 G₁).map G₁.subtype ≤ K ∧ K ⊔ G₂ = ⊤) ∨
       ((pResidual 2 G₂).map G₂.subtype ≤ K ∧ K ⊔ G₁ = ⊤)) := by
  obtain ⟨K, hK, hnormal, _, hlocal⟩ := cyclic_component_reduction hA hH e h hc
  exact ⟨K, hK, hnormal, component_central_quotient_model hA (hC _) hH
    (e.symm.toMonoidHom.comp (QuotientGroup.mk' _))
    (e.symm.surjective.comp (QuotientGroup.mk'_surjective _)) hK, hlocal⟩

/-- The degree-at-most-two restriction from Theorem C becomes degree one
for the nonsquare residues used in F.6.18(3)–(5). -/
theorem degree_one_of_small_degree_nonsquare_mod_eight {p e : ℕ}
    (he : e ≤ 2) (h8 : p ^ e % 8 = 3 ∨ p ^ e % 8 = 5) : e = 1 := by
  interval_cases e
  · norm_num at h8
  · rfl
  · have hp : p % 8 < 8 := Nat.mod_lt _ (by decide)
    interval_cases hm : p % 8 <;> norm_num [Nat.pow_mod, hm] at h8

omit [Finite G] in
/-- The prime-field and mod-24 clauses retain the actual PSL₂ model from
the preceding catalogue row. -/
theorem psl2_prime_model_of_source_parameters {p e : ℕ}
    (hp : p.Prime) (he : e ≤ 2)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 2 (p ^ e))
    (h8 : p ^ e % 8 = 3 ∨ p ^ e % 8 = 5)
    (h3 : (p ^ e % 4 = 1 ∧ p ^ e % 3 = 1) ∨
      (p ^ e % 4 = 3 ∧ p ^ e % 3 = 2)) :
    e = 1 ∧ p.Prime ∧ (p % 24 = 11 ∨ p % 24 = 13) ∧
      ClassicalGroup.IsPSL (K ⧸ center K) 2 p := by
  have heq := degree_one_of_small_degree_nonsquare_mod_eight he h8
  subst e
  simp only [pow_one] at hm h8 h3
  exact ⟨rfl, hp, primePower_mod24_of_source_congruences p h8 h3, hm⟩

end CFSG.Quasithin.ChapterF.SourceAssembly
