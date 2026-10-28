module
public import Stellmacher.SectionTen.TenOneCommonIntersection
public import Stellmacher.SectionNine.LemmaNineFive

/-!
# The transvection cases in Stellmacher (10.1)

If an actual first-module actor outside the terminal core has terminal-module
commutator of order two modulo the terminal center, the alternatives of (9.5) apply: the terminal
module has order eight with local quotient SL₂(2), or order thirty-two with
wreath-product quotient and endpoint-module intersection of order eight.
Only that genuine quotient-displacement case is assumed; the required
first-module commutator containment follows from the actual geometry.
The ambient order-two corollary retains its earlier public interface.

Both endpoint modules lie in the generated middle neighborhood. Its derived
upper bound therefore puts the actor commutator in their intersection. For
the ambient order-two corollary, the
faithful terminal quotient action shows that this commutator cannot lie in
the terminal center. Two distinct subgroups of order two inside the elementary
terminal module have a join of order four, giving the exact displacement
index used by (9.5). Critical length three identifies the predecessor in that
theorem with the first step.

Source: Stellmacher, Journal of Algebra 190 (1997), (10.1), printed p.60,
the paragraph yielding (5) and (6) after (4), `refs/files/stellmacher-n-group.pdf`.
The bars in the source mean V/Z, as defined on printed p.59. The wreath
alternative is retained here; its later exclusion is separate.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_quotient_transvection_cases
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (actor : G)
    (hactor : actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hout : actor ∉ QAt ctx.Γ ctx.criticalPath.a')
    (hindex : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    (Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2 ^ 3 ∧
        QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
          (QAt ctx.Γ ctx.criticalPath.a') SL2Two) ∨
      (Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2 ^ 5 ∧
        QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
          (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2 ∧
        Nat.card (VAt ctx.Γ ctx.criticalPath.a' ⊓
          VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) = 2 ^ 3) := by
  let Wnext := GeneratedNeighborhoodV ctx.Γ middle
  obtain ⟨_, hfirst, hterminal, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hVW (vertex : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent middle vertex) :
      VAt ctx.Γ vertex ≤ Wnext :=
    le_sSup ⟨vertex, (mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj, rfl⟩
  have hDderived : ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ≤
      DerivedAmbient Wnext := by
    rw [show DerivedAmbient Wnext = ⁅Wnext, Wnext⁆ from Subgroup.map_subtype_commutator Wnext]
    exact Subgroup.commutator_mono (hVW _ hterminal)
      ((Subgroup.zpowers_le.mpr hactor).trans (hVW _ hfirst))
  have hDI := hDderived.trans (ten_one_generated_derived_le_intersection ctx middle hpath)
  have hfirstPath : IsCriticalPathOffset ctx.Γ ctx.criticalPath
      (ctx.criticalPath.length - 2) ctx.criticalPath.firstStep := by
    refine ⟨⟨1, by rw [ctx.critical_length]; decide⟩, ?_, ctx.criticalPath.path_first⟩
    simp [ctx.critical_length]
  exact lemma_nine_five_ambient ctx.toAmbientSectionNineContext hb
    ctx.criticalPath.firstStep hfirstPath actor ⟨hactor, hout⟩ hindex (hDI.trans inf_le_left)


public theorem ten_one_transvection_cases
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (actor : G)
    (hactor : actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hout : actor ∉ QAt ctx.Γ ctx.criticalPath.a')
    (hcard : Nat.card (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ : Subgroup G) = 2) :
    (Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2 ^ 3 ∧
        QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
          (QAt ctx.Γ ctx.criticalPath.a') SL2Two) ∨
      (Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2 ^ 5 ∧
        QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
          (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2 ∧
        Nat.card (VAt ctx.Γ ctx.criticalPath.a' ⊓
          VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) = 2 ^ 3) := by
  let D := ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆
  let Z := ZAt ctx.Γ ctx.criticalPath.a'
  let Wnext := GeneratedNeighborhoodV ctx.Γ middle
  obtain ⟨_, hfirst, hterminal, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hVW (vertex : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent middle vertex) :
      VAt ctx.Γ vertex ≤ Wnext :=
    le_sSup ⟨vertex, (mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj, rfl⟩
  have hDderived : D ≤ DerivedAmbient Wnext := by
    rw [show DerivedAmbient Wnext = ⁅Wnext, Wnext⁆ from Subgroup.map_subtype_commutator Wnext]
    exact Subgroup.commutator_mono (hVW _ hterminal)
      ((Subgroup.zpowers_le.mpr hactor).trans (hVW _ hfirst))
  have hDI := hDderived.trans (ten_one_generated_derived_le_intersection ctx middle hpath)
  obtain ⟨mover, _, hmover⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  have horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep ctx.criticalPath.a' :=
    ⟨mover, hmover⟩
  have hdata := nine_next_center_commutator_and_kernel
    ctx.toAmbientSectionNineContext hb ctx.criticalPath.a' horbit
  have hactorP : actor ∈ GAt ctx.Γ ctx.criticalPath.a' :=
    (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.2 hactor
  have hnot : ¬ D ≤ Z := fun hle => hout ((hdata.2.2 actor hactorP).mp hle)
  have hZcard : Nat.card Z = 2 := hdata.1
  have hDcard : Nat.card D = 2 := hcard
  have hdisjoint : D ⊓ Z = ⊥ := by
    have hdiv := Subgroup.card_dvd_of_le (show D ⊓ Z ≤ D from inf_le_left)
    rw [hDcard] at hdiv
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hone | htwo
    · exact Subgroup.card_eq_one.mp hone
    · exact False.elim (hnot
        ((Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [htwo, hDcard])).ge.trans inf_le_right))
  let _ : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.a') :=
    (nine_three_second_extraction_inputs ctx.toLocalContext.toSectionNineLocalContext hb).2.2.1
  have hZU : Z ≤ VAt ctx.Γ ctx.criticalPath.a' := by
    dsimp only [Z]
    rw [← hdata.2.1]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((show QAt ctx.Γ ctx.criticalPath.a' ≤ GAt ctx.Γ ctx.criticalPath.a' from by
        rw [QAt, q, ctx.Γ.twoCoreAt_def]; exact twoCoreIn_le _).trans
          (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a'))
  have hnorm : Z ≤ Subgroup.normalizer (D : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro element helement
    rw [Subgroup.mem_centralizer_iff]
    intro other hother
    exact congrArg Subtype.val (mul_comm
      (⟨other, (hDI hother).2⟩ : VAt ctx.Γ ctx.criticalPath.a')
      (⟨element, hZU helement⟩ : VAt ctx.Γ ctx.criticalPath.a'))
  have hjoin := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes D Z hnorm
  rw [hDcard, hZcard, hdisjoint, Subgroup.card_bot, one_mul] at hjoin
  have hindex : QuotientCardEq (D ⊔ Z) Z 2 := by
    change Nat.card (D ⊔ Z : Subgroup G) = 2 * Nat.card Z
    rw [hZcard]
    exact hjoin.symm
  have hfirstPath : IsCriticalPathOffset ctx.Γ ctx.criticalPath
      (ctx.criticalPath.length - 2) ctx.criticalPath.firstStep := by
    refine ⟨⟨1, by rw [ctx.critical_length]; decide⟩, ?_, ctx.criticalPath.path_first⟩
    simp [ctx.critical_length]
  exact lemma_nine_five_ambient ctx.toAmbientSectionNineContext hb
    ctx.criticalPath.firstStep hfirstPath actor ⟨hactor, hout⟩ hindex (hDI.trans inf_le_left)

end Stellmacher.SectionTen
