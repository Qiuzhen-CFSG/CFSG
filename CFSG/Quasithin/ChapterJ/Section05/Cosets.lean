module

public import CFSG.Quasithin.ChapterJ.Section03.Source
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.Embedding
public import Theory.GroupAction.MaximalCosetOrbit
public import Mathlib.Data.Set.Card

/-!
# The original coset space in J.5.2–3

The original TypeRu order theorem and the earlier recognized full Ree subgroup
make G/F have 4060 points. A maximal first parabolic normalized by an element
outside N_G(F) gives the source suborbit of length1755, leaving2304 points.
The normalizer escape is retained explicitly: maximality alone does not
exclude equality of the two full point stabilizers.

The equivalence F≃²F₄(2) is the genuine earlier J.4.7 input, not an ambient
Rudvalis recognition premise. The source construction and its marked first
parabolic are assembled by the J.4 owner.

Source: Aschbacher–Smith J.5.2–3, printed p.445.
-/

@[expose] public section
noncomputable section
open Subgroup MulAction
namespace CFSG.Quasithin.ChapterJ.Section05
variable {G:Type*} [Group G] [Finite G]

/-- The original left-coset action, equivalent to the source right-action convention. -/
abbrev Cosets (F:Subgroup G) := G⧸F

/-- The original distinguished coset. -/
abbrev basePoint (F:Subgroup G) : Cosets F := ((1:G):G⧸F)

/-- J.5.2, using the original TypeRu order and the genuine earlier full-Ree recognition. -/
theorem source_coset_card (h:IsTypeRu G) (F:Subgroup G) (e:F≃*ReeF4.Model 0) :
    Nat.card (Cosets F)=4060 := by
  have hF:Nat.card F=35942400:=
    (Nat.card_congr e.toEquiv).trans Tits.ExceptionalParabolics.FullRee.group_card
  have hc:=card_eq_card_quotient_mul_card_subgroup F
  rw [Section03.theorem_J_3_1 h,hF] at hc
  change 2^14*3^3*5^3*7*13*29=Nat.card (Cosets F)*35942400 at hc
  norm_num at hc
  omega

/-- The source parabolic has the required suborbit size on the literal quotient. -/
theorem source_first_orbit_card {F M:Subgroup G} (e:F≃*ReeF4.Model 0)
    (hM:M⋖F) (hcard:Nat.card M=20480) {g:G}
    (hgM:g∈normalizer (M:Set G)) (hgF:g∉normalizer (F:Set G)) :
    Nat.card (orbit F (g•basePoint F))=1755 := by
  have hc:=card_coset_orbit_mul_card_of_covBy hM hgM hgF
  have hF:Nat.card F=35942400:=
    (Nat.card_congr e.toEquiv).trans Tits.ExceptionalParabolics.FullRee.group_card
  rw [hcard,hF] at hc
  change Nat.card (orbit F (g•basePoint F))*20480=35942400 at hc
  omega

omit [Finite G] in
/-- The base point is disjoint from a suborbit obtained by normalizer escape. -/
theorem base_not_mem_first_orbit {F:Subgroup G} {g:G}
    (hg:g∉normalizer (F:Set G)) : basePoint F∉orbit F (g•basePoint F) := by
  rintro ⟨a,ha⟩
  have haf:(a:G)•basePoint F=basePoint F:=
    (show (a:G)∈stabilizer G (basePoint F) from (stabilizer_quotient F).symm ▸ a.property)
  have he:g•basePoint F=basePoint F:=smul_left_cancel a (ha.trans haf.symm)
  exact hg (F.le_normalizer ((stabilizer_quotient F) ▸ he))

/-- The complement of the first two orbits has the literal source order2304. -/
theorem source_remainder_card (h:IsTypeRu G) {F M:Subgroup G} (e:F≃*ReeF4.Model 0)
    (hM:M⋖F) (hcard:Nat.card M=20480) {g:G}
    (hgM:g∈normalizer (M:Set G)) (hgF:g∉normalizer (F:Set G)) :
    (({basePoint F}:Set (Cosets F))∪orbit F (g•basePoint F))ᶜ.ncard=2304 := by
  have hc:=source_coset_card h F e
  have ho:=source_first_orbit_card e hM hcard hgM hgF
  have hd:Disjoint ({basePoint F}:Set (Cosets F)) (orbit F (g•basePoint F)):=
    Set.disjoint_singleton_left.mpr (base_not_mem_first_orbit hgF)
  have hh:=Set.ncard_add_ncard_compl (({basePoint F}:Set (Cosets F))∪orbit F (g•basePoint F))
  rw [Set.ncard_union_eq hd,Set.ncard_singleton,hc] at hh
  change 1+Nat.card (orbit F (g•basePoint F))+
    (({basePoint F}:Set (Cosets F))∪orbit F (g•basePoint F))ᶜ.ncard=4060 at hh
  rw [ho] at hh
  omega

end CFSG.Quasithin.ChapterJ.Section05
