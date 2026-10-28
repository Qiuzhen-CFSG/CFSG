module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeOvercomponent
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeExtension
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Generated

/-!
# Small full-extension completions of the original Ree normalizer pair

A compatible full-extension diagram on the two original full normalizers
gives a faithful completion in their join, with the literal whole overlap.
The ambient order bound implies the completion order bound. The Ree census
proves equality of orders and hence that the normalizers generate G; it also
gives a genuine generalized octagon with a sixteen-cycle.

The source realization of the extension, its compatible diagram and the
ambient order bound remain explicit earlier-source inputs. Recognition of
the octagon action as a native Ree extension is a further obligation; this
module does not yet assert a group isomorphism or GlobalExit.
Source: Aschbacher–Smith 5.3.1–4 and F.4.24, printed pp.658–659,287–288.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels
open ChapterF.SourceCompletion.GeneralReeExtension
open ChapterF.SourceCompletion
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G]

/-- Conditional source application with the original whole normalizers and
the entire extension order. No native recognition premise is used. -/
theorem Preparation.ree_full_normalizers_small_completion
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse))
    (E : SourceExtension m)
    (hext : Nonempty (RankTwoAmalgam.Iso
        (UnitaryNonbinary.Generated.amalgam (normalizer (L : Set G)) (normalizer (residual H : Set G))) E.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (UnitaryNonbinary.Generated.amalgam (normalizer (L : Set G)) (normalizer (residual H : Set G))) E.amalgam.reverse))
    (horder : Nat.card G ≤ Nat.card E.carrier) :
    2*m+1 = n ∧ 0 < m ∧
      normalizer (L : Set G) ⊔ normalizer (residual H : Set G) = ⊤ ∧
      Nat.card G = Nat.card E.carrier ∧
      ∃ c : Completion E (normalizer (L : Set G) ⊔ normalizer (residual H : Set G) : Subgroup G),
        c.left.range ⊓ c.right.range = c.middle.range ∧
        Function.Injective (MulAction.toPermHom
          (normalizer (L : Set G) ⊔ normalizer (residual H : Set G) : Subgroup G)
          (Vertex c.cosetFamily)) ∧
        (∀ v (p : (graph c.cosetFamily).Walk v v), p.IsCycle → 16 ≤ p.length) ∧
        (∀ v w, (graph c.cosetFamily).dist v w ≤ 8) ∧
        (∃ v, ∃ p : (graph c.cosetFamily).Walk v v, p.IsCycle ∧ p.length = 16) := by
  rcases he with he | he
  · exact (d.not_ree_unreversed h hH.1.1.2 hp m he).elim
  obtain ⟨e⟩ := he
  obtain ⟨hn,hm,_⟩ := d.ree_local_structure h hH.1.1.2 hp m e
  let X := normalizer (L : Set G) ⊔ normalizer (residual H : Set G)
  obtain ⟨c,hc⟩ := UnitaryNonbinary.Generated.exists_completion
    (normalizer (L : Set G)) (normalizer (residual H : Set G)) hext
  have hx : Nat.card X ≤ Nat.card G := Nat.card_le_card_of_injective _ X.subtype_injective
  have hcorder := hx.trans horder
  have heq := completion_order_eq E c hm hc hcorder
  have htop : X = ⊤ := X.eq_top_of_le_card (horder.trans_eq heq.symm)
  have hgorder : Nat.card G = Nat.card E.carrier :=
    le_antisymm horder (heq.symm.le.trans hx)
  exact ⟨hn,hm,htop,hgorder,c,hc,completion_vertex_action_injective E c hm hc,completion_octagon E c hm hc hcorder⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
