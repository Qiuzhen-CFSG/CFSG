module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.MarkedTorus
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.MarkedDiagonal

/-!
# The actual diagonal as the original five-line action kernel

The marked I acts onto both cyclic-five automorphism groups. Its restriction
to B₅ is therefore onto a group of order four, so the kernel has order four.
The original diagonal Iz already has that order and centralizes B₅, hence
is exactly I∩C_G(B₅). This identifies any transported scalar of order four
inside that kernel with the specified source Iz.

Source: Aschbacher–Smith, discussion before J.4.8, printed p.443.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
open Centralizers Centralizers.Choices MarkedInverter
open Tits.ExceptionalParabolics.FullRee
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
  {F : Subgroup G} (e : first ≃* F)

theorem sourceI_five_centralizer_card
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5)
    (hfusion : IsConj (sourceU e) c.z) :
    Nat.card (sourceI e⊓centralizer (B5Image B5:Set G) : Subgroup G)=4 := by
  let A := fixedFive B5 (sourceU e)
  let φ : sourceI e→*MulAut (B5Image B5) :=
    (MonoidHom.fst (MulAut (B5Image B5)) (MulAut A)).comp (sourceTorusAction c B5 e hz hfive)
  have hsurj : Function.Surjective φ := by
    intro a
    obtain ⟨i,hi⟩ := (sourceTorusAction_bijective c B5 e hz hfive hfusion).2 (a,1)
    exact ⟨i,congrArg Prod.fst hi⟩
  have hker : φ.ker.map (sourceI e).subtype=sourceI e⊓centralizer (B5Image B5:Set G) := by
    ext x
    constructor
    · rintro ⟨i,hi,rfl⟩
      refine ⟨i.property,?_⟩
      intro b hb
      have hh := congrArg (fun a:MulAut (B5Image B5) => (a ⟨b,hb⟩:G)) hi
      change (i:G)*b*(i:G)⁻¹=b at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · rintro ⟨hxI,hxC⟩
      refine ⟨⟨x,hxI⟩,?_,rfl⟩
      change φ ⟨x,hxI⟩=1
      apply MulEquiv.ext
      intro b
      apply Subtype.ext
      change x*(b:G)*x⁻¹=(b:G)
      exact mul_inv_eq_iff_eq_mul.mpr (hxC b b.property).symm
  have hB := B5Image_card d.card_Z B5
  let : IsCyclic (B5Image B5) := isCyclic_of_prime_card hB
  have hAut : Nat.card (MulAut (B5Image B5))=4 := by
    rw [IsCyclic.card_mulAut,hB,Nat.totient_prime (by decide : Nat.Prime 5)]
  have hh := φ.ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top.mpr hsurj,card_top,hAut,sourceI_card e] at hh
  have hk : Nat.card φ.ker=4 := by omega
  rw [← hker,card_map_of_injective (sourceI e).subtype_injective,hk]

/-- The original marked diagonal is exactly the line-action kernel. -/
theorem sourceIz_eq_five_centralizer
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5)
    (hfusion : IsConj (sourceU e) c.z) :
    sourceIz e=sourceI e⊓centralizer (B5Image B5:Set G) := by
  apply eq_of_le_of_card_ge (le_inf (sourceIz_le_I e) (sourceIz_le_G5 B5 e hfive))
  rw [sourceI_five_centralizer_card c B5 e hz hfive hfusion,sourceIz_card e]

/-- Any original cyclic-four scalar centralizing B₅ inside I is precisely Iz. -/
theorem eq_sourceIz_of_four
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5)
    (hfusion : IsConj (sourceU e) c.z) (C:Subgroup G) (hC:Nat.card C=4)
    (hCI:C≤sourceI e) (hCB:C≤centralizer (B5Image B5:Set G)) : C=sourceIz e := by
  rw [sourceIz_eq_five_centralizer c B5 e hz hfive hfusion]
  exact eq_of_le_of_card_ge (le_inf hCI hCB) (by
    rw [sourceI_five_centralizer_card c B5 e hz hfive hfusion,hC])

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
