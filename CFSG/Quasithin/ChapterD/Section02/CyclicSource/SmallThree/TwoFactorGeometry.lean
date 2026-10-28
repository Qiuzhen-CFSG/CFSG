module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.SmallThree.TwoFactorElementaryExclusion
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.Preparation
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.GlobalOrthogonal
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.GlobalTransport

/-!
# The two-support ambient order bound and generating involutions

Ambient conjugation permutes the literal canonical support factors.
Their two support planes therefore give the existing faithful embedding
in O₄⁺(2), whose order is 72. The starred family generates by elements
of square one, and a rank-one starred member supplies an actual involution
of fixed codimension two at cubic ratio two.

These are the representation inputs for the two-factor group argument
in Aschbacher--Smith D.2.25, printed p.190.
-/

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.CyclicSource.SmallThree
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

public theorem two_supports_card_dvd_seventy_two (hf : Function.Injective ρ)
    (P : Subgroup G) [P.Normal] [IsElementaryAbelian 3 P]
    (d : FittingConfigurations.SupportFactors ρ P 2) : Nat.card G ∣ 72 := by
  obtain ⟨_,f,hfi,_⟩ := d.exists_isometry_embedding ρ hf (d.factor_conj_closed ρ hf)
  exact (Subgroup.card_dvd_of_injective f hfi).trans
    (OrthogonalFourBinary.isometryGroup_card ▸ dvd_rfl)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
public theorem involution_generated_of_Jhat_eq_top (hgen : Jhat ρ = ⊤) :
    closure {g : G | g ^ 2 = 1} = ⊤ := by
  apply top_unique
  rw [← hgen]
  apply sSup_le
  intro A hA a ha
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  exact subset_closure (elemPow_eq_one_of_isElementaryAbelian a ha)

omit [FiniteDimensional (ZMod 2) V] in
public theorem exists_rank_two_involution (hratio : cubicRatio ρ = 2)
    (hrank : ∀ A ∈ QhatStar ρ, rank A = 1) :
    ∃ t : G, orderOf t = 2 ∧ fixedCodim ρ (zpowers t) = 2 := by
  obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff ρ).mpr (hratio ▸ le_rfl)
  obtain ⟨t,ht,he⟩ := starred_generator ρ hA (hrank A hA)
  refine ⟨t,ht,?_⟩
  rw [he]
  exact_mod_cast (starred_codimension ρ hA (hrank A hA)).trans hratio
end CFSG.Quasithin.ChapterD.CyclicSource.SmallThree
