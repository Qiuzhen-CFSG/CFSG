module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.CubicSylow.LocalAction

/-!
# Correcting cubic subgroup fusion into the ambient normalizer

In the abelian branch, the given conjugator from C_R(f) to B sends R
into C_G(B). Its image is therefore a three-subgroup of N_G(B) of the
same order as R. Sylow conjugacy in N_G(B) supplies a correction fixing
B and carrying that image back to R. Their product is an actual element
of N_G(R) carrying C_R(f) to B.

This proves the fusion step used by the source's point-orbit argument
without presuming that R is already an ambient Sylow subgroup.

Source: Aschbacher–Smith, final paragraph of J.2.7, printed p.437 (PDF p.448).
-/

public section
namespace CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow
open Subgroup LocalAction LocalAction.PointOrbits
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)
variable {hB : Nat.card c.B = 3}
variable {e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6))}
variable (D : LocalAction.Data c hB e)

/-- Abelian Sylow fusion changes the given F-to-B conjugator into an element
of the actual normalizer of R. -/
theorem fixed_fusion_in_normalizer (hc : IsMulCommutative (ambient c D.R)) :
    ∃ g : normalizer (ambient c D.R : Set G),
      (fixed c D.R (D.f : G)).map (MulAut.conj (g : G)).toMonoidHom = c.B := by
  let := hc
  obtain ⟨g, hg⟩ := D.fixed_fusion
  let U := (ambient c D.R).map (MulAut.conj g).toMonoidHom
  have hUN : U ≤ c.NB := by
    apply le_trans ?_ c.GB_le_NB
    rintro _ ⟨x, hx, rfl⟩ b hb
    rw [← hg] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    simpa only [Subgroup.coe_mul, map_mul, MulEquiv.coe_toMonoidHom] using congrArg (MulAut.conj g) (congrArg Subtype.val
      (mul_comm' (⟨a, ha.1⟩ : ambient c D.R) ⟨x, hx⟩))
  have hUc : Nat.card U = 27 := by
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact D.r_card
  have hUp : IsPGroup 3 (U.subgroupOf c.NB) :=
    ((ambient_isPGroup c D.R).map (MulAut.conj g).toMonoidHom).comap_subtype
  obtain ⟨Q, hQ⟩ := hUp.exists_le_sylow
  have hUQ : U.subgroupOf c.NB = (Q : Subgroup c.NB) := by
    apply eq_of_le_of_card_ge hQ
    rw [card c hB e Q,
      Nat.card_congr (subgroupOfEquivOfLe hUN).toEquiv, hUc]
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq c.NB Q D.R
  have hmap : U.map (MulAut.conj (n : G)).toMonoidHom = ambient c D.R := by
    rw [← map_subgroupOf_eq_of_le hUN, hUQ, map_map]
    change _ = (D.R : Subgroup c.NB).map c.NB.subtype
    rw [← hn]
    change _ = ((Q : Subgroup c.NB).map (MulAut.conj n).toMonoidHom).map c.NB.subtype
    rw [map_map]
    congr 1
  have hcomp (K : Subgroup G) :
      K.map (MulAut.conj ((n : G) * g)).toMonoidHom =
        (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj (n : G)).toMonoidHom := by
    rw [map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      mul_inv_rev, mul_assoc]
  have hnR : (n : G) * g ∈ normalizer (ambient c D.R : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact (hcomp _).trans hmap
  refine ⟨⟨(n : G) * g, hnR⟩, ?_⟩
  change (fixed c D.R (D.f : G)).map (MulAut.conj ((n : G) * g)).toMonoidHom = c.B
  rw [hcomp, hg]
  exact mem_normalizer_iff_map_conj_eq.mp n.property

end CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow
