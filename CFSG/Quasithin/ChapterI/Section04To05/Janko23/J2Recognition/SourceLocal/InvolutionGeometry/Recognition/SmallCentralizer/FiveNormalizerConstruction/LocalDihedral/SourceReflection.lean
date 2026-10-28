module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer.FiveNormalizerConstruction.LocalDihedral.Order
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer.FiveNormalizerConstruction.LocalDihedral.SourceReflection.MarkedA5
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer.FiveNormalizerConstruction.LocalDihedral.SourceReflection.Extension

/-!
# An inverting involution in the literal local five-normalizer

Let H = C_G(z), Q = F*(H), and P ∈ Syl₅(H). The quotient normalizer
contains a marked pentagon reflection. Coprime quotient-normalizer lifting
gives x ∈ N_H(P) above it, with x² ∈ Q ∩ N_H(P) = Z(H). The other ambient
involution class supplies an involution of H outside Q. Conjugating its image
in A₅ and applying the extraspecial central-norm calculation forces x² = 1.
Finally Q ∩ P = 1 transports the quotient inversion identity back to P.

This supplies the involution used to identify N_H(P) with D₂₀. It uses only
the seed and the source core-fusion clause, without an assumed local model
for H, splitting, or global recognition; the ambient order 51840 is unnecessary.

Source: Aschbacher, *Sporadic Groups* (1994), 46.8, 46.11, and the proof
of 47.1, printed pp.253–260.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer
variable {G : Type*} [Group G] [Finite G]
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The literal local Sylow five-normalizer contains an involution inverting P. -/
theorem exists_local_five_reflection (D : Seed G) (L : LocalCensus D)
    (P : Sylow 5 (involutionCentralizer D.z)) :
    ∃ s : normalizer (P : Set (involutionCentralizer D.z)),
      s ^ 2 = 1 ∧ ∀ p ∈ (P : Subgroup (involutionCentralizer D.z)),
        (s : involutionCentralizer D.z) * p * (s : involutionCentralizer D.z)⁻¹ = p⁻¹ := by
  let H := involutionCentralizer D.z
  let Q := localCore D.z
  let π := QuotientGroup.mk' Q
  have hdis : Disjoint Q (P : Subgroup H) :=
    IsPGroup.disjoint_of_coprime D.localType.core_isPGroup P.isPGroup' (by decide)
  have hmapP : Nat.card ((P : Subgroup H).map π) = 5 := by
    have he := relIndex_ker (K := (P : Subgroup H)) π
    rw [QuotientGroup.ker_mk', ← inf_relIndex_right, hdis.eq_bot, relIndex_bot_left] at he
    exact he.symm.trans (localFive_card D P)
  obtain ⟨r, hrN, hr2, hrinv⟩ := J2Reflection.exists_reflection
    D.localType.quotient_equiv.some ((P : Subgroup H).map π) hmapP
  have hn : normalizer (((P : Subgroup H).map π) : Set (H ⧸ Q)) =
      (normalizer (P : Set H)).map π := by
    let : Fact (IsPGroup 5 (P : Subgroup H)) := ⟨P.isPGroup'⟩
    exact normalizer_map_quotient_eq_map_normalizer 5 (P : Subgroup H) Q inferInstance
      (by change Nat.Coprime 5 (Nat.card (localCore D.z)); rw [D.localType.core_card]; decide)
  rw [hn] at hrN
  obtain ⟨x, hxN, hxπ⟩ := mem_map.mp hrN
  have hx2Q : x ^ 2 ∈ Q := by
    apply (QuotientGroup.eq_one_iff _).mp
    change π (x ^ 2) = 1
    rw [map_pow, hxπ, ← hr2]
    exact pow_orderOf_eq_one r
  have hx2Z : x ^ 2 ∈ center H := by
    rw [← localFive_core_normalizer_eq_center D P]
    exact ⟨hx2Q, pow_mem hxN 2⟩
  obtain ⟨t, ht, hzt⟩ := exists_commuting_other D
  have htH : t ∈ H := mem_centralizer_singleton_iff.mpr hzt.symm.eq
  let u : H := ⟨t, htH⟩
  have hu : orderOf u = 2 := (orderOf_coe u).symm.trans ht.1
  have huQ : u ∉ Q := by
    intro hm
    apply ht.2
    apply (L.core_fusion t htH ht.1).mpr
    exact mem_map_of_mem H.subtype hm
  have hx2 : x ^ 2 = 1 := MinusExtraspecial.reflection_square_eq_one Q
    D.localType.core_equiv.some (centralizer_generalizedFitting_le H)
    D.localType.quotient_equiv.some u hu huQ x (by rw [hxπ]; exact hr2) hx2Z
  refine ⟨⟨x, hxN⟩, Subtype.ext hx2, ?_⟩
  intro p hp
  change x * p * x⁻¹ = p⁻¹
  have hp' : x * p * x⁻¹ ∈ (P : Subgroup H) := (mem_normalizer_iff.mp hxN p).mp hp
  have he : π (x * p * x⁻¹) = π (p⁻¹) := by
    rw [map_mul, map_mul, map_inv, map_inv, hxπ]
    exact hrinv (π p) (mem_map_of_mem π hp)
  have hd : (x * p * x⁻¹) / p⁻¹ ∈ Q ⊓ (P : Subgroup H) :=
    ⟨QuotientGroup.eq_iff_div_mem.mp he,
      (P : Subgroup H).div_mem hp' ((P : Subgroup H).inv_mem hp)⟩
  rw [hdis.eq_bot] at hd
  exact div_eq_one.mp hd
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer
