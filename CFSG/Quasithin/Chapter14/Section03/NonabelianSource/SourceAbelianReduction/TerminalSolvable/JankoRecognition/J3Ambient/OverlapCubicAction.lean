module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.OverlapNormalizerOrder
public import Theory.SpecificGroups.AlternatingSix.TenSelfNormalizer

/-!
# The literal cubic action in the overlap normalizer

Inside the cubic centralizer, the actual overlap descends to an order-ten
subgroup of the recognized `A₆` quotient. That image is self-normalizing.
Taking the inverse image through the full cubic kernel proves that the
centralizer of the cubic inside the original overlap normalizer is exactly
the original overlap.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics

variable {G : Type*} [Group G] [Finite G]

/-- The literal cubic centralizer inside the overlap normalizer is the overlap itself. -/
theorem literal_overlap_cubic_centralizer_eq
    {D : Seed G} (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (a : A ≃* Plane) (j : SingerField.Model →* G)
    (hj : PlaneTransport.FieldEmbedding A C a j) :
    normalizer (overlap j : Set G) ⊓ centralizer ({j cubic} : Set G) = overlap j := by
  obtain ⟨⟨e⟩, _⟩ := literal_field_cubic_projective P hc A C a j hj
  let Z := centralizer ({j cubic} : Set G)
  let L := (overlap j).subgroupOf Z
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (cubicKernel (j cubic)))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hs : orderOf (j cubic) = 3 := (orderOf_injective j hj.1 _).trans cubic_order
  have hLZ : overlap j ≤ Z := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    apply mem_centralizer_singleton_iff.mpr
    exact ((cubic_commutes_complement ⟨y, hy⟩).map j).eq.symm
  have hk : q.ker = cubicKernel (j cubic) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hkL : q.ker ≤ L := by
    rw [hk]
    exact subgroupOf_mono Z (zpowers_le.mpr (mem_map_of_mem j cubic_mem))
  have hLc : Nat.card L = 30 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hLZ).toEquiv,
      Nat.card_congr (overlapEquiv j hj.1).toEquiv]
    norm_num [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      DihedralGroup.card, Sporadic.Janko3.SourceRecognition.Seventeen.Complement]
  let f := q.subgroupMap L
  have hfk : Nat.card f.ker = 3 := by
    rw [Subgroup.ker_subgroupMap,
      Nat.card_congr (subgroupOfEquivOfLe hkL).toEquiv, hk]
    exact cubicKernel_card (j cubic) hs
  have hfi : f.ker.index = Nat.card (L.map q) := by
    rw [index_eq_card, Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective f (q.subgroupMap_surjective L)).toEquiv]
  have himage : Nat.card (L.map q) = 10 := by
    have hh := f.ker.index_mul_card
    rw [hfi, hfk, hLc] at hh
    omega
  have hpre : (L.map q).comap q = L := comap_map_eq_self hkL
  have hself : normalizer (L : Set Z) = L := by
    have hh := congrArg (fun B : Subgroup (alternatingGroup (Fin 6)) => B.comap q)
      (AlternatingSix.TenSelfNormalizer.ten_normalizer_eq _ himage)
    rw [comap_normalizer_eq_of_surjective _ hq, hpre] at hh
    exact hh
  apply le_antisymm
  · intro x hx
    have hn : (⟨x, hx.2⟩ : Z) ∈ normalizer (L : Set Z) := by
      rw [show normalizer (L : Set Z) = (normalizer (overlap j : Set G)).subgroupOf Z
        from (subgroupOf_normalizer_eq hLZ).symm]
      exact hx.1
    rw [hself] at hn
    exact hn
  · exact le_inf (overlap j).le_normalizer hLZ

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
