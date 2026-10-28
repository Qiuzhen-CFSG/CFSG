module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged.SourceAlternatives
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Marking the surviving exchanged modules

The group input consists of an internal pair of commuting disjoint factors
and the product of their actual overlap subgroups. It contains no module
classification. Multiplication constructs the marked product, whose first
projection carries that Borel product onto the first overlap. Sylow conjugacy
then adjusts an independently identified module and its actor together.

On a constituent centralized by the other factor, C_I(K) = C_I(K₀).
This identifies the source's hatted constituent with the precise central
quotient required by the pair-coordinate construction.

Source: Aschbacher--Smith, E.2.2, pp.215--216, F.9.18(5), pp.325--326,
and 15.3.65(i),(iii), printed p.1152.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged
open PairCoordinates BorelReduction BorelReduction.SourceCases
variable {D E V X : Type*} [Group D] [Group E]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup X] [Module (ZMod 2) X]

/-- The marked product is constructed from ordinary group-theoretic pair
data, retaining the source right-conjugation convention. -/
theorem productMarking_of_disjoint {K K₀ : Subgroup D} {t : D}
    (ht : t ∈ normalizer (K₀ : Set D)) (hs : K ⊔ K.conjBy t⁻¹ = K₀)
    (hd : Disjoint K (K.conjBy t⁻¹)) (hc : K ≤ centralizer (K.conjBy t⁻¹ : Set D))
    (hr : K.conjBy t = K.conjBy t⁻¹) : Nonempty (ProductMarking K K₀ t) := by
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting K (K.conjBy t⁻¹) hd hc
  let c : K ≃* K.conjBy t⁻¹ := (MulAut.conj t⁻¹).subgroupMap K
  let p := ((MulEquiv.refl K).prodCongr c).trans (e.trans (MulEquiv.subgroupCongr hs))
  have hp (a b : K) : (p (a, b) : D) = a * (t⁻¹ * b * t) := by
    change (e (a, c b) : D) = _
    rw [he]
    congr 1
    exact ProductMarking.conjugateActor_coe b
  refine ⟨⟨hs ▸ le_sup_left, ht, p, ?_, ?_, hr⟩⟩
  · intro k
    rw [hp]
    simp
  · intro k
    rw [hp]
    simp

namespace PairCoordinates.ProductMarking
variable {K K₀ C B : Subgroup D} {t : D} (p : ProductMarking K K₀ t)

include p

/-- Inclusion of a subgroup of the first component followed by projection. -/
theorem firstProjection_subgroup (hC : C ≤ K) :
    (C.subgroupOf K₀).map p.firstProjection = C.subgroupOf K := by
  ext k
  constructor
  · rintro ⟨g, hg, rfl⟩
    change (p.firstProjection g : D) ∈ C
    have he : g = (⟨(⟨g, hC hg⟩ : K), p.le (hC hg)⟩ : K₀) := rfl
    rw [he, p.firstProjection_inclusion]
    exact hg
  · intro hk
    exact ⟨⟨k, p.le k.property⟩, hk, p.firstProjection_inclusion k⟩

/-- The second factor is exactly the projection kernel, so its overlap disappears. -/
theorem firstProjection_conjugate_subgroup (hC : C ≤ K) :
    ((C.conjBy t⁻¹).subgroupOf K₀).map p.firstProjection = ⊥ := by
  apply le_bot_iff.mp
  rintro _ ⟨g, hg, rfl⟩
  apply mem_bot.mpr
  apply (show g ∈ p.firstProjection.ker → p.firstProjection g = 1 from id)
  rw [p.firstProjection_ker]
  exact map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) hC hg

/-- The Borel pair projects onto its first literal overlap. -/
theorem firstProjection_borel (hC : C ≤ K) (hB : B = C ⊔ C.conjBy t⁻¹) :
    (B.subgroupOf K₀).map p.firstProjection = C.subgroupOf K := by
  have hCt : C.conjBy t⁻¹ ≤ K₀ :=
    (map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) hC).trans p.conjugate_le
  rw [hB, subgroupOf_sup (hC.trans p.le) hCt, Subgroup.map_sup,
    p.firstProjection_subgroup hC, p.firstProjection_conjugate_subgroup hC, sup_bot_eq]

/-- In the marked product, the two overlaps are the actual external product. -/
theorem product_borel (hC : C ≤ K) (hB : B = C ⊔ C.conjBy t⁻¹) :
    ((C.subgroupOf K).prod (C.subgroupOf K)).map p.product.toMonoidHom = B.subgroupOf K₀ := by
  apply le_antisymm
  · rintro _ ⟨⟨a,b⟩, ⟨ha,hb⟩, rfl⟩
    change (p.product (a,b) : D) ∈ B
    rw [hB, p.product_coe]
    exact mul_mem ((le_sup_left : C ≤ C ⊔ C.conjBy t⁻¹) ha)
      ((le_sup_right : C.conjBy t⁻¹ ≤ C ⊔ C.conjBy t⁻¹) ⟨b, hb, by simp⟩)
  · have hC₀ := hC.trans p.le
    have hCt : C.conjBy t⁻¹ ≤ K₀ :=
      (map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) hC).trans p.conjugate_le
    rw [hB, subgroupOf_sup hC₀ hCt]
    apply sup_le
    · intro g hg
      refine ⟨(⟨g, hC hg⟩, 1), ⟨hg, one_mem _⟩, ?_⟩
      exact Subtype.ext (p.first ⟨g, hC hg⟩)
    · rintro g ⟨c, hc, he⟩
      refine ⟨(1, ⟨c, hC hc⟩), ⟨one_mem _, hc⟩, ?_⟩
      apply Subtype.ext
      change (p.product (1, ⟨c, hC hc⟩) : D) = g
      rw [p.second]
      simpa using he

/-- The actual Borel product is a Sylow normalizer whenever its component
overlap is one. This is the input needed for orthogonal Borel alignment. -/
theorem borel_normalizer [Finite D] (hC : C ≤ K)
    (hB : B = C ⊔ C.conjBy t⁻¹)
    (hSyl : ∃ P : Sylow 2 K, normalizer (P : Set K) = C.subgroupOf K) :
    ∃ P : Sylow 2 K₀, normalizer (P : Set K₀) = B.subgroupOf K₀ := by
  apply exists_sylow_normalizer_of_equiv p.product.symm _ _
    ((map_symm_eq_iff_map_eq _).mpr (p.product_borel hC hB))
  exact exists_sylow_normalizer_prod _ _ hSyl hSyl

variable (ρ : Representation (ZMod 2) D V) {I : Submodule (ZMod 2) V}
  (hcross : subspaceCommutator ρ I (K.conjBy t⁻¹) = ⊥)

include hcross

/-- The two denominators agree on the constituent because the other
component centralizes it. No splitting of the central extension is used. -/
theorem constituent_fixed_eq :
    (fixedSpace ρ K).comap I.subtype = (fixedSpace ρ K₀).comap I.subtype := by
  ext i
  constructor
  · intro hi g
    change ρ g i = i
    rw [p.action_first ρ hcross]
    exact hi (p.firstProjection g)
  · intro hi k
    exact hi ⟨k, p.le k.property⟩

/-- Convert the source hatted natural constituent to its literal K-central quotient. -/
def centralIdentification {hI : K₀ ≤ subspaceStabilizer ρ I}
    {σ : Representation (ZMod 2) E X}
    (d : HatIdentification ρ K K₀ p.le I hI σ) :
    CentralQuotientIdentification ρ K I (p.le.trans hI) σ where
  groupEquiv := d.groupEquiv
  linearEquiv := (Submodule.quotEquivOfEq _ _ (p.constituent_fixed_eq ρ hcross)).trans d.linearEquiv
  equivariant := by
    intro g v
    induction v using Submodule.Quotient.induction_on with
    | _ v => exact d.equivariant g (Submodule.Quotient.mk v)

end PairCoordinates.ProductMarking

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged
