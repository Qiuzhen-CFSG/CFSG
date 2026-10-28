module

public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.Transvections
public import Theory.SpecificGroups.SymmetricTwoResidual
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# The alternating image of the two-residual

Surjections preserve the two-residual, and O²(S₅)=A₅. Restricting the
original Ru2 quotient map therefore gives a surjection K → A₅ with
kernel K ∩ Q, together with the corresponding marked quotient isomorphism.
Once the preceding J.2.2(1) containment Q ≤ K is supplied, this is K/Q.
No replacement of the inherited alternating-group marking is made.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.2(3), printed p.432 (PDF p.443).
-/

@[expose] public section
open Subgroup Representation
noncomputable section
namespace CFSG.Quasithin.ChapterJ
variable {G : Type*} [Group G] [Finite G]

theorem TypeRuSetup.K_le_H (d : TypeRuSetup G) : d.K ≤ d.H := map_subtype_le _

theorem TypeRuSetup.K_subgroupOf_H (d : TypeRuSetup G) :
    d.K.subgroupOf d.H = pResidual 2 d.H := by
  change ((pResidual 2 d.H).map d.H.subtype).comap d.H.subtype = _
  exact comap_map_eq_self_of_injective d.H.subtype_injective _

theorem TypeRuSetup.quotientMap_K (d : TypeRuSetup G) :
    (d.K.subgroupOf d.H).map d.ru2.quotientMap = alternatingGroup (Fin 5) := by
  rw [d.K_subgroupOf_H, map_pResidual_of_surjective 2 _ d.ru2.quotient_surjective,
    Equiv.Perm.twoResidual_eq_alternating]

def TypeRuSetup.alternatingMap (d : TypeRuSetup G) : d.K →* alternatingGroup (Fin 5) :=
  (d.ru2.quotientMap.comp (inclusion d.K_le_H)).codRestrict _ (fun k => by
    rw [← d.quotientMap_K]
    exact mem_map.mpr ⟨inclusion d.K_le_H k, k.property, rfl⟩)

theorem TypeRuSetup.alternatingMap_apply (d : TypeRuSetup G) (k : d.K) :
    (d.alternatingMap k : S5) = d.ru2.quotientMap ⟨k, d.K_le_H k.property⟩ := rfl

theorem TypeRuSetup.alternatingMap_surjective (d : TypeRuSetup G) :
    Function.Surjective d.alternatingMap := by
  intro a
  have ha : (a : S5) ∈ (d.K.subgroupOf d.H).map d.ru2.quotientMap := by
    simpa only [d.quotientMap_K] using a.property
  obtain ⟨h, hh, he⟩ := ha
  exact ⟨⟨h, hh⟩, Subtype.ext he⟩

theorem TypeRuSetup.alternatingMap_kernel (d : TypeRuSetup G) :
    d.alternatingMap.ker = d.Q.subgroupOf d.K := by
  ext k
  change d.alternatingMap k = 1 ↔ (k : G) ∈ d.Q
  rw [Subtype.ext_iff]
  change d.ru2.quotientMap (inclusion d.K_le_H k) = 1 ↔ _
  change inclusion d.K_le_H k ∈ d.ru2.quotientMap.ker ↔ _
  rw [d.ru2.quotient_kernel]
  rfl

theorem TypeRuSetup.Q_normal_in_K (d : TypeRuSetup G) :
    (d.Q.subgroupOf d.K).Normal := by
  rw [← d.alternatingMap_kernel]
  infer_instance

def TypeRuSetup.alternatingQuotientEquiv (d : TypeRuSetup G)
    [(d.Q.subgroupOf d.K).Normal] :
    (d.K ⧸ d.Q.subgroupOf d.K) ≃* alternatingGroup (Fin 5) :=
  (QuotientGroup.quotientMulEquivOfEq d.alternatingMap_kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective d.alternatingMap d.alternatingMap_surjective)

theorem TypeRuSetup.alternatingQuotientEquiv_mk (d : TypeRuSetup G)
    [(d.Q.subgroupOf d.K).Normal] (k : d.K) :
    d.alternatingQuotientEquiv (QuotientGroup.mk' (d.Q.subgroupOf d.K) k) =
      d.alternatingMap k := rfl

end CFSG.Quasithin.ChapterJ
