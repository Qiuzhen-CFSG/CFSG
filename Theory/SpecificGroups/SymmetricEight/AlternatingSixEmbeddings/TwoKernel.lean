module
public import Theory.GroupTheory.PResidual.ConjugacyLift
public import Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings
public import Theory.SpecificGroups.Alternating.EightSectionExtension
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# Alternating-six sections above a two-group kernel

In a group mapping onto the actual A8 with two-group kernel, any A6
section has an A6 image: a subgroup of A8 with a factor five has trivial
two-core. If the kernel normalizes two such two-perfect subgroups, the
conjugacy of their images lifts to conjugacy in the original group.

The application retains the literal L_v in Aschbacher--Smith 12.6.16(1),
printed p.826, rather than replacing it by a subgroup-family label.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] {p : ℕ}
theorem exists_conjugate_of_alternatingSix_images
    (f : G →* alternatingGroup (Fin 8)) (hf : Function.Surjective f)
    (A B : Subgroup G) (hA : IsPPerfect p A) (hB : IsPPerfect p B)
    (hk : IsPGroup p f.ker)
    (hnA : f.ker ≤ normalizer (A : Set G))
    (hnB : f.ker ≤ normalizer (B : Set G))
    (a : A.map f ≃* alternatingGroup (Fin 6))
    (b : B.map f ≃* alternatingGroup (Fin 6)) :
    ∃ g : G, A.map (MulAut.conj g).toMonoidHom = B := by
  let fa := (A.map f).subtype.comp a.symm.toMonoidHom
  let fb := (B.map f).subtype.comp b.symm.toMonoidHom
  obtain ⟨x,hx⟩ := Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings.ranges_conjugate
    fa fb ((A.map f).subtype_injective.comp a.symm.injective)
    ((B.map f).subtype_injective.comp b.symm.injective)
  have ha : fa.range = A.map f := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr a.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  have hb : fb.range = B.map f := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr b.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  rw [ha,hb] at hx
  obtain ⟨g,rfl⟩ := hf x
  exact ⟨g,conjugate_eq_of_map_conjugate_eq f A B hA hB hk hnA hnB g hx⟩
end Subgroup

namespace Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings
variable {G : Type*} [Group G] [Finite G]

theorem six_section_image (f : G →* alternatingGroup (Fin 8))
    (hk : IsPGroup 2 f.ker) (A : Subgroup G)
    (e : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6)) :
    Nonempty (A.map f ≃* alternatingGroup (Fin 6)) := by
  have hkA : IsPGroup 2 (f.subgroupMap A).ker := by
    rw [Subgroup.ker_subgroupMap]
    exact hk.comap_subtype
  let a := (f.subgroupMap A).pCoreQuotientEquiv (f.subgroupMap_surjective A) hkA
  let b := a.symm.trans e
  have h5 : 5 ∣ Nat.card (A.map f) := by
    apply dvd_trans _ (card_quotient_dvd_card (pCore 2 (A.map f)))
    rw [Nat.card_congr b.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hc := Theory.SpecificGroups.Alternating.EightSectionExtension.twoCore_eq_bot_of_five
    ⊤ (A.map f) (Subgroup.topEquiv) le_top h5
  exact ⟨QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hc).symm.trans b)⟩

theorem six_sections_conjugate (f : G →* alternatingGroup (Fin 8))
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (A B : Subgroup G) (hA : IsPPerfect 2 A) (hB : IsPPerfect 2 B)
    (hnA : f.ker ≤ normalizer (A : Set G))
    (hnB : f.ker ≤ normalizer (B : Set G))
    (a : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6))
    (b : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) :
    ∃ g : G, A.map (MulAut.conj g).toMonoidHom = B := by
  obtain ⟨a'⟩ := six_section_image f hk A a
  obtain ⟨b'⟩ := six_section_image f hk B b
  exact exists_conjugate_of_alternatingSix_images f hf A B hA hB hk hnA hnB a' b'
end Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings
