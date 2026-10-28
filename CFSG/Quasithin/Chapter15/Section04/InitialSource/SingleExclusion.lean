module
public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.C2S4Geometry

/-!
# Excluding the single-factor symmetric model

For the actual family member `X`, an isomorphism `XT ≃ C₂ × S₄` supplies
the three central involution classes and the dihedral fusion cover used by
Thompson transfer. Transfer contradicts nonabelian simplicity. The source
`S₂ × S₄` convention is obtained through the cyclic group of order two.

Aschbacher–Smith, *The Classification of Quasithin Groups*, 15.4.13,
printed p.1161.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The canonical Y-family cannot produce C₂ × S₄ in a nonabelian simple group. -/
theorem no_c2_s4_of_mem_Y [IsSimpleGroup G] (hna : ¬IsMulCommutative G)
    (T : Sylow 2 G) {X : Subgroup G} (hX : X∈Y (T:Subgroup G)) :
    ¬Nonempty ((X⊔(T:Subgroup G):Subgroup G)≃*Multiplicative (ZMod 2)×Equiv.Perm (Fin 4)) := by
  rintro ⟨e⟩
  obtain ⟨R,a,b,c,t,z,hR,ha,hb,hc,hab,hac,hbc,hcover⟩ :=
    FamilySource.C2S4Geometry.exists_transfer_inputs T X
      (YFamily.perfect hX) (YFamily.invariant hX) e
  exact FamilySource.Transfer.two_class_cover_impossible hna T R hR a b c ha hb hc hab hac hbc t z hcover

private noncomputable def permTwoEquiv : Equiv.Perm (Fin 2)≃*Multiplicative (ZMod 2) := by
  have hc : Nat.card (Equiv.Perm (Fin 2))=2 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    decide
  let : IsCyclic (Equiv.Perm (Fin 2)):=isCyclic_of_prime_card hc
  exact mulEquivOfCyclicCardEq (by simpa using hc)

/-- Source 15.4.13 retains the actual YT subgroup and the source S₂×S₄ convention. -/
theorem lemma_15_4_13 {κ : GroupClass} (hG : IsSimpleQTKE κ G)
    (T : Sylow 2 G) {X : Subgroup G} (hX : X∈Y (T:Subgroup G)) :
    ¬Nonempty ((X⊔(T:Subgroup G):Subgroup G)≃*Equiv.Perm (Fin 2)×Equiv.Perm (Fin 4)) := by
  let : IsSimpleGroup G:=hG.simple
  rintro ⟨e⟩
  exact no_c2_s4_of_mem_Y hG.nonabelian T hX
    ⟨e.trans (permTwoEquiv.prodCongr (MulEquiv.refl _))⟩

end CFSG.Quasithin.Chapter15.Section04.InitialSource
