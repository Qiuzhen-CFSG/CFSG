module
public import Theory.SpecificGroups.SL2.ResidualSylowGeneration
public import Theory.SpecificGroups.SL2.TwoCore
public import Theory.GroupTheory.AbelianGeneratorCore
public import Theory.ElementaryAbelian.Injective

/-!
# Original-degree Sylow pairs in a binary rank-one extension

A surjection to SL₂ with kernel exactly O₂ identifies the actual Sylow
quotient with the additive field. A conjugator in the original two-residual
gives two Sylows generating the whole extension, whose intersection is
exactly O₂: their abelian images intersect in the trivial model two-core.
All maps retain the full kernel and every characteristic-two field degree.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 2.2 and the
initial pair in Proposition 4.2, printed pp.29,44. The concrete consumer is
the original F₀ in MS93 (5.1), CriticalReduction.RootProductNilesPair.
-/

public noncomputable section
open Subgroup
namespace Matrix.SpecialLinearGroup
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

theorem sylow_quotient_equiv_additive_of_core_kernel
    (q : G →* SpecialLinearGroup (Fin 2) F) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 G) (P : Sylow 2 G) :
    Nonempty ((P ⧸ (pCore 2 G).subgroupOf (P : Subgroup G)) ≃* Multiplicative F) := by
  let r := q.subgroupMap (P : Subgroup G)
  have hr : Function.Surjective r := q.subgroupMap_surjective _
  have hker : r.ker = (pCore 2 G).subgroupOf (P : Subgroup G) := by
    ext x
    change r x = 1 ↔ x.val ∈ pCore 2 G
    rw [←hk]
    exact Subtype.ext_iff
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective r hr).trans
      (sylowEquivAdditive F 2 (P.mapSurjective hq)).symm)⟩

theorem sylow_core_relIndex
    (q : G →* SpecialLinearGroup (Fin 2) F) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 G) (P : Sylow 2 G) :
    (pCore 2 G).relIndex (P : Subgroup G) = Nat.card F := by
  obtain ⟨e⟩ := sylow_quotient_equiv_additive_of_core_kernel q hq hk P
  rw [relIndex,index_eq_card,Nat.card_congr e.toEquiv]
  exact Nat.card_congr Multiplicative.toAdd

theorem generating_sylow_intersection_of_core_kernel
    (q : G →* SpecialLinearGroup (Fin 2) F) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 G) (P T : Sylow 2 G)
    (hg : (P : Subgroup G) ⊔ (T : Subgroup G) = ⊤) :
    (P : Subgroup G) ⊓ (T : Subgroup G) = pCore 2 G := by
  let P' := P.mapSurjective hq
  let T' := T.mapSurjective hq
  let : IsMulCommutative P' :=
    ⟨⟨fun x y => (sylowEquivAdditive F 2 P').symm.injective (by simp [mul_comm])⟩⟩
  let : IsMulCommutative T' :=
    ⟨⟨fun x y => (sylowEquivAdditive F 2 T').symm.injective (by simp [mul_comm])⟩⟩
  have hgen : (P' : Subgroup (SpecialLinearGroup (Fin 2) F)) ⊔ T' = ⊤ := by
    change (P : Subgroup G).map q ⊔ (T : Subgroup G).map q = ⊤
    rw [←Subgroup.map_sup,hg,map_top_of_surjective q hq]
  have hi : (P' : Subgroup (SpecialLinearGroup (Fin 2) F)) ⊓ T' = ⊥ := by
    apply le_bot_iff.mp
    exact (abelian_generator_intersection_le_pCore 2 _ _ P'.isPGroup' hgen).trans
      (Matrix.SL2.twoCore_eq_bot F).le
  refine le_antisymm ?_ (le_inf (pCore_isPGroup.le_sylow_of_normal P)
    (pCore_isPGroup.le_sylow_of_normal T))
  rw [←hk,←Subgroup.map_eq_bot_iff]
  exact le_bot_iff.mp ((map_inf_le _ _ _).trans hi.le)

theorem exists_residual_generating_sylow_pair
    (q : G →* SpecialLinearGroup (Fin 2) F) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 G) (P : Sylow 2 G) :
    ∃ g : G, g ∈ pResidual 2 G ∧
      (P : Subgroup G) ⊔ (P : Subgroup G).map (MulAut.conj g).toMonoidHom = ⊤ ∧
      (P : Subgroup G) ⊓ (P : Subgroup G).map (MulAut.conj g).toMonoidHom = pCore 2 G := by
  obtain ⟨g,hg,hgen⟩ := exists_residual_conjugate_sylow_image_sup_eq_top P q hq
  have hgen' : (P : Subgroup G) ⊔ (P : Subgroup G).map (MulAut.conj g).toMonoidHom = ⊤ := by
    have hh := congrArg (Subgroup.comap q) hgen
    rw [←Subgroup.map_sup,comap_map_eq_self
      (hk.symm ▸ (pCore_isPGroup.le_sylow_of_normal P).trans le_sup_left),comap_top] at hh
    exact hh
  exact ⟨g,hg,hgen',generating_sylow_intersection_of_core_kernel q hq hk P
    (P.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective) hgen'⟩
end Matrix.SpecialLinearGroup
