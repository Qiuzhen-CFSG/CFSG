module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.Statement
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.GroupTheory.PCoreProduct
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore


/-!
# The local two-core when the offender splits

The odd-degree natural SL₃ action makes the actual component centerless.
If A lies in L C_A(L), then LA=L×C_A(L). Transporting the two-core along
this multiplication equivalence proves O₂(LA)=C_A(L), with the two-core
taken inside LA and mapped to G exactly as in NaturalSeed.

The supplement condition is the group consequence of B=C_A(L)=A_C in the
equality case of the source rank estimates. That equality still has to be
proved; it is not built into NaturalSeed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9,
printed p.108, final paragraph.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
open QuasisimpleSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

omit [Finite G] in
theorem seed_center_eq_bot {A L : Subgroup G} (seed : NaturalSeed ρ A L) :
    center L = ⊥ := by
  have hz : center (Matrix.SpecialLinearGroup (Fin 3) seed.field.Carrier) = ⊥ := by
    apply (Matrix.SL3.center_eq_bot_iff_card_mod_three seed.field.Carrier).mpr
    rw [seed.field.card_eq]
    obtain ⟨k, hk⟩ := seed.odd_degree
    rw [hk]
    norm_num [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
  apply bot_unique
  intro l hl
  change l = 1
  apply seed.natural.groupEquiv.injective
  have hmem : seed.natural.groupEquiv l ∈
      center (Matrix.SpecialLinearGroup (Fin 3) seed.field.Carrier) := by
    apply mem_center_iff.mpr
    intro g
    obtain ⟨x, rfl⟩ := seed.natural.groupEquiv.surjective g
    simpa only [map_mul] using congrArg seed.natural.groupEquiv ((mem_center_iff.mp hl) x)
  simpa only [hz, mem_bot, map_one] using hmem

private theorem core_of_commuting_product (L B : Subgroup G)
    (hd : Disjoint L B) (hc : L ≤ centralizer (B : Set G))
    (hL : pCore 2 L = ⊥) (hB : IsPGroup 2 B) :
    (pCore 2 ↥(L ⊔ B)).map (L ⊔ B).subtype = B := by
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting L B hd hc
  have hBcore : pCore 2 B = ⊤ :=
    top_unique (le_sSup ⟨inferInstance, hB.of_equiv Subgroup.topEquiv.symm⟩)
  have hcore : pCore 2 ↥(L ⊔ B) = ((⊥ : Subgroup L).prod ⊤).map e.toMonoidHom := by
    rw [← pCore_map_iso 2 e, pCore_prod, hL, hBcore]
  rw [hcore]
  apply le_antisymm
  · rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    have hz1 : z.1 = 1 := hz.1
    change (e (z.1, z.2) : G) ∈ B
    rw [he, hz1, OneMemClass.coe_one, one_mul]
    exact z.2.property
  · intro b hb
    refine ⟨e (1, ⟨b, hb⟩), ⟨(1, ⟨b, hb⟩), ⟨by simp, mem_top _⟩, rfl⟩, ?_⟩
    change (e (1, ⟨b, hb⟩) : G) = b
    simpa only [OneMemClass.coe_one, one_mul] using he 1 ⟨b, hb⟩

theorem localTwoCore_eq_centralizer_of_split {A L : Subgroup G}
    (seed : NaturalSeed ρ A L) (hL : IsComponent G L)
    (hA : IsElementaryAbelian 2 A)
    (hsplit : A ≤ L ⊔ (A ⊓ centralizer (L : Set G))) :
    localTwoCore L A = A ⊓ centralizer (L : Set G) := by
  let B := A ⊓ centralizer (L : Set G)
  let : IsQuasisimple L := hL.2
  let : IsElementaryAbelian 2 A := hA
  have hz := seed_center_eq_bot ρ seed
  have hLB : L ⊔ A = L ⊔ B := le_antisymm (sup_le le_sup_left hsplit)
    (sup_le le_sup_left (inf_le_left.trans le_sup_right))
  have hd : Disjoint L B := by
    apply Subgroup.disjoint_def.mpr
    intro x hx hb
    have hxc : (⟨x, hx⟩ : L) ∈ center L := by
      apply mem_center_iff.mpr
      intro l
      exact Subtype.ext (hb.2 l l.property)
    have hxe : (⟨x, hx⟩ : L) = 1 := by simpa only [hz, mem_bot] using hxc
    exact congrArg Subtype.val hxe
  unfold localTwoCore
  rw [hLB]
  apply core_of_commuting_product L B hd (le_centralizer_iff.mp inf_le_right)
  · exact le_bot_iff.mp ((IsQuasisimple.pCore_le_center 2).trans hz.le)
  · exact (IsElementaryAbelian.isPGroup 2 A).to_le inf_le_left

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
