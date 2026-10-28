module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticResidual
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.KernelResidual
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.PResidual.AutomorphismCentralizer

/-!
# Two-perfect actors centralize the original quintic kernels

The permutation action on the two original factors has two-group image.
A two-perfect subgroup consequently preserves each factor. The marked
order-five kernel is that factor's two-residual, so the subgroup normalizes
it. Its automorphism group has order four, forcing centralization.

This uses the literal original factor embeddings. It applies in particular
to the image of the actual partner residual of a third local, without
identifying that residual's kernel on the full original module.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

/-- Every two-perfect subgroup of the original action centralizes each
of the two literal quintic kernels. -/
theorem ThompsonPair.twoPerfect_centralizes_quintic_kernels
    {T : Sylow 2 G} {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hdec : SourceCases.Decomposable (imageRepresentation M V hn) (T : Subgroup G) M
      (actionHom M V hn).rangeRestrict c d π)
    (hfive : s.prime = 5)
    (B : Subgroup (internalActionImage M V hn)) (hB : IsPPerfect 2 B) :
    ∀ k, B ≤ centralizer ((s.marking k).kernel.map
      (c.ambientFactor d k).embedding.groupMap : Set (internalActionImage M V hn)) := by
  have hperm : IsPGroup 2 (Equiv.Perm d.Index) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_perm,hdec.1]
    decide
  have hπ : ∀ b ∈ B, π b = 1 := by
    intro b hb
    exact congrArg (fun f : B →* Equiv.Perm d.Index => f ⟨b,hb⟩)
      (hB.hom_eq_one_of_isPGroup hperm (π.comp B.subtype))
  intro k
  let F := c.ambientFactor d k
  let P := (s.marking k).kernel.map F.embedding.groupMap
  have hBF : B ≤ normalizer (F.actor : Set (internalActionImage M V hn)) := by
    intro b hb
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (c.ambientFactor d k).actor.map (MulAut.conj b).toMonoidHom =
      (c.ambientFactor d k).actor
    simpa only [hπ b hb,Equiv.Perm.one_apply] using hp b k
  have hres : P = (pResidual 2 F.actor).map F.actor.subtype := by
    change (s.marking k).kernel.map F.embedding.groupMap = _
    rw [(s.marking k).kernel_eq_twoResidual]
    change (pResidual 2 F.Carrier).map F.embedding.groupMap =
      (pResidual 2 F.embedding.groupMap.range).map F.embedding.groupMap.range.subtype
    calc
      _ = ((pResidual 2 F.Carrier).map F.embedding.groupMap.rangeRestrict).map
          F.embedding.groupMap.range.subtype := by rw [map_map]; rfl
      _ = _ := by rw [map_pResidual_of_surjective 2 F.embedding.groupMap.rangeRestrict
        F.embedding.groupMap.rangeRestrict_surjective]
  have hBP : B ≤ normalizer (P : Set (internalActionImage M V hn)) := by
    rw [hres]
    exact hBF.trans (normalizer_le_normalizer_characteristic_image F.actor (pResidual 2 F.actor))
  have hc : Nat.card P = 5 := (s.kernel_card k).trans hfive
  let : IsCyclic P := isCyclic_of_prime_card hc
  have hAut : IsPGroup 2 (MulAut P) := by
    apply IsPGroup.of_card (n := 2)
    rw [IsCyclic.card_mulAut,hc]
    decide
  have hz := embedded_pResidual_le_centralizer_of_aut_isPGroup 2 B P hBP hAut
  simpa only [(pResidual_eq_top_iff 2 B).mpr hB,←MonoidHom.range_eq_map,range_subtype] using hz

end CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
