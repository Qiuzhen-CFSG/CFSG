module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.Actors
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.Models
public import Theory.GroupTheory.SymmetricThreeTwoCore

/-!
# The direct-product row of the terminal comparison

In the ambient S₃ × S₃ row, the marked first local group is nonabelian,
so it surjects onto at least one coordinate. The normalized two-subgroup
J(T) has trivial image in that coordinate, since S₃ has trivial two-core.
Sylow conjugacy shows that the global Thompson image is the normal closure
of the image of J(T), so it lies in the other coordinate factor. Its
nontrivial commutator then identifies it with that S₃ factor.

The normal-closure and local-core lemmas preserve the original first local
label and are also available for the remaining low rows. This argument does
not equate the Thompson image with the whole ambient or offender group.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), final proof
of 15.3.1, printed p.1155; F.6.16 and F.6.18(2), printed pp.308–310.
-/

public section

open Subgroup
open scoped Pointwise

private theorem thompson_le_normal_of_sylow {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (N : Subgroup H) [N.Normal]
    (hJN : Stellmacher.elementaryAbelianMaxJ (T : Subgroup H) ≤ N) :
    Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup H) ≤ N := by
  apply sSup_le
  intro A hA
  obtain ⟨S, hAS⟩ := hA.2.1.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H S T
  let e := MulAut.conj g
  have hST : (S : Subgroup H).map e.toMonoidHom = (T : Subgroup H) := by
    change ((g • S : Sylow 2 H) : Subgroup H) = (T : Subgroup H)
    rw [hg]
  have hAT : A.map e.toMonoidHom ≤ (T : Subgroup H) :=
    (map_mono hAS).trans hST.le
  have hmax : A.map e.toMonoidHom ∈
      Stellmacher.elementaryAbelianMaxSubgroups (T : Subgroup H) := by
    refine ⟨hAT, hA.2.1.map e.toMonoidHom, ?_⟩
    intro B _ hB
    rw [card_map_of_injective e.injective]
    exact hA.2.2 B le_top hB
  have hmap : A.map e.toMonoidHom ≤ N.map e.toMonoidHom := by
    rw [show N.map e.toMonoidHom = N from Subgroup.Normal.map_conj_eq N g]
    exact (le_sSup hmax).trans hJN
  exact (map_le_map_iff_of_injective e.injective).mp hmap

private theorem symmetricThree_image_top {P : Type*} [Group P]
    (f : P →* Equiv.Perm (Fin 3)) (h : ⁅f.range, f.range⁆ ≠ ⊥) :
    Function.Surjective f := by
  apply MonoidHom.range_eq_top.mp
  simpa only [sup_idem] using
    sup_eq_top_of_symmetricThree_commutator_ne_bot _ _ h

private theorem commutator_ne_bot_of_symmetricThree_quotient
    {D : Type*} [Group D] (P : Subgroup D)
    (f : P →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f) : ⁅P,P⁆ ≠ ⊥ := by
  intro h
  have hc := commutator_eq_bot_iff_le_centralizer.mp h
  obtain ⟨x, hx⟩ := hf (Equiv.swap (0 : Fin 3) 1)
  obtain ⟨y, hy⟩ := hf (Equiv.swap (1 : Fin 3) 2)
  have he : y * x = x * y := Subtype.ext (hc x.property y y.property)
  have hh := congrArg f he
  rw [map_mul, map_mul, hx, hy] at hh
  exact (by decide : Equiv.swap (1 : Fin 3) 2 * Equiv.swap 0 1 ≠
    Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2) hh

private theorem one_coordinate_surjective
    (P : Subgroup (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (h : ⁅P,P⁆ ≠ ⊥) :
    P.map (MonoidHom.fst _ _) = ⊤ ∨ P.map (MonoidHom.snd _ _) = ⊤ := by
  by_contra! hn
  have hfst : ⁅P.map (MonoidHom.fst _ _), P.map (MonoidHom.fst _ _)⁆ = ⊥ := by
    by_contra hne
    exact hn.1 (by simpa only [sup_idem] using
      sup_eq_top_of_symmetricThree_commutator_ne_bot _ _ hne)
  have hsnd : ⁅P.map (MonoidHom.snd _ _), P.map (MonoidHom.snd _ _)⁆ = ⊥ := by
    by_contra hne
    exact hn.2 (by simpa only [sup_idem] using
      sup_eq_top_of_symmetricThree_commutator_ne_bot _ _ hne)
  apply h
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro x hx y hy
  exact Prod.ext
    (commutator_eq_bot_iff_le_centralizer.mp hfst
      (mem_map.mpr ⟨x, hx, rfl⟩) _ (mem_map.mpr ⟨y, hy, rfl⟩))
    (commutator_eq_bot_iff_le_centralizer.mp hsnd
      (mem_map.mpr ⟨x, hx, rfl⟩) _ (mem_map.mpr ⟨y, hy, rfl⟩))


private theorem symmetricThree_twoCore : pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
  have h := ker_eq_twoCore_of_surjective_perm_three (MonoidHom.id (Equiv.Perm (Fin 3)))
    Function.surjective_id (by rw [MonoidHom.ker_id]; exact IsPGroup.of_bot)
  simpa using h.symm

private theorem normalized_twoGroup_killed {D : Type*} [Group D]
    (P J : Subgroup D) (hJ : IsPGroup 2 J)
    (hn : P ≤ normalizer (J : Set D)) (f : D →* Equiv.Perm (Fin 3))
    (hf : P.map f = ⊤) : J.map f = ⊥ := by
  have hnorm : (J.map f).Normal := by
    rw [← normalizer_eq_top_iff]
    exact top_unique (hf ▸ (map_mono hn).trans (le_normalizer_map f))
  have hle : J.map f ≤ pCore 2 (Equiv.Perm (Fin 3)) :=
    le_sSup ⟨hnorm, hJ.map f⟩
  exact le_bot_iff.mp (symmetricThree_twoCore ▸ hle)

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

namespace SourceInput

variable {H : Type*} [Group H] [Finite H] {V : Subgroup H} (d : SourceInput V)
include d

/-- The marked first local image is nonabelian: its two-core quotient is S₃. -/
theorem first_image_commutator_ne_bot :
    ⁅d.G1.map coreProjection, d.G1.map coreProjection⁆ ≠ ⊥ := by
  obtain ⟨e⟩ := (goldschmidt_twoCore_quotient d.G1 d.G2 d.goldschmidt).quotient_left
  exact commutator_ne_bot_of_symmetricThree_quotient _
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (d.G1.map coreProjection))))
    (e.surjective.comp (QuotientGroup.mk'_surjective _))

/-- A normal subgroup containing the marked Sylow Thompson image contains
the whole Thompson image, by Sylow conjugacy of maximal elementary subgroups. -/
theorem thompson_image_le_normal (N : Subgroup (coreQuotient H)) [N.Normal]
    (hJ : (Stellmacher.elementaryAbelianMaxJ (d.T : Subgroup H)).map coreProjection ≤ N) :
    (thompsonGroup H).map coreProjection ≤ N := by
  rw [map_le_iff_le_comap] at hJ ⊢
  exact thompson_le_normal_of_sylow d.T _ hJ

/-- The global Thompson image is the normal closure of the marked Sylow image. -/
theorem thompson_image_eq_normalClosure :
    (thompsonGroup H).map coreProjection =
      normalClosure ((Stellmacher.elementaryAbelianMaxJ (d.T : Subgroup H)).map
        coreProjection : Set (coreQuotient H)) := by
  apply le_antisymm
  · exact thompson_image_le_normal d _ le_normalClosure
  · exact normalClosure_le_normal
      (map_mono (Stellmacher.elementaryAbelianMaxJ_sylow_le_top d.T))

omit [Finite H] in
/-- Normalization by the original first local group puts the Sylow Thompson
image in that local group's actual embedded two-core. -/
theorem sylow_thompson_image_le_first_core :
    (Stellmacher.elementaryAbelianMaxJ (d.T : Subgroup H)).map coreProjection ≤
      (d.G1.map coreProjection).pCoreIn 2 := by
  apply le_pCoreIn_of_normalizes
  · exact (d.T.isPGroup'.to_le (sSup_le fun _ hA => hA.1)).map coreProjection
  · apply map_mono
    exact (sSup_le fun _ hA => hA.1).trans (d.first_local.symm ▸ le_sup_right)
  · exact d.sylow_thompson_image_normalized

private theorem directProduct_first_coordinate
    (e : coreQuotient H ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (he : ((d.G1.map coreProjection).map e.toMonoidHom).map (MonoidHom.fst _ _) = ⊤) :
    Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3)) := by
  let f := (MonoidHom.fst (Equiv.Perm (Fin 3)) (Equiv.Perm (Fin 3))).comp e.toMonoidHom
  let g := (MonoidHom.snd (Equiv.Perm (Fin 3)) (Equiv.Perm (Fin 3))).comp e.toMonoidHom
  let J := Stellmacher.elementaryAbelianMaxJ (d.T : Subgroup H)
  have hJp : IsPGroup 2 (J.map coreProjection) :=
    (d.T.isPGroup'.to_le (sSup_le fun _ hA => hA.1)).map coreProjection
  have hJ : (J.map coreProjection).map f = ⊥ :=
    normalized_twoGroup_killed _ _ hJp d.sylow_thompson_image_normalized f
      (by simpa only [map_map, f, MonoidHom.comp_assoc] using he)
  have hJN : J ≤ (f.comp coreProjection).ker := by
    apply (Subgroup.map_eq_bot_iff _).mp
    simpa only [map_map] using hJ
  have hX : (thompsonGroup H).map coreProjection ≤ f.ker := by
    rw [map_le_iff_le_comap]
    exact thompson_le_normal_of_sylow d.T _ hJN
  let k := g.comp ((thompsonGroup H).map coreProjection).subtype
  have hki : Function.Injective k := by
    intro x y hxy
    apply Subtype.ext
    apply e.injective
    apply Prod.ext
    · exact (hX x.property).trans (hX y.property).symm
    · exact hxy
  have hkn : ⁅k.range, k.range⁆ ≠ ⊥ := by
    have hxc : ⁅(⊤ : Subgroup ((thompsonGroup H).map coreProjection)),
        (⊤ : Subgroup ((thompsonGroup H).map coreProjection))⁆ ≠ ⊥ := by
      intro hz
      apply d.thompson_image_commutator_ne_bot
      have hh := congrArg (Subgroup.map ((thompsonGroup H).map coreProjection).subtype) hz
      simpa only [map_commutator, ← MonoidHom.range_eq_map, range_subtype, Subgroup.map_bot] using hh
    rw [MonoidHom.range_eq_map, ← map_commutator]
    exact fun hz => hxc ((map_eq_bot_iff_of_injective _ hki).mp hz)
  exact ⟨MulEquiv.ofBijective k ⟨hki, symmetricThree_image_top k hkn⟩⟩

/-- In the S₃ × S₃ ambient row, the Thompson image is one S₃ factor.
Only the genuine configuration is used; no FF classification is needed. -/
theorem thompson_symmetricThree_of_directProduct
    (e : coreQuotient H ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :
    Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3)) := by
  have hn : ⁅(d.G1.map coreProjection).map e.toMonoidHom,
      (d.G1.map coreProjection).map e.toMonoidHom⁆ ≠ ⊥ := by
    rw [← map_commutator]
    exact fun hz => first_image_commutator_ne_bot d
      ((map_eq_bot_iff_of_injective _ e.injective).mp hz)
  rcases one_coordinate_surjective _ hn with hl | hr
  · exact directProduct_first_coordinate d e hl
  · apply directProduct_first_coordinate d (e.trans MulEquiv.prodComm)
    rw [map_map]
    change (d.G1.map coreProjection).map ((MonoidHom.snd _ _).comp e.toMonoidHom) = ⊤
    simpa only [map_map, MonoidHom.comp_assoc] using hr

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
