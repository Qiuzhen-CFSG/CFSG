module
public import CFSG.Quasithin.ChapterG.Section10.Components.Homogeneous
public import CFSG.Quasithin.ChapterG.Section09.ConstituentAction
public import Theory.ElementaryAbelian.GeneratorRank
public import Theory.LinearAlgebra.AlternatingPlane
/-!
# The G.11.7 action-image input from G.10 geometry

A constituent through the marked point is X-invariant and homogeneous
for the normal orbit H of the moved component. Its faithful H-action
and the one- or two-conjugate orbit supply the literal component data
on Aut_HX(I). Faithfulness of X is retained as the source contradiction
assumption; the SQTK cover is pulled back through HX.

Total isotropy gives the sharper degree dim I ≤ m(X)+1 used by the
subsequent G.9 row exclusion. This is the homogeneous case of
Aschbacher--Smith G.11.7, printed pp.366–367; it does not supply the earlier
exchanged-constituent reduction of G.10.15.
-/
@[expose] public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section10
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
private theorem orbit_pair (L : Subgroup G) (hi : (normalizer (L : Set G)).index ≤ 2) :
    componentOrbit L ⊤ = L ∨ ∃ g : G,
      componentOrbit L ⊤ = L ⊔ L.map (MulAut.conj g).toMonoidHom := by
  classical
  by_cases hn : L.Normal
  · let := hn
    left
    apply le_antisymm ?_ (le_componentOrbit L ⊤)
    exact iSup_conjugates_le_of_le_normalizer L ⊤ L le_rfl (by rw [normalizer_eq_top_iff.mpr hn])
  have hidx : (normalizer (L : Set G)).index = 2 := by
    have hp := (normalizer (L : Set G)).index_ne_zero_of_finite
    have h1 : (normalizer (L : Set G)).index ≠ 1 := by
      intro he
      exact hn (normalizer_eq_top_iff.mp (index_eq_one.mp he))
    omega
  have hN : normalizer (L : Set G) ≠ ⊤ := fun he => hn (normalizer_eq_top_iff.mp he)
  have hex : ∃ g : G, g ∉ normalizer (L : Set G) := by
    by_contra! hall
    exact hN (eq_top_iff.mpr (fun g _ => hall g))
  obtain ⟨g,hg⟩ := hex
  right
  refine ⟨g,le_antisymm ?_ (sup_le (le_componentOrbit L ⊤) ?_)⟩
  · refine iSup_le fun a => ?_
    by_cases ha : (a : G) ∈ normalizer (L : Set G)
    · have he : L.map (MulAut.conj (a : G)).toMonoidHom = L :=
        mem_normalizer_iff_map_conj_eq.mp ha
      rw [he]
      exact le_sup_left
    have hga : g⁻¹ * (a : G) ∈ normalizer (L : Set G) :=
      (mul_mem_iff_of_index_two hidx).mpr (iff_of_false (by simpa using hg) ha)
    have he : L.map (MulAut.conj (a : G)).toMonoidHom = L.map (MulAut.conj g).toMonoidHom := by
      calc
        _ = (L.map (MulAut.conj (g⁻¹ * (a : G))).toMonoidHom).map
            (MulAut.conj g).toMonoidHom := by
          rw [map_map]
          congr 1
          ext x
          simp [MulAut.conj_apply,mul_assoc]
        _ = _ := congrArg (map (MulAut.conj g).toMonoidHom)
          (mem_normalizer_iff_map_conj_eq.mp hga)
    rw [he]
    exact le_sup_right
  · exact le_iSup (fun a : (⊤ : Subgroup G) => L.map (MulAut.conj (a : G)).toMonoidHom)
      ⟨g,mem_top g⟩


namespace Hypothesis
variable {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
 {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
 [IsElementaryAbelian 2 X] {X₀ : Subgroup X} (h : Hypothesis ρ B v W X X₀)
include h

/-- The isotropic constituent has the sharper degree needed in G.11.7. -/
theorem isotropic_degree_le_actor_rank_add_one
 {I : Submodule (ZMod 2) V} (hiso : ∀u∈I,∀w∈I,B u w=0) :
 finrank (ZMod 2) I ≤ finrank (ZMod 2) (Additive X)+1 := by
  have hi := B.twice_finrank_le_of_isotropic h.nondegenerate I hiso
  have hr := (Group.rank_le_of_surjective (QuotientGroup.mk' X₀)
    (QuotientGroup.mk'_surjective X₀)).trans (IsElementaryAbelian.rank_le_finrank (p:=2) X)
  have hd := h.dimension_bound.1
  omega

/-- G.9.3 on the actual Aut_HX(I), with the source assumption that X acts
faithfully on I kept explicit. Homogeneity supplies the component pair and
faithfulness on H; the original cover is pulled back to HX. -/
theorem componentHypothesis_of_marked_constituent {K : GroupClass.{u}}
 (cover : Nonempty (Section09.SQTKCover K G))
 (hn : ¬ Group.IsSolvable G) {L : Subgroup G} (hL : IsComponent G L)
 (hm : ⁅L,X⁆ ≠ ⊥) (S : Sylow 2 G)
 (hnX : (S : Subgroup G) ≤ normalizer (X : Set G))
 (hind : (normalizer (L : Set G)).index ≤ 2)
 {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ (componentOrbit L ⊤) I)
 (hv : v ∈ I)
 (hfX : Function.Injective (fun x : X => (ρ (x : G)).comp I.subtype)) :
 let H := componentOrbit L ⊤
 letI : H.Normal := componentOrbit_top_normal L
 let hXI := h.stabilizes_constituent_of_point_mem (h.irreducible_of_not_solvable hn) H hI hv
 let σ := Section09.constituentAction ρ H X I hI.choose hXI
 let P := H ⊔ X
 let q := QuotientGroup.mk' σ.ker
 Section09.ComponentHypothesis K (kerRepresentation σ) ((X.subgroupOf P).map q)
   ((L.subgroupOf P).map q) ((H.subgroupOf P).map q)
   (finrank (ZMod 2) (Additive X)) := by
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  have hi := h.irreducible_of_not_solvable hn
  have hXI := h.stabilizes_constituent_of_point_mem hi H hI hv
  have hR := hI.irreducible_of_normal_restriction ρ hi H
  have hh := h.constituent_sameModule_of_point_mem hn hL hm S hnX hind hI hv
  have hfH := (h.constituent_homogeneous_faithful_selfDual_of_point_mem
    hn hL hm S hnX hind hI hv).2.1
  have hfx : Function.Injective (invariantSubspace ρ X I hXI).toRepresentation := by
    intro a b hab
    apply hfX
    ext w
    exact congrArg Subtype.val (LinearMap.congr_fun hab w)
  have hd : finrank (ZMod 2) I ≤ 2*(finrank (ZMod 2) (Additive X)+1) := by
    have hr := (Group.rank_le_of_surjective (QuotientGroup.mk' X₀)
      (QuotientGroup.mk'_surjective X₀)).trans (IsElementaryAbelian.rank_le_finrank (p:=2) X)
    exact I.finrank_le.trans (h.dimension_bound.1.trans (by omega))
  refine Section09.componentHypothesis_constituent ρ cover X L H I hI.choose hXI hfH hfx hR
    (finrank (ZMod 2) (Additive X)) ?_ hd hL hm (le_componentOrbit L ⊤) ?_
  · change Nat.card (Additive X) = _
    rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod]
  · rcases orbit_pair L hind with he | ⟨g,he⟩
    · exact Or.inl he
    have h₂H : L.map (MulAut.conj g).toMonoidHom ≤ H := by
      rw [show H = L ⊔ L.map (MulAut.conj g).toMonoidHom from he]
      exact le_sup_right
    exact Or.inr ⟨_,h₂H,hL.map_equiv (MulAut.conj g),he,
      Section09.constituent_quasiequivalent_conjugate ρ H I hI.choose hR hh L
        (le_componentOrbit L ⊤) g _ _⟩
end Hypothesis
end CFSG.Quasithin.ChapterG.Section10
