module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoBetaSaturation

/-!
# The two actual adjacent-core factors in (10.7)

The saturated alpha core is the join of its intersections with the beta
and opposite cores. Their intersection is exactly D_alpha. The elementary
quotient therefore splits as the direct product of these two literal
images, with multiplication as the isomorphism. The original-source
application transports both intersections and the denominator through the
reduced-completion inclusion; no alternative quotient coordinates are used.

The original degree-one unitary rows remain explicit, as in the saturation
theorem. Source: DGS, Groups and Graphs (1985), (10.7)(a)--(b), pp.158--159.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G]

private theorem quotient_core_factors (Q A C D : Subgroup G)
    (hAQ : A ≤ Q) (hCQ : C ≤ Q) (hD : D = A ⊓ C) (hgen : A ⊔ C = Q)
    [(D.subgroupOf Q).Normal] [IsElementaryAbelian 2 (Q ⧸ D.subgroupOf Q)] :
    let q := QuotientGroup.mk' (D.subgroupOf Q)
    let A' := (A.subgroupOf Q).map q
    let C' := (C.subgroupOf Q).map q
    Disjoint A' C' ∧ ∃ e : A' × C' ≃* (Q ⧸ D.subgroupOf Q),
      ∀ a c, e (a,c) = (a : Q ⧸ D.subgroupOf Q) * c := by
  let q := QuotientGroup.mk' (D.subgroupOf Q)
  let A' := (A.subgroupOf Q).map q
  let C' := (C.subgroupOf Q).map q
  have hd : Disjoint A' C' := by
    apply disjoint_def.mpr
    rintro x ⟨a,ha,rfl⟩ ⟨c,hc,he⟩
    have hac : a*c⁻¹ ∈ q.ker := by
      change q (a*c⁻¹) = 1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    have hacD : ((a*c⁻¹ : Q) : G) ∈ D := by
      rw [QuotientGroup.ker_mk'] at hac
      exact hac
    have haC : (a : G) ∈ C := by
      have hh : (a : G) * (c : G)⁻¹ * (c : G) ∈ C :=
        C.mul_mem ((hD ▸ hacD).2) hc
      simpa only [inv_mul_cancel_right] using hh
    exact (QuotientGroup.eq_one_iff a).mpr (hD ▸ ⟨ha,haC⟩)
  have hg : A' ⊔ C' = ⊤ := by
    have hh := congrArg (fun U : Subgroup G => (U.subgroupOf Q).map q) hgen
    rwa [subgroupOf_sup hAQ hCQ,Subgroup.map_sup,subgroupOf_self,
      map_top_of_surjective q (QuotientGroup.mk'_surjective _)] at hh
  have hc : A' ≤ centralizer (C' : Set (Q ⧸ D.subgroupOf Q)) := by
    intro a _ c _
    exact mul_comm c a
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A' C' hd hc
  exact ⟨hd,e.trans ((MulEquiv.subgroupCongr hg).trans Subgroup.topEquiv),he⟩

namespace Reduction
open DGS85.Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true

/-- Actual core-intersection factorization on the original full alpha
endpoint. Every factor, denominator, and multiplication map is retained. -/
theorem original_bTwo_core_factors_or_small_unitary
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S))) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let Q₁ := (parabolic L S 1).pCoreIn 2
    let Q₂ := (Q F₀ t).map (G₀ L S).subtype
    let D₀ := Q₁ ⊓ Q₂
    ClassicalGroup.IsPSU (L 1 ⧸ pCore 2 (L 1)) 3 2 ∨
      IsSU (L 1 ⧸ pCore 2 (L 1)) 3 2 ∨
      ∃ hN : (D₀.subgroupOf Q₀).Normal, letI := hN
        ∃ hE : IsElementaryAbelian 2 (Q₀ ⧸ D₀.subgroupOf Q₀), letI := hE
          let q := QuotientGroup.mk' (D₀.subgroupOf Q₀)
          let A := ((Q₀ ⊓ Q₁).subgroupOf Q₀).map q
          let C := ((Q₀ ⊓ Q₂).subgroupOf Q₀).map q
          Disjoint A C ∧ ∃ e : A × C ≃* (Q₀ ⧸ D₀.subgroupOf Q₀),
            ∀ a c, e (a,c) = (a : Q₀ ⧸ D₀.subgroupOf Q₀) * c := by
  rcases original_bTwo_central_core_or_small_unitary h hb c hactor hcentral ht hne hcomm hnot
    with hp | hs | ⟨hsat,_,_,_,hN,hE,_⟩
  · exact Or.inl hp
  · exact Or.inr (Or.inl hs)
  · right; right
    refine ⟨hN,hE,?_⟩
    let := hN
    let := hE
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let Q₁ := (parabolic L S 1).pCoreIn 2
    let Q₂ := (Q F₀ t).map (G₀ L S).subtype
    have hgen : (Q₀ ⊓ Q₁) ⊔ (Q₀ ⊓ Q₂) = Q₀ := by
      have hseed : centralSeed F₀ α β t =
          (Q F₀ α ⊓ Q F₀ β) ⊔ (Q F₀ α ⊓ Q F₀ t) := by
        simpa only [reducedFamily] using
          c.seed_eq_core_intersections (reduced_triple h) (reduced_kernel_sylow h) hb ht hne
      have hh := congrArg (map (G₀ L S).subtype) hseed
      rw [hsat,Subgroup.map_sup,map_inf _ _ _ (G₀ L S).subtype_injective,
        map_inf _ _ _ (G₀ L S).subtype_injective,
        reduced_base_Q_map h false,reduced_base_Q_map h true] at hh
      exact hh.symm
    obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift (reduced_triple h) ht hne
    obtain ⟨d,_,_⟩ := c.exists_oppositeGeometry (reduced_triple h)
      (reduced_kernel_sylow h) hb g hg hop
    have hDle : Q₁ ⊓ Q₂ ≤ Q₀ := by
      have hh := map_mono (f := (G₀ L S).subtype) d.separated
      change (Q F₀ β ⊓ Q F₀ t).map (G₀ L S).subtype ≤
        (Q F₀ α).map (G₀ L S).subtype at hh
      rwa [map_inf _ _ _ (G₀ L S).subtype_injective,
        reduced_base_Q_map h false,reduced_base_Q_map h true] at hh
    have hD : Q₁ ⊓ Q₂ = (Q₀ ⊓ Q₁) ⊓ (Q₀ ⊓ Q₂) := by
      apply le_antisymm
      · exact le_inf (le_inf hDle inf_le_left) (le_inf hDle inf_le_right)
      · exact le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
    exact quotient_core_factors Q₀ (Q₀ ⊓ Q₁) (Q₀ ⊓ Q₂) (Q₁ ⊓ Q₂)
      inf_le_left inf_le_left hD hgen

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
