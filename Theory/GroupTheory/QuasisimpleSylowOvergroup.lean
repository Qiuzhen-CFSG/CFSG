module
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Theory.GroupTheory.PerfectCenterFrattini
public import Theory.Quasithin.CoprimeRank

/-!
# A Sylow overgroup criterion for non-enlargement

In a quasisimple group, a subgroup normalized by a full Sylow subgroup
cannot enlarge properly if every overgroup of their images in a central
quotient is the whole quotient. Perfectness removes the central supplement;
the subgroup is then normal and hence central or the whole group.
Odd prime rank survives the restricted central quotient when its source
center is a two-group. The criterion is applied to the literal projective
linear and symplectic targets in the source 2.5.6 argument.
-/
public section
open Subgroup
namespace Theory.GroupTheory
variable {C X : Type*} [Group C] [Finite C] [Group X] [Finite X]

/-- Odd rank survives the actual restriction of a central quotient to a subgroup. -/
theorem odd_rank_subgroupMap_of_central_kernel
    (f : C →* X) (hk : f.ker ≤ center C) (K : Subgroup C)
    (hZ : IsPGroup 2 (center K)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hr : 2 ≤ primeRank p K) : 2 ≤ primeRank p (K.map f) := by
  let g := f.subgroupMap K
  have hker : g.ker ≤ center K := by
    intro x hx
    have hx' : (x : C) ∈ f.ker := congrArg Subtype.val (show g x=1 from hx)
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp (hk hx') y)
  have hp : IsPGroup 2 g.ker := hZ.to_le hker
  rw [←primeRank_quotient_eq_of_isTwoGroup p ho g.ker hp,
    primeRank_congr p (QuotientGroup.quotientKerEquivOfSurjective g (f.subgroupMap_surjective K))] at hr
  exact hr

omit [Finite X] in
/-- The exact central-image Sylow criterion used by both even rank-two targets. -/
theorem eq_top_of_central_image_sylow_overgroups [IsQuasisimple C]
    (K : Subgroup C) [IsQuasisimple K] (P : Sylow 2 C)
    (hn : (P : Subgroup C) ≤ normalizer (K : Set C))
    (f : C →* X) (hf : Function.Surjective f) (hk : f.ker ≤ center C)
    (hforce : ∀ D : Subgroup X,
      ((P.mapSurjective hf) : Subgroup X) ≤ D → K.map f ≤ D → D=⊤) : K=⊤ := by
  let D := K ⊔ (P : Subgroup C)
  have hmap : D.map f=⊤ := hforce (D.map f) (map_mono le_sup_right) (map_mono le_sup_left)
  have hsup : D ⊔ center C=⊤ := by
    apply top_unique
    have he : D ⊔ f.ker=⊤ := by
      rw [←comap_map_eq, hmap, comap_top]
    rw [←he]
    exact sup_le le_sup_left (hk.trans le_sup_right)
  have hD : D=⊤ := eq_top_of_sup_center_eq_top D hsup
  let : K.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [←hD]
    exact sup_le K.le_normalizer hn))
  rcases IsQuasisimple.normal_le_center_or_eq_top K with hc | ht
  · let : Group.IsSolvable K := Group.isSolvable_of_comm
      (fun a b => Subtype.ext (mem_center_iff.mp (hc a.property) b).symm)
    let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
    let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
    exact (Group.IsPerfect.not_isSolvable K inferInstance).elim
  · exact ht

end Theory.GroupTheory
