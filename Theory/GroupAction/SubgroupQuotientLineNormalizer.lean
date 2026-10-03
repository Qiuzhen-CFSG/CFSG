module
public import Theory.GroupAction.SubgroupQuotientSupportLift
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# The normalizer of a lifted quotient line

For a supplied literal quotient conjugation action, the ambient normalizer
of the full lift of a quotient subgroup of order two, restricted to the
acting subgroup, is exactly the preimage of its nonidentity point's stabilizer
in the original action range. The action and quotient instances remain fixed.

Lifting commutes with conjugation by `lift_support_conjugate`. The quotient
preimage and ambient subtype map are injective on subgroups, so preservation
of the lift is equivalent to preservation of the quotient line. An automorphism
preserves a group of order two exactly when it fixes its unique nonidentity
point. This source-neutral transfer supplies the local normalizer X used in
Stellmacher (9.9), printed p.56/PDF p.46 of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Subgroup
universe u

private theorem line_map_eq_iff_fixed
    {W : Type u} [Group W] (L : Subgroup W) (hL : Nat.card L=2)
    (r : W) (hr : r∈L) (hne : r≠1) (a : MulAut W) :
    L.map a.toMonoidHom=L ↔ a r=r := by
  obtain ⟨point,hpoint,hunique⟩ := (Nat.card_eq_two_iff' (1:L)).mp hL
  have hrpoint : (⟨r,hr⟩ : L)=point := hunique _ (fun h => hne (congrArg Subtype.val h))
  have hcases (w : W) (hw : w∈L) : w=1∨w=r := by
    by_cases heq : w=1
    · exact Or.inl heq
    · exact Or.inr (congrArg Subtype.val ((hunique ⟨w,hw⟩
        (fun h => heq (congrArg Subtype.val h))).trans hrpoint.symm))
  constructor
  · intro hmap
    have hmem : a r∈L := hmap ▸ mem_map_of_mem a.toMonoidHom hr
    rcases hcases _ hmem with hone|heq
    · exact (hne (a.injective (hone.trans (map_one a).symm))).elim
    · exact heq
  · intro hfix
    apply le_antisymm
    · rintro w ⟨v,hv,rfl⟩
      rcases hcases v hv with rfl|rfl
      · simp
      · simpa only [MulEquiv.coe_toMonoidHom,hfix] using hr
    · intro w hw
      rcases hcases w hw with hw1|hwr
      · rw [hw1]
        exact (L.map a.toMonoidHom).one_mem
      · rw [hwr]
        exact ⟨r,hr,hfix⟩

public theorem lift_line_normalizer_eq_comap_stabilizer
    {G : Type u} [Group G] (P U Z : Subgroup G)
    (hPU : P ≤ normalizer (U : Set G))
    (hN : (Z.subgroupOf U).Normal) :
    let _ := hN
    ∀ action : P →* MulAut (U ⧸ Z.subgroupOf U),
      (∀ mover : P, ∀ point : U,
        action mover (QuotientGroup.mk' (Z.subgroupOf U) point) =
          QuotientGroup.mk' (Z.subgroupOf U)
            ⟨(mover:G)*(point:G)*(mover:G)⁻¹,
              (mem_normalizer_iff.mp (hPU mover.property) point).mp point.property⟩) →
      ∀ line : Subgroup (U ⧸ Z.subgroupOf U), Nat.card line=2 →
      ∀ r : U ⧸ Z.subgroupOf U, r∈line → r≠1 →
      ((normalizer (((line.comap (QuotientGroup.mk' (Z.subgroupOf U))).map U.subtype :
        Subgroup G) : Set G)).subgroupOf P) =
          (MulAction.stabilizer action.range r).comap action.rangeRestrict := by
  let _ := hN
  dsimp only
  intro action hact line hline r hr hne
  let q := QuotientGroup.mk' (Z.subgroupOf U)
  ext mover
  change (mover:G)∈normalizer (((line.comap q).map U.subtype : Subgroup G):Set G) ↔
    action.rangeRestrict mover ∈ MulAction.stabilizer action.range r
  rw [MulAction.mem_stabilizer_iff]
  change _ ↔ action mover r=r
  rw [← line_map_eq_iff_fixed line hline r hr hne (action mover)]
  constructor
  · intro hnorm
    have hmap : ((line.comap q).map U.subtype).map (MulAut.conj (mover:G)).toMonoidHom =
        (line.comap q).map U.subtype := mem_normalizer_iff_map_conj_eq.mp hnorm
    have hconj := lift_support_conjugate P U Z hPU action hact line mover
    dsimp only at hconj
    rw [hconj] at hmap
    have hcomap := map_injective U.subtype_injective hmap
    exact comap_injective (QuotientGroup.mk'_surjective _) hcomap
  · intro hmap
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hconj := lift_support_conjugate P U Z hPU action hact line mover
    dsimp only at hconj
    rw [hmap] at hconj
    exact hconj

end Subgroup
