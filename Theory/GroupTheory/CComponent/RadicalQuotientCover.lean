module
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement
public import Theory.GroupTheory.PerfectCenterFrattini
public import Theory.GroupTheory.PCoreCoverEquiv

/-!
# Two-core supplements from radical quotient orders

If a subgroup B of a finite group G has radical quotient at least as large
as G's, its image in G/R(G) is the whole quotient. The kernel of that image
is solvable, so its order is bounded by R(B). If G/O₂(G) is quasisimple,
the image of R(G) is central there; perfectness removes this central
supplement and gives G = B O₂(G).

The ambient version retains the original subgroup inclusions and the full
two-core. It supplies the replacement equality I_Z = K_Z O₂(I_Z) in
Aschbacher--Smith 4.4.3, printed p.623, without discarding an odd covering
center or assuming that center has order three.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Equal radical quotient orders force a supplement to the intrinsic two-core. -/
theorem subgroup_sup_twoCore_of_radical_quotient_card
    [IsQuasisimple (G ⧸ pCore 2 G)] (B : Subgroup G)
    (hc : Nat.card (G ⧸ solvableRadical G) ≤ Nat.card (B ⧸ solvableRadical B)) :
    B ⊔ pCore 2 G = ⊤ := by
  let q := QuotientGroup.mk' (solvableRadical G)
  let f := q.comp B.subtype
  let k : f.ker →* solvableRadical G := {
    toFun x := ⟨x.val.val,(QuotientGroup.eq_one_iff _).mp x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective
    (f := k) (by intro x y he; exact Subtype.ext (Subtype.ext (congrArg (fun z : solvableRadical G => (z : G)) he)))
  have hk : f.ker ≤ solvableRadical B := le_solvableRadical _ inferInstance inferInstance
  let g := QuotientGroup.lift f.ker (QuotientGroup.mk' (solvableRadical B))
    (by simpa only [QuotientGroup.ker_mk'] using hk)
  have hg : Function.Surjective g := QuotientGroup.lift_surjective_of_surjective _ _
    (QuotientGroup.mk'_surjective _) _
  have hb : Nat.card (G ⧸ solvableRadical G) ≤ Nat.card f.range := hc.trans
    ((Nat.le_of_dvd Nat.card_pos (card_dvd_of_surjective g hg)).trans_eq
      (Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv))
  have hf : f.range = ⊤ := f.range.eq_top_of_card_eq
    (le_antisymm (card_le_card_group _) hb)
  have hB : B.map q = ⊤ := by rwa [MonoidHom.range_comp,range_subtype] at hf
  have hr : B ⊔ solvableRadical G = ⊤ := by
    have hh := congrArg (comap q) hB
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using hh
  let r := QuotientGroup.mk' (pCore 2 G)
  have hz : (solvableRadical G).map r ≤ center (G ⧸ pCore 2 G) :=
    (map_solvableRadical_le_of_surjective r (QuotientGroup.mk'_surjective _)).trans
      IsQuasisimple.solvableRadical_le_center
  have hi : B.map r ⊔ center (G ⧸ pCore 2 G) = ⊤ := by
    apply top_unique
    rw [←map_top_of_surjective r (QuotientGroup.mk'_surjective _),←hr,Subgroup.map_sup]
    exact sup_le_sup le_rfl hz
  have hf : B.map r = ⊤ := eq_top_of_sup_center_eq_top _ hi
  have hh := congrArg (comap r) hf
  simpa only [comap_map_eq,r,QuotientGroup.ker_mk',comap_top] using hh

open scoped Pointwise
/-- The corresponding product identity retains both original ambient subgroups. -/
theorem subgroup_cover_twoCore_of_radical_quotient_card
    (B R : Subgroup G) (hBR : B ≤ R)
    [IsQuasisimple (R ⧸ pCore 2 R)]
    (hc : Nat.card (R ⧸ solvableRadical R) ≤ Nat.card (B ⧸ solvableRadical B)) :
    (R : Set G) = (B : Set G) * (R.pCoreIn 2 : Set G) := by
  let E := B.subgroupOf R
  let e : E ≃* B := subgroupOfEquivOfLe hBR
  let d := QuotientGroup.congr (solvableRadical E) (solvableRadical B) e
    (map_solvableRadical_equiv e)
  have he : E ⊔ pCore 2 R = ⊤ := subgroup_sup_twoCore_of_radical_quotient_card E
    (hc.trans_eq (Nat.card_congr d.toEquiv).symm)
  ext x
  constructor
  · intro hx
    have hm : (⟨x,hx⟩ : R) ∈ E ⊔ pCore 2 R := he ▸ mem_top _
    obtain ⟨b,hb,c,hc,hbc⟩ := mem_sup_of_normal_right.mp hm
    exact ⟨b,hb,c,mem_map_of_mem R.subtype hc,congrArg R.subtype hbc⟩
  · rintro ⟨b,hb,c,hc,rfl⟩
    exact R.mul_mem (hBR hb) (map_subtype_le _ hc)

end Theory.GroupTheory
