module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Rank

/-!
# Rank-one Sylow subgroups in ambient extensions

Suppose every proper overgroup of a Sylow subgroup P in a normal subgroup L
normalizes P. An ambient overgroup K of P either contains L or normalizes P:
otherwise K ∩ L is a proper overgroup of P, and every K-conjugate of P is a
p-subgroup of N_L(P), hence lies in P. This permits arbitrary outer actions.

If L is nonsolvable and simple, its embedding into any overgroup remains
injective modulo a solvable normal subgroup. Consequently the image of every
subgroup of L has the same generator rank in that quotient.

These elementary group-theoretic facts support the lower bound in
Aschbacher--Smith, *The Classification of Quasithin Groups*, E.1.14(1),
printed p.214, with the quotient conventions of E.1.2 and E.1.5.
-/

public section
open Subgroup
namespace Subgroup.RankOneSylowExtension
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- An ambient overgroup either contains the normal rank-one group or normalizes its Sylow. -/
theorem le_or_le_normalizer (L : Subgroup G) [L.Normal] {p : ℕ} (P : Sylow p L)
    (hproper : ∀ H : Subgroup L, (P : Subgroup L) ≤ H → H ≠ ⊤ →
      H ≤ normalizer (P : Set L))
    (K : Subgroup G) (hPK : (P : Subgroup L).map L.subtype ≤ K) :
    L ≤ K ∨ K ≤ normalizer ((P : Subgroup L).map L.subtype : Set G) := by
  by_cases hLK : L ≤ K
  · exact Or.inl hLK
  right
  have hPH : (P : Subgroup L) ≤ K.subgroupOf L := map_le_iff_le_comap.mp hPK
  have hH : K.subgroupOf L ≠ ⊤ := by
    intro he
    apply hLK
    intro x hx
    exact (show (⟨x, hx⟩ : L) ∈ K.subgroupOf L from he ▸ mem_top _)
  have hHN := hproper _ hPH hH
  apply le_normalizer_iff.mpr
  intro k hk x hx
  obtain ⟨u, hu, rfl⟩ := hx
  let e : MulAut L := MulAut.conjNormal k
  have heH : (P : Subgroup L).map e.toMonoidHom ≤ K.subgroupOf L := by
    rintro _ ⟨v, hv, rfl⟩
    change k * (v : G) * k⁻¹ ∈ K
    exact K.mul_mem (K.mul_mem hk (hPK (mem_map_of_mem _ hv))) (K.inv_mem hk)
  have heP : (P : Subgroup L).map e.toMonoidHom ≤ (P : Subgroup L) := by
    have hi := (P.isPGroup'.map e.toMonoidHom).inf_normalizer_sylow P
    rw [inf_eq_left.mpr (heH.trans hHN)] at hi
    exact inf_eq_left.mp hi.symm
  exact mem_map.mpr ⟨e u, heP (mem_map_of_mem _ hu), rfl⟩

omit [Finite G] in
/-- A nonsolvable simple group embeds in the quotient by a solvable normal subgroup. -/
theorem simple_quotient_injective {H : Type*} [Group H] [IsSimpleGroup H]
    (hH : ¬ Group.IsSolvable H) (j : H →* G) (hj : Function.Injective j)
    (R : Subgroup G) [R.Normal] [Group.IsSolvable R] :
    Function.Injective ((QuotientGroup.mk' R).comp j) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (((QuotientGroup.mk' R).comp j).ker) inferInstance with h | h
  · exact h
  · exfalso
    apply hH
    let f : H →* R := j.codRestrict R (fun x => by
      have hx : x ∈ ((QuotientGroup.mk' R).comp j).ker := h ▸ mem_top x
      exact (QuotientGroup.eq_one_iff _).mp hx)
    exact Group.isSolvable_of_isSolvable_injective (f := f)
      (fun x y hxy => hj (congrArg Subtype.val hxy))

/-- The image of a subgroup of a nonsolvable simple group retains its rank
in the intrinsic solvable quotient of an overgroup. -/
theorem rank_image_solvable_quotient_eq (L A K : Subgroup G) [IsSimpleGroup L]
    (hL : ¬ Group.IsSolvable L) (hAL : A ≤ L) (hLK : L ≤ K)
    (R : Subgroup K) [R.Normal] [Group.IsSolvable R] :
    Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' R)) = Group.rank A := by
  let j : L →* K := inclusion hLK
  have hj : Function.Injective j := inclusion_injective hLK
  have hq := simple_quotient_injective hL j hj R
  have hinj : Function.Injective ((QuotientGroup.mk' R).comp (A.subgroupOf K).subtype) := by
    intro x y hxy
    have h := hq (a₁ := ⟨x.val.val, hAL x.property⟩)
      (a₂ := ⟨y.val.val, hAL y.property⟩) hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : L => (z : G)) h
  let e := MonoidHom.ofInjective hinj
  have he : ((QuotientGroup.mk' R).comp (A.subgroupOf K).subtype).range =
      (A.subgroupOf K).map (QuotientGroup.mk' R) := by
    rw [MonoidHom.range_comp, range_subtype]
  exact (Group.rank_congr (e.trans (MulEquiv.subgroupCongr he))).symm.trans
    (Group.rank_congr (subgroupOfEquivOfLe (hAL.trans hLK)))

end Subgroup.RankOneSylowExtension
