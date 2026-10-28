module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreE8Orbit
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CoreAbelianBounds
public import Theory.GroupTheory.ElementaryEightFixedPointOrder24
public import Theory.ElementaryAbelian.EightQuotientRank

/-!
# Full centralizers of the nonseed elementary eights

The original five-seed marking forces a pointwise centralizer to fix the
three seeds intersecting a nonseed eight in planes. Its quotient image
therefore has order at most two, and its point-core intersection has order
sixteen. Conversely, the actual order768 normalizer acts on the eight while
fixing the marked involution, so its action has order at most24. These two
bounds identify the full ambient centralizer, without a splitting premise.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private theorem triple_fixing_card (T : Finset (Fin 5)) (hT : T.card = 3) :
    Nat.card (fixingSubgroup (Equiv.Perm (Fin 5)) (T : Set (Fin 5))) = 2 := by
  classical
  let e : fixingSubgroup (Equiv.Perm (Fin 5)) (T : Set (Fin 5)) ≃
      {g : Equiv.Perm (Fin 5) // ∀ i ∈ T, g i = i} :=
    Equiv.subtypeEquivRight fun _ => mem_fixingSubgroup_iff _
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  have hc : ∀ T : Finset (Fin 5), T.card = 3 →
      Fintype.card {g : Equiv.Perm (Fin 5) // ∀ i ∈ T, g i = i} = 2 := by
    decide +kernel
  exact hc T hT

omit [Finite G] in
private theorem centralizer_le_point (E : pointCoreEights z) :
    centralizer (E.val : Set G) ≤ involutionCentralizer z := by
  intro g hg
  exact mem_centralizer_singleton_iff.mpr (hg z E.property.2.1).symm

private theorem nonseed_centralizer_upper (h : TypeAt z V) (E : pointCoreEights z)
    (hEn : E.val ∉ pointCoreSeedOrbit z V) :
    Nat.card (centralizer (E.val : Set G)) ≤ 32 := by
  classical
  obtain ⟨f, S, T, _, hk, hSi, hSr, hSe, hT, hTc, _, _⟩ :=
    h.point_core_nonseed_eight_marking E hEn
  let H := involutionCentralizer z
  let K := centralizer (E.val : Set G)
  let KH := K.subgroupOf H
  have hKH : K ≤ H := centralizer_le_point E
  have hfix : KH.map f ≤ fixingSubgroup (Equiv.Perm (Fin 5))
      (T : Set (Fin 5)) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [mem_fixingSubgroup_iff]
    intro i hi
    change f g i = i
    by_contra hne
    have hc : Nat.card (E.val ⊓ S i : Subgroup G) = 4 := by
      rw [hT] at hi
      exact (Finset.mem_filter.mp hi).2
    have hseed (j : Fin 5) : S j ∈ pointCoreSeedOrbit z V := by
      rw [← hSr]
      exact ⟨j, rfl⟩
    have he := h.point_core_seed_pair_intersection (hseed i) (hseed (f g i))
      (hSi.ne (Ne.symm hne))
    have hle : E.val ⊓ S i ≤ S i ⊓ S (f g i) := by
      intro x hx
      refine ⟨hx.2, ?_⟩
      rw [hSe]
      refine ⟨x, hx.2, ?_⟩
      change (g : G) * x * (g : G)⁻¹ = x
      have hcomm : x * (g : G) = (g : G) * x := hg x hx.1
      rw [← hcomm, mul_inv_cancel_right]
    have hb := card_le_of_le (hle.trans_eq he)
    rw [hc, Nat.card_zpowers, h.involution] at hb
    omega
  have himage : Nat.card (KH.map f) ≤ 2 :=
    (card_le_of_le hfix).trans_eq (triple_fixing_card T hTc)
  have hkernel : Nat.card (KH ⊓ f.ker : Subgroup H) = 16 := by
    rw [← card_subtype H (KH ⊓ f.ker), map_inf _ _ _ H.subtype_injective,
      hk, subgroupOf_map_subtype, inf_eq_left.mpr hKH]
    change Nat.card (K ⊓ H.pCoreIn 2 : Subgroup G) = 16
    rw [inf_comm]
    exact h.point_core_eight_centralizer_card E
  have hprod := IsElementaryAbelian.card_inf_ker_mul_card_map KH f
  rw [hkernel, Nat.card_congr (subgroupOfEquivOfLe hKH).toEquiv] at hprod
  change Nat.card K ≤ 32
  omega

private theorem nonseed_centralizer_lower (h : TypeAt z V) (E : pointCoreEights z)
    (hEn : E.val ∉ pointCoreSeedOrbit z V) :
    32 ≤ Nat.card (centralizer (E.val : Set G)) := by
  classical
  let H := involutionCentralizer z
  let K := centralizer (E.val : Set G)
  let N := H ⊓ normalizer (E.val : Set G)
  let f : N →* MulAut E.val := E.val.normalizerMonoidHom.comp (inclusion inf_le_right)
  let : IsElementaryAbelian 2 E.val := E.property.2.2.1
  have hKN : K ≤ N := le_inf (centralizer_le_point E) (centralizer_le_normalizer _)
  have hk : f.ker = K.subgroupOf N := by
    ext g
    change E.val.normalizerMonoidHom (inclusion inf_le_right g) = 1 ↔ (g : G) ∈ K
    change inclusion inf_le_right g ∈ E.val.normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker]
    rfl
  have hfixed : ∀ a : f.range, (a : MulAut E.val) ⟨z, E.property.2.1⟩ =
      ⟨z, E.property.2.1⟩ := by
    rintro ⟨_, g, rfl⟩
    apply Subtype.ext
    change (g : G) * z * (g : G)⁻¹ = z
    have hg := mem_centralizer_singleton_iff.mp g.property.1
    rw [hg, mul_inv_cancel_right]
  have hz : (⟨z, E.property.2.1⟩ : E.val) ≠ 1 := by
    intro he
    have hz1 : z = 1 := congrArg Subtype.val he
    have hi := h.involution
    simp [hz1] at hi
  have himage : Nat.card f.range ≤ 24 := Nat.le_of_dvd (by decide)
    (elementaryEight_fixed_point_image_card_dvd_twentyfour
      E.property.2.2.2 ⟨z, E.property.2.1⟩ hz f.range hfixed)
  have hprod := f.ker.card_mul_index
  rw [index_ker, hk, Nat.card_congr (subgroupOfEquivOfLe hKN).toEquiv,
    h.point_core_nonseed_eight_normalizer_card E hEn] at hprod
  change 32 ≤ Nat.card K
  nlinarith

/-- A nonseed elementary eight through the marked involution has full
ambient centralizer of order thirty-two. -/
theorem TypeAt.point_core_nonseed_eight_centralizer_card (h : TypeAt z V)
    (E : pointCoreEights z) (hEn : E.val ∉ pointCoreSeedOrbit z V) :
    Nat.card (centralizer (E.val : Set G)) = 32 :=
  Nat.le_antisymm (nonseed_centralizer_upper h E hEn) (nonseed_centralizer_lower h E hEn)

end CFSG.Quasithin.HigmanSims
