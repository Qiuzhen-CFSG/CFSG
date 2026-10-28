module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.JointCentralizer
public import Theory.GroupTheory.OrderNineAutomorphisms
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.CComponent.Basic
public import Theory.GroupTheory.SolvableResidual

/-!
# The field residual lies in the ordinary layer

The source defines a two-component as a C-component whose quotient by its odd
core is quasisimple (Aschbacher--Smith, 1 March 2004 manuscript, printed p.414).
If the ambient odd core embeds in E₉, the odd core of each two-component has
order dividing nine. Its automorphism group is solvable, so the perfect
two-component centralizes it and is an ordinary component. A perfect subgroup
of the odd-extended two-layer consequently lies in the ordinary layer.

This proves the passage from the genuine I.3.2 embedding to `L_f ≤ E(G_f)`
on printed p.1137. The balance embedding itself remains an explicit input.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion
variable {G : Type*} [Group G] [Finite G]

private theorem oddCore_subnormal_le {J : Subgroup G} (hJ : J.IsSubnormal) :
    (pPrimeCore 2 J).map J.subtype ≤ pPrimeCore 2 G := by
  induction hJ with
  | top => exact pPrimeCore_map_subtype_le_pPrimeCore_of_normal 2 ⊤
  | step J K hJK hK hn ih =>
    let := hn
    have h := map_mono (f := K.subtype)
      (pPrimeCore_map_subtype_le_pPrimeCore_of_normal 2 (J.subgroupOf K))
    have he : K.subtype.comp (J.subgroupOf K).subtype =
        J.subtype.comp (subgroupOfEquivOfLe hJK).toMonoidHom := by ext x; rfl
    rw [map_map, he, ← map_map, pPrimeCore_map_iso] at h
    exact h.trans ih

private theorem aut_solvable_of_card_dvd_nine {H : Type*} [Group H] [Finite H]
    (hH : Nat.card H ∣ 9) : Group.IsSolvable (MulAut H) := by
  have hc : Nat.card H = 1 ∨ Nat.card H = 3 ∨ Nat.card H = 9 := by
    have hd : Nat.card H ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨hH, by decide⟩
    have he : Nat.divisors 9 = {1, 3, 9} := by decide
    simpa only [he, Finset.mem_insert, Finset.mem_singleton] using hd
  rcases hc with h | h | h
  · let : Subsingleton H := (Nat.card_eq_one_iff_unique.mp h).1
    exact Group.isSolvable_of_comm (fun a b => by ext x; exact Subsingleton.elim _ _)
  · let : IsCyclic H := isCyclic_of_prime_card h
    exact Group.isSolvable_of_isSolvable_injective
      (f := (IsCyclic.mulAutMulEquiv H).toMonoidHom) (IsCyclic.mulAutMulEquiv H).injective
  · exact MulAut.isSolvable_of_card_nine h

private theorem perfect_hom_eq_one {H D : Type*} [Group H] [Group D]
    [Group.IsPerfect H] [Group.IsSolvable D] (φ : H →* D) : φ = 1 := by
  let : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have hb : φ.range = ⊥ := by
    by_contra hb
    let : Nontrivial φ.range := (nontrivial_iff_ne_bot _).mpr hb
    exact Group.IsPerfect.not_isSolvable φ.range inferInstance
  exact MonoidHom.range_eq_bot_iff.mp hb

private theorem central_of_perfect_of_small_normal {H : Type*} [Group H] [Finite H]
    [Group.IsPerfect H] (N : Subgroup H) [N.Normal] (hN : Nat.card N ∣ 9) :
    N ≤ center H := by
  let : Group.IsSolvable (MulAut N) := aut_solvable_of_card_dvd_nine hN
  have ht : (MulAut.conjNormal : H →* MulAut N) = 1 := perfect_hom_eq_one _
  intro n hn
  rw [mem_center_iff]
  intro h
  have he := congrArg (fun φ : H →* MulAut N => φ h ⟨n, hn⟩) ht
  have he' : h * n * h⁻¹ = n := congrArg Subtype.val he
  exact (mul_inv_eq_iff_eq_mul.mp he')

/-- O_{2',E}(G), using actual two-components and the odd core. -/
@[expose] def oddExtendedTwoComponentLayer (G : Type*) [Group G] : Subgroup G :=
  pPrimeCore 2 G ⊔ sSup {J : Subgroup G |
    J.IsCComponent ∧ IsQuasisimple (J ⧸ pPrimeCore 2 J)}

/-- The rank-two odd-core bound makes each two-component an ordinary component. -/
theorem component_of_twoComponent_of_oddCore_embedding
    (ι : pPrimeCore 2 G →* ElementaryNine) (hι : Function.Injective ι)
    (J : Subgroup G) (hJ : J.IsCComponent)
    (hquot : IsQuasisimple (J ⧸ pPrimeCore 2 J)) : IsComponent G J := by
  let := hJ.perfect
  let := hquot
  have hO : Nat.card (pPrimeCore 2 J) ∣ 9 := by
    have h₁ := card_dvd_of_injective ι hι
    have h₂ := card_dvd_of_le (oddCore_subnormal_le hJ.subnormal)
    rw [card_map_of_injective J.subtype_injective] at h₂
    have hcard : Nat.card ElementaryNine = 9 := by
      simp [ElementaryNine, Nat.card_eq_fintype_card]
    rw [hcard] at h₁
    exact h₂.trans h₁
  let c : PerfectCentralCovering.Cover J (J ⧸ pPrimeCore 2 J) := {
    toMonoidHom := QuotientGroup.mk' (pPrimeCore 2 J)
    surjective := QuotientGroup.mk'_surjective _
    isPerfect := inferInstance
    ker_le_center := by
      rw [QuotientGroup.ker_mk']
      exact central_of_perfect_of_small_normal _ hO }
  exact ⟨hJ.subnormal, c.isQuasisimple⟩

omit [Finite G] in
private theorem layer_normal : (componentLayer G).Normal := by
  have hchar : (componentLayer G).Characteristic := by
    apply characteristic_iff_map_le.mpr
    intro e
    rw [map_le_iff_le_comap]
    apply sSup_le
    intro J hJ
    exact map_le_iff_le_comap.mp (le_sSup (hJ.map_equiv e))
  let := hchar
  infer_instance

omit [Finite G] in
private theorem perfect_le_normal_of_solvable_supplement
    (F A N : Subgroup G) [Group.IsPerfect F] [Group.IsSolvable A] [N.Normal]
    (hF : F ≤ A ⊔ N) : F ≤ N := by
  let q := QuotientGroup.mk' N
  have hmap : F.map q ≤ A.map q := by
    have h := map_mono (f := q) hF
    simpa only [q, Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq] using h
  let : Group.IsSolvable (A.map q) :=
    Group.isSolvable_of_surjective (q.subgroupMap_surjective A)
  let : Group.IsSolvable (F.map q) := Group.isSolvable_of_isSolvable_injective
    (f := inclusion hmap) (inclusion_injective hmap)
  have ht := perfect_hom_eq_one (q.subgroupMap F)
  intro f hf
  apply (QuotientGroup.eq_one_iff f).mp
  exact congrArg Subtype.val (DFunLike.congr_fun ht ⟨f, hf⟩)

/-- A perfect subgroup in the genuine odd-extended two-component layer lies
in E(G) when the odd core embeds in E₉. -/
theorem le_layer_of_balance_embedding (F : Subgroup G) [Group.IsPerfect F]
    (ι : pPrimeCore 2 G →* ElementaryNine) (hι : Function.Injective ι)
    (hF : F ≤ oddExtendedTwoComponentLayer G) : F ≤ componentLayer G := by
  have hl : oddExtendedTwoComponentLayer G ≤ pPrimeCore 2 G ⊔ componentLayer G := by
    apply sup_le le_sup_left
    apply sSup_le
    rintro J ⟨hJ, hquot⟩
    have hJL : J ≤ componentLayer G :=
      le_sSup (component_of_twoComponent_of_oddCore_embedding ι hι J hJ hquot)
    exact hJL.trans le_sup_right
  let : (componentLayer G).Normal := layer_normal
  let : Group.IsSolvable (pPrimeCore 2 G) :=
    Group.isSolvable_of_isSolvable_injective (f := ι) hι
  exact perfect_le_normal_of_solvable_supplement F _ _ (hF.trans hl)
end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion
