module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Notation
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Families
public import Theory.SpecificGroups.Alternating.FiveProperSubgroups
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# The A₅ equality step in component control

Minimal nonsolvability of the actual alternating group on five letters forces
K₀ to cover K₂ modulo its two-core. The two-core is contained in T. Since
C_T(v) has index two and normalizes K₀, the normalizer of K₀ in K₂ has index
at most two. Perfectness makes that normalizer all of K₂, and the remaining
solvable quotient is trivial.

This is the equality step K₂ = K₀ in Aschbacher–Smith, Lemma 13.6.16(1),
combined 1 March 2004 manuscript, printed p.930. The A₅ quotient is an actual
multiplicative equivalence; no family label or recognition assumption is used.
-/

@[expose] public section
open Subgroup
open CFSG.Quasithin
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
variable {G : Type*} [Group G] [Finite G]

private theorem sup_core_eq_top (B : Subgroup G)
    (hB : ¬ Group.IsSolvable B)
    (e : (G ⧸ pCore 2 G) ≃* alternatingGroup (Fin 5)) :
    B ⊔ pCore 2 G = ⊤ := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have him : B.map q = ⊤ := by
    by_contra hn
    let : Group.IsSolvable (B.map q) :=
      alternatingGroup.isSolvable_subgroup_of_equiv_five e _ hn
    let f := q.subgroupMap B
    have hker : f.ker ≤ (pCore 2 G).subgroupOf B := by
      intro x hx
      exact (QuotientGroup.eq_one_iff (N := pCore 2 G) (x : G)).mp
        (congrArg Subtype.val hx)
    have hp : IsPGroup 2 f.ker :=
      (pCore_isPGroup (p := 2) (G := G)).comap_subtype.to_le hker
    let := hp.isNilpotent
    exact hB (Group.isSolvable_of_ker_le_range f.ker.subtype f (by simp))
  have he := congrArg (comap q) him
  simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using he

private theorem perfect_supplement_eq_top [Group.IsPerfect G]
    (B Q R S : Subgroup G) [Q.Normal] [Group.IsSolvable Q]
    (hBQ : B ⊔ Q = ⊤) (hQS : Q ≤ S)
    (hRN : R ≤ normalizer (B : Set G)) (hidx : R.relIndex S ∣ 2) : B = ⊤ := by
  let N := normalizer (B : Set G)
  have hNi : N.index ∣ 2 := by
    obtain ⟨a, ha, hc⟩ := relIndex_dvd_two_iff.mp hidx
    apply index_dvd_two_iff.mpr
    refine ⟨a, ?_⟩
    intro x
    obtain ⟨b, hb, q, hq, rfl⟩ := mem_sup_of_normal_right.mp (hBQ.symm ▸ mem_top x)
    rcases hc q (hQS hq) with hr | hr
    · exact Or.inl (by simpa only [mul_assoc] using N.mul_mem (B.le_normalizer hb) (hRN hr))
    · exact Or.inr (N.mul_mem (B.le_normalizer hb) (hRN hr))
  have hNt : N = ⊤ := top_le_iff.mp
    (le_of_isPerfect_of_index_le_two ⊤ N (Nat.le_of_dvd (by decide) hNi))
  let : B.Normal := normalizer_eq_top_iff.mp hNt
  let q := QuotientGroup.mk' B
  have hQmap : Q.map q = ⊤ := by
    have he := congrArg (map q) hBQ
    simpa only [Subgroup.map_sup, (map_eq_bot_iff B).mpr (show B ≤ q.ker by simp [q]),
      bot_sup_eq, map_top_of_surjective q (show Function.Surjective q from QuotientGroup.mk'_surjective B)] using he
  let f := q.comp Q.subtype
  have hsur : Function.Surjective f := by
    rw [← MonoidHom.range_eq_top]
    simpa only [f, MonoidHom.range_comp, range_subtype] using hQmap
  let : Group.IsSolvable (G ⧸ B) := Group.isSolvable_of_surjective hsur
  exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ B)

/-- The minimal-nonsolvability and perfectness step of 13.6.16(1).
The containing component is normalized by the actual ambient Sylow group,
whereas the smaller component is initially invariant only under R. -/
theorem eq_of_a5_quotient_of_index_two
    (T : Sylow 2 G) (R K₀ K₂ : Subgroup G)
    (_hR : R ≤ T) (hidx : R.relIndex (T : Subgroup G) = 2)
    (hK₀ : K₀ ∈ Chapter1.L G R)
    (hRK₀ : R ≤ normalizer (K₀ : Set G))
    (hle : K₀ ≤ K₂) (hTK₂ : (T : Subgroup G) ≤ normalizer (K₂ : Set G))
    [Group.IsPerfect K₂]
    (e : (K₂ ⧸ pCore 2 K₂) ≃* alternatingGroup (Fin 5)) : K₂ = K₀ := by
  let B := K₀.subgroupOf K₂
  have hBns : ¬ Group.IsSolvable B := by
    intro hs
    let := hs
    exact Chapter1.mem_L_not_isSolvable hK₀
      (Group.isSolvable_of_surjective
        (f := (subgroupOfEquivOfLe hle).toMonoidHom) (subgroupOfEquivOfLe hle).surjective)
  have hBQ := sup_core_eq_top B hBns e
  have hcoreT : K₂.pCoreIn 2 ≤ T := by
    have hn : (K₂ ⊔ (T : Subgroup G)) ≤ normalizer (K₂.pCoreIn 2 : Set G) :=
      (sup_le K₂.le_normalizer hTK₂).trans
        (normalizer_le_normalizer_characteristic_image K₂ (pCore 2 K₂))
    have hcore : K₂.pCoreIn 2 ≤ (K₂ ⊔ (T : Subgroup G)).pCoreIn 2 :=
      le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 K₂)
        ((pCoreIn_le 2 K₂).trans le_sup_left) hn
    exact hcore.trans (by
      simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
        pCoreIn_le_sylow (K₂ ⊔ (T : Subgroup G)) (T.subtype le_sup_right))
  have hQS : pCore 2 K₂ ≤ (T : Subgroup G).subgroupOf K₂ := by
    intro x hx
    exact hcoreT (mem_map.mpr ⟨x, hx, rfl⟩)
  have hRN : R.subgroupOf K₂ ≤ normalizer (B : Set K₂) := by
    apply le_normalizer_iff.mpr
    intro x hx y hy
    exact (mem_normalizer_iff.mp (hRK₀ hx) (y : G)).mp hy
  have hi : (R.subgroupOf K₂).relIndex ((T : Subgroup G).subgroupOf K₂) ∣ 2 := by
    have hib : (R.subgroupOf K₂).relIndex ((T : Subgroup G).subgroupOf K₂) ≤ 2 := by
      change (R.comap K₂.subtype).relIndex ((T : Subgroup G).subgroupOf K₂) ≤ 2
      rw [relIndex_comap, subgroupOf_map_subtype]
      exact (relIndex_le_of_le_right inf_le_left (by rw [hidx]; decide)).trans_eq hidx
    have hip : (R.subgroupOf K₂).relIndex ((T : Subgroup G).subgroupOf K₂) ≠ 0 :=
      index_ne_zero_of_finite
    have hc : (R.subgroupOf K₂).relIndex ((T : Subgroup G).subgroupOf K₂) = 1 ∨
        (R.subgroupOf K₂).relIndex ((T : Subgroup G).subgroupOf K₂) = 2 := by omega
    rcases hc with h | h <;> simp [h]
  let := (pCore_isPGroup (p := 2) (G := K₂)).isNilpotent
  have he := perfect_supplement_eq_top B (pCore 2 K₂) (R.subgroupOf K₂)
    ((T : Subgroup G).subgroupOf K₂) hBQ hQS hRN hi
  exact le_antisymm ((subgroupOf_eq_top).mp he) hle

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
end
