module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.CubicAction

/-!
# The order-four or order-eight cubic centralizer

The actual action of C_Q(X₁) on the cyclic Z(U) has kernel Z(U): its
intersection with C_Q(Z(U)) centralizes U and hence equals C_T(U)=Z(U).
Since Aut(Z(U)) has order two, C_Q(X₁) has order four or eight. The original
product decomposition yields |Q|=16|C_Q(X₁)|. The order-four branch gives
Q=U; the remaining branch has |Q|=128 and nonabelian C_Q(X₁) of order eight.
The outer branch is retained for the source extremal-fusion argument.

Source: Aschbacher--Smith, proof of 14.3.33(3), printed p.1005.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Fixing Z(U) inside C_Q(X₁) forces membership in precisely Z(U). -/
theorem core_cubic_center_centralizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.H) (hx3 : orderOf x = 3) :
    (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G)) ⊓ centralizer (F.ZU : Set G) = F.ZU := by
  let := h.chosen.elementary
  obtain ⟨K,hKH,hK,hKT,hU,_⟩ := s.component
  have hTU := (sylow_closure_and_component_centralizers h structural alternatives F s hne
    K hKH hK hKT hU).1
  have hZU : F.ZU ≤ F.U := map_subtype_le (center F.U)
  have hUQ : F.U ≤ F.H.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsPGroup.of_card (n := 6) s.core_shape.card) F.U_le_H (le_normalizer_conjugateSpanBy V F.H)
  have hZC : F.ZU ≤ centralizer (zpowers x : Set G) :=
    le_centralizer_iff.mp (zpowers_le.mpr (point_cubic_centralizes_center F s x hx hx3))
  apply le_antisymm ?_ (le_inf (le_inf (hZU.trans hUQ) hZC)
    ((centerIn_le_centralizer F.U).trans (centralizer_le hZU)))
  rintro q ⟨hq,hqZ⟩
  rw [← hTU]
  refine ⟨point_core_le_sylow F hq.1, ?_⟩
  have hfix : F.U ≤ centralizer ({q} : Set G) := by
    rw [closure_cubic_decomposition F s x hx hx3]
    refine sup_le ?_ ?_
    · intro d hd
      exact mem_centralizer_singleton_iff.mpr
        ((core_cubic_centralizes_commutator F s x hx hx3 hq) d hd)
    · intro z hz
      exact mem_centralizer_singleton_iff.mpr (hqZ z hz)
  intro u hu
  exact mem_centralizer_singleton_iff.mp (hfix hu)

/-- The order-four center has automorphism group of order two, and the kernel
of its actual C_Q(X₁)-action is Z(U). Thus only orders four and eight occur. -/
theorem core_cubic_centralizer_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.H) (hx3 : orderOf x = 3) :
    Nat.card (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) : Subgroup G) = 4 ∨
    Nat.card (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) : Subgroup G) = 8 := by
  let C := F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G)
  obtain ⟨e⟩ := center_model F s
  let := e.isCyclic.mpr inferInstance
  have hZ : Nat.card F.ZU = 4 := (Nat.card_congr e.toEquiv).trans (Nat.card_zmod 4)
  have ha : Nat.card (MulAut F.ZU) = 2 := by rw [IsCyclic.card_mulAut, hZ]; decide
  have hn : C ≤ normalizer (F.ZU : Set G) :=
    inf_le_left.trans ((pCoreIn_le 2 F.H).trans F.H_normalizes_ZU)
  let f : C →* MulAut F.ZU := F.ZU.normalizerMonoidHom.comp
    (C.subtype.codRestrict _ (fun c => hn c.property))
  have hk : f.ker.map C.subtype = F.ZU := by
    trans C ⊓ centralizer (F.ZU : Set G)
    · ext c
      constructor
      · rintro ⟨y,hy,rfl⟩
        refine ⟨y.property,?_⟩
        change (C.subtype.codRestrict _ (fun c => hn c.property)) y ∈
          F.ZU.normalizerMonoidHom.ker at hy
        rwa [normalizerMonoidHom_ker] at hy
      · rintro ⟨hc,hcz⟩
        refine ⟨⟨c,hc⟩,?_,rfl⟩
        change (C.subtype.codRestrict _ (fun c => hn c.property)) ⟨c,hc⟩ ∈
          F.ZU.normalizerMonoidHom.ker
        rwa [normalizerMonoidHom_ker]
    · exact core_cubic_center_centralizer h structural alternatives F s hne x hx hx3
  have hkc : Nat.card f.ker = 4 := by rw [← card_map_of_injective C.subtype_injective,hk,hZ]
  have hr : Nat.card f.range = 1 ∨ Nat.card f.range = 2 :=
    (Nat.dvd_prime (by decide : Nat.Prime 2)).mp (ha ▸ f.range.card_subgroup_dvd_card)
  have hh := f.ker.card_mul_index
  rw [hkc,index_ker] at hh
  change 4 * Nat.card f.range = Nat.card C at hh
  rcases hr with hr | hr
  · rw [hr] at hh
    exact Or.inl hh.symm
  · rw [hr] at hh
    exact Or.inr hh.symm

/-- The original cubic centralizer supplements U, and intersects it in Z(U). -/
theorem point_core_cubic_supplement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3) :
    F.H.pCoreIn 2 = F.U ⊔ (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G)) ∧
      F.U ⊓ (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G)) = F.ZU := by
  let := h.chosen.elementary
  have hUQ : F.U ≤ F.H.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsPGroup.of_card (n := 6) s.core_shape.card) F.U_le_H (le_normalizer_conjugateSpanBy V F.H)
  have hXU : zpowers x ≤ normalizer (F.U : Set G) :=
    (zpowers_le.mpr (F.Li_le L 1 hx).2).trans (le_normalizer_conjugateSpanBy V F.H)
  constructor
  · apply le_antisymm ?_ (sup_le hUQ inf_le_left)
    exact (point_core_cubic_decomposition h structural alternatives F s hne x hx hx3).le.trans
      (sup_le_sup_right (le_normalizer_iff_commutator_le_left.mp hXU) _)
  · rw [← inf_assoc,inf_eq_left.mpr hUQ]
    exact closure_cubic_centralizer F s x (F.Li_le L 1 hx).2 hx3

/-- The original Q has order 64 or 128, with its order controlled by the
actual cubic centralizer, rather than by an abstract local model. -/
theorem point_core_card_eq_sixteen_mul_cubic_centralizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3) :
    Nat.card (F.H.pCoreIn 2) =
      16 * Nat.card (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) : Subgroup G) := by
  obtain ⟨hjoin,hinter⟩ := point_core_cubic_supplement h structural alternatives F s hne x hx hx3
  have hn : F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) ≤ normalizer (F.U : Set G) :=
    inf_le_left.trans ((pCoreIn_le 2 F.H).trans (le_normalizer_conjugateSpanBy V F.H))
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes F.U _ hn
  obtain ⟨e⟩ := center_model F s
  have hZ : Nat.card F.ZU = 4 := (Nat.card_congr e.toEquiv).trans (Nat.card_zmod 4)
  rw [s.core_shape.card,hinter,hZ,← hjoin] at hc
  omega

/-- The easy side of the source dichotomy: a cubic centralizer of order four
forces Q=U. -/
theorem closure_core_of_cubic_centralizer_card_four
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3)
    (hc : Nat.card (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) : Subgroup G) = 4) :
    F.U = F.H.pCoreIn 2 := by
  let := h.chosen.elementary
  apply eq_of_le_of_card_ge (le_pCoreIn_of_normalizes
    (IsPGroup.of_card (n := 6) s.core_shape.card) F.U_le_H (le_normalizer_conjugateSpanBy V F.H))
  rw [point_core_card_eq_sixteen_mul_cubic_centralizer h structural alternatives F s hne x hx hx3,
    hc,s.core_shape.card]

/-- Every actual cubic produces the terminal core equality or the nonabelian
order-eight shadow. The latter still requires the original extremal fusion. -/
theorem closure_core_or_outer_cubic
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3) :
    F.U = F.H.pCoreIn 2 ∨
      (Nat.card (F.H.pCoreIn 2) = 128 ∧
       Nat.card (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) : Subgroup G) = 8 ∧
       ¬ IsMulCommutative (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) : Subgroup G)) := by
  rcases core_cubic_centralizer_card h structural alternatives F s hne x (F.Li_le L 1 hx).2 hx3
    with hc | hc
  · exact Or.inl (closure_core_of_cubic_centralizer_card_four h structural alternatives F s hne x hx hx3 hc)
  · refine Or.inr ⟨?_,hc,?_⟩
    · rw [point_core_card_eq_sixteen_mul_cubic_centralizer h structural alternatives F s hne x hx hx3,hc]
    · intro hab
      let := hab
      let C := F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G)
      have he := core_cubic_center_centralizer h structural alternatives F s hne x
        (F.Li_le L 1 hx).2 hx3
      have hZC : F.ZU ≤ C := he.symm.le.trans inf_le_left
      have hCZ : C ≤ centralizer (F.ZU : Set G) := (le_centralizer C).trans (centralizer_le hZC)
      rw [inf_eq_left.mpr hCZ] at he
      obtain ⟨e⟩ := center_model F s
      have hZ : Nat.card F.ZU = 4 := (Nat.card_congr e.toEquiv).trans (Nat.card_zmod 4)
      change Nat.card C = 8 at hc
      rw [he,hZ] at hc
      omega


end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
