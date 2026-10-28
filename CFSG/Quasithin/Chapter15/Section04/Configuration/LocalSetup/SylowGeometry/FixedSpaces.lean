module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CentralGeometry
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ActionConstruction.Coordinates

/-!
# Fixed spaces for the two-factor decomposition

The index-four decomposition in Aschbacher–Smith 15.4.12(5–6) gives two
fixed lines: each invariant factor has a nontrivial fixed subgroup by the
two-group fixed-point theorem, and their product has order four. A larger
actor normalizing both factors fixes these lines pointwise. Restricting the
internal direct product therefore gives the fixed hyperplanes and the exact
cardinality needed in 15.4.19.

All products, centralizers and normalizers are taken in the common ambient
group. The source adapter in `CentralAssembly` uses these calculations with
the actual Thompson omega center and the actual subgroup commutator modules.
The decomposition and conjugation witnesses still have to be realized from
the earlier source construction.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed pp.1160–1163, especially the second paragraph of 15.4.19.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup
open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem normalizer_le_centralizer_of_card_two (A : Subgroup G)
    (hA : Nat.card A = 2) : normalizer (A : Set G) ≤ centralizer (A : Set G) := by
  obtain ⟨z, _, hzuniq⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
  intro g hg
  apply mem_centralizer_iff.mpr
  intro x hx
  by_cases hxone : x = 1
  · simp [hxone]
  let xA : A := ⟨x, hx⟩
  let yA : A := ⟨g * x * g⁻¹, (hg x).mp hx⟩
  have hyne : yA ≠ 1 := by
    intro hy
    apply hxone
    have hy' : g * x * g⁻¹ = 1 := congrArg Subtype.val hy
    have h := congrArg (fun a : G => g⁻¹ * a * g) hy'
    simpa [mul_assoc] using h
  have heq : yA = xA := (hzuniq yA hyne).trans (hzuniq xA (by
    intro hx'
    exact hxone (congrArg Subtype.val hx'))).symm
  exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val heq)).symm

/-- A nontrivial normal subgroup of a finite two-group has nontrivial fixed subgroup. -/
theorem fixed_subgroup_ne_bot_of_normalized_two_subgroup {S V : Subgroup G}
    (hS : IsPGroup 2 S) (hVS : V ≤ S) (hn : S ≤ normalizer (V : Set G))
    (hV : V ≠ ⊥) : V ⊓ centralizer (S : Set G) ≠ ⊥ := by
  let Vₛ := V.subgroupOf S
  have hVₛ : Vₛ ≠ ⊥ := by
    intro hb
    apply hV
    rw [← map_subgroupOf_eq_of_le hVS]
    change Vₛ.map S.subtype = ⊥
    rw [hb, Subgroup.map_bot]
  let : Vₛ.Normal := normal_subgroupOf_of_le_normalizer hn
  let : Nontrivial Vₛ := (nontrivial_iff_ne_bot Vₛ).mpr hVₛ
  let : Fact (IsPGroup 2 S) := ⟨hS⟩
  obtain ⟨v, hv, hc⟩ := exists_nontrivial_center_mem_normal (p := 2) Vₛ
  intro hb
  have hvc : ((v : S) : G) ∈ centralizer (S : Set G) := by
    apply mem_centralizer_iff.mpr
    intro s hs
    exact congrArg Subtype.val ((mem_center_iff.mp hc) ⟨s, hs⟩)
  have hv1 := mem_bot.mp (hb ▸ (show ((v : S) : G) ∈ V ⊓ centralizer (S : Set G)
    from ⟨v.property, hvc⟩))
  exact hv (Subtype.ext (Subtype.ext hv1))

/-- The index-four decomposition of 15.4.12 forces both invariant factors to
have fixed lines. This derives their orders from the decomposition, rather than
assuming the two hyperplanes needed later. -/
theorem fixed_lines_of_index_four {E C S V₁ V₂ : Subgroup G}
    [IsMulCommutative E]
    (hS : IsPGroup 2 S) (hV₁S : V₁ ≤ S) (hV₂S : V₂ ≤ S)
    (hn₁ : S ≤ normalizer (V₁ : Set G)) (hn₂ : S ≤ normalizer (V₂ : Set G))
    (hV₁ : V₁ ≠ ⊥) (hV₂ : V₂ ≠ ⊥)
    (hcomm : V₁ ≤ centralizer (V₂ : Set G)) (hdis : Disjoint V₁ V₂)
    (hCdis : Disjoint C (V₁ ⊔ V₂))
    (hE : C ⊔ ((V₁ ⊔ V₂) ⊓ centralizer (S : Set G)) = E)
    (hindex : C.relIndex E = 4) :
    Nat.card (V₁ ⊓ centralizer (S : Set G) : Subgroup G) = 2 ∧
    Nat.card (V₂ ⊓ centralizer (S : Set G) : Subgroup G) = 2 := by
  let F₁ := V₁ ⊓ centralizer (S : Set G)
  let F₂ := V₂ ⊓ centralizer (S : Set G)
  have hsplit := TwoFactors.fixed_subgroup_split_of_internal_factors hdis hcomm hn₁ hn₂
  have he : C ⊔ (F₁ ⊔ F₂) = E := hsplit ▸ hE
  have hCE : C ≤ E := he ▸ le_sup_left
  have hFE : F₁ ⊔ F₂ ≤ E := he ▸ le_sup_right
  have hnorm : F₁ ⊔ F₂ ≤ normalizer (C : Set G) :=
    (hFE.trans ((le_centralizer E).trans (centralizer_le hCE))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hcard := card_sup_eq_mul_of_normalizes_of_disjoint C (F₁ ⊔ F₂) hnorm
    (hCdis.mono_right (sup_le_sup inf_le_left inf_le_left))
  rw [he] at hcard
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G) C E bot_le hCE
  rw [relIndex_bot_left, relIndex_bot_left, hindex, hcard] at hi
  have hFcard : Nat.card (F₁ ⊔ F₂ : Subgroup G) = 4 :=
    (Nat.eq_of_mul_eq_mul_left Nat.card_pos hi).symm
  have hprod := card_sup_eq_mul_of_normalizes_of_disjoint F₁ F₂
    ((show F₂ ≤ V₂ from inf_le_left).trans
      (((le_centralizer_iff.mp hcomm).trans (centralizer_le
        (show F₁ ≤ V₁ from inf_le_left))).trans (Subgroup.centralizer_le_normalizer _)))
    (hdis.mono inf_le_left inf_le_left)
  have h₁ := (one_lt_card_iff_ne_bot F₁).mpr
    (fixed_subgroup_ne_bot_of_normalized_two_subgroup hS hV₁S hn₁ hV₁)
  have h₂ := (one_lt_card_iff_ne_bot F₂).mpr
    (fixed_subgroup_ne_bot_of_normalized_two_subgroup hS hV₂S hn₂ hV₂)
  rw [hFcard] at hprod
  constructor <;> nlinarith

omit [Finite G] in
/-- A subgroup normalizing a fixed line fixes it pointwise. Thus enlarging the
actor from the Baumann subgroup to the common factor stabilizer preserves that line. -/
theorem fixed_line_unchanged {S U V : Subgroup G} (hSU : S ≤ U)
    (hnS : U ≤ normalizer (S : Set G)) (hnV : U ≤ normalizer (V : Set G))
    (hcard : Nat.card (V ⊓ centralizer (S : Set G) : Subgroup G) = 2) :
    V ⊓ centralizer (U : Set G) = V ⊓ centralizer (S : Set G) := by
  apply le_antisymm (inf_le_inf_left _ (centralizer_le hSU))
  have hn : U ≤ normalizer ((V ⊓ centralizer (S : Set G) : Subgroup G) : Set G) :=
    (le_inf hnV (hnS.trans (normalizer_le_normalizer_centralizer S))).trans
      inf_normalizer_le_normalizer_inf
  exact le_inf inf_le_left (le_centralizer_iff.mp
    (hn.trans (normalizer_le_centralizer_of_card_two _ hcard)))

/-- Restrict a fixed-free line decomposition to an overgroup of its original actor.
The result constructs both the fixed hyperplane and its disjoint fixed line. -/
theorem fixed_hyperplane_of_line_decomposition {E C S U V L : Subgroup G}
    [IsMulCommutative E]
    (hE : C ⊔ (V ⊓ centralizer (S : Set G)) = E)
    (hC : C ≤ centralizer (L : Set G))
    (hfree : (V ⊓ centralizer (S : Set G)) ⊓ centralizer (L : Set G) = ⊥)
    (hSU : S ≤ U) (hnS : U ≤ normalizer (S : Set G))
    (hnV : U ≤ normalizer (V : Set G)) (hnC : U ≤ normalizer (C : Set G))
    (hcard : Nat.card (V ⊓ centralizer (S : Set G) : Subgroup G) = 2) :
    (E ⊓ centralizer ((L ⊔ U : Subgroup G) : Set G)).relIndex
      (E ⊓ centralizer (U : Set G)) = 2 ∧
    V ⊓ centralizer (U : Set G) ≤ E ∧
    Nat.card (V ⊓ centralizer (U : Set G) : Subgroup G) = 2 ∧
    (E ⊓ centralizer ((L ⊔ U : Subgroup G) : Set G)) ⊓
      (V ⊓ centralizer (U : Set G)) = ⊥ := by
  let F := V ⊓ centralizer (S : Set G)
  have hCE : C ≤ E := hE ▸ le_sup_left
  have hFE : F ≤ E := hE ▸ le_sup_right
  have hc : C ≤ centralizer (F : Set G) :=
    hCE.trans ((le_centralizer E).trans (centralizer_le hFE))
  have hd : Disjoint C F := by
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    exact (le_inf inf_le_right (inf_le_left.trans hC)).trans hfree.le
  have hnF : U ≤ normalizer (F : Set G) :=
    (le_inf hnV (hnS.trans (normalizer_le_normalizer_centralizer S))).trans
      inf_normalizer_le_normalizer_inf
  have hFU : F ≤ centralizer (U : Set G) := le_centralizer_iff.mp
    (hnF.trans (normalizer_le_centralizer_of_card_two F hcard))
  have he : (C ⊓ centralizer (U : Set G)) ⊔ F = E ⊓ centralizer (U : Set G) := by
    rw [← hE, TwoFactors.fixed_subgroup_split_of_internal_factors hd hc hnC hnF,
      inf_of_le_left hFU]
  have hfixed : E ⊓ centralizer ((L ⊔ U : Subgroup G) : Set G) =
      (E ⊓ centralizer (U : Set G)) ⊓ centralizer (L : Set G) := by
    rw [fixed_subgroup_join]
    simp only [inf_assoc, inf_left_comm, inf_comm, inf_left_idem]
  have hline := fixed_line_unchanged hSU hnS hnV hcard
  have hcomm : C ⊓ centralizer (U : Set G) ≤ centralizer (F : Set G) := inf_le_left.trans hc
  have hi := TwoFactors.centralizer_index_two_of_fixed_complement he hcomm
    (inf_le_left.trans hC) hfree hcard
  refine ⟨hfixed ▸ hi, hline ▸ hFE, hline ▸ hcard, ?_⟩
  apply le_bot_iff.mp
  rw [hline]
  exact (le_inf inf_le_right (inf_le_left.trans
    (inf_le_right.trans (centralizer_le (show L ≤ L ⊔ U from le_sup_left))))).trans hfree.le


/-- The complete fixed-space calculation for the two modules belonging to one
of the source overgroups. The index-four decomposition and two-group fixed-point
theorem construct the two lines, and their invariance constructs the hyperplanes. -/
theorem two_factor_fixed_geometry {E C S U : Subgroup G}
    (V L : Bool → Subgroup G) [IsMulCommutative E]
    (hS : IsPGroup 2 S) (hSU : S ≤ U)
    (hVS : ∀ i, V i ≤ S) (hnV : ∀ i, U ≤ normalizer (V i : Set G))
    (hVne : ∀ i, V i ≠ ⊥)
    (hnS : U ≤ normalizer (S : Set G)) (hnC : U ≤ normalizer (C : Set G))
    (hcomm : V false ≤ centralizer (V true : Set G))
    (hdis : Disjoint (V false) (V true))
    (hCdis : Disjoint C (V false ⊔ V true))
    (hE : C ⊔ ((V false ⊔ V true) ⊓ centralizer (S : Set G)) = E)
    (hindex : C.relIndex E = 4)
    (hCL : C ≤ centralizer ((L false ⊔ L true : Subgroup G) : Set G))
    (hcross : ∀ i, V (!i) ≤ centralizer (L i : Set G))
    (hfree : (V false ⊔ V true) ⊓
      centralizer ((L false ⊔ L true : Subgroup G) : Set G) = ⊥) :
    (∀ i, (E ⊓ centralizer ((L i ⊔ U : Subgroup G) : Set G)).relIndex
        (E ⊓ centralizer (U : Set G)) = 2 ∧
      V i ⊓ centralizer (U : Set G) ≤ E ∧
      Nat.card (V i ⊓ centralizer (U : Set G) : Subgroup G) = 2 ∧
      (E ⊓ centralizer ((L i ⊔ U : Subgroup G) : Set G)) ⊓
        (V i ⊓ centralizer (U : Set G)) = ⊥) ∧
    Nat.card (E ⊓ centralizer (U : Set G) : Subgroup G) =
      Nat.card (C ⊓ centralizer (U : Set G) : Subgroup G) * 4 := by
  let F (i : Bool) := V i ⊓ centralizer (S : Set G)
  have hcard := fixed_lines_of_index_four hS (hVS false) (hVS true)
    (hSU.trans (hnV false)) (hSU.trans (hnV true)) (hVne false) (hVne true)
    hcomm hdis hCdis hE hindex
  have hFc (i : Bool) : Nat.card (F i) = 2 := by
    cases i
    · exact hcard.1
    · exact hcard.2
  have hsplit := TwoFactors.fixed_subgroup_split_of_internal_factors hdis hcomm
    (hSU.trans (hnV false)) (hSU.trans (hnV true))
  have he : C ⊔ (F false ⊔ F true) = E := hsplit ▸ hE
  have hFle (i : Bool) : F i ≤ E := by
    apply (show F i ≤ F false ⊔ F true from ?_).trans (he ▸ le_sup_right)
    cases i
    · exact le_sup_left
    · exact le_sup_right
  have hCLe : C ≤ E := he ▸ le_sup_left
  have hnF (i : Bool) : U ≤ normalizer (F i : Set G) :=
    (le_inf (hnV i) (hnS.trans (normalizer_le_normalizer_centralizer S))).trans
      inf_normalizer_le_normalizer_inf
  have hFU (i : Bool) : F i ≤ centralizer (U : Set G) := le_centralizer_iff.mp
    ((hnF i).trans (normalizer_le_centralizer_of_card_two _ (hFc i)))
  have hVle (i : Bool) : V i ≤ V false ⊔ V true := by
    cases i
    · exact le_sup_left
    · exact le_sup_right
  have hLle (i : Bool) : L i ≤ L false ⊔ L true := by
    cases i
    · exact le_sup_left
    · exact le_sup_right
  have hfreei (i : Bool) : F i ⊓ centralizer (L i : Set G) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    apply hfree.le
    refine ⟨hVle i hx.1.1, ?_⟩
    have hc : x ∈ centralizer (L (!i) : Set G) := by
      have hh := hcross (!i)
      simp only [Bool.not_not] at hh
      exact hh hx.1.1
    have hh : zpowers x ≤ centralizer ((L false ⊔ L true : Subgroup G) : Set G) := by
      apply le_centralizer_iff.mpr
      apply sup_le
      all_goals apply le_centralizer_iff.mp; rw [zpowers_le]
      · cases i
        · exact hx.2
        · exact hc
      · cases i
        · exact hc
        · exact hx.2
    exact hh (mem_zpowers x)
  constructor
  · intro i
    let D := C ⊔ F (!i)
    have hDE : D ⊔ F i = E := by
      cases i <;> simpa only [D, Bool.not_false, Bool.not_true,
        sup_assoc, sup_comm, sup_left_comm] using he
    have hDL : D ≤ centralizer (L i : Set G) :=
      sup_le (hCL.trans (centralizer_le (hLle i))) (inf_le_left.trans (hcross i))
    have hnD : U ≤ normalizer (D : Set G) := by
      exact (le_inf hnC (hnF (!i))).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
    exact fixed_hyperplane_of_line_decomposition hDE hDL (hfreei i)
      hSU hnS (hnV i) hnD (hFc i)
  · have hFcomm : F false ≤ centralizer (F true : Set G) :=
      inf_le_left.trans (hcomm.trans (centralizer_le inf_le_left))
    have hFdis := hdis.mono (show F false ≤ V false from inf_le_left)
      (show F true ≤ V true from inf_le_left)
    have hprod : Nat.card (F false ⊔ F true : Subgroup G) = 4 := by
      rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
        ((le_centralizer_iff.mp hFcomm).trans (Subgroup.centralizer_le_normalizer _)) hFdis,
        hFc false, hFc true]
    have hCFcomm : C ≤ centralizer ((F false ⊔ F true : Subgroup G) : Set G) :=
      hCLe.trans ((le_centralizer E).trans (centralizer_le (sup_le (hFle false) (hFle true))))
    have hCFdis : Disjoint C (F false ⊔ F true) :=
      hCdis.mono_right (sup_le_sup inf_le_left inf_le_left)
    have hnFF : U ≤ normalizer ((F false ⊔ F true : Subgroup G) : Set G) :=
      (le_inf (hnF false) (hnF true)).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
    have hFFU : F false ⊔ F true ≤ centralizer (U : Set G) := sup_le (hFU false) (hFU true)
    rw [← he, TwoFactors.fixed_subgroup_split_of_internal_factors hCFdis hCFcomm hnC hnFF,
      inf_of_le_left hFFU]
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
      (((le_centralizer_iff.mp hCFcomm).trans (centralizer_le
        (show C ⊓ centralizer (U : Set G) ≤ C from inf_le_left))).trans
        (Subgroup.centralizer_le_normalizer _)) (hCFdis.mono_left inf_le_left), hprod]


end CFSG.Quasithin.Chapter15.Section04.LocalSetup
