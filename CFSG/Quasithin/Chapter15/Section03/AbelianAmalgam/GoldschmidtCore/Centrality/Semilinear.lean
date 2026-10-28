module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Assembly
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.SpecificGroups.PSL3Two.Parabolics.Fano
public import Theory.Representation.PSL3Two.SmallModules
public import Theory.Representation.PSL3Two.SmallModuleProperties

/-!
# The actual quotient action in the terminal two-local

This file records the action which is used in the non-central (``bad
character'') branch of the proof of 15.3.68.  The action is on the literal
quotient `B / O₂(B)`: it is obtained from the conjugation action of the actual
overgroup `H` and retains the formula on quotient representatives.  In
particular, `chi` is not an arbitrary map to a group of order two.

The recognition and F.6.18/B.5.6 arguments consume the small interface below.
Their source hypotheses are kept as explicit propositions.  The generic
lemmas prove the quotient action, the containment of the local two-core in
the ambient two-core, and the two kernel reductions used in the final
assembly.  The last part also exports the checked seven-point Fano geometry
and the actual binary natural module of `SL₃(2)`.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), printed
pp.1153--1155 (PDF pp.1170--1172), especially 15.3.67--68 and the terminal
module argument.
-/

@[expose] public section

open Subgroup Stellmacher
open scoped Pointwise

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear

universe u
variable {G : Type u} [Group G]

/-- The ambient image and intrinsic form of the local two-core. -/
abbrev ambientTwoCore (B : Subgroup G) : Subgroup G :=
  (pCore 2 B).map B.subtype

abbrev localTwoCore (B : Subgroup G) : Subgroup B :=
  (ambientTwoCore B).subgroupOf B

theorem localTwoCore_eq_pCore (B : Subgroup G) :
    localTwoCore B = pCore 2 B := subgroupOf_map_subtype_eq _

theorem ambientTwoCore_eq_pCoreIn (B : Subgroup G) :
    ambientTwoCore B = B.pCoreIn 2 := rfl

instance localTwoCore_normal (B : Subgroup G) : (localTwoCore B).Normal := by
  dsimp [localTwoCore, ambientTwoCore]
  rw [subgroupOf_map_subtype_eq]
  infer_instance

/-! ## The literal quotient action -/

/-- The conjugation action of `H` on the actual local quotient `B/O₂(B)`.

The two normalizer hypotheses are deliberately derived from `H ≤ N(B)`: the
two-core is characteristic in `B`, so no independent normality of `O₂(B)` in
`H` is smuggled into the definition. -/
noncomputable def quotientAction (H B : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G)) :
    H →* MulAut (B ⧸ localTwoCore B) := by
  let hH0 : H ≤ normalizer (ambientTwoCore B : Set G) :=
    hHB.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  let ρ := Classical.choose (exists_quotient_conjugation_action H B (ambientTwoCore B)
    hHB hH0 inferInstance)
  exact ρ

/-- The action on a quotient representative is the ambient conjugation formula. -/
theorem quotientAction_apply (H B : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G))
    (h : H) (b : B) :
    quotientAction H B hHB h (QuotientGroup.mk' _ b) =
      QuotientGroup.mk' _
        ⟨(h : G) * (b : G) * (h : G)⁻¹,
          (mem_normalizer_iff.mp
            (hHB h.property) b).mp b.property⟩ := by
  let hH0 : H ≤ normalizer (ambientTwoCore B : Set G) :=
    hHB.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  exact Classical.choose_spec (exists_quotient_conjugation_action H B (ambientTwoCore B)
    hHB hH0 inferInstance) h b

/-- The kernel criterion for the actual action.  This is the useful form when
proving that a particular source subgroup is `N = Q ∩ ker(chi)`. -/
theorem quotientAction_mem_ker_iff (H B : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G)) (h : H) :
    h ∈ (quotientAction H B hHB).ker ↔
      ∀ b : B,
        QuotientGroup.mk' (localTwoCore B)
            ⟨(h : G) * (b : G) * (h : G)⁻¹,
              (mem_normalizer_iff.mp
                (hHB h.property) b).mp b.property⟩ =
          QuotientGroup.mk' (localTwoCore B) b := by
  constructor
  · intro hh b
    rw [MonoidHom.mem_ker] at hh
    have := congrArg (fun a : MulAut (B ⧸ localTwoCore B) =>
      a (QuotientGroup.mk' (localTwoCore B) b)) hh
    rw [quotientAction_apply H B hHB h b] at this
    exact this
  · intro hh
    rw [MonoidHom.mem_ker]
    ext z
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (localTwoCore B) z
    rw [quotientAction_apply H B hHB h b]
    exact hh b

/-- The local two-core embeds in the ambient two-core whenever the local group
is contained in `H` and `H` normalizes the local group. -/
theorem local_twoCore_le_ambient_twoCore (H B : Subgroup G)
    (hBH : B ≤ H) (hHB : H ≤ normalizer (B : Set G)) :
    ambientTwoCore B ≤ ambientTwoCore H := by
  let hH0 : H ≤ normalizer (ambientTwoCore B : Set G) :=
    hHB.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 B)
    ((pCoreIn_le 2 B).trans hBH) hH0

/-! ## The source-local kernel interface -/

/-- The actual data used by the bad-character reduction.

`U` is the normal closure of the original binary four-group.  The
`kernel_centralizer_iff` field is the finite local action calculation, stated
pointwise so that later consumers cannot silently replace it by a common-core
assertion.  The remaining fields are earlier source conclusions or explicit
recognition inputs, rather than definitions of the desired result. -/
structure SourceData (H B Q U V : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G)) where
  hBH : B ≤ H
  hQ : Q = ambientTwoCore H
  hQH : Q ≤ H
  hU : U ≤ H
  hV : V ≤ U
  hB0U : ambientTwoCore B ≤ centralizer (U : Set G)
  hC_le_Q : H ⊓ centralizer (U : Set G) ≤ Q
  /-- The finite local action calculation, stated pointwise on `Q`. -/
  kernel_centralizer_iff :
    ∀ q : Q,
      (⟨q.1, hQH q.2⟩ : H) ∈ (quotientAction H B hHB).ker ↔
        (q : G) ∈ centralizer (U : Set G)

namespace SourceData

variable {H B Q U V : Subgroup G}
variable {hHB : H ≤ normalizer (B : Set G)}

/-- The kernel intersection `N = Q ∩ ker(chi)` is the actual centralizer of
the constructed module. -/
theorem kernel_inter_eq_centralizer (d : SourceData H B Q U V hHB) :
    Q ⊓ ((quotientAction H B hHB).ker.map H.subtype) =
      H ⊓ centralizer (U : Set G) := by
  ext x
  constructor
  · intro hx
    rcases hx.2 with ⟨h, hh, rfl⟩
    have hcent := (d.kernel_centralizer_iff ⟨(h : G), hx.1⟩).mp hh
    exact ⟨d.hQH hx.1, hcent⟩
  · intro hx
    have hxQ : x ∈ Q := d.hC_le_Q hx
    have hker := (d.kernel_centralizer_iff
      ⟨x, hxQ⟩).mpr hx.2
    exact ⟨hxQ, mem_map.mpr ⟨⟨x, d.hQH hxQ⟩, hker, rfl⟩⟩

/-- The source-local identity also gives the inclusion needed in the ambient
group, with all subgroup coercions retained. -/
theorem kernel_inter_le_centralizer (d : SourceData H B Q U V hHB) :
    Q ⊓ ((quotientAction H B hHB).ker.map H.subtype) ≤
      centralizer (U : Set G) := by
  rw [kernel_inter_eq_centralizer d]
  exact inf_le_right

theorem local_twoCore_le_core (d : SourceData H B Q U V hHB) :
    ambientTwoCore B ≤ Q := by
  rw [d.hQ]
  exact local_twoCore_le_ambient_twoCore H B d.hBH hHB

end SourceData

/-!
## The good/bad split

The dependent coercion is intentionally avoided in the public split below. It
gives the parent a plain proposition about the actual restriction of `chi` to
`Q`, while retaining the quotient action itself.
-/

theorem core_action_trichotomy (H B Q : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G)) (hQ : Q ≤ H) :
    (∀ q : Q, quotientAction H B hHB ⟨q.1, hQ q.2⟩ = 1) ∨
      ∃ q : Q, quotientAction H B hHB ⟨q.1, hQ q.2⟩ ≠ 1 := by
  by_cases h : ∀ q : Q, quotientAction H B hHB ⟨q.1, hQ q.2⟩ = 1
  · exact Or.inl h
  · exact Or.inr (not_forall.mp h)

/-- In the trivial branch the actual quotient action kills the ambient image of
`Q`.  This records exactly what follows from `chi(Q)=1`; centralizing `V`
requires the additional source calculation represented by `SourceData`. -/
theorem trivial_branch_quotient_kernel_le
    (H B Q : Subgroup G) (hHB : H ≤ normalizer (B : Set G))
    (hQH : Q ≤ H)
    (htriv : ∀ q : Q, quotientAction H B hHB ⟨q.1, hQH q.2⟩ = 1) :
    Q ≤ (quotientAction H B hHB).ker.map H.subtype := by
  intro q hq
  refine mem_map.mpr ⟨⟨q, hQH hq⟩, ?_, rfl⟩
  exact MonoidHom.mem_ker.mpr (htriv ⟨q, hq⟩)

/-! ## Concrete binary Fano data used by the exceptional branch -/

open Matrix.PSL3Two.Fano

/-- The orbit set in the marked `L₃(2)` case has seven nonzero points. -/
theorem fano_nonzero_point_card : Fintype.card Point = 7 := card_point

/-- There are seven lines in the actual binary Fano model. -/
theorem fano_line_card : Fintype.card Line = 7 := card_line

/-- Every actual Fano line has three points. -/
theorem fano_points_on_line (l : Line) :
    Fintype.card {p : Point // Incident p l} = 3 := points_on_line l

/-- Distinct points determine a unique actual line. -/
theorem fano_unique_line (p q : Point) (hpq : p ≠ q) :
    ∃! l : Line, Incident p l ∧ Incident q l := unique_line p q hpq

/-- The two concrete natural modules used for the `L₃(2)` marking. -/
abbrev naturalGroup := BinaryLinearThree.Group
abbrev naturalVector := BinaryLinearThree.Vector
abbrev naturalModule : Representation (ZMod 2) naturalGroup naturalVector :=
  BinaryLinearThree.W

theorem natural_module_faithful : Function.Injective naturalModule :=
  BinaryLinearThree.natural_injective

theorem natural_module_finrank :
    Module.finrank (ZMod 2) naturalVector = 3 := by
  simp [naturalVector]

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
