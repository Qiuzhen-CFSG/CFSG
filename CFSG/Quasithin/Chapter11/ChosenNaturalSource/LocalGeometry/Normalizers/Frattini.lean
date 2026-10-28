module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Relative Frattini arguments for the source line normalizer

Frattini's argument is transported from the actual relative normal subgroup
back to the common ambient group. For the zero-fixed-space branch of 11.2.3,
normality of C_G(V1)XT gives the required centralizer supplement. For the
other branch the argument uses a Sylow subgroup of the actual section-action
kernel inside C_G(V1). The line-action and Sylow identifications remain
explicit; these lemmas do not claim to establish them from the chosen module.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.2.3, printed pp.768--769.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
variable {G : Type*} [Group G] [Finite G]

/-- Conjugation by the actual normalizer on A/O₂(A). -/
def coreQuotientAction (A : Subgroup G) :
    normalizer (A : Set G) →* MulAut (A ⧸ pCore 2 A) :=
  (quotientAut (pCore 2 A)).comp A.normalizerMonoidHom

/-- The literal C_{C_G(U)}(A/O₂(A)), embedded in the common ambient group. -/
def lineSectionKernel (U A : Subgroup G) : Subgroup G :=
  centralizer (U : Set G) ⊓
    (coreQuotientAction A).ker.map (normalizer (A : Set G)).subtype

omit [Finite G] in
/-- Normalizing U and A normalizes this actual section-action kernel. -/
theorem lineSectionKernel_normalized {U A : Subgroup G}
    (hA : normalizer (U : Set G) ≤ normalizer (A : Set G)) :
    normalizer (U : Set G) ≤ normalizer (lineSectionKernel U A : Set G) := by
  apply (le_inf (normalizer_le_normalizer_centralizer U) ?_).trans
    inf_normalizer_le_normalizer_inf
  apply hA.trans
  intro g hg
  apply (coreQuotientAction A).ker.le_normalizer_map (normalizer (A : Set G)).subtype
  exact ⟨⟨g, hg⟩, (coreQuotientAction A).ker.normalizer_eq_top ▸ mem_top _, rfl⟩

/-- The Frattini argument with all subgroups returned to the original ambient group. -/
theorem relative_frattini {Y N R : Subgroup G} (hNY : N ≤ Y)
    (hn : Y ≤ normalizer (N : Set G)) (P : Sylow 2 N)
    (hP : (P : Subgroup N).map N.subtype = R) :
    Y = N ⊔ (Y ⊓ normalizer (R : Set G)) := by
  let e := (subgroupOfEquivOfLe hNY).symm
  let Q : Sylow 2 (N.subgroupOf Y) := P.mapSurjective
    (f := e.toMonoidHom) (show Function.Surjective e.toMonoidHom from e.surjective)
  let : (N.subgroupOf Y).Normal := (normal_subgroupOf_iff_le_normalizer hNY).mpr hn
  have hRY : R ≤ Y := hP ▸ (map_subtype_le _).trans hNY
  have hQ : (Q : Subgroup (N.subgroupOf Y)).map (N.subgroupOf Y).subtype =
      R.subgroupOf Y := by
    apply map_injective Y.subtype_injective
    rw [map_subgroupOf_eq_of_le hRY]
    change (((P : Subgroup N).map e.toMonoidHom).map
      (N.subgroupOf Y).subtype).map Y.subtype = R
    rw [map_map, map_map]
    have he : (Y.subtype.comp (N.subgroupOf Y).subtype).comp e.toMonoidHom = N.subtype := rfl
    rw [he]
    exact hP
  have hh := congrArg (map Y.subtype) (Sylow.normalizer_sup_eq_top Q)
  rw [hQ, ← subgroupOf_normalizer_eq hRY, Subgroup.map_sup,
    subgroupOf_map_subtype, map_subgroupOf_eq_of_le hNY, ← MonoidHom.range_eq_map,
    range_subtype] at hh
  simpa only [inf_comm, sup_comm] using hh.symm

/-- The line action needs only normality of C_G(U)XT in N_G(U).
Frattini then produces the source centralizer-times-relative-normalizer equality. -/
theorem line_normalizer_decomposition {T : Sylow 2 G} {U X M : Subgroup G}
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hXU : X ≤ normalizer (U : Set G)) (hXM : X ≤ M)
    (hTM : (T : Subgroup G) ≤ M)
    (hNT : normalizer (T : Set G) ≤ M)
    (hn : normalizer (U : Set G) ≤
      normalizer ((centralizer (U : Set G) ⊔ X ⊔ (T : Subgroup G) : Subgroup G) : Set G)) :
    normalizer (U : Set G) = centralizer (U : Set G) ⊔
      (M ⊓ normalizer (U : Set G)) := by
  let C := centralizer (U : Set G)
  let Y := normalizer (U : Set G)
  let N := C ⊔ X ⊔ (T : Subgroup G)
  have hNY : N ≤ Y := sup_le (sup_le (centralizer_le_normalizer _) hXU) hTU
  have hh := relative_frattini hNY hn (T.subtype (show (T : Subgroup G) ≤ N from le_sup_right))
    (by simpa only [Sylow.coe_subtype] using
      (map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ N from le_sup_right)))
  apply le_antisymm
  · calc
      Y = N ⊔ (Y ⊓ normalizer (T : Set G)) := hh
      _ ≤ C ⊔ (M ⊓ Y) := sup_le
        (sup_le (sup_le le_sup_left (le_sup_right.trans' (le_inf hXM hXU)))
          (le_sup_right.trans' (le_inf hTM hTU)))
        (le_sup_right.trans' (le_inf (inf_le_right.trans hNT) inf_le_left))
  · exact sup_le (centralizer_le_normalizer _) inf_le_right

/-- The nonzero-fixed-space branch uses a normal subgroup of C_G(U)
whose Sylow two-subgroup is the literal point radical R. -/
theorem line_normalizer_le_of_radical {U R M K : Subgroup G}
    (hK : K ≤ centralizer (U : Set G))
    (hKn : normalizer (U : Set G) ≤ normalizer (K : Set G))
    (P : Sylow 2 K) (hP : (P : Subgroup K).map K.subtype = R)
    (hC : centralizer (U : Set G) ≤ M) (hR : normalizer (R : Set G) ≤ M) :
    normalizer (U : Set G) ≤ M := by
  rw [relative_frattini (hK.trans (centralizer_le_normalizer _)) hKn P hP]
  exact sup_le (hK.trans hC) (inf_le_right.trans hR)

open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource

/-- Apply the supplement argument to the original chosen line and Cartan.
The missing line-action theorem must prove the displayed normality and
the source Sylow-normalizer bound, rather than assume the supplement. -/
theorem chosen_line_decomposition {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    {X : Subgroup G} (hX : IsCartan T L X)
    (hXU : X ≤ normalizer (f.Vi 0 : Set G))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hn : normalizer (f.Vi 0 : Set G) ≤
      normalizer ((centralizer (f.Vi 0 : Set G) ⊔ X ⊔ (T : Subgroup G) : Subgroup G) : Set G)) :
    normalizer (f.Vi 0 : Set G) = centralizer (f.Vi 0 : Set G) ⊔
      (normalizer (L : Set G) ⊓ normalizer (f.Vi 0 : Set G)) :=
  line_normalizer_decomposition (f.invariant 0) hXU
    (hX.1.trans inf_le_left |>.trans L.le_normalizer)
    D.sylow_normalizes_component hNT hn

/-- The supplement equality is literally the product in the source:
N_M(V1) normalizes C_G(V1), so the join equals their set product. -/
theorem chosen_line_product {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    {X : Subgroup G} (hX : IsCartan T L X)
    (hXU : X ≤ normalizer (f.Vi 0 : Set G))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hn : normalizer (f.Vi 0 : Set G) ≤
      normalizer ((centralizer (f.Vi 0 : Set G) ⊔ X ⊔ (T : Subgroup G) : Subgroup G) : Set G)) :
    ∀ g ∈ normalizer (f.Vi 0 : Set G),
      ∃ a ∈ centralizer (f.Vi 0 : Set G),
        ∃ b ∈ normalizer (L : Set G) ⊓ normalizer (f.Vi 0 : Set G), g = a * b := by
  intro g hg
  rw [chosen_line_decomposition D S f hX hXU hNT hn] at hg
  have hh := coe_mul_of_right_le_normalizer_left (centralizer (f.Vi 0 : Set G))
    (normalizer (L : Set G) ⊓ normalizer (f.Vi 0 : Set G))
    (inf_le_right.trans (normalizer_le_normalizer_centralizer _))
  have hg' : g ∈ (centralizer (f.Vi 0 : Set G) : Set G) *
      ((normalizer (L : Set G) ⊓ normalizer (f.Vi 0 : Set G) : Subgroup G) : Set G) := by
    rw [← hh]
    exact hg
  obtain ⟨a, ha, b, hb, hab⟩ := hg'
  exact ⟨a, ha, b, hb, hab.symm⟩

/-- The positive fixed-space Frattini step on the literal chosen radical.
K is to be instantiated with C_{C_G(V1)}(L1/O₂(L1)); its Sylow and
normality identifications belong to the line-action prerequisite. -/
theorem chosen_line_le_of_radical {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {F : BinaryField} {c : Coordinates D F}
    (f : InvariantFlag c) {K : Subgroup G}
    (hK : K ≤ centralizer (f.Vi 0 : Set G))
    (hKn : normalizer (f.Vi 0 : Set G) ≤ normalizer (K : Set G))
    (P : Sylow 2 K) (hP : (P : Subgroup K).map K.subtype = f.Ri 0)
    (hC : centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G))
    (hR : normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) :
    normalizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G) :=
  line_normalizer_le_of_radical hK hKn P hP hC hR

/-- The actual section-kernel application in 11.2.3(2). Only the preceding
component-normalizer and Sylow identifications remain to be established. -/
theorem chosen_line_le_of_section_sylow {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {F : BinaryField} {c : Coordinates D F}
    (f : InvariantFlag c)
    (hL₁ : normalizer (f.Vi 0 : Set G) ≤ normalizer (f.Li 0 : Set G))
    (P : Sylow 2 (lineSectionKernel (f.Vi 0) (f.Li 0)))
    (hP : (P : Subgroup (lineSectionKernel (f.Vi 0) (f.Li 0))).map
      (lineSectionKernel (f.Vi 0) (f.Li 0)).subtype = f.Ri 0)
    (hC : centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G))
    (hR : normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) :
    normalizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G) :=
  chosen_line_le_of_radical f inf_le_left (lineSectionKernel_normalized hL₁) P hP hC hR

/-- Both clauses of 11.2.3 from the pending line-action analysis and 11.1.5.
The exceptional radical branch is excluded by the nonzero original C_V(L),
using V ≤ T. The original hypotheses of both clauses are retained. -/
theorem chosen_source_11_2_3_of_action_steps {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    {X : Subgroup G} (hX : IsCartan T L X)
    (hXU : X ≤ normalizer (f.Vi 0 : Set G))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hzero : V ⊓ centralizer (L : Set G) = ⊥ →
      normalizer (f.Vi 0 : Set G) ≤
        normalizer ((centralizer (f.Vi 0 : Set G) ⊔ X ⊔ (T : Subgroup G) : Subgroup G) : Set G))
    (hpositive : V ⊓ centralizer (L : Set G) ≠ ⊥ →
      centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G) →
      normalizer (f.Vi 0 : Set G) ≤ normalizer (f.Li 0 : Set G) ∧
        ∃ P : Sylow 2 (lineSectionKernel (f.Vi 0) (f.Li 0)),
          (P : Subgroup (lineSectionKernel (f.Vi 0) (f.Li 0))).map
            (lineSectionKernel (f.Vi 0) (f.Li 0)).subtype = f.Ri 0)
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree) :
    (V ⊓ centralizer (L : Set G) = ⊥ →
      normalizer (f.Vi 0 : Set G) = centralizer (f.Vi 0 : Set G) ⊔
        (normalizer (L : Set G) ⊓ normalizer (f.Vi 0 : Set G))) ∧
    (centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G) →
      normalizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G)) := by
  have hs := fun h => chosen_line_decomposition D S f hX hXU hNT (hzero h)
  refine ⟨hs, ?_⟩
  intro hC
  by_cases hz : V ⊓ centralizer (L : Set G) = ⊥
  · rw [hs hz]
    exact sup_le hC inf_le_left
  obtain ⟨hL₁, P, hP⟩ := hpositive hz hC
  have hR : normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G) := by
    rcases hradical with hR | ⟨_, _, hT, _⟩
    · exact hR
    · exact (hz (le_bot_iff.mp ((inf_le_inf_right _ D.le_sylow).trans_eq hT))).elim
  exact chosen_line_le_of_section_sylow f hL₁ P hP hC hR

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
