module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special.Elementary
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special.Model
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special.Order

/-!
# The center of the original SL₃ closure

The full marked point radical fixes exactly V₁ in V. A central element
of U fixes V and therefore belongs to S=V C_U(L). This identifies the
actual ambient center with V₁ C_U(L), preserving both central factors.
Source: Aschbacher--Smith 11.5.7, refs/quasithin.pdf, printed p.782.
-/

@[expose] public noncomputable section
open Subgroup Matrix
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterG.Section02.LinearThree
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D) {x y : G}
  (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)

include d

omit d in
theorem center_eq_inf : closureCenter E = E.W ⊓ centralizer (E.W : Set G) := by
  ext u
  constructor
  · rintro ⟨z,hz,rfl⟩
    refine ⟨z.property, ?_⟩
    intro w hw
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨w,hw⟩)
  · intro hu
    refine ⟨⟨u,hu.1⟩, ?_, rfl⟩
    exact mem_center_iff.mpr (fun w => Subtype.ext (hu.2 w w.property))

set_option backward.isDefEq.respectTransparency false in
theorem chosen_closure_fixed
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁) :
    V ⊓ centralizer (E.W : Set G) = E.V₁ := by
  apply le_antisymm
  · intro v hv
    have hvV : v ∈ V := hv.1
    have hvC : v ∈ centralizer (E.W : Set G) := hv.2
    let vv : (setup E).V := ⟨v,hvV⟩
    apply (d.point_mem vv).mpr
    apply (radical_fixed d.point d.point_dimension _).mp
    intro a ha
    obtain ⟨u, hu, rfl⟩ := (d.pointRadicalImage_eq_radical hUT hf
      (d.star_U_le_star_L hUT hf)).ge ha
    change (d.model u).val *ᵥ (d.coordinates vv).toAdd = _
    obtain ⟨w, hw, he⟩ := hu
    have he' : (u : (setup E).Star) = QuotientGroup.mk' (pCore 2 (setup E).LT) w := he.symm
    have hact := d.naturalAction_apply w vv
    have hsame : (⟨(w : G) * vv * (w : G)⁻¹,
        (mem_normalizer_iff.mp (d.LT_normalizes_V w.property) vv).mp vv.property⟩ :
        (setup E).V) = vv := by
      apply Subtype.ext
      change (w : G) * v * (w : G)⁻¹ = v
      rw [hvC w hw, mul_inv_cancel_right]
    rw [hsame] at hact
    calc
      _ = (d.starAction (u : (setup E).Star) (d.coordinates vv)).toAdd :=
        (d.starAction_on_L u (d.coordinates vv).toAdd).symm
      _ = (d.naturalAction w (d.coordinates vv)).toAdd := by rw [he', d.starAction_mk]
      _ = (d.coordinates vv).toAdd := congrArg Multiplicative.toAdd hact
  · intro v hv
    exact ⟨E.V₁_le hv, ((center_eq_inf E).le (point_le_center E d hv)).2⟩

theorem closureCenter_eq
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y) :
    closureCenter E = E.V₁ ⊔ (E.W ⊓ centralizer (L : Set G)) := by
  let C := E.W ⊓ centralizer (L : Set G)
  have hCZ : C ≤ closureCenter E := by
    rw [center_eq_inf]
    exact le_inf inf_le_left (closure_centralizer_central E d hUT hf hc)
  apply le_antisymm
  · intro z hz
    have hz' := (center_eq_inf E).le hz
    have hzS : z ∈ threeCore E x y := by
      apply (threeGroup_chosen_centralizer E d hUT hf).le
      exact ⟨(threeGroup_eq_join d hUT hf).ge (mem_sup_right hz'.1),
        centralizer_le (le_conjugateSpanBy V E.G₁) hz'.2⟩
    have hS : threeCore E x y = V ⊔ C := by
      rw [threeCore_split E d hUT hf hc, threeCore_centralizer E d hUT hf hc]
    have hzprod : z ∈ (V : Set G) * (C : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left V C
        ((inf_le_right.trans (centralizer_le D.le_component)).trans (centralizer_le_normalizer _)),
        ← hS]
      exact hzS
    obtain ⟨v,hv,c,hcC,he⟩ := hzprod
    have hvfix : v ∈ centralizer (E.W : Set G) := by
      have hh := (centralizer (E.W : Set G)).mul_mem hz'.2
        ((centralizer (E.W : Set G)).inv_mem ((center_eq_inf E).le (hCZ hcC)).2)
      simpa only [← he, mul_inv_cancel_right] using hh
    rw [← he]
    exact mul_mem_sup ((chosen_closure_fixed E d hUT hf).le ⟨hv,hvfix⟩) hcC
  · exact sup_le (point_le_center E d) hCZ

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special
