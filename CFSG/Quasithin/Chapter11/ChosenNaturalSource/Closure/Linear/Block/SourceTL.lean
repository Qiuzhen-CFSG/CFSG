module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Splitting
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Setup

/-!
# The source T_L splitting

Once the size comparison gives O₂(L)=V, the two-core Q=O₂(LT) has
[Q,L]≤V and centralizes V. The natural H¹ splitting therefore gives
Q=V C_Q(L). The preceding exact equality C_T(V)=Q puts C_T(L) in Q,
and intersecting LQ with T gives T_L=(T∩L)C_T(L).

The only new input is O₂(L)=V, retained explicitly for the later
multiplicity and order comparison. The earlier Sylow-centralizer
conclusion is discharged by the original chosen-module theorem.

Source: Aschbacher--Smith, 11.5.7, printed p.782, equation (*).
-/

@[expose] public noncomputable section
open Subgroup Matrix
open scoped Pointwise commutatorElement
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterG.Section02.LinearThree
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D) {x y : G}
  (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)
include d

/-- The source (*) splitting, once the preceding size comparison has killed
 the central part of O₂(L). -/
theorem sourceTL_split_of_core_centralizer (hcore : L.pCoreIn 2 = V)
    (hCT : (T : Subgroup G) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    LocalGeometry.sourceTL T L = ((T : Subgroup G) ⊓ L) ⊔
      ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hnorm : L ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    sup_le L.le_normalizer D.sylow_normalizes_component
  have hQC : Q ≤ centralizer (V : Set G) := D.core_centralizes
  have hQnormal : L ⊔ (T : Subgroup G) ≤ normalizer (Q : Set G) :=
    (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hcomm : ⁅Q,L⁆ ≤ V := by
    rw [←hcore]
    apply le_trans _ (inf_pCoreIn_le_of_le 2 (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left))
    exact le_inf
      (le_normalizer_iff_commutator_le_right.mp ((pCoreIn_le 2 _).trans hnorm))
      (le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans hQnormal))
  have hVQ : V ≤ Q := by
    rw [←hcore]
    exact pCoreIn_mono_of_normalizes le_sup_left hnorm
  have hsplit : Q = V ⊔ (Q ⊓ centralizer (L : Set G)) :=
    split_of_commutator E d Q hVQ hcomm (by rw [hcore]; exact hQC)
  have hQT : Q ≤ (T : Subgroup G) := by
    obtain ⟨P,hP⟩ := d.setup.sylow_LT
    exact (pCoreIn_le_sylow _ P).trans_eq hP
  have hCQ : (T : Subgroup G) ⊓ centralizer (L : Set G) ≤ Q := by
    change _ ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2
    rw [← hCT]
    exact inf_le_inf_left _ (centralizer_le D.le_component)
  have hC : Q ⊓ centralizer (L : Set G) =
      (T : Subgroup G) ⊓ centralizer (L : Set G) :=
    le_antisymm (inf_le_inf_right _ hQT) (le_inf hCQ inf_le_right)
  have hJ : L ⊔ Q = L ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
    rw [hsplit,hC,←sup_assoc,sup_eq_left.mpr D.le_component]
  change (T : Subgroup G) ⊓ (L ⊔ Q) = _
  rw [hJ]
  let C := (T : Subgroup G) ⊓ centralizer (L : Set G)
  apply le_antisymm
  · intro t ht
    have hp : t ∈ (C : Set G) * (L : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right C L
        (inf_le_right.trans (Subgroup.centralizer_le_normalizer _)),sup_comm]
      exact ht.2
    obtain ⟨c,hc,l,hl,he⟩ := hp
    have hlT : l ∈ (T : Subgroup G) := by
      have hh := (T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem hc.1) ht.1
      simpa only [←he,inv_mul_cancel_left] using hh
    rw [←he]
    exact (((T : Subgroup G) ⊓ L) ⊔ C).mul_mem
      (mem_sup_right hc) (mem_sup_left ⟨hlT,hl⟩)
  · exact sup_le (le_inf inf_le_left (inf_le_right.trans le_sup_left))
      (le_inf inf_le_left le_sup_right)

/-- The exact source splitting, with the preceding Sylow centralizer discharged. -/
theorem sourceTL_split (hcore : L.pCoreIn 2 = V) :
    LocalGeometry.sourceTL T L = ((T : Subgroup G) ⊓ L) ⊔
      ((T : Subgroup G) ⊓ centralizer (L : Set G)) :=
  sourceTL_split_of_core_centralizer E d hcore
    (LocalGeometry.WeakClosure.seed_sylow_centralizer D E.input)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block
