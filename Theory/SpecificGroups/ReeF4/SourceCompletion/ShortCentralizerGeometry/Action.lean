module
public import Theory.SpecificGroups.ReeF4.SourceCompletion.ShortCentralizerGeometry.Radical
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Linear.FullLeviRepresentation
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Mathlib.GroupTheory.Nilpotent
-- Internal proof split: compare the literal conjugation actions without changing
-- the public definition bodies in the established plane and Levi modules.
import all Theory.SpecificGroups.ReeF4.SourceCompletion.ShortCentralizerGeometry.Plane
import all Theory.SpecificGroups.ReeF4.ConverseParabolics.Linear.LeviRetraction

/-!
# The actual action of every placed short centralizer

The faithful fixed PSL₂ action makes the kernel on the full Levi embed in
its complementary torus. The radical centralizes the plane, so the full
parabolic action has solvable kernel. Restricting to any short centralizer
contained in this parabolic preserves solvability of the kernel. Its actual
PSL₂ subgroup therefore acts faithfully on this same plane, by simplicity.
This includes the marker chosen extremally inside a full endpoint; no
conjugacy assumption inside the native parabolic is needed.

Source: Aschbacher--Smith F.4.42, printed p.295 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup
namespace ReeF4.SourceCompletion.ShortCentralizerGeometry
open Parabolics LargeLocalSeeds ElementaryTwoBound
open LocalBlockInput.PairRigidity FixedCollection.SeedGeneration
open ConverseParabolics.FullLeviRepresentation
open SectionGeometry.LinearRadical (fullLevi)

/-- Conjugation by the full Levi on the literal plane. -/
def fullLeviPlaneAction (m : ℕ) (hm : 0 < m) :
    fullLevi m →* MulAut (Replacement.V m) :=
  (Replacement.V m).normalizerMonoidHom.comp
    ((fullLevi m).subtype.codRestrict _ (fun x =>
      parabolic_normalizes_plane m hm (SectionGeometry.LinearRadical.fullLevi_le_parabolic m x.property)))

private theorem fullLeviProductEquiv_symm_coe (m : ℕ) (hm : 0 < m)
    (x : fixedLevi (canonicalLocalBlockInput m) .linear × (CoefficientField m)ˣ) :
    ((fullLeviProductEquiv hm).symm x : Model m) =
      seedLeviHom m x.1 * complementHom m x.2 := rfl

private theorem fullLeviPlaneAction_product (m : ℕ) (hm : 0 < m)
    (x : fixedLevi (canonicalLocalBlockInput m) .linear) :
    fullLeviPlaneAction m hm ((fullLeviProductEquiv hm).symm (x,1)) =
      leviPlaneAction m hm x := by
  apply MulEquiv.ext
  intro v
  apply Subtype.ext
  change (((fullLeviProductEquiv hm).symm (x,1) : fullLevi m) : Model m) *
      v.val * (((fullLeviProductEquiv hm).symm (x,1) : fullLevi m) : Model m)⁻¹ =
    seedLeviHom m x * v.val * (seedLeviHom m x)⁻¹
  rw [fullLeviProductEquiv_symm_coe, map_one, mul_one]

/-- The kernel of the full Levi action embeds in the complementary torus. -/
theorem fullLeviPlaneAction_ker_solvable (m : ℕ) (hm : 0 < m) :
    Group.IsSolvable (fullLeviPlaneAction m hm).ker := by
  let e := fullLeviProductEquiv hm
  let k := (fullLeviPlaneAction m hm).ker
  let f : k →* (CoefficientField m)ˣ :=
    (MonoidHom.snd _ _).comp (e.toMonoidHom.comp k.subtype)
  apply Group.isSolvable_of_isSolvable_injective (f := f)
  apply (injective_iff_map_eq_one f).mpr
  intro x hx
  have hx2 : (e x.val).2 = 1 := hx
  have he : x.val = e.symm ((e x.val).1,1) := by
    rw [← hx2]
    exact (e.symm_apply_apply x.val).symm
  have ha : leviPlaneAction m hm (e x.val).1 = 1 := by
    rw [← fullLeviPlaneAction_product m hm, ← he]
    exact x.property
  have hx1 : (e x.val).1 = 1 :=
    leviPlaneAction_injective m hm (ha.trans (map_one _).symm)
  apply Subtype.ext
  apply e.injective
  exact Prod.ext hx1 hx2 |>.trans e.map_one.symm

open MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry (parabolic_eq_rootParabolic)
open Theory.GroupTheory

/-- The full parabolic acts on the plane, including its complementary torus. -/
def parabolicPlaneAction (m : ℕ) (hm : 0 < m) :
    ConverseParabolics.parabolic m .linear →*
      MulAut (Replacement.V m) :=
  (Replacement.V m).normalizerMonoidHom.comp
    ((ConverseParabolics.parabolic m .linear).subtype.codRestrict _
      (fun x => parabolic_normalizes_plane m hm
        (by
          change x.val ∈ Parabolics.parabolic m .linear
          simpa only [parabolic_eq_rootParabolic] using x.property)))

private theorem parabolicPlaneAction_radical (m : ℕ) (hm : 0 < m)
    (r : ConverseParabolics.parabolic m .linear)
    (hr : r.val ∈ Parabolics.radical m .linear) :
    parabolicPlaneAction m hm r = 1 := by
  apply MulEquiv.ext
  intro v
  apply Subtype.ext
  change r.val * v.val * r.val⁻¹ = v.val
  rw [← (radical_centralizes_plane m hr v.val v.property)]
  group

/-- Factoring by the radical leaves exactly the full Levi plane action. -/
theorem parabolicPlaneAction_eq (m : ℕ) (hm : 0 < m) :
    parabolicPlaneAction m hm =
      (fullLeviPlaneAction m hm).comp (ConverseParabolics.linearLeviRetraction m) := by
  apply MonoidHom.ext
  intro x
  obtain ⟨r,hr,l,hl,he⟩ := SectionGeometry.LinearRadical.exists_radical_fullLevi_factors m x.val
    (by simpa only [parabolic_eq_rootParabolic] using x.property)
  let rP : ConverseParabolics.parabolic m .linear :=
    ⟨r, ConverseParabolics.radical_le_parabolic m .linear
      (by rwa [ConverseParabolics.radical_eq_rootRadical])⟩
  let lL : fullLevi m := ⟨l,hl⟩
  have hx : rP * ConverseParabolics.linearFullLeviInclusion m lL = x := Subtype.ext he
  have hrk : ConverseParabolics.linearLeviRetraction m rP = 1 := by
    apply (ConverseParabolics.linearLeviRetraction m).mem_ker.mp
    rw [ConverseParabolics.linearLeviRetraction_ker]
    change r ∈ ConverseParabolics.radical m .linear
    rwa [ConverseParabolics.radical_eq_rootRadical]
  rw [←hx, map_mul, parabolicPlaneAction_radical m hm rP hr, one_mul,
    MonoidHom.comp_apply, map_mul, hrk, one_mul,
    ConverseParabolics.linearLeviRetraction_inclusion]
  rfl

/-- The full parabolic action has solvable kernel. -/
theorem parabolicPlaneAction_ker_solvable (m : ℕ) (hm : 0 < m) :
    Group.IsSolvable (parabolicPlaneAction m hm).ker := by
  rw [parabolicPlaneAction_eq]
  let := fullLeviPlaneAction_ker_solvable m hm
  let := (ConverseParabolics.linearLeviRetraction_ker_isPGroup m).isNilpotent
  let : Group.IsSolvable (ConverseParabolics.linearLeviRetraction m).ker := inferInstance
  exact isSolvable_comap_of_solvable_ker (ConverseParabolics.linearLeviRetraction m)
    (fullLeviPlaneAction m hm).ker

/-- The literal conjugation action of a placed native short centralizer. -/
def shortPlaneAction {m : ℕ} (hm : 0 < m) {t : Model m}
    (hC : centralizer ({t} : Set (Model m)) ≤ parabolic m .linear) :
    centralizer ({t} : Set (Model m)) →* MulAut (Replacement.V m) :=
  (parabolicPlaneAction m hm).comp (inclusion
    (show centralizer ({t} : Set (Model m)) ≤ ConverseParabolics.parabolic m .linear
      from hC.trans_eq (parabolic_eq_rootParabolic m .linear).symm))

theorem shortPlaneAction_apply {m : ℕ} (hm : 0 < m) {t : Model m}
    (hC : centralizer ({t} : Set (Model m)) ≤ parabolic m .linear)
    (x : centralizer ({t} : Set (Model m))) (v : Replacement.V m) :
    (shortPlaneAction hm hC x v : Model m) = x.val * v.val * x.val⁻¹ := by rfl

/-- The native short-centralizer action on the plane has solvable kernel. -/
theorem shortPlaneAction_ker_solvable {m : ℕ} (hm : 0 < m) {t : Model m}
    (hC : centralizer ({t} : Set (Model m)) ≤ parabolic m .linear) :
    Group.IsSolvable (shortPlaneAction hm hC).ker := by
  let := parabolicPlaneAction_ker_solvable m hm
  let hCP := hC.trans_eq (parabolic_eq_rootParabolic m .linear).symm
  let f := inclusion hCP
  let j : (shortPlaneAction hm hC).ker →* (parabolicPlaneAction m hm).ker :=
    (f.comp (shortPlaneAction hm hC).ker.subtype).codRestrict _ (fun x => x.property)
  apply Group.isSolvable_of_isSolvable_injective (f := j)
  intro x y hxy
  apply Subtype.ext
  exact (inclusion_injective hCP) (congrArg Subtype.val hxy)

/-- Every placed short marker has an actual PSL₂ subgroup acting faithfully
on the same long-root plane, even after the extremal rechoice. -/
theorem short_plane_faithful_psl {m : ℕ} (hm : 0 < m) {t : Model m}
    (ht : EvenInvolutionGeometry.IsShortRootInvolution t)
    (hC : centralizer ({t} : Set (Model m)) ≤ parabolic m .linear) :
    ∃ f : LinearQuotient m →* centralizer ({t} : Set (Model m)),
      Function.Injective f ∧ Function.Injective ((shortPlaneAction hm hC).comp f) := by
  obtain ⟨f,hf⟩ := short_centralizer_embedding hm ht
  let a := (shortPlaneAction hm hC).comp f
  let := linearQuotient_simple m hm
  let := linearQuotient_perfect m hm
  refine ⟨f,hf,(MonoidHom.ker_eq_bot_iff a).mp ?_⟩
  rcases a.normal_ker.eq_bot_or_eq_top with hk | hk
  · exact hk
  · have ha : a = 1 := MonoidHom.ker_eq_top_iff.mp hk
    let j : LinearQuotient m →* (shortPlaneAction hm hC).ker :=
      f.codRestrict _ (fun x => by
        change a x = 1
        rw [ha]
        rfl)
    let := shortPlaneAction_ker_solvable hm hC
    exact (Group.IsPerfect.not_isSolvable (LinearQuotient m)
      (Group.isSolvable_of_isSolvable_injective (f := j)
        ((MonoidHom.injective_codRestrict _ _ _).mpr hf))).elim

/-- The induced native short-centralizer action is nonsolvable. -/
theorem shortPlaneAction_range_not_solvable {m : ℕ} (hm : 0 < m) {t : Model m}
    (ht : EvenInvolutionGeometry.IsShortRootInvolution t)
    (hC : centralizer ({t} : Set (Model m)) ≤ parabolic m .linear) :
    ¬ Group.IsSolvable (shortPlaneAction hm hC).range := by
  obtain ⟨f,_,hf⟩ := short_plane_faithful_psl hm ht hC
  intro hs
  let := hs
  let := linearQuotient_simple m hm
  let := linearQuotient_perfect m hm
  let j := (shortPlaneAction hm hC).rangeRestrict.comp f
  have hj : Function.Injective j := by
    intro x y he
    exact hf (congrArg Subtype.val he)
  exact Group.IsPerfect.not_isSolvable (LinearQuotient m)
    (Group.isSolvable_of_isSolvable_injective hj)

end ReeF4.SourceCompletion.ShortCentralizerGeometry
