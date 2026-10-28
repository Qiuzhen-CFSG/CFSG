module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallSpecialUnitaryAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallUnitaryApplication

/-!
# Small special-unitary scalar control on the original F.1.1 data

The reduced overlap has the original full Borel's two-core. Transporting
that literal core into the reduced starred data defines its action on the
original marked quotient Lᵢ/O₂(Lᵢ). On representatives it is the original
ambient conjugation; neither the actor nor the scalar center is replaced.
The full Borel core fixes the SU₃(2) center, and every semilinear formula
for its action has identity field parameter.

Semilinear coverage of these actors then gives the original enlarged
quotient marking, both original-core 6.5 obstructions, and the actual 6.6
center-product application. This coverage remains explicit and unproved
for arbitrary SU₃(2) actors. These conditional consumers do not establish
unrestricted 6.1 or close the PSU₃(2) branch. All remaining source assembly
obligations are retained.
Source: Aschbacher--Smith F.1.1 and F.1.9, pp.259--262; DGS, Groups and
Graphs (1985), reduction p.95, 6.1 pp.118--119 and 6.5--6.6 pp.121--123.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem reduced_borel_closed (h : HypothesisF11 L S) :
    ∃ T : Sylow 2 (commonBorel L (SuzukiContainment.reducedSylow L S)),
      (T : Subgroup (commonBorel L (SuzukiContainment.reducedSylow L S))) =
        pCore 2 (commonBorel L (SuzukiContainment.reducedSylow L S)) := by
  apply f11_borel_core_sylow (SuzukiContainment.reduced_hypothesis h)
  exact (normal_subgroupOf_iff_le_normalizer
    (show SuzukiContainment.reducedSylow L S ≤ commonBorel L (SuzukiContainment.reducedSylow L S)
      from le_sup_right)).mp (SuzukiContainment.reduced_sylow_normal h)

/-- The actual original full-Borel-core action on the original local quotient marking. -/
@[expose] def originalMarkedBorelCoreAction (h : HypothesisF11 L S) (i : Fin 2)
    {D : Type*} [Group D] (e : (L i ⧸ pCore 2 (L i)) ≃* D) :
    (commonBorel L S).pCoreIn 2 →* MulAut D :=
  (markedBorelCoreAction ((SuzukiContainment.reduced_hypothesis h).starredLocalRankOneData i)
    (((SuzukiContainment.reduced_hypothesis h).starredQuotientEquiv i).symm.trans e)).comp
      (MulEquiv.subgroupCongr (SuzukiContainment.reduced_borel_core h).symm).toMonoidHom

-- Keep the original/reduced subtype comparison out of the starred quotient calculation.
private theorem starred_marked_mk (h : HypothesisF11 L S) (i : Fin 2)
    {D : Type*} [Group D] (e : (L i ⧸ pCore 2 (L i)) ≃* D)
    (r : (commonBorel L S).pCoreIn 2) (hr : (r : G) ∈ S) (x : L i) :
    markedBorelCoreAction (h.starredLocalRankOneData i)
      ((h.starredQuotientEquiv i).symm.trans e) r (e (QuotientGroup.mk' (pCore 2 (L i)) x)) =
      e (QuotientGroup.mk' (pCore 2 (L i))
        ((L i).normalizerMonoidHom ⟨r,h.S_normalizes i hr⟩ x)) := by
  let d := h.starredLocalRankOneData i
  let eS : (d.Pstar ⧸ pCore 2 d.Pstar) ≃* D := (h.starredQuotientEquiv i).symm.trans e
  let j : L i →* d.Pstar := inclusion (local_le_starredParabolic i)
  have hj (y : L i) : eS (QuotientGroup.mk' (pCore 2 d.Pstar) (j y)) =
      e (QuotientGroup.mk' (pCore 2 (L i)) y) := by
    apply congrArg e
    apply (h.starredQuotientEquiv i).symm_apply_eq.mpr
    exact (h.starredQuotientEquiv_mk i y).symm
  let y := (L i).normalizerMonoidHom ⟨r,h.S_normalizes i hr⟩ x
  change markedBorelCoreAction d eS r (e (QuotientGroup.mk' (pCore 2 (L i)) x)) =
    e (QuotientGroup.mk' (pCore 2 (L i)) y)
  calc
    _ = markedBorelCoreAction d eS r (eS (QuotientGroup.mk' (pCore 2 d.Pstar) (j x))) :=
      congrArg (markedBorelCoreAction d eS r) (hj x).symm
    _ = eS (QuotientGroup.mk' (pCore 2 d.Pstar)
        (d.Pstar.normalizerMonoidHom ⟨r,
          (((pCoreIn_le 2 _).trans (le_sup_right.trans d.supplement.le)).trans
            ((normal_subgroupOf_iff_le_normalizer d.Pstar_le).mp d.normal)) r.property⟩ (j x))) :=
      markedBorelCoreAction_mk d eS r (j x)
    _ = eS (QuotientGroup.mk' (pCore 2 d.Pstar) (j y)) := rfl
    _ = _ := hj y

private theorem originalMarkedBorelCoreAction_apply (h : HypothesisF11 L S) (i : Fin 2)
    {D : Type*} [Group D] (e : (L i ⧸ pCore 2 (L i)) ≃* D)
    (r : (commonBorel L S).pCoreIn 2) :
    originalMarkedBorelCoreAction h i e r =
      markedBorelCoreAction ((SuzukiContainment.reduced_hypothesis h).starredLocalRankOneData i)
        (((SuzukiContainment.reduced_hypothesis h).starredQuotientEquiv i).symm.trans e)
        ((MulEquiv.subgroupCongr (SuzukiContainment.reduced_borel_core h).symm) r) := rfl

/-- Each original local representative is acted on by the original ambient conjugation. -/
theorem originalMarkedBorelCoreAction_mk (h : HypothesisF11 L S) (i : Fin 2)
    {D : Type*} [Group D] (e : (L i ⧸ pCore 2 (L i)) ≃* D)
    (r : (commonBorel L S).pCoreIn 2) (x : L i) :
    originalMarkedBorelCoreAction h i e r (e (QuotientGroup.mk' (pCore 2 (L i)) x)) =
      e (QuotientGroup.mk' (pCore 2 (L i))
        ((L i).normalizerMonoidHom ⟨r,
          (SuzukiContainment.reduced_hypothesis h).S_normalizes i r.property⟩ x)) := by
  let hh := SuzukiContainment.reduced_hypothesis h
  let eR : (commonBorel L S).pCoreIn 2 ≃*
      (commonBorel L (SuzukiContainment.reducedSylow L S)).pCoreIn 2 :=
    MulEquiv.subgroupCongr (SuzukiContainment.reduced_borel_core h).symm
  have hv : (eR r : G) = r := MulEquiv.subgroupCongr_apply _ r
  have hr : (eR r : G) ∈ SuzukiContainment.reducedSylow L S := by
    rw [hv]
    exact r.property
  have hm := starred_marked_mk hh i e (eR r) hr x
  apply (congrArg (fun a : MulAut D => a (e (QuotientGroup.mk' (pCore 2 (L i)) x)))
    (originalMarkedBorelCoreAction_apply h i e r)).trans
  apply hm.trans
  apply congrArg e
  apply congrArg (QuotientGroup.mk' (pCore 2 (L i)))
  apply Subtype.ext
  change (eR r : G) * (x : G) * (eR r : G)⁻¹ = (r : G) * (x : G) * (r : G)⁻¹
  rw [hv]

/-- The original full Borel core fixes the cubic scalar center, with no coverage premise. -/
theorem original_small_special_borel_core_fixes_center (h : HypothesisF11 L S) (i : Fin 2)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* J.specialSubgroup)
    (r : (commonBorel L S).pCoreIn 2) :
    ∀ z ∈ center J.specialSubgroup, originalMarkedBorelCoreAction h i e r z = z :=
  small_special_borel_core_fixes_center
    ((SuzukiContainment.reduced_hypothesis h).starredLocalRankOneData i)
    (reduced_borel_closed h) J hc hconj
    (((SuzukiContainment.reduced_hypothesis h).starredQuotientEquiv i).symm.trans e)
    ((MulEquiv.subgroupCongr (SuzukiContainment.reduced_borel_core h).symm) r)

/-- Any semilinear formula for an original full-Borel-core actor has identity field parameter. -/
theorem original_small_special_field_parameter (h : HypothesisF11 L S) (i : Fin 2)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* J.specialSubgroup)
    (r : (commonBorel L S).pCoreIn 2) (σ : F ≃+* F)
    (hs : J.HasSpecialUnitarySemilinearForm (originalMarkedBorelCoreAction h i e r) σ) : σ = 1 :=
  HermitianForm.SmallSpecialNormalizer.field_eq_one_of_center_fixed J hc hconj
    (originalMarkedBorelCoreAction h i e r) σ hs
    (original_small_special_borel_core_fixes_center h i J hc hconj e r)

/-- Semilinear coverage of the actual actors gives literal equality with the original starred endpoint. -/
theorem original_small_special_enlargement_of_semilinear (h : HypothesisF11 L S) (i : Fin 2)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* J.specialSubgroup)
    (hs : ∀ r : (commonBorel L S).pCoreIn 2, ∃ σ : F ≃+* F,
      J.HasSpecialUnitarySemilinearForm (originalMarkedBorelCoreAction h i e r) σ) :
    enlargedEndpoint L S i = starredParabolic L S i := by
  let hh := SuzukiContainment.reduced_hypothesis h
  let d := hh.starredLocalRankOneData i
  let eS : (d.Pstar ⧸ pCore 2 d.Pstar) ≃* J.specialSubgroup :=
    (hh.starredQuotientEquiv i).symm.trans e
  let eR : (commonBorel L S).pCoreIn 2 ≃*
      (commonBorel L (SuzukiContainment.reducedSylow L S)).pCoreIn 2 :=
    MulEquiv.subgroupCongr (SuzukiContainment.reduced_borel_core h).symm
  have hs' (r : (commonBorel L (SuzukiContainment.reducedSylow L S)).pCoreIn 2) :
      ∃ σ : F ≃+* F, J.HasSpecialUnitarySemilinearForm (markedBorelCoreAction d eS r) σ := by
    obtain ⟨σ,hσ⟩ := hs (eR.symm r)
    refine ⟨σ,?_⟩
    change J.HasSpecialUnitarySemilinearForm (markedBorelCoreAction d eS (eR (eR.symm r))) σ at hσ
    rwa [eR.apply_symm_apply] at hσ
  have he := localEnlargement_eq_star_of_small_special_semilinear d
    (reduced_borel_closed h) J hc hconj eS hs'
  change localEnlargement (hh.starredLocalRankOneData i) = (hh.starredLocalRankOneData i).Pstar at he
  rw [reduced_localEnlargement_eq h i,HypothesisF11.starredLocalRankOneData_Pstar,
    SuzukiContainment.reduced_starredParabolic h i] at he
  exact he

/-- The original quotient marking supplies the enlarged SU₃(2) marking after the proved equality. -/
theorem original_small_special_enlarged_marking_of_semilinear (h : HypothesisF11 L S) (i : Fin 2)
    {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* J.specialSubgroup)
    (hs : ∀ r : (commonBorel L S).pCoreIn 2, ∃ σ : F ≃+* F,
      J.HasSpecialUnitarySemilinearForm (originalMarkedBorelCoreAction h i e r) σ) :
    IsSU (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) 3 2 := by
  have he := original_small_special_enlargement_of_semilinear h i J hc hconj e hs
  let a := MulEquiv.subgroupCongr he
  let b := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  exact ⟨F,inferInstance,inferInstance,J,hc,hconj,
    ⟨b.trans ((h.starredQuotientEquiv i).symm.trans e)⟩⟩

/-- Both original 6.5 conclusions, retaining only small-special semilinear coverage as an extra premise. -/
theorem original_small_special_obstruction_of_semilinear (h : HypothesisF11 L S) (i : Fin 2)
    {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2)
    (e : (L (other i) ⧸ pCore 2 (L (other i))) ≃* J.specialSubgroup)
    (hs : ∀ r : (commonBorel L S).pCoreIn 2, ∃ σ : F ≃+* F,
      J.HasSpecialUnitarySemilinearForm (originalMarkedBorelCoreAction h (other i) e r) σ) :
    (¬ enlargedEndpoint L S (other i) ≤ normalizer
      (↑((parabolic L S i).pCoreIn 2 ⊓ (parabolic L S (other i)).pCoreIn 2) : Set G)) ∧
    (¬ parabolic L S (other i) ≤ normalizer
      (↑((parabolic L S i).pCoreIn 2 ⊓ (parabolic L S (other i)).pCoreIn 2) : Set G)) ∧
    ¬ ∃ T : Sylow 2 (conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i))),
      (T : Subgroup (conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i)))).map
        (conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i))).subtype =
          (parabolic L S i).pCoreIn 2 :=
  original_small_unitary_enlargement_obstruction h i (Or.inr
    (original_small_special_enlarged_marking_of_semilinear h (other i) J hc hconj e hs))

open Subgroup.CosetGeometry.RankTwo in
/-- The same actual enlarged marking discharges the degree-one 6.6 consumer. -/
theorem reduced_small_special_center_product_of_semilinear (h : HypothesisF11 L S) (j : Bool)
    {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2)
    (e : (L (other (if j then 1 else 0)) ⧸ pCore 2 (L (other (if j then 1 else 0)))) ≃*
      J.specialSubgroup)
    (hs : ∀ r : (commonBorel L S).pCoreIn 2, ∃ σ : F ≃+* F,
      J.HasSpecialUnitarySemilinearForm
        (originalMarkedBorelCoreAction h (other (if j then 1 else 0)) e r) σ)
    (hn : stabilizer (reducedFamily L S) (base (reducedFamily L S) (!j)) ≤ normalizer
      (↑(Z (reducedFamily L S) (base (reducedFamily L S) j) ⊔
        Z (reducedFamily L S) (base (reducedFamily L S) (!j))) : Set (G₀ L S))) :
    (∀ T : Sylow 2 (stabilizer (reducedFamily L S) (base (reducedFamily L S) j)),
      Z (reducedFamily L S) (base (reducedFamily L S) j) = omegaCenterIn
        ((T : Subgroup (stabilizer (reducedFamily L S) (base (reducedFamily L S) j))).map
          (stabilizer (reducedFamily L S) (base (reducedFamily L S) j)).subtype)) ∧
      Z (reducedFamily L S) (base (reducedFamily L S) j) ≤
        Z (reducedFamily L S) (base (reducedFamily L S) (!j)) :=
  reduced_small_unitary_enlargement_center_product h j (Or.inr
    (original_small_special_enlarged_marking_of_semilinear h (other (if j then 1 else 0))
      J hc hconj e hs)) hn
end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
