module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.PrimeSelection.Model
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.Equal
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Prime
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Witness.OddExtension
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.OddIndex.Sylow
public import Theory.SpecificGroups.SL2.CardFourEquiv

/-!
# Generation one for an original source-selected outside subgroup

In the prime PSL₂ row the original R₁ is O₂(KT). The full quotient map
therefore carries L₁ to the A₅ supplied by its field-four marking.
The solvable involution-centralizer construction in Model lifts to an
actual subgroup of KT containing T. It escapes M, since M ∩ G₁
normalizes L₁. H-star selection inside this solvable subgroup gives
n(H)=1 and O²(H) ≤ K on the original carriers.

Combining this choice with the completed equality and odd-extension
choices supplies a selected H of generation one in every surviving row.
This is an existential selection theorem. The source claim n(H)=1 for
every outside H still requires exclusion of the previously isolated A₅
residual; no uniqueness of abstract A₅ overgroups is used here.

Earlier geometry, full 11.3.2, the surviving list and Kz=K retain
qt-d-1222-natural-local-geometry, qt-d-1222-shadow-linear-geometry,
qt-d-1222-shadow-component-triangle and qt-d-1222-shadow-component-comparison.
OddKernelNormalizer remains with qt-d-1222-natural-odd-kernel-normalizer.
Their final discharge belongs to qt-d-1222-shadow-components.
Source: Aschbacher--Smith 11.4.3--11.5.1 and E.1.13,
printed pp.778--779 and214 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.PrimeSelection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)

/-- In the original prime row, an involution centralizer above R₁ supplies
an actual solvable outside H-star, with the literal O² residual alternative. -/
theorem ofFlag_prime_selected_solvable
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hfour : S.field.degree = 2)
    {p : ℕ} (hp : p.Prime) (hbig : 11 ≤ p)
    (hm : ClassicalGroup.IsPSL ((ofFlag S f X z H).K ⧸
      pCore 2 (ofFlag S f X z H).K) 2 p)
    (hR : (ofFlag S f X z H).R₁ ≤
      (solvableRadical ((ofFlag S f X z H).K ⊔ (T : Subgroup G) : Subgroup G)).map
        ((ofFlag S f X z H).K ⊔ (T : Subgroup G)).subtype) :
    ∃ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      J ≤ Gz (ofFlag S f X z J) ∧ SelectedResidualAlternative (ofFlag S f X z J) ∧
      Group.IsSolvable J ∧ ChapterE.generationParameter J = 1 := by
  let E := ofFlag S f X z H
  let C := E.K ⊔ (T : Subgroup G)
  let K := E.K.subgroupOf C
  let A := (f.Li 0).subgroupOf C
  have hAK : f.Li 0 ≤ E.K := le_conjugateSpanBy _ _
  have hAC : f.Li 0 ≤ C := hAK.trans le_sup_left
  have hTK := (f.invariant 0).trans E.G₁_normalizes_K
  let : K.Normal := normal_subgroupOf_of_le_normalizer (sup_le E.K.le_normalizer hTK)
  let eK : K ≃* E.K := subgroupOfEquivOfLe (show E.K ≤ C from le_sup_left)
  let : Group.IsPerfect E.K := Radical.relative_component_perfect h.line_component
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := eK.symm.toMonoidHom) eK.symm.surjective
  let erK := QuotientGroup.congr (pCore 2 K) (pCore 2 E.K) eK (pCore_map_iso 2 eK)
  have hKm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p := hm.of_mulEquiv erK
  have hgen : K ⊔ (T.subtype (show (T : Subgroup G) ≤ C from le_sup_right) : Subgroup C) = ⊤ := by
    change E.K.subgroupOf C ⊔ (T : Subgroup G).subgroupOf C = ⊤
    rw [←subgroupOf_sup (show E.K ≤ C from le_sup_left) (show (T : Subgroup G) ≤ C from le_sup_right),subgroupOf_self]
  have hseed : Nonempty ((f.Li 0 ⧸ pCore 2 (f.Li 0)) ≃*
      Theory.PSL2.Group S.field.Carrier) := by
    obtain ⟨f₀,hu,_,hq,_⟩ := LocalGeometry.exists_unique_marked_flag D S c
    have hh : f.Li 0 = f₀.Li 0 := congrArg
      (fun U => LocalGeometry.localResidual L (c.preimage U))
      (hu 0 _ (f.dimension 0) (f.invariant 0))
    exact hh.symm ▸ hq 0
  obtain ⟨e5⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (S.field.card_eq.trans (by rw [hfour]; rfl))
  let eA : A ≃* f.Li 0 := subgroupOfEquivOfLe hAC
  let erA := QuotientGroup.congr (pCore 2 A) (pCore 2 (f.Li 0)) eA (pCore_map_iso 2 eA)
  let eA5 : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5) := erA.trans (hseed.some.trans e5)
  have hcore : E.R₁ = C.pCoreIn 2 := prime_radical_eq_core E h (f.invariant 0) hR (by omega) hm
  have hAcoreG : (f.Li 0).pCoreIn 2 ≤ C.pCoreIn 2 := by
    rw [←hcore]
    exact pCoreIn_mono_of_normalizes (show f.Li 0 ≤ f.Li 0 ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le (f.Li 0).le_normalizer (f.sylow_normalizes_Li 0))
  have hAcore : A.pCoreIn 2 ≤ pCore 2 C := by
    apply (map_le_map_iff_of_injective (f := C.subtype) C.subtype_injective).mp
    rw [map_pCoreIn_of_injective 2 A C.subtype C.subtype_injective,
      map_subgroupOf_eq_of_le hAC]
    exact hAcoreG
  have hSA : (T.subtype (show (T : Subgroup G) ≤ C from le_sup_right) : Subgroup C) ≤
      normalizer (A : Set C) := by
    rw [←subgroupOf_normalizer_eq hAC]
    intro t ht
    exact f.sylow_normalizes_Li 0 ht
  obtain ⟨B,hTB,hBs,hBN⟩ := solvable_escape_above_twoCore K hp (by omega) hKm
    (T.subtype (show (T : Subgroup G) ≤ C from le_sup_right)) hgen A eA5 hAcore hSA
  let B₀ := B.map C.subtype
  have hT₀ : (T : Subgroup G) ≤ B₀ := by
    have hh := map_mono (f := C.subtype) hTB
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ C from le_sup_right)] at hh
  have hC₁ : C ≤ E.G₁ := sup_le E.K_le_G₁ (f.invariant 0)
  have hB₀ : B₀ ≤ C := map_subtype_le _
  have hout : ¬ B₀ ≤ normalizer (L : Set G) := by
    intro hh
    apply hBN
    have hn : B₀ ≤ normalizer (f.Li 0 : Set G) :=
      (le_inf hh (hB₀.trans hC₁)).trans
        Comparison.EarlierGeometry.line_stabilizer_normalizes_seed
    rw [←subgroupOf_normalizer_eq hAC]
    intro b hb
    exact hn (mem_map_of_mem C.subtype hb)
  have hCz : C ≤ Gz E := sup_le (he ▸ h.point_component.1) h.sylow_le_pointCentralizer
  obtain ⟨J,hJ,hJB⟩ := exists_HStar_below_point E h B₀ hT₀ (hB₀.trans hCz) hout
  have hJC : J ≤ C := hJB.trans hB₀
  have hJz : J ≤ Gz E := hJC.trans hCz
  have hres : (pResidual 2 J).map J.subtype ≤ E.K := residual_le_factor E.K J hTK hJC
  let := hBs
  let : Group.IsSolvable B₀ := Group.isSolvable_of_surjective (C.subtype.subgroupMap_surjective B)
  let : Group.IsSolvable J := Group.isSolvable_of_isSolvable_injective (inclusion_injective hJB)
  have h' : Comparison.EarlierGeometry (ofFlag S f X z J) :=
    ⟨h.point_mem,h.point_fixed,h.point_ne_one,h.seed_centralizes,
      h.line_component,h.point_component,h.normalizer_split⟩
  exact ⟨J,hJ,hJz,Or.inr hres,inferInstance,
    Nat.le_antisymm ChapterE.generationParameter_le_one_of_solvable
      (selected_generation_spec (ofFlag S f X z J) h' hJ hJz).1⟩


/-- Source-selected generation one for every surviving row. The equality
row uses the Hall argument, the odd-extension row its solvable Fitting
preimage, and the prime row the actual solvable involution centralizer.
This existential conclusion does not assert the universal 11.4.4 bound. -/
theorem ofFlag_surviving_selected_generation_one
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) (ofFlag S f X z H).K 1 S.field.degree)
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V)) :
    ∃ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      J ≤ Gz (ofFlag S f X z J) ∧ SelectedResidualAlternative (ofFlag S f X z J) ∧
      ChapterE.generationParameter J = 1 := by
  let E := ofFlag S f X z H
  have hKc : Source.NormalComponentIn (centralizer (f.Vi 0 : Set G)) E.K :=
    ⟨⟨h.line_component_centralizes,h.line_component.2.subgroupOf_of_le
      h.line_component_centralizes (Subgroup.centralizer_le_normalizer _)⟩,
      normal_subgroupOf_of_le_normalizer
        ((Subgroup.centralizer_le_normalizer _).trans E.G₁_normalizes_K)⟩
  have hR := (Chapter1.isSylowIn_iff.mp (Radical.ofFlag_surviving_sylow_radical S f X z H
    E.K hKc (le_conjugateSpanBy _ _) ((f.invariant 0).trans E.G₁_normalizes_K) hcase)).2.1
  cases hcase with
  | equal hEq =>
    obtain ⟨J,hJ,hJz,hsel,hn,_⟩ :=
      ofFlag_equal_selected_generation_one S f X z H h he hEq.symm hNT hlinear h1132 hcontrol
    exact ⟨J,hJ,hJz,hsel,hn⟩
  | sl2Prime _ hn p hp hm =>
    obtain ⟨J,hJ,hJz,hsel,hgen,_⟩ :=
      ofFlag_odd_selected_radical_witness S f X z H h he hn hp hm
    exact ⟨J,hJ,hJz,hsel,hgen⟩
  | psl2Prime _ hn p hp hbig hm _ =>
    obtain ⟨J,hJ,hJz,hsel,_,hgen⟩ := ofFlag_prime_selected_solvable S f X z H h he hn hp hbig hm hR
    exact ⟨J,hJ,hJz,hsel,hgen⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.PrimeSelection
