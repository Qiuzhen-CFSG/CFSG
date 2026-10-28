module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianParabolics
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.GroupTheory.PrimeRankSylow

/-!
# The center action in the orthogonal branch of 12.9.4

An odd subgroup fixing the hatted plane and Z(U) acts quadratically on
V₂Z(U), hence fixes V₂ by coprime action. If the centralizer of Z(U) had
full dotted image, a Sylow three-subgroup above the dotted point centralizer
would therefore lie in the original tilded-plane centralizer. The source
three-rank bound excludes this, since the actual A₈ point centralizer has
three-rank at least two.

The image of C_H(Z(U)) is normal in the simple dotted A₈, so it is trivial.
The original returning center has nontrivial dotted image and thus does
not centralize Z(U). This supplies the nontrivial center action used after
equation (*) in 12.9.4, without a new component-action hypothesis.

Source: Aschbacher--Smith 12.8.13(5) and 12.9.4, printed pp.856,860
of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

omit [Finite G] in
private theorem center_normalized (F : InvariantFlag T V n) :
    F.H ≤ normalizer (F.ZU : Set G) :=
  (le_normalizer_conjugateSpanBy V F.H).trans
    (normalizer_le_normalizer_characteristic_image F.U (Subgroup.center F.U))

omit [Finite G] in
private theorem hat_plane_commutator
    (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (v : Additive F.Uhat)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v})
    (S : Subgroup G) (hSH : S ≤ F.H)
    (hfix : ∀ s : S, F.terminalRepresentation
      (QuotientGroup.mk' F.terminalHatAction.ker (inclusion hSH s)) v = v) :
    ⁅S,F.Vi 2⁆ ≤ F.ZU := by
  apply commutator_le.mpr
  intro s hs w hw
  let a : F.H := ⟨s,hSH hs⟩
  let u : F.U := ⟨w,le_conjugateSpanBy V F.H (F.le_seed 2 hw)⟩
  have hu : hatElement F u ∈ Submodule.span (ZMod 2) {v} :=
    hline ▸ show hatElement F u ∈ hatSpace F (F.Vi 2) from ⟨u,hw,rfl⟩
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hu
  have hh : F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a)
      (hatElement F u) = hatElement F u := by
    have hsf : F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) v = v :=
      hfix ⟨s,hs⟩
    rw [←hc,map_smul,hsf]
  have he := congrArg Additive.toMul hh
  rw [F.terminalRepresentation_apply_mk] at he
  change F.terminalHatAction a (QuotientGroup.mk' (center F.U) u) =
    QuotientGroup.mk' (center F.U) u at he
  rw [F.terminalHatAction_apply_mk] at he
  refine ⟨F.uAction a u / u,QuotientGroup.eq_iff_div_mem.mp he,?_⟩
  change s * w * s⁻¹ / w = ⁅s,w⁆
  simp only [commutatorElement_def,div_eq_mul_inv]

/-- Odd subgroups fixing both the hatted plane and the whole center fix the
original plane. Coprime quadratic action removes the central error. -/
theorem nonabelian_odd_fixes_plane_of_center
    {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (v : Additive F.Uhat)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v})
    (S : Subgroup G) (hS : IsPGroup 3 S) (hSH : S ≤ F.H)
    (hSZ : S ≤ centralizer (F.ZU : Set G))
    (hfix : ∀ s : S, F.terminalRepresentation
      (QuotientGroup.mk' F.terminalHatAction.ker (inclusion hSH s)) v = v) :
    S ≤ centralizer (F.Vi 2 : Set G) := by
  let := h.chosen.elementary
  let Q := F.Vi 2 ⊔ F.ZU
  have hPU : F.Vi 2 ≤ F.U := (F.le_seed 2).trans (le_conjugateSpanBy V F.H)
  have hZU : F.ZU ≤ F.U := map_subtype_le _
  have hQU : Q ≤ F.U := sup_le hPU hZU
  have htwo := F.localKernel_UH_isPGroup h.source.simpleQTKE L _ F.H
    (by have := h.rank; omega) h.chosen.le_sylow h.chosen.normalizes
    (h.sylow_normalizes earlier.structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
    (h.point_mem_Hz F earlier.alternatives)
  have hQtwo : IsPGroup 2 Q := htwo.to_le hQU
  let : Group.IsNilpotent Q := hQtwo.isNilpotent
  have hcomm : ⁅Q,S⁆ ≤ F.ZU := by
    apply commutator_sup_le_of_relative_normal F.H (F.Vi 2) F.ZU S F.ZU
      (center_normalized F) (hPU.trans F.U_le_H) (hZU.trans F.U_le_H)
    · rw [commutator_comm]
      exact hat_plane_commutator F v hline S hSH hfix
    · exact (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hSZ)).le.trans bot_le
  have hSQ : S ≤ normalizer (Q : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hcomm.trans le_sup_right)
  have hquad : ⁅⁅Q,S⁆,S⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (commutator_mono hcomm le_rfl).trans
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hSZ)).le
  have hc := commutator_eq_bot_of_coprime_quadratic Q S hSQ inferInstance
    (IsPGroup.coprime_card_of_ne 3 2 (by decide) S Q hS hQtwo) hquad
  exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)).trans
    (centralizer_le (fun _ hx => (show F.Vi 2 ≤ Q from le_sup_left) hx))

private theorem point_three_rank_of_center_image_top
    {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (v : Additive F.Uhat)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v})
    (htop : F.terminalDot (centralizer (F.ZU : Set G)) = ⊤) :
    primeRank 3 (F.terminalPointCentralizer v) ≤ 1 := by
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  let A : Subgroup F.H := (centralizer (F.ZU : Set G)).subgroupOf F.H ⊓
    (F.terminalPointCentralizer v).comap q
  let S : Sylow 3 A := Classical.choice inferInstance
  let j : A →* G := F.H.subtype.comp A.subtype
  let R := (S : Subgroup A).map j
  have hRH : R ≤ F.H := by
    rintro _ ⟨s,hs,rfl⟩
    exact s.val.property
  have hRZ : R ≤ centralizer (F.ZU : Set G) := by
    rintro _ ⟨s,hs,rfl⟩
    exact s.property.1
  have hRfix : ∀ r : R, F.terminalRepresentation (q (inclusion hRH r)) v = v := by
    intro r
    obtain ⟨s,hs,he⟩ := r.property
    have he' : inclusion hRH r = s.val := Subtype.ext he.symm
    rw [he']
    exact s.property.2
  have hRC := nonabelian_odd_fixes_plane_of_center h earlier F v hline R
    (S.isPGroup'.map j) hRH hRZ hRfix
  have hRT : R ≤ F.terminalTildePlaneCentralizer := by
    intro r hr
    refine ⟨⟨r,hRH hr⟩,?_,rfl⟩
    intro y hy
    obtain ⟨w,hw,rfl⟩ := hy
    have hc : w * (⟨r,hRH hr⟩ : F.H) = (⟨r,hRH hr⟩ : F.H) * w :=
      Subtype.ext (hRC hr w hw)
    simpa only [map_mul] using congrArg (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.H)) hc
  let f : S →* F.terminalTildePlaneCentralizer :=
    (j.comp (S : Subgroup A).subtype).codRestrict _
      (fun s => hRT (mem_map_of_mem j s.property))
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (Subtype.ext (Subtype.ext
      (congrArg (fun z : F.terminalTildePlaneCentralizer => (z:G)) he)))
  have hr : primeRank 3 A ≤ 1 := by
    rw [S.primeRank_eq]
    exact (Theory.GroupTheory.primeRank_le_of_injective 3 f hf).trans
      (nonabelian_tilde_plane_three_rank h earlier F hne g hgP hgH)
  let r : A →* F.terminalPointCentralizer v :=
    (q.comp A.subtype).codRestrict _ (fun x => x.property.2)
  have hs : Function.Surjective r := by
    intro x
    have hx : x.val ∈ F.terminalDot (centralizer (F.ZU : Set G)) := htop ▸ mem_top _
    obtain ⟨t,ht,he⟩ := hx
    exact ⟨⟨t,ht,show q t ∈ F.terminalPointCentralizer v from he.symm ▸ x.property⟩,Subtype.ext he⟩
  exact S.primeRank_le_one_of_surjective
    (S.isCyclic_of_odd_of_primeRank_le_one (by decide) hr) r hs

/-- In the actual A₈ action the centralizer of Z(U) has trivial dotted
image. A full image would lift the rank-two point centralizer to an odd
subgroup fixing V₂, contrary to the original tilded-plane rank bound. -/
theorem nonabelian_caseFive_center_centralizer_dot
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B) :
    F.terminalDot (centralizer (F.ZU : Set G)) = ⊥ := by
  obtain ⟨e⟩ := nonabelian_caseFive_alternating_eight h hn earlier F hne B h5
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup F.TerminalHdot := e.isSimpleGroup
  let C := (centralizer (F.ZU : Set G)).subgroupOf F.H
  have hHC := (center_normalized F).trans (normalizer_le_normalizer_centralizer F.ZU)
  let : C.Normal := normal_subgroupOf_of_le_normalizer (by
    intro a ha z
    exact hHC ha (z:G))
  have hnormal : (F.terminalDot (centralizer (F.ZU : Set G))).Normal :=
    (inferInstance : C.Normal).map (QuotientGroup.mk' F.terminalHatAction.ker)
      (QuotientGroup.mk'_surjective _)
  apply hnormal.eq_bot_or_eq_top.resolve_right
  intro ht
  obtain ⟨_,_,v,_,_,_,hv,hline,_⟩ :=
    nonabelian_transvection_geometry h earlier F hne g hgP hgH
  have hlow := point_three_rank_of_center_image_top h earlier F hne g hgP hgH v hline ht
  have hhigh := nonabelian_caseFive_point_rank h hn earlier F hne B h5 v hv hline
  omega

/-- The original returning center acts nontrivially on Z(U), before any
natural-four reduction or constituent choice. -/
theorem nonabelian_caseFive_centers_noncommuting
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B) :
    ¬ conjugate F.ZU g ≤ centralizer (F.ZU : Set G) := by
  intro hc
  apply (nonabelian_caseFive_center h hn earlier F hne g hgP hgH B h5).2
  apply le_bot_iff.mp
  exact (map_mono (comap_mono hc)).trans
    (nonabelian_caseFive_center_centralizer_dot h hn earlier F hne g hgP hgH B h5).le

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components

