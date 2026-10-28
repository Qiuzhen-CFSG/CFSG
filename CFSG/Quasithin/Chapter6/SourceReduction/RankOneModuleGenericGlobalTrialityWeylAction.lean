module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityWeylActionModel
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionTriality
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalCompletion

/-!
# Weyl constraints on the original triality torus normalizer

Conjugation by an element of the original Sylow T normalizes both source
parabolics. The same compatible comparison transports these actions to the
genuine triality parabolics. The whole-overlap torus marking makes each
transported action preserve the actual torus, so the proved local normalizer
calculation puts the image of each simple reflection in its original torus coset.

This constructs both Weyl constraints needed for the root-action identity.
No full-carrier automorphism is assumed. Reconstruction of the common
coefficient action and ambient Sylow placement in F.4.37 remain necessary
before using the fixed-point bounds to prove S=T. Exhaustive comparison,
original uniqueness and ambient recognition retain their assembly obligations.

Source: Aschbacher--Smith F.4.29, F.4.37--38, pp.289,293--294, and 5.3.3,
p.659 (`refs/quasithin.pdf`); GLS3 §§2.3--2.4. The local conjugation
transports are kept here to avoid importing the independent G₂ implementation.
-/


public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics Triality.Standard.ConcreteBruhat

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem source_parabolics_normalized
    {T : Sylow 2 G} {L H : Subgroup G}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) (i : Fin 2) :
    (T : Subgroup G) ≤ normalizer
      (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i : Set G) := by
  have hS := sylow_normalizes_sourceS hTL hTH
  have hK (j : Fin 2) : (T : Subgroup G) ≤ normalizer (![L,residual H] j : Set G) := by
    fin_cases j
    · exact hTL
    · exact hTH.trans (le_normalizer_residual H)
  have hB (j : Fin 2) : (T : Subgroup G) ≤ normalizer
      (ChapterF.Source.borel (![L,residual H] j) (sourceS L H) : Set G) := by
    have hi := (le_inf hS (hK j)).trans inf_normalizer_le_normalizer_inf
    exact (le_inf (hK j) (hi.trans (normalizer _).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  exact (le_inf ((le_inf (hK i) hS).trans (normalizer_inf_normalizer_le_normalizer_sup _ _))
    (hB (ChapterF.Source.other i))).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

omit [Finite G] in
private theorem torus_action_map
    {M : Type*} [Group M] [Finite M] (P : Subgroup G) (Q E : Subgroup M)
    (e : P ≃* Q) (D : Subgroup G) (t : G)
    (htP : t ∈ normalizer (P : Set G)) (htD : t ∈ normalizer (D : Set G))
    (hmark : ∀ x : P, x.val∈D ↔ (e x).val∈E) :
    (E.subgroupOf Q).map
      (MulAut.congr e (P.normalizerMonoidHom ⟨t,htP⟩)).toMonoidHom = E.subgroupOf Q := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,hx,rfl⟩
    have hd : (e.symm x).val ∈ D := (hmark _).mpr (by simpa only [e.apply_symm_apply] using (show x.val∈E from hx))
    have htd := (mem_normalizer_iff.mp htD _).mp hd
    exact (hmark (P.normalizerMonoidHom ⟨t,htP⟩ (e.symm x))).mp htd
  · rw [card_map_of_injective (MulAut.congr e (P.normalizerMonoidHom ⟨t,htP⟩)).injective]

omit [Finite G] in
private theorem conjugation_of_transport_eq
    {M : Type*} [Group M] (P : Subgroup G) (Q : Subgroup M)
    (e : P ≃* Q) (g : G) (hg : g∈normalizer (P : Set G)) (x y : Q)
    (hxy : MulAut.congr e (P.normalizerMonoidHom ⟨g,hg⟩) x=y) :
    g*(e.symm x).val*g⁻¹=(e.symm y).val := by
  have he := congrArg (fun z : Q => (e.symm z).val) hxy
  change (e.symm (e (P.normalizerMonoidHom ⟨g,hg⟩ (e.symm x)))).val = _ at he
  rw [e.symm_apply_apply] at he
  exact he

omit [Finite G] in
private theorem conjugation_coset_of_transport
    {M : Type*} [Group M] (Q : Subgroup G) (P E : Subgroup M)
    (e : Q ≃* P) (D : Subgroup G) (t : G)
    (htQ : t ∈ normalizer (Q : Set G)) (hEP : E ≤ P)
    (hmark : ∀ x : Q, x.val ∈ D ↔ (e x).val ∈ E)
    (w : Q) (u : E)
    (hu : (MulAut.congr e (Q.normalizerMonoidHom ⟨t,htQ⟩) (e w)).val =
      u.val * (e w).val) :
    ∃ v ∈ D, t*w.val*t⁻¹ = v*w.val := by
  let z : P := inclusion hEP u
  have he : MulAut.congr e (Q.normalizerMonoidHom ⟨t,htQ⟩) (e w) = z * e w :=
    Subtype.ext hu
  have ht := conjugation_of_transport_eq Q P e t htQ (e w) (z*e w) he
  refine ⟨(e.symm z).val, (hmark _).mpr ?_, ?_⟩
  · rw [e.apply_symm_apply]
    exact u.property
  · simpa only [map_mul, e.symm_apply_apply, Subgroup.coe_mul] using ht

omit [Finite G] in
private theorem marking_of_overlap
    {M : Type*} [Group M] (Q I : Subgroup G) (C J E : Subgroup M)
    (e : Q ≃* C) (f : I ≃* J) (hIQ : I ≤ Q)
    (D : Subgroup G) (hD : D ≤ I) (hE : E ≤ J)
    (hc : ∀ y : I, (e (inclusion hIQ y)).val = (f y).val)
    (hmark : ∀ y : I, y.val ∈ D ↔ (f y).val ∈ E)
    (x : Q) : x.val ∈ D ↔ (e x).val ∈ E := by
  constructor
  · intro hx
    let y : I := ⟨x.val, hD hx⟩
    have he : (e x).val = (f y).val := hc y
    exact he.symm ▸ (hmark y).mp hx
  · intro hx
    let z : J := ⟨(e x).val, hE hx⟩
    let y : I := f.symm z
    have hfy : f y = z := f.apply_symm_apply z
    have he : e (inclusion hIQ y) = e x :=
      Subtype.ext ((hc y).trans (congrArg Subtype.val hfy))
    have hv : y.val = x.val := congrArg Subtype.val (e.injective he)
    have hd : y.val ∈ D := (hmark y).mpr ((congrArg Subtype.val hfy).symm ▸ hx)
    exact hv ▸ hd

omit [Finite G] in
private theorem transported_weyl_coset
    (m : ℕ) (hm : 0<m) (hm2 : 1<m) (a : Node)
    (Q : Subgroup G) (e : Q ≃* parabolic (binaryParameters m hm) a)
    (D : Subgroup G) (t : G) (htQ : t∈normalizer (Q : Set G))
    (htD : t∈normalizer (D : Set G))
    (hmark : ∀ x : Q, x.val∈D ↔ (e x).val∈torus (binaryParameters m hm))
    (w : Q) (hw : (e w).val = simpleRepresentative (binaryParameters m hm) rfl a) :
    ∃ u ∈ D, t*w.val*t⁻¹ = u*w.val := by
  let b := MulAut.congr e (Q.normalizerMonoidHom ⟨t,htQ⟩)
  have hb := torus_action_map (M := Carrier (binaryParameters m hm)) Q
    (parabolic (binaryParameters m hm) a) (torus (binaryParameters m hm)) e D t htQ htD hmark
  obtain ⟨u,hu⟩ := TrialityWeylAction.parabolic_aut_weyl m hm hm2 a b hb
  have hew : e w = ⟨simpleRepresentative (binaryParameters m hm) rfl a,
      simpleRepresentative_mem_parabolic (binaryParameters m hm) rfl a⟩ := Subtype.ext hw
  have he : (b (e w)).val = u.val * (e w).val :=
    (congrArg (fun x => (b x).val) hew).trans
      (hu.trans (congrArg (u.val * ·) hw.symm))
  exact conjugation_coset_of_transport (M := Carrier (binaryParameters m hm))
    Q (parabolic (binaryParameters m hm) a)
    (torus (binaryParameters m hm)) e D t htQ
    ((torus_le_borel (binaryParameters m hm)).trans
      (borel_le_parabolic (binaryParameters m hm) a)) hmark w u he

omit [Finite G] in
private theorem exists_transported_weyl_coset
    (m : ℕ) (hm : 0<m) (hm2 : 1<m) (a : Node)
    (Q : Subgroup G) (e : Q ≃* parabolic (binaryParameters m hm) a)
    (D : Subgroup G) (t : G) (htQ : t∈normalizer (Q : Set G))
    (htD : t∈normalizer (D : Set G))
    (hmark : ∀ x : Q, x.val∈D ↔ (e x).val∈torus (binaryParameters m hm)) :
    ∃ w : Q, (e w).val = simpleRepresentative (binaryParameters m hm) rfl a ∧
      ∃ u ∈ D, t*w.val*t⁻¹ = u*w.val := by
  let w : Q := e.symm ⟨simpleRepresentative (binaryParameters m hm) rfl a,
    simpleRepresentative_mem_parabolic (binaryParameters m hm) rfl a⟩
  have hw : (e w).val = simpleRepresentative (binaryParameters m hm) rfl a :=
    congrArg Subtype.val (e.apply_symm_apply _)
  exact ⟨w,hw,transported_weyl_coset m hm hm2 a Q e D t htQ htD hmark w hw⟩

omit [Finite G] in
private theorem inclusion_amalgam_markings
    {M : Type*} [Group M] (Q P : Subgroup G) (C J F E : Subgroup M)
    (hJC : J ≤ C) (hJF : J ≤ F)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups Q (Q ⊓ P) P inf_le_left inf_le_right)
      (RankTwoAmalgam.ofSubgroups C J F hJC hJF))
    (D : Subgroup G) (hD : D ≤ Q ⊓ P) (hE : E ≤ J)
    (hmark : ∀ y : (Q ⊓ P : Subgroup G), y.val ∈ D ↔ (e.middle y).val ∈ E) :
    (∀ x : Q, x.val ∈ D ↔ (e.left x).val ∈ E) ∧
    (∀ x : P, x.val ∈ D ↔ (e.right x).val ∈ E) := by
  constructor
  · exact marking_of_overlap Q (Q ⊓ P) C J E e.left e.middle inf_le_left D hD hE
      (fun y => congrArg Subtype.val (e.left_commutes y)) hmark
  · exact marking_of_overlap P (Q ⊓ P) F J E e.right e.middle inf_le_right D hD hE
      (fun y => congrArg Subtype.val (e.right_commutes y)) hmark

omit [Finite G] in
private theorem source_triality_torus_markings
    {L H D : Subgroup G} (m : ℕ) (hm : 0<m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)
    (hD : D ≤ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
      ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1)
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val ∈ D ↔ (e.middle b).val ∈ torus (binaryParameters m hm)) :
    (∀ x : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0,
      x.val ∈ D ↔ (e.left x).val ∈ torus (binaryParameters m hm)) ∧
    (∀ x : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1,
      x.val ∈ D ↔ (e.right x).val ∈ torus (binaryParameters m hm)) :=
  inclusion_amalgam_markings
    (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0)
    (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1)
    (parabolic (binaryParameters m hm) .central) (borel (binaryParameters m hm))
    (parabolic (binaryParameters m hm) .arms) (torus (binaryParameters m hm))
    (borel_le_parabolic _ .central) (borel_le_parabolic _ .arms) e D hD
    (torus_le_borel _) hmark

/-- The original Sylow actor carries each marked triality reflection into
its torus coset through the same whole-overlap comparison. This constructs
the local Weyl constraints used to recover the root action. -/
theorem Preparation.triality_torus_normalizer_weyl_action
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0<m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)
    (hD : D ≤ ChapterF.Source.commonBorel ![L,residual H] (sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val ∈ D ↔ (e.middle b).val ∈ torus (binaryParameters m hm))
    (t : T) (htD : t.val ∈ normalizer (D : Set G)) :
    ∃ w₀ : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0,
    ∃ w₁ : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1,
    (e.left w₀).val = simpleRepresentative (binaryParameters m hm) rfl .central ∧
    (e.right w₁).val = simpleRepresentative (binaryParameters m hm) rfl .arms ∧
    (∃ u ∈ D, t.val*w₀.val*t.val⁻¹ = u*w₀.val) ∧
    (∃ u ∈ D, t.val*w₁.val*t.val⁻¹ = u*w₁.val) := by
  have hC := (ChapterF.Source.lemma_F_1_3_6 (d.hypothesisF11 h hTH)).ge
  obtain ⟨hml,hmr⟩ := source_triality_torus_markings m hm e (hD.trans hC) hmark
  have htP := source_parabolics_normalized h.sylow_normalizes hTH 1 t.property
  have htQ := source_parabolics_normalized h.sylow_normalizes hTH 0 t.property
  have hm2 : 1<m := (d.triality_local_structure h hTH hp m hm e).2.1
  obtain ⟨w₀,hw₀,hu₀⟩ := exists_transported_weyl_coset m hm hm2 .central
    (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0) e.left D t.val htQ htD hml
  obtain ⟨w₁,hw₁,hu₁⟩ := exists_transported_weyl_coset m hm hm2 .arms
    (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1) e.right D t.val htP htD hmr
  exact ⟨w₀,w₁,hw₀,hw₁,hu₀,hu₁⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
