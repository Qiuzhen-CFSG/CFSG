module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Action
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Statements
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.Models
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.G64Source
public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.Quotient
public import Theory.GroupTheory.SylowNormalIntersection
public import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# G.6.4 on the faithful images of the split constituents

Each K-invariant constituent stabilized by v carries the literal action of
K⟨v⟩. Irreducibility survives this extension and passage to its faithful image.
A normal two-subgroup acts trivially on an irreducible binary module, proving
that the image has trivial two-core. Rank-one displacement gives a genuine
transvection, whose orbit spans by irreducibility.

The marked element remains central in an actual Sylow subgroup: the original
Sylow normalizes K⟨v⟩, so its intersection is Sylow there, and its image is Sylow
in the faithful image. The SQTK cover is restricted to the full preimage of
K⟨v⟩ before composing with the action map.

These results prove the application hypotheses of the exact universal G.6.4.
They do not assert faithfulness on K or choose a recognized model. Those steps
still require the source displacement-plane restriction and model exclusions.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.6.1–4,
printed pp.345–346, and the split paragraph of 15.3.58, printed p.1149.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition
open CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component
open CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.G64Natural
universe u
variable {A E : Type u} [Group A] [AddCommGroup E] [Module (ZMod 2) E]

/-- A binary rank-one displacement has nonzero center and form, with isotropic pairing. -/
theorem transvection_of_rank_one [Finite E]
    (ρ : Representation (ZMod 2) A E) (t : A)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) = 1) :
    IsTransvection ρ t := by
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom t)
  obtain ⟨f, v, he⟩ := LinearEquiv.mem_dilatransvections_iff_finrank.mpr
    (show Module.finrank (ZMod 2) (LinearMap.range (e.toLinearMap - LinearMap.id)) ≤ 1 from hr.le)
  have hact (w : E) : ρ t w = w + f w • v := LinearMap.congr_fun he w
  have hne : ρ t ≠ LinearMap.id := by
    intro h
    rw [h, sub_self, LinearMap.range_zero] at hr
    have hz : Module.finrank (ZMod 2) (⊥ : Submodule (ZMod 2) E) = 0 := finrank_bot _ _
    omega
  have hf : f ≠ 0 := by
    intro h
    apply hne
    ext w
    simp [h] at hact
    exact hact w
  have hv : v ≠ 0 := by
    intro h
    apply hne
    ext w
    simp [h] at hact
    exact hact w
  refine ⟨f, v, hf, hv, ?_, hact⟩
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (f v) with h | h
  · exact h
  · have hev : e v = 0 := by
      change ρ t v = 0
      rw [hact, h, one_smul, ZModModule.add_self]
    exact (hv (e.map_eq_zero_iff.mp hev)).elim

/-- The orbit span of a nonzero transvection displacement is the whole irreducible module. -/
theorem orbit_eq_top_of_irreducible
    (ρ : Representation (ZMod 2) A E) [ρ.IsIrreducible]
    (t : A) (ht : IsTransvection ρ t) : displacementOrbit ρ t = ⊤ := by
  rcases eq_bot_or_eq_top (displacementRepresentation ρ t) with hb | hh
  · have he : displacementOrbit ρ t = ⊥ :=
      congrArg Subrepresentation.toSubmodule hb
    obtain ⟨f, v, hf, hv, hfv, hact⟩ := ht
    obtain ⟨w, hw⟩ : ∃ w, f w ≠ 0 := by
      by_contra! h
      exact hf (LinearMap.ext h)
    have hd : ρ t w - w ∈ displacementOrbit ρ t :=
      Submodule.subset_span ⟨1, w, by simp⟩
    rw [he, Submodule.mem_bot, hact, add_sub_cancel_left] at hd
    exact ((smul_eq_zero.mp hd).elim hw hv).elim
  · exact congrArg Subrepresentation.toSubmodule hh

/-- The two-core acts trivially on an irreducible binary module and dies by faithfulness. -/
theorem twoCore_eq_bot [Finite A] [Finite E]
    (ρ : Representation (ZMod 2) A E) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) : pCore 2 A = ⊥ := by
  apply le_bot_iff.mp
  exact (normal_p_subgroup_le_ker ρ (pCore 2 A) (pCore_isPGroup (p := 2))).trans
    (ρ.ker_eq_bot_iff.mpr hf).le

/-- A surjection sends the marked central element to the center of its Sylow image. -/
theorem central_image [Finite A] {B : Type u} [Group B]
    (f : A →* B) (hf : Function.Surjective f)
    (T : Sylow 2 A) (t : A) (ht : t ∈ (center T).map (T : Subgroup A).subtype) :
    f t ∈ (center (T.mapSurjective hf)).map
      (T.mapSurjective hf : Subgroup B).subtype := by
  obtain ⟨t, ht, rfl⟩ := ht
  have htm : f t ∈ (T.mapSurjective hf : Subgroup B) :=
    mem_map_of_mem f t.property
  refine ⟨⟨f t, htm⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  rintro ⟨b, hb⟩
  obtain ⟨a, ha, rfl⟩ := hb
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, map_mul] using
    congrArg f (congrArg Subtype.val (mem_center_iff.mp ht ⟨a, ha⟩))

/-- Apply all hypotheses of the exact G.6.4 and then its Sylow-central refinement. -/
theorem image_g64 [Finite A] [Finite E] {κ : GroupClass.{u}}
    (hG64 : G64SourceTheorem κ)
    (ρ : Representation (ZMod 2) A E) [ρ.IsIrreducible]
    (t : A) (T : Sylow 2 A) (ht : t ∈ (center T).map (T : Subgroup A).subtype)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) = 1)
    {Cover : Type u} [Group Cover] [Finite Cover]
    (q : Cover →* A) (hq : Function.Surjective q) (hcover : IsSQTK κ Cover) :
    normalClosure ({actionHom ρ t} : Set (actionImage ρ)) = ⊤ ∧
      G64CentralAlternative (imageRepresentation ρ) := by
  let σ := imageRepresentation ρ
  let f := actionHom ρ
  have hf : Function.Surjective f := ρ.asGroupHom.rangeRestrict_surjective
  let : σ.IsIrreducible := (irreducible_comp_surjective_iff f hf σ).mp
    (show ρ.IsIrreducible from inferInstance)
  have htr : IsTransvection σ (f t) := transvection_of_rank_one σ (f t) hr
  have hfaith := imageRepresentation_injective ρ
  have hc := hG64 σ (f t) (f.comp q) hcover (hf.comp hq)
    (twoCore_eq_bot σ hfaith) hfaith (transvection_square hfaith htr) htr.ne_one
    (by rw [transvection_displacement_rank htr]; decide)
    (orbit_eq_top_of_irreducible σ (f t) htr) htr
  exact hc.2 (T.mapSurjective hf) (central_image f hf T t ht)

section Constituents
variable {ρ : Representation (ZMod 2) A E} {K : Subgroup A} {v : A}

/-- The literal overgroup used to apply G.6.4 on a constituent. -/
abbrev extensionActor (K : Subgroup A) (v : A) : Subgroup A := K ⊔ zpowers v

/-- Its marked element is the original involution. -/
def extensionMark (K : Subgroup A) (v : A) : extensionActor K v :=
  ⟨v, (le_sup_right : zpowers v ≤ extensionActor K v) (mem_zpowers v)⟩

/-- K-invariance and v-invariance give invariance under their generated overgroup. -/
theorem constituent_stable (J : Subrepresentation (ρ.comp K.subtype))
    (hv : J.toSubmodule.map (ρ v) = J.toSubmodule) :
    extensionActor K v ≤ subspaceStabilizer ρ J.toSubmodule := by
  refine sup_le ?_ (zpowers_le.mpr ?_)
  · apply le_subspaceStabilizer
    intro a ha w hw
    exact J.apply_mem_toSubmodule ⟨a, ha⟩ hw
  · intro w
    constructor
    · intro hw
      rw [← hv] at hw
      obtain ⟨x, hx, he⟩ := hw
      have he' : x = w :=
        (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom v)).injective he
      exact he' ▸ hx
    · intro hw
      rw [← hv]
      exact ⟨w, hw, rfl⟩

/-- Extend the literal constituent action from K to K⟨v⟩. -/
def constituentAction (J : Subrepresentation (ρ.comp K.subtype))
    (hv : J.toSubmodule.map (ρ v) = J.toSubmodule) :
    Representation (ZMod 2) (extensionActor K v) J.toSubmodule :=
  (stabilizerRepresentation ρ J.toSubmodule).comp
    (inclusion (constituent_stable J hv))

/-- The extended action is the original action on the same vectors. -/
theorem constituentAction_apply (J : Subrepresentation (ρ.comp K.subtype))
    (hv : J.toSubmodule.map (ρ v) = J.toSubmodule)
    (a : extensionActor K v) (w : J.toSubmodule) :
    (constituentAction J hv a w : E) = ρ a w := rfl

/-- Restricting back to K recovers the literal constituent representation. -/
theorem constituentAction_comp (J : Subrepresentation (ρ.comp K.subtype))
    (hv : J.toSubmodule.map (ρ v) = J.toSubmodule) :
    (constituentAction J hv).comp (inclusion (le_sup_left : K ≤ extensionActor K v)) =
      J.toRepresentation := rfl

/-- An action extending an irreducible action is irreducible. -/
theorem constituentAction_irreducible (J : Subrepresentation (ρ.comp K.subtype))
    (hv : J.toSubmodule.map (ρ v) = J.toSubmodule) (hJ : J.toRepresentation.IsIrreducible) :
    (constituentAction J hv).IsIrreducible := by
  let := hJ
  let : Nontrivial J.toSubmodule := Subrepresentation.irreducible_module_nontrivial J.toRepresentation
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  let R : Subrepresentation J.toRepresentation :=
    ⟨S.toSubmodule, fun k _ hw => S.apply_mem_toSubmodule
      (inclusion (le_sup_left : K ≤ extensionActor K v) k) hw⟩
  rcases eq_bot_or_eq_top R with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun U : Subrepresentation J.toRepresentation => U.toSubmodule) h
  · right
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun U : Subrepresentation J.toRepresentation => U.toSubmodule) h

/-- Embedding the internal displacement image preserves its dimension. -/
theorem constituentAction_rank (J : Subrepresentation (ρ.comp K.subtype))
    (hv : J.toSubmodule.map (ρ v) = J.toSubmodule) :
    Module.finrank (ZMod 2)
        (LinearMap.range (constituentAction J hv (extensionMark K v) - LinearMap.id)) =
      Module.finrank (ZMod 2)
        (LinearMap.range ((ρ v - LinearMap.id).comp J.toSubmodule.subtype)) := by
  let d := constituentAction J hv (extensionMark K v) - LinearMap.id
  have he : J.toSubmodule.subtype.comp d = (ρ v - LinearMap.id).comp J.toSubmodule.subtype := by
    ext w
    rfl
  rw [← he, LinearMap.range_comp, Submodule.finrank_map_subtype_eq]

end Constituents

/-- Intersect the normalizing Sylow with K⟨v⟩, retaining centrality of v. -/
theorem extension_sylow [Finite A] (K : Subgroup A) [K.Normal]
    (v : A) (T : Sylow 2 A) (ht : v ∈ (center T).map (T : Subgroup A).subtype) :
    ∃ P : Sylow 2 (extensionActor K v),
      extensionMark K v ∈ (center P).map (P : Subgroup (extensionActor K v)).subtype := by
  obtain ⟨z, hz, hzv⟩ := ht
  have hvT : v ∈ T := hzv ▸ z.property
  have hc (a : A) (ha : a ∈ T) : Commute a v := by
    rw [← hzv]
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨a, ha⟩)
  have hn : (T : Subgroup A) ≤ normalizer (extensionActor K v : Set A) := by
    apply le_trans (le_inf (show (T : Subgroup A) ≤ normalizer (K : Set A) by
      rw [normalizer_eq_top]; exact le_top) ?_) (normalizer_inf_normalizer_le_normalizer_sup K (zpowers v))
    intro a ha
    apply Subgroup.centralizer_le_normalizer
    rw [zpowers_eq_closure, centralizer_closure]
    exact mem_centralizer_singleton_iff.mpr (hc a ha)
  let L := extensionActor K v
  let B := L ⊔ (T : Subgroup A)
  let _ : (L.subgroupOf B).Normal :=
    (normal_subgroupOf_iff_le_normalizer (show L ≤ B from le_sup_left)).mpr
      (sup_le L.le_normalizer hn)
  obtain ⟨P, hP⟩ := (T.subtype (show (T : Subgroup A) ≤ B from le_sup_right)).exists_subgroupOf_eq_of_normal (L.subgroupOf B)
  let e := subgroupOfEquivOfLe (show L ≤ B from le_sup_left)
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ : (Q : Subgroup L) = (T : Subgroup A).subgroupOf L := by
    change (P : Subgroup _).map e.toMonoidHom = _
    rw [hP]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨⟨x, (le_sup_left : L ≤ B) x.property⟩, x.property⟩, hx, rfl⟩
  refine ⟨Q, ?_⟩
  have hvm : extensionMark K v ∈ (Q : Subgroup L) := by
    rw [hQ]
    exact hvT
  refine ⟨⟨extensionMark K v, hvm⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  intro a
  apply Subtype.ext
  apply Subtype.ext
  exact hc a.val.val (show a.val ∈ (T : Subgroup A).subgroupOf L from hQ ▸ a.property)

/-- Restrict an SQTK cover to the actual preimage of K⟨v⟩. -/
theorem constituent_g64 [Finite A] [Finite E] {κ : GroupClass.{u}}
    (hG64 : G64SourceTheorem κ)
    (ρ : Representation (ZMod 2) A E) (K : Subgroup A) [K.Normal]
    (v : A) (T : Sylow 2 A) (ht : v ∈ (center T).map (T : Subgroup A).subtype)
    (J : Subrepresentation (ρ.comp K.subtype))
    (hv : J.toSubmodule.map (ρ v) = J.toSubmodule)
    (hJ : J.toRepresentation.IsIrreducible)
    (hr : Module.finrank (ZMod 2)
      (LinearMap.range ((ρ v - LinearMap.id).comp J.toSubmodule.subtype)) = 1)
    {Cover : Type u} [Group Cover] [Finite Cover]
    (q : Cover →* A) (hq : Function.Surjective q) (hcover : IsSQTK κ Cover) :
    normalClosure ({actionHom (constituentAction J hv) (extensionMark K v)} :
      Set (actionImage (constituentAction J hv))) = ⊤ ∧
      G64CentralAlternative (imageRepresentation (constituentAction J hv)) := by
  let := constituentAction_irreducible J hv hJ
  obtain ⟨P, hP⟩ := extension_sylow K v T ht
  apply image_g64 hG64 (constituentAction J hv) (extensionMark K v) P hP
    ((constituentAction_rank J hv).trans hr)
    (q.subgroupComap (extensionActor K v))
    (q.subgroupComap_surjective_of_surjective _ hq)
    (hcover.subgroup _)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.G64Natural
