module
public import Theory.SpecificGroups.G2.RootPresentationRecognition.Recognition
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage.FrameAlignment.RankOneNormalizers
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage.FrameAlignment.TorusAlignment
public import Theory.GroupTheory.Amalgam.AutomorphismGroup

/-!
# Native G₂ lifting for original DGS restoration

Align the image of the full split torus by Hall conjugacy inside the Borel.
The two rank-one torus normalizers put the Weyl images in their prescribed
cosets. A torus–Weyl calculation proves their braid relation. All other
presentation equations lie in one of the two endpoints, so the proved G₂
presentation extends both compatible endpoint maps simultaneously.

This removes the kernel-preservation premise in the nonbinary G₂ restoration.
The proof uses the actual six octonion roots, full torus and both parabolics.
Source: DGS, Groups and Graphs (1985), (15.2), pp.226–228, and the G₂
presentation used for Theorem D, p.224. Model formulas and the local torus
normalizers are from the licensed ATLAS port; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff. The local Hall proof adapts the existing
FrameAlignment/TorusAlignment proof to the common endpoint restriction.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.G2.RootPresentationRecognition
open Atlas.G2.Explicit
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.G2NativeLift
private theorem marked_left {X : Type*} [Group X] (P B Q : Subgroup X)
    (hBP : B ≤ P) (hBQ : B ≤ Q)
    (a : RankTwoAmalgam.Iso (.ofSubgroups P B Q hBP hBQ) (.ofSubgroups P B Q hBP hBQ))
    (x : B) : (a.middle x).val = (a.left (inclusion hBP x)).val :=
  (congrArg Subtype.val (a.left_commutes x)).symm

private theorem marked_right {X : Type*} [Group X] (P B Q : Subgroup X)
    (hBP : B ≤ P) (hBQ : B ≤ Q)
    (a : RankTwoAmalgam.Iso (.ofSubgroups P B Q hBP hBQ) (.ofSubgroups P B Q hBP hBQ))
    (x : B) : (a.middle x).val = (a.right (inclusion hBQ x)).val :=
  (congrArg Subtype.val (a.right_commutes x)).symm

private def corrected {X : Type*} [Group X] (P B Q : Subgroup X)
    (hBP : B ≤ P) (hBQ : B ≤ Q)
    (a : RankTwoAmalgam.Iso (.ofSubgroups P B Q hBP hBQ) (.ofSubgroups P B Q hBP hBQ))
    (g : B) : RankTwoAmalgam.Iso (.ofSubgroups P B Q hBP hBQ) (.ofSubgroups P B Q hBP hBQ) :=
  a.trans {
    left := MulAut.conj (inclusion hBP g)
    middle := MulAut.conj g
    right := MulAut.conj (inclusion hBQ g)
    left_commutes := fun _ => rfl
    right_commutes := fun _ => rfl }

private theorem corrected_map {X : Type*} [Group X] (P B Q : Subgroup X)
    (hBP : B ≤ P) (hBQ : B ≤ Q)
    (a : RankTwoAmalgam.Iso (.ofSubgroups P B Q hBP hBQ) (.ofSubgroups P B Q hBP hBQ))
    (g : B) (C : Subgroup B)
    (hg : C = (C.map a.middle.toMonoidHom).map (MulAut.conj g).toMonoidHom) :
    C.map (corrected P B Q hBP hBQ a g).middle.toMonoidHom = C := by
  change C.map ((MulAut.conj g).toMonoidHom.comp a.middle.toMonoidHom) = C
  rw [←map_map]
  exact hg.symm

private theorem undo_corrected {X : Type*} [Group X] (P B Q : Subgroup X)
    (hBP : B ≤ P) (hBQ : B ≤ Q)
    (a : RankTwoAmalgam.Iso (.ofSubgroups P B Q hBP hBQ) (.ofSubgroups P B Q hBP hBQ))
    (g : B) (f : X →* X)
    (hl : ∀ x : P, f x.val = ((corrected P B Q hBP hBQ a g).left x).val)
    (hr : ∀ x : Q, f x.val = ((corrected P B Q hBP hBQ a g).right x).val) :
    ∃ j : X →* X, (∀ x : P, j x.val = (a.left x).val) ∧
      (∀ x : Q, j x.val = (a.right x).val) := by
  refine ⟨(MulAut.conj g.val⁻¹).toMonoidHom.comp f,?_,?_⟩
  · intro x
    change MulAut.conj g.val⁻¹ (f x.val) = _
    rw [hl]
    change g.val⁻¹ * (g.val * (a.left x).val * g.val⁻¹) * (g.val⁻¹)⁻¹ = _
    group
  · intro x
    change MulAut.conj g.val⁻¹ (f x.val) = _
    rw [hr]
    change g.val⁻¹ * (g.val * (a.right x).val * g.val⁻¹) * (g.val⁻¹)⁻¹ = _
    group

private theorem sixth_power_of_images {X : Type*} [Group X] {a b c d : X}
    (ha : a = c) (hb : b = d) (hc : (c*d)^6 = 1) : (a*b)^6 = 1 := by
  rw [ha,hb]
  exact hc

variable {F : Type*} [Field F]

abbrev diagram : RankTwoAmalgam (parabolic₁ (F := F)) (Atlas.G2.borel (K := F)) (parabolic₂ (F := F)) :=
  .ofSubgroups _ _ _ borel_le_parabolic₁ borel_le_parabolic₂

private theorem root_mem_borel (i : Fin 6) (a : Multiplicative F) :
    (modelData (F := F)).root i a ∈ Atlas.G2.borel := by
  apply (show unipotent (K := F) ≤ Atlas.G2.borel from le_sup_left)
  fin_cases i <;> exact subset_closure (by simp [modelData,modelRoots])

private def rootInB (i : Fin 6) : Multiplicative F →* Atlas.G2.borel (K := F) :=
  (modelData.root i).codRestrict _ (root_mem_borel i)

private def torusInB : Fˣ × Fˣ →* Atlas.G2.borel (K := F) :=
  torusHom.codRestrict _ (fun p => (show splitTorus ≤ Atlas.G2.borel (K := F) from le_sup_right) ⟨p,rfl⟩)

private def rInP : parabolic₂ (F := F) := ⟨weylR,weylR_mem_parabolic⟩
private def sInP : parabolic₁ (F := F) := ⟨weylS,mem_sup_right (subset_closure (by simp))⟩

private def transportedData (a : RankTwoAmalgam.Iso (diagram (F := F)) (diagram (F := F))) :
    BorelWeylData F (Model F) where
  root i := Atlas.G2.borel.subtype.comp (a.middle.toMonoidHom.comp (rootInB i))
  torus := Atlas.G2.borel.subtype.comp (a.middle.toMonoidHom.comp torusInB)
  r := (a.right rInP).val
  s := (a.left sInP).val

private theorem left_borel (a : RankTwoAmalgam.Iso (diagram (F := F)) (diagram (F := F))) (x : Atlas.G2.borel (K := F)) :
    (a.middle x).val = (a.left (inclusion borel_le_parabolic₁ x)).val :=
  marked_left parabolic₁ Atlas.G2.borel parabolic₂ borel_le_parabolic₁ borel_le_parabolic₂ a x
private theorem right_borel (a : RankTwoAmalgam.Iso (diagram (F := F)) (diagram (F := F))) (x : Atlas.G2.borel (K := F)) :
    (a.middle x).val = (a.right (inclusion borel_le_parabolic₂ x)).val :=
  marked_right parabolic₁ Atlas.G2.borel parabolic₂ borel_le_parabolic₁ borel_le_parabolic₂ a x

variable [CharP F 2]

private theorem torus_root_inB (l m : Fˣ) (i : Fin 6) (t : F) :
    torusInB (l,m) * rootInB i (Multiplicative.ofAdd t) * (torusInB (l,m))⁻¹ =
      rootInB i (Multiplicative.ofAdd (BorelWeylData.weight l m i * t)) := by
  apply Subtype.ext
  dsimp only [torusInB,rootInB,MonoidHom.codRestrict_apply,Subgroup.coe_mul,Subgroup.coe_inv]
  exact (model_relations (F := F)).torus_root l m i t

private theorem transported_relations (a : RankTwoAmalgam.Iso (diagram (F := F)) (diagram (F := F)))
    (hb : ((a.right rInP).val * (a.left sInP).val)^6 = 1) :
    (transportedData a).Relations := by
  let b := Atlas.G2.borel.subtype.comp a.middle.toMonoidHom
  let p := parabolic₁.subtype.comp a.left.toMonoidHom
  let q := parabolic₂.subtype.comp a.right.toMonoidHom
  have hl (x : Atlas.G2.borel (K := F)) : b x = p (inclusion borel_le_parabolic₁ x) := left_borel a x
  have hr (x : Atlas.G2.borel (K := F)) : b x = q (inclusion borel_le_parabolic₂ x) := right_borel a x
  change ({ root := (fun i => b.comp (rootInB i)), torus := b.comp torusInB, r := q rInP, s := p sInP } : BorelWeylData F (Model F)).Relations
  refine {
    toCharTwoRelations := ?_, torus_root := ?_, r_sq := ?_, s_sq := ?_,
    braid := hb, r_torus := ?_, s_torus := ?_, rA := ?_, rB := ?_, rC := ?_, rD := ?_, rF := ?_,
    sA := ?_, sB := ?_, sC := ?_, sD := ?_, sE := ?_, long_word := ?_, short_word := ?_ }
  · constructor
    · constructor
      · intro s t
        simp only [PositiveRoots.x, MonoidHom.comp_apply]
        simp only [← map_mul]
        apply congrArg b
        apply Subtype.ext
        exact model_relations.ba s t
      · intro s t
        simp only [PositiveRoots.x, MonoidHom.comp_apply]
        simp only [← map_mul]
        apply congrArg b
        apply Subtype.ext
        exact model_relations.ca s t
      · intro s t
        simp only [PositiveRoots.x, MonoidHom.comp_apply]
        simp only [← map_mul]
        apply congrArg b
        apply Subtype.ext
        exact model_relations.cb s t
      · intro s t
        simp only [PositiveRoots.x, MonoidHom.comp_apply]
        simp only [← map_mul]
        apply congrArg b
        apply Subtype.ext
        exact model_relations.da s t
      · intro s t
        simp only [PositiveRoots.x, MonoidHom.comp_apply]
        simp only [← map_mul]
        apply congrArg b
        apply Subtype.ext
        exact model_relations.db s t
      · intro s t
        simp only [PositiveRoots.x, MonoidHom.comp_apply]
        simp only [← map_mul]
        apply congrArg b
        apply Subtype.ext
        exact model_relations.ea s t
      · intro s t
        simp only [PositiveRoots.x, MonoidHom.comp_apply]
        simp only [← map_mul]
        apply congrArg b
        apply Subtype.ext
        exact model_relations.ec s t
      · intro s t
        simp only [PositiveRoots.x, MonoidHom.comp_apply]
        simp only [← map_mul]
        apply congrArg b
        apply Subtype.ext
        exact model_relations.ed s t
      · intro s t
        simp only [PositiveRoots.x, MonoidHom.comp_apply]
        simp only [← map_mul]
        apply congrArg b
        apply Subtype.ext
        exact model_relations.fa s t
      · intro s t
        simp only [PositiveRoots.x, MonoidHom.comp_apply]
        simp only [← map_mul]
        apply congrArg b
        apply Subtype.ext
        exact model_relations.fb s t
    · intro s t
      simp only [PositiveRoots.x, MonoidHom.comp_apply]
      simp only [← map_mul]
      apply congrArg b
      apply Subtype.ext
      exact model_relations.dc s t
    · intro s t
      simp only [PositiveRoots.x, MonoidHom.comp_apply]
      simp only [← map_mul]
      apply congrArg b
      apply Subtype.ext
      exact model_relations.eb s t
    · intro s t
      simp only [PositiveRoots.x, MonoidHom.comp_apply]
      simp only [← map_mul]
      apply congrArg b
      apply Subtype.ext
      exact model_relations.fc s t
    · intro s t
      simp only [PositiveRoots.x, MonoidHom.comp_apply]
      simp only [← map_mul]
      apply congrArg b
      apply Subtype.ext
      exact model_relations.fd s t
    · intro s t
      simp only [PositiveRoots.x, MonoidHom.comp_apply]
      simp only [← map_mul]
      apply congrArg b
      apply Subtype.ext
      exact model_relations.fe s t
  · intro l m i t
    simp only [PositiveRoots.x, MonoidHom.comp_apply]
    rw [← map_inv b, ← map_mul b, ← map_mul b]
    exact congrArg b (torus_root_inB l m i t)
  · rw [← map_pow, show rInP ^ 2 = (1 : parabolic₂ (F := F)) from Subtype.ext weylR_sq, map_one]
  · rw [← map_pow, show sInP ^ 2 = (1 : parabolic₁ (F := F)) from Subtype.ext weylS_sq, map_one]
  · intro l m
    simp only [MonoidHom.comp_apply]
    simp only [hr, ← map_mul, ← map_inv]
    apply congrArg q
    apply Subtype.ext
    exact model_relations.r_torus l m
  · intro l m
    simp only [MonoidHom.comp_apply]
    simp only [hl, ← map_mul, ← map_inv]
    apply congrArg p
    apply Subtype.ext
    exact model_relations.s_torus l m
  · intro t
    simp only [PositiveRoots.x, MonoidHom.comp_apply]
    simp only [hr, ← map_mul, ← map_inv]
    apply congrArg q
    apply Subtype.ext
    exact model_relations.rA t
  · intro t
    simp only [PositiveRoots.x, MonoidHom.comp_apply]
    simp only [hr, ← map_mul, ← map_inv]
    apply congrArg q
    apply Subtype.ext
    exact model_relations.rB t
  · intro t
    simp only [PositiveRoots.x, MonoidHom.comp_apply]
    simp only [hr, ← map_mul, ← map_inv]
    apply congrArg q
    apply Subtype.ext
    exact model_relations.rC t
  · intro t
    simp only [PositiveRoots.x, MonoidHom.comp_apply]
    simp only [hr, ← map_mul, ← map_inv]
    apply congrArg q
    apply Subtype.ext
    exact model_relations.rD t
  · intro t
    simp only [PositiveRoots.x, MonoidHom.comp_apply]
    simp only [hr, ← map_mul, ← map_inv]
    apply congrArg q
    apply Subtype.ext
    exact model_relations.rF t
  · intro t
    simp only [PositiveRoots.x, MonoidHom.comp_apply]
    simp only [hl, ← map_mul, ← map_inv]
    apply congrArg p
    apply Subtype.ext
    exact model_relations.sA t
  · intro t
    simp only [PositiveRoots.x, MonoidHom.comp_apply]
    simp only [hl, ← map_mul, ← map_inv]
    apply congrArg p
    apply Subtype.ext
    exact model_relations.sB t
  · intro t
    simp only [PositiveRoots.x, MonoidHom.comp_apply]
    simp only [hl, ← map_mul, ← map_inv]
    apply congrArg p
    apply Subtype.ext
    exact model_relations.sC t
  · intro t
    simp only [PositiveRoots.x, MonoidHom.comp_apply]
    simp only [hl, ← map_mul, ← map_inv]
    apply congrArg p
    apply Subtype.ext
    exact model_relations.sD t
  · intro t
    simp only [PositiveRoots.x, MonoidHom.comp_apply]
    simp only [hl, ← map_mul, ← map_inv]
    apply congrArg p
    apply Subtype.ext
    exact model_relations.sE t
  · intro u
    simp only [PositiveRoots.x, MonoidHom.comp_apply]
    simp only [hr, ← map_mul, ← map_inv]
    apply congrArg q
    apply Subtype.ext
    exact model_relations.long_word u
  · intro u
    simp only [PositiveRoots.x, MonoidHom.comp_apply]
    simp only [hl, ← map_mul, ← map_inv]
    apply congrArg p
    apply Subtype.ext
    exact model_relations.short_word u

omit [CharP F 2] in
private theorem torus_braid (l m u v : Fˣ) :
    ((torus l m * weylR) * (torus u v * weylS)) ^ 6 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;>
    simp [pow_succ, torus, torusEquiv, torusLinear, torusWeights,
      weylR, weylREquiv, weylRLinear, weylRApply,
      weylS, weylSEquiv, weylSLinear, weylSApply] <;> field_simp


private theorem endpoint_agrees {X Y : Type*} [Group X] [Group Y]
    (B P : Subgroup X) (hBP : B ≤ P) (w : X) (hw : w ∈ P)
    (hgen : P = B ⊔ closure {w}) (f : X →* Y) (p : P →* Y)
    (hb : ∀ b : B, f b.val = p (inclusion hBP b))
    (hwp : f w = p ⟨w,hw⟩) (x : P) : f x.val = p x := by
  let K := (f.comp P.subtype).eqLocus p
  have hP : P ≤ K.map P.subtype := by
    apply le_trans hgen.le
    refine sup_le ?_ ((closure_le _).mpr ?_)
    · intro b hb'
      exact ⟨⟨b,hBP hb'⟩,hb ⟨b,hb'⟩,rfl⟩
    · intro z hz
      have hz' : z = w := Set.mem_singleton_iff.mp hz
      subst z
      exact ⟨⟨w,hw⟩,hwp,rfl⟩
  obtain ⟨y,hy,he⟩ := hP x.property
  have hyx : y = x := Subtype.ext he
  exact hyx ▸ hy

private theorem exists_lift_of_braid
    (a : RankTwoAmalgam.Iso (diagram (F := F)) (diagram (F := F)))
    (hb : ((a.right rInP).val * (a.left sInP).val)^6 = 1) :
    ∃ f : Model F →* Model F,
      (∀ x : parabolic₁ (F := F), f x.val = (a.left x).val) ∧
      (∀ x : parabolic₂ (F := F), f x.val = (a.right x).val) := by
  let d := transportedData a
  let R := transported_relations a hb
  let f := d.modelHom R
  let b := Atlas.G2.borel.subtype.comp a.middle.toMonoidHom
  have hfb (x : Atlas.G2.borel (K := F)) : f x.val = b x := by
    have hx : x.val ∈ (modelData (F := F)).borel := (model_borel (F := F)).symm ▸ x.property
    obtain ⟨t,p,he⟩ := (BorelWeylData.mem_borel_iff (modelData (F := F)) (model_relations (F := F)) x.val).mp hx
    have he' : x = (rootInB 0 (.ofAdd (t 0))) * rootInB 1 (.ofAdd (t 1)) *
        rootInB 2 (.ofAdd (t 2)) * rootInB 3 (.ofAdd (t 3)) *
        rootInB 4 (.ofAdd (t 4)) * rootInB 5 (.ofAdd (t 5)) * torusInB p :=
      Subtype.ext he
    rw [he']
    simp only [map_mul, Subgroup.coe_mul]
    change f (modelData.x 0 (t 0)) * f (modelData.x 1 (t 1)) *
      f (modelData.x 2 (t 2)) * f (modelData.x 3 (t 3)) *
      f (modelData.x 4 (t 4)) * f (modelData.x 5 (t 5)) * f (torusHom p) = _
    simp only [f, BorelWeylData.modelHom_root, BorelWeylData.modelHom_torus]
    rfl
  refine ⟨f,?_,?_⟩
  · exact endpoint_agrees Atlas.G2.borel parabolic₁ borel_le_parabolic₁ weylS sInP.property rfl f
      (parabolic₁.subtype.comp a.left.toMonoidHom)
      (fun b => (hfb b).trans (left_borel a b)) (BorelWeylData.modelHom_s d R)
  · exact endpoint_agrees Atlas.G2.borel parabolic₂ borel_le_parabolic₂ weylR rInP.property rfl f
      (parabolic₂.subtype.comp a.right.toMonoidHom)
      (fun b => (hfb b).trans (right_borel a b)) (BorelWeylData.modelHom_r d R)

open Atlas.G2.LieAutomorphismExtensions.InnerFieldCoverage
open Atlas.G2.EvenBorelTorus

omit [CharP F 2] in
private theorem image_weyl (P : Subgroup (Model F)) (hTP : splitTorus ≤ P)
    (w : Model F) (hw : w ∈ P)
    (hwN : w ∈ normalizer (splitTorus (K := F) : Set (Model F)))
    (hwT : w ∉ splitTorus)
    (hcover : RankOneTorusNormalizerCover P w)
    (a : MulAut P) (hT : (splitTorus.subgroupOf P).map a.toMonoidHom = splitTorus.subgroupOf P) :
    ∃ l m : Fˣ, (a ⟨w,hw⟩).val = torus l m * w := by
  have hn : (⟨w,hw⟩ : P) ∈ normalizer (splitTorus.subgroupOf P : Set P) := by
    rw [← subgroupOf_normalizer_eq hTP]
    exact hwN
  have hn' : a ⟨w,hw⟩ ∈ normalizer (splitTorus.subgroupOf P : Set P) := by
    have he : (normalizer (splitTorus.subgroupOf P : Set P)).map a.toMonoidHom =
        normalizer (splitTorus.subgroupOf P : Set P) := by
      rw [map_equiv_normalizer_eq,hT]
    rw [←he]
    exact mem_map_of_mem _ hn
  rw [← subgroupOf_normalizer_eq hTP] at hn'
  rcases hcover (a ⟨w,hw⟩).val (a ⟨w,hw⟩).property hn' with ht | he
  · have ht' : a ⟨w,hw⟩ ∈ splitTorus.subgroupOf P := ht
    rw [←hT] at ht'
    obtain ⟨v,hv,hv'⟩ := ht'
    have hvw : (v : Model F) = w := congrArg Subtype.val (a.injective hv')
    change v.val ∈ splitTorus at hv
    exact (hwT (hvw ▸ hv)).elim
  · exact he

omit [CharP F 2] in
private theorem endpoint_torus
    (B P T : Subgroup (Model F)) (hTB : T ≤ B) (hBP : B ≤ P)
    (a : MulAut P) (b : MulAut B)
    (hab : ∀ x : B, (a (inclusion hBP x)).val = (b x).val)
    (hb : (T.subgroupOf B).map b.toMonoidHom = T.subgroupOf B) :
    (T.subgroupOf P).map a.toMonoidHom = T.subgroupOf P := by
  apply le_antisymm
  · rintro y ⟨x,hx,rfl⟩
    have he := hab ⟨x.val,hTB hx⟩
    change (a x).val = (b ⟨x.val,hTB hx⟩).val at he
    change (a x).val ∈ T
    rw [he]
    exact hb.le (mem_map_of_mem b.toMonoidHom
      (show (⟨x.val,hTB hx⟩ : B) ∈ T.subgroupOf B from hx))
  · intro x hx
    obtain ⟨y,hy,he⟩ := hb.ge (show (⟨x.val,hTB hx⟩ : B) ∈ T.subgroupOf B from hx)
    refine ⟨inclusion hBP y,hy,?_⟩
    apply Subtype.ext
    exact (hab y).trans (congrArg Subtype.val he)

private theorem braid_of_torus (hq : 2 < Nat.card F)
    [Finite F] (a : RankTwoAmalgam.Iso (diagram (F := F)) (diagram (F := F)))
    (hT : (complement (F := F)).map a.middle.toMonoidHom = complement) :
    ((a.right rInP).val * (a.left sInP).val)^6 = 1 := by
  have hl := endpoint_torus Atlas.G2.borel parabolic₁ splitTorus le_sup_right borel_le_parabolic₁
    a.left a.middle (fun b => congrArg Subtype.val (a.left_commutes b)) hT
  have hr := endpoint_torus Atlas.G2.borel parabolic₂ splitTorus le_sup_right borel_le_parabolic₂
    a.right a.middle (fun b => congrArg Subtype.val (a.right_commutes b)) hT
  obtain ⟨l,m,hr⟩ := image_weyl parabolic₂
    ((show splitTorus ≤ Atlas.G2.borel (K := F) from le_sup_right).trans borel_le_parabolic₂)
    weylR rInP.property weylR_mem_torusNormalizer weylR_not_mem_torus
    (rankOne_torusNormalizerCover_long hq) a.right hr
  obtain ⟨u,v,hl⟩ := image_weyl parabolic₁
    ((show splitTorus ≤ Atlas.G2.borel (K := F) from le_sup_right).trans borel_le_parabolic₁)
    weylS sInP.property weylS_mem_torusNormalizer weylS_not_mem_torus
    (rankOne_torusNormalizerCover_short hq) a.left hl
  exact sixth_power_of_images hr hl (torus_braid l m u v)

variable [Finite F]

private theorem torus_hall :
    IsHallSubgroup {p : Nat.Primes | p.val ≠ 2} (complement (F := F)) := by
  refine ⟨?_, ?_⟩
  · intro p hp he
    have hc : Nat.card (complement (F := F)) = Nat.card (splitTorus (K := F)) :=
      Nat.card_congr (subgroupOfEquivOfLe
        (show splitTorus (K := F) ≤ Atlas.G2.borel from le_sup_right)).toEquiv
    rw [he, hc] at hp
    exact card_torus_odd.not_two_dvd_nat hp
  · intro p hp hne
    rw [radical_isComplement.index_eq_card] at hp
    obtain ⟨n, hn⟩ := radical_isTwoGroup (F := F) |>.exists_card_eq
    rw [hn] at hp
    exact hne ((Nat.prime_dvd_prime_iff_eq p.property Nat.prime_two).mp
      (p.property.dvd_of_dvd_pow hp))

/-- A compatible automorphism of the two full G₂ endpoints extends to the
actual octonion group; the full middle and both endpoint maps are retained. -/
theorem native_lifts (hq : 2 < Nat.card F)
    (a : RankTwoAmalgam.Iso (diagram (F := F)) (diagram (F := F))) :
    ∃ f : Model F →* Model F,
      (∀ x : parabolic₁ (F := F), f x.val = (a.left x).val) ∧
      (∀ x : parabolic₂ (F := F), f x.val = (a.right x).val) := by
  obtain ⟨g,hg⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable
    (DerivedNormalizerSolvable.isSolvable_borel (F := F))
    (torus_hall.map_mulAut a.middle) torus_hall
  let b := corrected parabolic₁ Atlas.G2.borel parabolic₂ borel_le_parabolic₁ borel_le_parabolic₂ a g
  have hT : (complement (F := F)).map b.middle.toMonoidHom = complement :=
    corrected_map parabolic₁ Atlas.G2.borel parabolic₂ borel_le_parabolic₁ borel_le_parabolic₂ a g _ hg
  obtain ⟨f,hl,hr⟩ := exists_lift_of_braid b (braid_of_torus hq b hT)
  exact undo_corrected parabolic₁ Atlas.G2.borel parabolic₂ borel_le_parabolic₁ borel_le_parabolic₂
    a g f hl hr

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.G2NativeLift
