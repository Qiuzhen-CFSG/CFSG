module
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.EndpointAction.Path
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.NormalizerCentralizer
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.ParabolicFamily.Colors.Source
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.CoreReflection
/-!
# The original endpoint normalizer fixes all six colored parabolics

The genuine endpoint no-switch theorem makes N_F1(⟨z,u⟩) centralize
⟨z,u⟩ pointwise. Common-cover short-path transport puts that normalizer
inside the fourth parabolic, giving a fixed member of the u-colored pair.
The actual quaternion reflection fixes F1 and z while sending u to zu;
it transports this member to a zu-colored parabolic containing the same
normalizer. F1 itself supplies the z-colored member. Each color family has
two elements, so fixing its one specified member fixes both.

The final theorem acts on the unchanged original six-member family through
its literal conjugation action. Its inputs are the original source choices
and compatible endpoint marking; no action-kernel, Small, or global completion
recognition hypothesis is required. This is the source action used in the
J.4.10 adjacency reduction, printed pp.443--445.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.EndpointAction
open ParabolicFamily MarkedInverter MarkedNormalizer Centralizers Centralizers.Choices
open Tits.ExceptionalParabolics.FullRee Tits.ExceptionalParabolics.FullRee.LongRootPaths
open ChapterF.SourceCompletion.BinaryRee

private theorem fixes_two_set {X:Type*} (S:Set X) (hc:Nat.card S=2)
    (f:X→X) (hf:Function.Injective f) (hS:∀x∈S,f x∈S)
    (a:X) (ha:a∈S) (hfa:f a=a) : ∀x∈S,f x=x := by
  let g:S→S := fun x=>⟨f x,hS x x.property⟩
  have hg:Function.Injective g := fun x y h=>Subtype.ext (hf (congrArg Subtype.val h))
  let a':S:=⟨a,ha⟩
  have hga:g a'=a':=Subtype.ext hfa
  obtain ⟨b,hba,hall⟩ := (Nat.card_eq_two_iff' a').mp hc
  intro x hx
  have hh:g ⟨x,hx⟩=⟨x,hx⟩ := by
    by_cases he:(⟨x,hx⟩:S)=a'
    · rw [he,hga]
    · have hb:g b=b:=hall _ (fun hh=>hba (hg (hh.trans hga.symm)))
      rw [hall _ he,hb]
  exact congrArg Subtype.val hh

private theorem conjugation_injective {G:Type*} [Group G] (n:G) :
    Function.Injective (fun E:Subgroup G=>E.conjBy n) := by
  intro E F h
  have hh:=congrArg (fun H:Subgroup G=>H.conjBy n⁻¹) h
  simpa only [conjBy_inv] using hh

variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G}
  {K:Type*} [Group K] (q:Completion K)
  (p:Plane d) (s:SourceChoice p) (c:Choices d) (B5:Sylow 5 d.toTypeRuSetup.H)
  (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
  (e:first≃*p.F₁ B5) (f:K→*G)
  (hleft:∀a:first,f (q.left a)=(e a:G)) (hz:(e modelZ:G)=c.z)
  (hfive:(zpowers modelRotation).map ((p.F₁ B5).subtype.comp e.toMonoidHom)=B5Image B5)

include hz in
private theorem pair_le_endpoint : pairSpan c.z (sourceU e) ≤ p.F₁ B5 :=
  sup_le (zpowers_le.mpr (hz ▸ (e modelZ).property)) (zpowers_le.mpr (e modelU).property)

include hz in
private theorem endpointNormalizer_le_centralizer :
    p.F₁ B5 ⊓ normalizer (pairSpan c.z (sourceU e):Set G) ≤
      centralizer (pairSpan c.z (sourceU e):Set G) :=
  source_plane_normalizer_centralizes c e hz

include hleft hz in
/-- The actual endpoint plane normalizer lies in the original fourth parabolic. -/
theorem endpointNormalizer_le_fourth :
    p.F₁ B5 ⊓ normalizer (pairSpan c.z (sourceU e):Set G) ≤
      (p.F₁ B5).conjBy (f (completionFourthWord q)) := by
  apply (le_inf inf_le_left ?_).trans (source_centralizer_le_fourth q e f hleft)
  exact (endpointNormalizer_le_centralizer p c B5 e hz).trans
    (centralizer_le (Set.singleton_subset_iff.mpr (mem_sup_right (mem_zpowers _))))

include hleft hz in
/-- The fourth-word conjugate is an actual u-colored member containing the plane. -/
theorem fourth_mem_colorFamily :
    (p.F₁ B5).conjBy (f (completionFourthWord q)) ∈
      colorFamily p B5 c.z (sourceU e) (sourceU e) := by
  refine ⟨f (completionFourthWord q),rfl,source_fourth_conjugates q e f hleft c.z hz,?_⟩
  exact (le_inf (pair_le_endpoint p c B5 e hz) (pairSpan c.z (sourceU e)).le_normalizer).trans
    (endpointNormalizer_le_fourth q p c B5 e f hleft hz)

private theorem normalizes_pair_of_images (z u n:G)
    (hz:n*z*n⁻¹∈pairSpan z u) (hu:n*u*n⁻¹∈pairSpan z u) :
    n∈normalizer (pairSpan z u:Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rw [pairSpan,Subgroup.map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
    exact sup_le (zpowers_le.mpr hz) (zpowers_le.mpr hu)
  · rw [card_map_of_injective (MulAut.conj n).injective]

include q s hi f hleft hz hfive in
/-- Every actor in the original endpoint plane normalizer fixes each member of each color. -/
theorem endpointNormalizer_fixes_color (v:G) (hv:v∈colors c.z (sourceU e))
    (n:G) (hn:n∈p.F₁ B5 ⊓ normalizer (pairSpan c.z (sourceU e):Set G))
    (E:Subgroup G) (hE:E∈colorFamily p B5 c.z (sourceU e) v) : E.conjBy n=E := by
  let V:=pairSpan c.z (sourceU e)
  let N:=p.F₁ B5 ⊓ normalizer (V:Set G)
  have hNC:N≤centralizer (V:Set G):=endpointNormalizer_le_centralizer p c B5 e hz
  have hcolor (w:G) (hw:w∈colors c.z (sourceU e))
      (E0:Subgroup G) (h0:E0∈colorFamily p B5 c.z (sourceU e) w) (hNE:N≤E0) :
      ∀D∈colorFamily p B5 c.z (sourceU e) w,D.conjBy n=D := by
    have hnw:n*w*n⁻¹=w := mul_inv_eq_of_eq_mul
      ((hNC hn) w ((colors_iff p B5 c e hz w).mp hw).1).symm
    apply fixes_two_set (colorFamily p B5 c.z (sourceU e) w)
      (source_color_family_card q p s c B5 hi e f hleft hz hfive w hw)
      (fun D=>D.conjBy n) (conjugation_injective n)
      (fun D hD=>by simpa only [hnw] using color_conjugate_mem p B5 c.z (sourceU e) n hn.2 hD)
      E0 h0
    exact mem_normalizer_iff_map_conj_eq.mp (E0.le_normalizer (hNE hn))
  have hzcolor:c.z∈colors c.z (sourceU e):=by simp [colors]
  have hucolor:sourceU e∈colors c.z (sourceU e):=by simp [colors]
  have hf0:p.F₁ B5∈colorFamily p B5 c.z (sourceU e) c.z :=
    ⟨1,(conjBy_one _).symm,by simp,pair_le_endpoint p c B5 e hz⟩
  let E0:Subgroup G:=(p.F₁ B5).conjBy (f (completionFourthWord q))
  have h0:E0∈colorFamily p B5 c.z (sourceU e) (sourceU e):=
    fourth_mem_colorFamily q p c B5 e f hleft hz
  have hN0:N≤E0:=endpointNormalizer_le_fourth q p c B5 e f hleft hz
  obtain ⟨r,_,_,hrz,hru,hrfix⟩ := source_parabolic_reflection q p s c B5 hi e f hleft hz hfive
  have hrF:r∈normalizer (p.F₁ B5:Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact hrfix (p.F₁ B5) ⟨1,by simp only [coe_one,conjBy_one]⟩
  have hrV:r∈normalizer (V:Set G) := normalizes_pair_of_images c.z (sourceU e) r
    (by rw [hrz];exact mem_sup_left (mem_zpowers _))
    (by rw [hru];exact mul_mem_sup (mem_zpowers _) (mem_zpowers _))
  have hN1:N≤E0.conjBy r := by
    intro a ha
    have hai:r⁻¹*a*r∈N := by
      change r⁻¹*a*r∈p.F₁ B5 ∧ r⁻¹*a*r∈normalizer (V:Set G)
      constructor
      · simpa only [inv_inv] using (mem_normalizer_iff.mp
          ((normalizer (p.F₁ B5:Set G)).inv_mem hrF) a).mp ha.1
      · exact (normalizer (V:Set G)).mul_mem
          ((normalizer (V:Set G)).mul_mem ((normalizer (V:Set G)).inv_mem hrV) ha.2) hrV
    refine ⟨r⁻¹*a*r,hN0 hai,?_⟩
    change r*(r⁻¹*a*r)*r⁻¹=a
    group
  have h1:E0.conjBy r∈colorFamily p B5 c.z (sourceU e) (c.z*sourceU e) := by
    simpa only [hru] using color_conjugate_mem p B5 c.z (sourceU e) r hrV h0
  simp only [colors,Set.mem_insert_iff,Set.mem_singleton_iff] at hv
  rcases hv with rfl|rfl|rfl
  · exact hcolor _ hzcolor _ hf0 inf_le_left E hE
  · exact hcolor _ hucolor _ h0 hN0 E hE
  · exact hcolor _ (by simp [colors]) _ h1 hN1 E hE

include q s hi f hleft hz hfive in
/-- Pointwise fixation of the original six-member parabolic family. -/
theorem endpointNormalizer_fixes_global
    (n:G) (hn:n∈p.F₁ B5 ⊓ normalizer (pairSpan c.z (sourceU e):Set G))
    (E:Subgroup G) (hE:E∈globalFamily p B5 c.z (sourceU e)) : E.conjBy n=E := by
  obtain ⟨v,hv,hE⟩:=hE
  exact endpointNormalizer_fixes_color q p s c B5 hi e f hleft hz hfive v hv n hn E hE
include q s hi f hleft hz hfive in
/-- The unchanged canonical normalizer action is trivial on the endpoint normalizer. -/
theorem endpointNormalizer_action_trivial
    (n:G) (hn:n∈p.F₁ B5 ⊓ normalizer (pairSpan c.z (sourceU e):Set G))
    (E:globalFamily p B5 c.z (sourceU e)) :
    (normalizerAction p B5 c e hz).smul ⟨n,hn.2⟩ E=E := by
  apply Subtype.ext
  change E.val.conjBy n=E.val
  exact endpointNormalizer_fixes_global q p s c B5 hi e f hleft hz hfive n hn E.val E.property

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.EndpointAction
