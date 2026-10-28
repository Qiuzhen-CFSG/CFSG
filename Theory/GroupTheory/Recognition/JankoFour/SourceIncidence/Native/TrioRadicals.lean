module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Native.LineOrbit
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Native.Coplanarity
public import Theory.Mathieu.M24.ChapterHStabilizers.TrioAction.Transport

/-!
# Native trio radical intersections and noncoplanar orbits

The intrinsic two-core has the existing zero-sum translation coordinates on
three octads. Five explicit translations give distinct images of each of the
two already classified noncoplanar representatives. For intersections, a
64-translation check uses octad preservation and semiregularity on each
octad; its only possible nonidentity survivor fixes one point but moves
another in the same octad. The existing orbital transporters give both
conclusions for arbitrary trios, with their literal intrinsic cores.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (3.12), p.596,
applied to (5.5) and (5.7), p.601. No new catalogue is enumerated.
The complete representative probe took 46.45 s including import preparation,
with peak RSS 2,162,444 KiB. All finite checks use kernel reduction.
-/

@[expose] public section
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
open MathieuCode.TrioCalculation
open scoped Pointwise Matrix
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeTrioRadicals
open SourceCycleBase.Native NativeLineOrbit

 theorem core_smul (g : M24) (l : Line) :
    M24ChapterHStabilizers.TrioAction.coreAt (g • l) = (M24ChapterHStabilizers.TrioAction.coreAt l).map (MulAut.conj g).toMonoidHom := by
  change (trioStabilizer (g • l)).pCoreIn 2 =
    ((trioStabilizer l).pCoreIn 2).map (MulAut.conj g).toMonoidHom
  rw [Subgroup.map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective]
  congr 1
  exact MulAction.stabilizer_smul_eq_stabilizer_map_conj g l.parts

private theorem normal_form (l m : Line) (hn : ¬ Coplanar l m) :
    ∃ r : Fin 2, ∃ g : M24, g • standardTrio = l ∧
      g • rootLine ⟨r.val+3,by omega⟩ = m := by
  obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq M24 standardTrio l
  obtain ⟨i,hi,_⟩ := partition standardTrio (g⁻¹ • m)
  have hil : 2 < i.val := by
    by_contra hh
    have hc := (NativeCoplanarity.coplanar_iff _ _).mpr ⟨i,by omega,hi⟩
    exact hn (coplanar_transport g rfl (by simp) hc)
  obtain ⟨b,hb,hbm⟩ := transitive standardTrio (rootLine i) (g⁻¹ • m) i
    ((root_delta_iff i i).mpr rfl) hi
  refine ⟨⟨i.val-3,by omega⟩,g*b,?_,?_⟩
  · rw [mul_smul,hb]
  · have he : (⟨(i.val-3)+3,by omega⟩ : Fin 5) = i := Fin.ext (by dsimp; omega)
    rw [he,mul_smul,hbm,smul_inv_smul]

private def first : Fin 5 → Vector := ![0,0,0,0,![1,0,0]]
private def second : Fin 5 → Vector := ![0,![1,0,0],![0,1,0],![1,1,0],0]
private noncomputable def mover (i : Fin 5) : M24ChapterHStabilizers.TrioAction.core :=
  ⟨((pairedTranslation 1 (first i)) * (pairedTranslation 0 (second i))).val,
    ⟨_,(pCore 2 _).mul_mem (pairedTranslation_mem_twoCore _ _)
      (pairedTranslation_mem_twoCore _ _),rfl⟩⟩
private noncomputable def moverFn (i : Fin 5) (x : Fin 24) : Fin 24 :=
  pointTable (coordinates x).1 (vectorIndex ((coordinates x).2 +
    (if (coordinates x).1 = 0 then 0 else second i) +
    (if (coordinates x).1 = 1 then 0 else first i)))
private theorem mover_apply (i : Fin 5) (x : Fin 24) : (mover i).val.val x = moverFn i x := by
  obtain ⟨⟨j,w⟩,rfl⟩ := point.surjective x
  change (pairedTranslation 1 (first i)).val.val
    ((pairedTranslation 0 (second i)).val.val (point (j,w))) = _
  rw [pairedTranslation_point,pairedTranslation_point]
  simp only [moverFn,coordinates_point]
  rfl

private theorem five_check (r : Fin 2) : Function.Injective (fun i : Fin 5 =>
    (FarOrbit.parts (rootMasks ⟨r.val+3,by omega⟩)).image
      (fun A => A.image (moverFn i))) := by
  revert r
  decide +kernel

private theorem five_root (r : Fin 2) : Function.Injective (fun i : Fin 5 =>
    ((mover i).val : M24) • rootLine ⟨r.val+3,by omega⟩) := by
  intro i j he
  apply five_check r
  have hh := congrArg Trio.parts he
  change (mover i).val • (rootLine _).parts = (mover j).val • (rootLine _).parts at hh
  rw [root_parts] at hh
  change (FarOrbit.parts (rootMasks _)).image (fun A => A.image (mover i).val.val) =
    (FarOrbit.parts (rootMasks _)).image (fun A => A.image (mover j).val.val) at hh
  simpa only [show (mover i).val.val = moverFn i from funext (mover_apply i),
    show (mover j).val.val = moverFn j from funext (mover_apply j)] using hh

/-- A noncoplanar trio has at least five distinct images under the literal
intrinsic two-core of the first trio's stabilizer (AS91 (3.12)(2)). -/
theorem five_images (l m : Line) (hn : ¬ Coplanar l m) :
    ∃ f : Fin 5 → M24ChapterHStabilizers.TrioAction.coreAt l, Function.Injective (fun i => (f i).val • m) := by
  obtain ⟨r,g,hl,hm⟩ := normal_form l m hn
  have hcore : M24ChapterHStabilizers.TrioAction.core.map (MulAut.conj g).toMonoidHom = M24ChapterHStabilizers.TrioAction.coreAt l :=
    M24ChapterHStabilizers.TrioAction.core_map g (congrArg Trio.parts hl)
  let f : Fin 5 → M24ChapterHStabilizers.TrioAction.coreAt l := fun i => ⟨g*(mover i).val*g⁻¹,by
    rw [←hcore]
    exact ⟨(mover i).val,(mover i).property,rfl⟩⟩
  refine ⟨f,?_⟩
  intro i j he
  apply five_root r
  change (g*(mover i).val*g⁻¹) • m = (g*(mover j).val*g⁻¹) • m at he
  rw [←hm,mul_smul,mul_smul,inv_smul_smul,mul_smul,mul_smul,inv_smul_smul] at he
  exact MulAction.injective g he

private theorem standard_part_action (g : M24)
    (hg : g ∈ M24ChapterHStabilizers.TrioAction.core)
    (A : Finset (Fin 24)) (hA : A ∈ standardTrio.parts) :
    g • A = A ∧ ∀ x ∈ A, g.val x = x → ∀ y ∈ A, g.val y = y := by
  obtain ⟨k,hk,rfl⟩ := hg
  obtain ⟨t,ht⟩ := (mem_standardTwoCore_iff k).mp hk
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
  have acts (v : Vector) := ht i v
  constructor
  · apply Finset.eq_of_subset_of_card_le ?_ (by simp)
    intro x hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_smul_finset.mp hx
    obtain ⟨⟨j,v⟩,rfl⟩ := point.surjective b
    have hj : j = i := (point_mem_octad_iff j i v).mp hb
    subst j
    change k.val.val (point (i,v)) ∈ standardTrioOctad i
    rw [ht]
    exact point_mem_octad i (v+t i)
  · intro x hx hfix y hy
    obtain ⟨⟨j,v⟩,rfl⟩ := point.surjective x
    have hj : j = i := (point_mem_octad_iff j i v).mp hx
    subst j
    have hzero : t i = 0 := by
      have hh := congrArg Prod.snd (point.injective ((ht i v).symm.trans hfix))
      exact add_left_cancel (hh.trans (add_zero v).symm)
    obtain ⟨⟨j,w⟩,rfl⟩ := point.surjective y
    have hj : j = i := (point_mem_octad_iff j i w).mp hy
    subst j
    change k.val.val (point (i,w)) = point (i,w)
    rw [ht,hzero,add_zero]

/-- Native trio translations are semiregular on each octad separately. -/
theorem part_action (l : Line) (g : M24)
    (hg : g ∈ M24ChapterHStabilizers.TrioAction.coreAt l)
    (A : Finset (Fin 24)) (hA : A ∈ l.parts) :
    g • A = A ∧ ∀ x ∈ A, g.val x = x → ∀ y ∈ A, g.val y = y := by
  obtain ⟨k,hk,hcore⟩ := M24ChapterHStabilizers.TrioAction.exists_core_conjugator l
  rw [←hcore] at hg
  obtain ⟨u,hu,rfl⟩ := hg
  rw [←hk] at hA
  obtain ⟨B,hB,rfl⟩ := Finset.mem_smul_finset.mp hA
  obtain ⟨hpres,hreg⟩ := standard_part_action u hu B hB
  constructor
  · change (k*u*k⁻¹) • (k • B) = k • B
    rw [mul_smul,mul_smul,inv_smul_smul,hpres]
  · intro x hx hfix y hy
    obtain ⟨b,hb,rfl⟩ := Finset.mem_smul_finset.mp hx
    obtain ⟨c,hc,rfl⟩ := Finset.mem_smul_finset.mp hy
    change (k*u*k⁻¹) • (k • c) = k • c
    have huf : u.val b = b := by
      change (k*u*k⁻¹) • (k • b) = k • b at hfix
      rw [mul_smul,mul_smul,inv_smul_smul] at hfix
      exact MulAction.injective k hfix
    rw [mul_smul,mul_smul,inv_smul_smul]
    exact congrArg (k • ·) (hreg b hb huf c hc)

private noncomputable def translationFn (v w : Vector) (x : Fin 24) : Fin 24 :=
  pointTable (coordinates x).1 (vectorIndex ((coordinates x).2 +
    (![v,w,v+w] : Fin 3 → Vector) (coordinates x).1))

private theorem core_translation (g : M24)
    (hg : g ∈ M24ChapterHStabilizers.TrioAction.core) :
    ∃ v w : Vector, ∀ x, g.val x = translationFn v w x := by
  obtain ⟨k,hk,rfl⟩ := hg
  obtain ⟨t,ht⟩ := M24ChapterHStabilizers.TrioAction.translationEquiv.surjective ⟨k,hk⟩
  refine ⟨t.toAdd.val 0,t.toAdd.val 1,?_⟩
  intro x
  obtain ⟨⟨i,v⟩,rfl⟩ := point.surjective x
  have hh := M24ChapterHStabilizers.TrioAction.translation_point t i v
  rw [show M24ChapterHStabilizers.TrioAction.translation t = ⟨k,hk⟩ from ht] at hh
  change k.val.val (point (i,v)) = _
  change k.val.val (point (i,v)) = _ at hh
  rw [hh]
  simp only [translationFn,coordinates_point]
  rw [show (![t.toAdd.val 0,t.toAdd.val 1,t.toAdd.val 0+t.toAdd.val 1] : Fin 3 → Vector) i =
      t.toAdd.val i from by
        fin_cases i <;> simp [M24ChapterHStabilizers.TrioAction.translationSpace_last]]
  rfl

private theorem intersection_check (r : Fin 2) (v w : Vector)
    (hp : ∀ j : Fin 3,
      (FarOrbit.support (rootMasks ⟨r.val+3,by omega⟩ j)).image (translationFn v w) =
        FarOrbit.support (rootMasks ⟨r.val+3,by omega⟩ j))
    (hf : translationFn v w 1 = 1 → translationFn v w 4 = 4) : v = 0 ∧ w = 0 := by
  revert r v w
  decide +kernel

private theorem root_anchor_check (r : Fin 2) :
    (1 : Fin 24) ∈ FarOrbit.support (rootMasks ⟨r.val+3,by omega⟩ 0) ∧
    (4 : Fin 24) ∈ FarOrbit.support (rootMasks ⟨r.val+3,by omega⟩ 0) := by
  revert r; decide +kernel

private theorem root_intersection (r : Fin 2) (g : M24)
    (hg : g ∈ M24ChapterHStabilizers.TrioAction.core)
    (hk : g ∈ M24ChapterHStabilizers.TrioAction.coreAt (rootLine ⟨r.val+3,by omega⟩)) : g = 1 := by
  obtain ⟨v,w,hvw⟩ := core_translation g hg
  have mempart (j : Fin 3) : FarOrbit.support (rootMasks ⟨r.val+3,by omega⟩ j) ∈
      (rootLine ⟨r.val+3,by omega⟩).parts := by
    rw [root_parts]
    apply Finset.mem_image.mpr
    refine ⟨_,?_,rfl⟩
    fin_cases j <;> simp [FarOrbit.maskParts]
  have hact (j : Fin 3) := part_action _ g hk _ (mempart j)
  have hn := intersection_check r v w (fun j => by
    have hh := (hact j).1
    change (FarOrbit.support (rootMasks _ j)).image g.val = _ at hh
    rwa [show g.val = translationFn v w from funext hvw] at hh)
    (fun hx => by
      have hx' : g.val 1 = 1 := (hvw 1).trans hx
      have hxmem : (1 : Fin 24) ∈ FarOrbit.support (rootMasks ⟨r.val+3,by omega⟩ 0) := by
        exact (root_anchor_check r).1
      have hymem : (4 : Fin 24) ∈ FarOrbit.support (rootMasks ⟨r.val+3,by omega⟩ 0) := by
        exact (root_anchor_check r).2
      exact (hvw 4).symm.trans ((hact 0).2 1 hxmem hx' 4 hymem))
  apply Subtype.ext
  apply Equiv.ext
  intro x
  rw [hvw,hn.1,hn.2]
  simp only [translationFn,zero_add]
  have hz : (![0,0,0] : Fin 3 → Vector) = 0 := by decide
  rw [hz,Pi.zero_apply,add_zero]
  exact point_coordinates x

/-- Two noncoplanar trios have trivial intrinsic-radical intersection,
with both radicals embedded in the same native M24 (AS91 (3.12)(1)). -/
theorem intersection_trivial (l m : Line) (hn : ¬ Coplanar l m)
    (g : M24) (hgl : g ∈ M24ChapterHStabilizers.TrioAction.coreAt l)
    (hgm : g ∈ M24ChapterHStabilizers.TrioAction.coreAt m) : g = 1 := by
  obtain ⟨r,k,hl,hm⟩ := normal_form l m hn
  have hcl : M24ChapterHStabilizers.TrioAction.core.map (MulAut.conj k).toMonoidHom =
      M24ChapterHStabilizers.TrioAction.coreAt l :=
    M24ChapterHStabilizers.TrioAction.core_map k (congrArg Trio.parts hl)
  rw [←hcl] at hgl
  obtain ⟨u,hu,rfl⟩ := hgl
  rw [←hm,core_smul] at hgm
  have hum : u ∈ M24ChapterHStabilizers.TrioAction.coreAt (rootLine ⟨r.val+3,by omega⟩) := by
    obtain ⟨v,hv,he⟩ := hgm
    exact (MulAut.conj k).injective he ▸ hv
  rw [root_intersection r u hu hum,map_one]
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeTrioRadicals
