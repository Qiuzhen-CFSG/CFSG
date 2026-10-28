module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionSourceCore
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionEndpointsRoots
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionEndpointsTransport
public import Theory.GroupTheory.SpecificGroups.SymmetricFourCoreClasses

/-!
# The original endpoint root-class counts

Each graph centralizer is E4 × S4, whose two-core has four central singleton
orbits and four orbits of size three. In the point endpoint the central pair
is (f,z) and the noncentral representative is t; the established source
fusions select two singletons and one triple. In the plane endpoint the
central pair is (f,t) and representative z; three triples are selected.
Thus the literal A1 and A2 root-class intersections have orders five and nine.
In A2 the short class and its root translate meet in the exact pair t,tz;
the literal matrix marking excludes a trivial central coordinate for the root.

The short involution centralizes E2 because E2 preserves [Q2,f]=<t>.
It belongs to A1 because it centralizes Tf, which contains the self-centralizing
point two-core. These facts retain the original completion maps and avoid
requiring a separate coordinate marking for either abstract endpoint model.
Source: Aschbacher--Smith F.5.3(8), printed p.300; consumed by F.5.4--5.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)

omit [Finite G] in
theorem source_short_mem_E (b : Bool) : sourceMarkedShort c i∈E c i b :=
  ⟨sylowImage_le_M c i b (source_short_mem_sylowImage c i),
    mem_centralizer_singleton_iff.mpr (source_short_commutes_graph c i).eq⟩

theorem source_short_centralizes_E_plane (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) (x : G) (hx : x∈E c i true) :
    x*sourceMarkedShort c i=sourceMarkedShort c i*x := by
  have hQ : x∈normalizer (Q c i true : Set G) := by
    rw [normalizer_Q_eq_plane c i z h]
    exact hx.1
  have hf : x∈normalizer (zpowers (Source.graphElement c i) : Set G) := by
    rw [normalizer_zpowers_eq_centralizer_of_order_two _ (source_graph_order c i h.embedding_injective)]
    exact hx.2
  have ht : x∈normalizer (zpowers (sourceMarkedShort c i) : Set G) := by
    rw [←source_short_commutator c i h.embedding_injective,mem_normalizer_iff_map_conj_eq]
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp hQ,mem_normalizer_iff_map_conj_eq.mp hf]
  rw [normalizer_zpowers_eq_centralizer_of_order_two _ (source_short_order c i h.embedding_injective)] at ht
  exact mem_centralizer_singleton_iff.mp ht

omit [Finite G] in
theorem source_graph_ne_short (hi : Function.Injective i) :
    Source.graphElement c i≠sourceMarkedShort c i := by
  intro he
  have hf : (i.comp c.right) ((Extension.amalgam 1 hn).right
      UnitaryTwo.GraphCentralizer.graphInvolution) = Source.graphElement c i :=
    endpointMap_graph c i true
  have he' := (hi.comp c.right_injective) (hf.trans he)
  have he'' := congrArg (fun x : Extension.plane 1 hn => x.val.right) he'
  change (Multiplicative.ofAdd (1 : ZMod 2))=1 at he''
  exact (by decide : (Multiplicative.ofAdd (1 : ZMod 2))≠1) he''


local notation "FModel" => SymmetricFourCoreClasses.Model

omit [Finite G] in
private theorem endpoint_core_image (b : Bool) (e : E c i b ≃* FModel) :
    SymmetricFourCoreClasses.Core.map ((E c i b).subtype.comp e.symm.toMonoidHom)=A c i b := by
  rw [←map_map,SymmetricFourCoreClasses.core_eq,pCore_map_iso]
  rfl

omit [Finite G] in
private theorem endpoint_core_selfcentralizer (b : Bool) (e : E c i b ≃* FModel) :
    centralizer (pCore 2 (E c i b) : Set (E c i b))=pCore 2 (E c i b) := by
  ext x
  constructor
  · intro hx
    have he : e x∈centralizer (SymmetricFourCoreClasses.Core : Set FModel) := by
      rintro y hy
      have hye : e.symm y∈pCore 2 (E c i b) := by
        rw [←pCore_map_iso 2 e.symm,←SymmetricFourCoreClasses.core_eq]
        exact mem_map_of_mem _ hy
      have hh := mem_centralizer_iff.mp hx _ hye
      have hh' := congrArg e hh
      simpa only [map_mul,e.apply_symm_apply] using hh'
    rw [SymmetricFourCoreClasses.centralizer_core,SymmetricFourCoreClasses.core_eq,
      ←pCore_map_iso 2 e] at he
    exact (mem_map_iff_mem e.injective).mp he
  · intro hx
    have he : e x∈SymmetricFourCoreClasses.Core := by
      rw [SymmetricFourCoreClasses.core_eq,←pCore_map_iso 2 e]
      exact mem_map_of_mem _ hx
    rw [←SymmetricFourCoreClasses.centralizer_core] at he
    intro y hy
    apply e.injective
    simpa only [map_mul] using mem_centralizer_iff.mp he (e y) (by
      rw [SymmetricFourCoreClasses.core_eq,←pCore_map_iso 2 e]
      exact mem_map_of_mem _ hy)

/-- The marked short involution belongs to the point graph core: it centralizes
Tf, while the endpoint two-core lies in Tf and is self-centralizing locally. -/
theorem source_short_mem_A_point (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z) :
    sourceMarkedShort c i∈A c i false := by
  let t : E c i false := ⟨sourceMarkedShort c i,source_short_mem_E c i false⟩
  have ht : t∈pCore 2 (E c i false) := by
    rw [←endpoint_core_selfcentralizer c i false (source_E_point_equiv c i h.embedding_injective)]
    intro a ha
    apply Subtype.ext
    have haA : a.val∈A c i false := mem_map_of_mem (E c i false).subtype ha
    have haTf : a.val∈TfImage c i := by
      obtain ⟨S,hS⟩ := source_Tf_sylow_point c i h.embedding_injective
      rw [←hS]
      exact pCoreIn_le_sylow (E c i false) S haA
    exact source_short_centralizes_E_plane c i z h a.val ((TfImage_le_E c i true) haTf)
  exact mem_map_of_mem (E c i false).subtype ht

omit [Finite G] in
private theorem source_center_cases (b : Bool) (e : E c i b ≃* FModel)
    (a d x : E c i b) (ha : a∈center (E c i b)) (hd : d∈center (E c i b))
    (ha1 : a≠1) (hd1 : d≠1) (had : a≠d) (hx : x∈center (E c i b)) :
    x=1 ∨ x=a ∨ x=d ∨ x=a*d := by
  have hc {v : E c i b} (hv : v∈center (E c i b)) : e v∈center FModel := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨w,rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hv w)
  have hh := SymmetricFourCoreClasses.center_cases (e a) (e d) (e x)
    (hc ha) (hc hd) (fun h => ha1 (e.injective (h.trans e.map_one.symm)))
    (fun h => hd1 (e.injective (h.trans e.map_one.symm))) (fun h => had (e.injective h)) (hc hx)
  simpa only [←map_one e,←map_mul,e.injective.eq_iff] using hh

omit [Finite G] in
private theorem count_endpoint (b plane : Bool) (e : E c i b ≃* FModel)
    (P : G → Prop) (hP : ∀ x y, IsConj x y → (P x ↔ P y)) (a d v : E c i b)
    (ha : a∈center (E c i b)) (hd : d∈center (E c i b))
    (ha1 : a≠1) (hd1 : d≠1) (had : a≠d)
    (hv : v∈pCore 2 (E c i b)) (hvZ : v∉center (E c i b))
    (h1 : ¬P 1) (hPa : ¬P a.val) (hPd : P d.val ↔ plane=false)
    (hPad : P (a.val*d.val) ↔ plane=false) (hPv : P v.val ↔ plane=true)
    (hPav : P (a.val*v.val) ↔ plane=true) (hPdv : ¬P (d.val*v.val))
    (hPadv : P (a.val*d.val*v.val)) :
    Nat.card {x : A c i b // P x.val}=if plane then 9 else 5 := by
  let j : FModel →* G := (E c i b).subtype.comp e.symm.toMonoidHom
  have hj : Function.Injective j := (E c i b).subtype_injective.comp e.symm.injective
  have hjv (x : E c i b) : j (e x)=x.val := congrArg Subtype.val (e.symm_apply_apply x)
  have hc {x : E c i b} (hx : x∈center (E c i b)) : e x∈center FModel := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨w,rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hx w)
  have hev : e v∈SymmetricFourCoreClasses.Core := by
    rw [SymmetricFourCoreClasses.core_eq,←pCore_map_iso 2 e]
    exact mem_map_of_mem _ hv
  have hevZ : e v∉center FModel := by
    intro h
    apply hvZ
    apply mem_center_iff.mpr
    intro y
    apply e.injective
    simpa only [map_mul] using mem_center_iff.mp h (e y)
  have hh := SymmetricFourCoreClasses.predicate_card_map j hj plane P hP (e a) (e d) (e v)
    (hc ha) (hc hd) (fun h => ha1 (e.injective (h.trans e.map_one.symm)))
    (fun h => hd1 (e.injective (h.trans e.map_one.symm))) (fun h => had (e.injective h)) hev hevZ
    h1 (by simpa only [hjv] using hPa) (by simpa only [hjv] using hPd)
    (by simpa only [←map_mul,hjv,Subgroup.coe_mul] using hPad)
    (by simpa only [hjv] using hPv)
    (by simpa only [←map_mul,hjv,Subgroup.coe_mul] using hPav)
    (by simpa only [←map_mul,hjv,Subgroup.coe_mul] using hPdv)
    (by simpa only [←map_mul,hjv,Subgroup.coe_mul] using hPadv)
  rwa [endpoint_core_image c i b e] at hh


omit [Finite G] in
private theorem core_mem_of_mem_A (b : Bool) (x : E c i b) (hx : x.val∈A c i b) :
    x∈pCore 2 (E c i b) := by
  exact (mem_map_iff_mem (E c i b).subtype_injective).mp hx

omit [Finite G] in
private theorem graph_central_in_E (b : Bool) :
    (⟨Source.graphElement c i,graph_mem_E c i b⟩ : E c i b) ∈ center (E c i b) := by
  apply mem_center_iff.mpr
  intro x
  exact Subtype.ext (mem_centralizer_singleton_iff.mp x.property.2)

private theorem root_nonfusion_package (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z) :
    ¬IsConj (rootElement c i z) 1 ∧
    ¬IsConj (rootElement c i z) (Source.graphElement c i) ∧
    ¬IsConj (rootElement c i z) (sourceMarkedShort c i) ∧
    ¬IsConj (rootElement c i z) (Source.graphElement c i*sourceMarkedShort c i) ∧
    ¬IsConj (rootElement c i z) (sourceMarkedShort c i*rootElement c i z) := by
  have hroot (x : G) (hf : IsConj (Source.graphElement c i) x) :
      ¬IsConj (rootElement c i z) x := fun hx =>
    Source.graph_not_conjugate_root c i z h (hf.trans hx.symm)
  refine ⟨?_,hroot _ (IsConj.refl _),hroot _ (source_short_fusion_of_hypotheses c i z h),?_,?_⟩
  · intro he
    have hr := isConj_one_left.mp he
    have ho := source_root_order c i z h
    rw [hr,orderOf_one] at ho
    omega
  · obtain ⟨q,_,hq,_⟩ := source_graph_short_conjugator c i z h
    exact hroot _ (isConj_iff.mpr ⟨q,hq⟩)
  · obtain ⟨y,_,hy⟩ := source_short_root_conjugator c i z h
    exact hroot _ ((source_short_fusion_of_hypotheses c i z h).trans (isConj_iff.mpr ⟨y,hy⟩))

/-- The root class meets the literal point graph core in five elements. -/
theorem source_root_class_A_point (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z) :
    Nat.card (classIntersection (rootElement c i z) (A c i false))=5 := by
  let e := source_E_point_equiv c i h.embedding_injective
  let f : E c i false := ⟨Source.graphElement c i,graph_mem_E c i false⟩
  let r : E c i false := ⟨rootElement c i z,A_le_E c i false (source_root_mem_A c i z h false)⟩
  let t : E c i false := ⟨sourceMarkedShort c i,source_short_mem_E c i false⟩
  have hfZ : f∈center (E c i false) := graph_central_in_E c i false
  have hrZ : r∈center (E c i false) := by
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp ((source_root_centralizer c i z h).symm ▸ x.property.1)
  have hf1 : f≠1 := by
    intro he
    have ho := source_graph_order c i h.embedding_injective
    have he' : Source.graphElement c i=1 := congrArg Subtype.val he
    rw [he',orderOf_one] at ho
    omega
  have hr1 : r≠1 := by
    intro he
    have ho := source_root_order c i z h
    have he' : rootElement c i z=1 := congrArg Subtype.val he
    rw [he',orderOf_one] at ho
    omega
  obtain ⟨h1,hf,ht,hft,htz⟩ := root_nonfusion_package c i z h
  have hfr : f≠r := by
    intro he
    apply hf
    have he' : Source.graphElement c i=rootElement c i z := congrArg Subtype.val he
    rw [he']
  have htCore : t∈pCore 2 (E c i false) :=
    core_mem_of_mem_A c i false t (source_short_mem_A_point c i z h)
  have htZ : t∉center (E c i false) := by
    intro hh
    rcases source_center_cases c i false e f r t hfZ hrZ hf1 hr1 hfr hh with he | he | he | he
    · have ho := source_short_order c i h.embedding_injective
      have he' : sourceMarkedShort c i=1 := congrArg Subtype.val he
      rw [he',orderOf_one] at ho
      omega
    · exact source_graph_ne_short c i h.embedding_injective (congrArg Subtype.val he).symm
    · apply ht
      have he' : sourceMarkedShort c i=rootElement c i z := congrArg Subtype.val he
      rw [he']
    · apply ht
      have he' : sourceMarkedShort c i=Source.graphElement c i*rootElement c i z := congrArg Subtype.val he
      rw [he']
      exact source_root_product_fusion c i z h
  have hzt : r.val*t.val=t.val*r.val := (source_short_commutes_root c i z h).eq.symm
  have hprod : IsConj (rootElement c i z) (f.val*r.val*t.val) := by
    rw [mul_assoc,hzt,←mul_assoc]
    exact source_root_short_product_fusion c i z h
  exact count_endpoint c i false false e (IsConj (rootElement c i z))
    (fun x y hxy => ⟨fun hx => hx.trans hxy,fun hy => hy.trans hxy.symm⟩) f r t
    hfZ hrZ hf1 hr1 hfr htCore htZ h1 hf
    (iff_of_true (IsConj.refl _) rfl)
    (iff_of_true (source_root_product_fusion c i z h) rfl)
    (iff_of_false ht (by decide)) (iff_of_false hft (by decide))
    (fun hh => htz (hzt ▸ hh)) hprod


/-- The root class meets the literal plane graph core in nine elements. -/
theorem source_root_class_A_plane_of_equiv (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) (e : E c i true ≃* FModel) :
    Nat.card (classIntersection (rootElement c i z) (A c i true))=9 := by
  let f : E c i true := ⟨Source.graphElement c i,graph_mem_E c i true⟩
  let t : E c i true := ⟨sourceMarkedShort c i,source_short_mem_E c i true⟩
  let r : E c i true := ⟨rootElement c i z,A_le_E c i true (source_root_mem_A c i z h true)⟩
  have hfZ : f∈center (E c i true) := graph_central_in_E c i true
  have htZ : t∈center (E c i true) := mem_center_iff.mpr fun x =>
    Subtype.ext (source_short_centralizes_E_plane c i z h x.val x.property)
  have hf1 : f≠1 := by
    intro he
    have ho := source_graph_order c i h.embedding_injective
    have he' : Source.graphElement c i=1 := congrArg Subtype.val he
    rw [he',orderOf_one] at ho
    omega
  have ht1 : t≠1 := by
    intro he
    have ho := source_short_order c i h.embedding_injective
    have he' : sourceMarkedShort c i=1 := congrArg Subtype.val he
    rw [he',orderOf_one] at ho
    omega
  have hftne : f≠t := fun he =>
    source_graph_ne_short c i h.embedding_injective (congrArg Subtype.val he)
  obtain ⟨h1,hf,ht,hft,htz⟩ := root_nonfusion_package c i z h
  have hrCore : r∈pCore 2 (E c i true) :=
    core_mem_of_mem_A c i true r (source_root_mem_A c i z h true)
  have hrZ : r∉center (E c i true) := by
    intro hh
    rcases source_center_cases c i true e f t r hfZ htZ hf1 ht1 hftne hh with he | he | he | he
    · exact h1 (show IsConj (rootElement c i z) 1 from
        (show rootElement c i z=1 from congrArg Subtype.val he) ▸ IsConj.refl _)
    · apply hf
      have he' : rootElement c i z=Source.graphElement c i := congrArg Subtype.val he
      rw [he']
    · apply ht
      have he' : rootElement c i z=sourceMarkedShort c i := congrArg Subtype.val he
      rw [he']
    · apply hft
      have he' : rootElement c i z=Source.graphElement c i*sourceMarkedShort c i := congrArg Subtype.val he
      rw [he']
  exact count_endpoint c i true true e (IsConj (rootElement c i z))
    (fun x y hxy => ⟨fun hx => hx.trans hxy,fun hy => hy.trans hxy.symm⟩) f t r
    hfZ htZ hf1 ht1 hftne hrCore hrZ h1 hf
    (iff_of_false ht (by decide)) (iff_of_false hft (by decide))
    (iff_of_true (IsConj.refl _) rfl)
    (iff_of_true (source_root_product_fusion c i z h) rfl) htz
    (source_root_short_product_fusion c i z h)

/-- Both source endpoint counts have their local recognition input discharged. -/
theorem source_root_class_A_plane (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) :
    Nat.card (classIntersection (rootElement c i z) (A c i true))=9 :=
  source_root_class_A_plane_of_equiv c i z h (source_E_plane_equiv c i h.embedding_injective)


/-- The short class and its root translate cut out the marked pair t,tz
in the plane two-core. The coordinate premise records the literal root. -/
theorem source_plane_short_pair_of_equiv (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) (e : E c i true ≃* FModel)
    (hmark : (e ⟨rootElement c i z,A_le_E c i true (source_root_mem_A c i z h true)⟩).1≠1)
    (x : G) (hx : x∈A c i true) :
    (IsConj (Source.graphElement c i) x ∧ IsConj (Source.graphElement c i) (rootElement c i z*x)) ↔
      x=sourceMarkedShort c i ∨ x=sourceMarkedShort c i*rootElement c i z := by
  let f : E c i true := ⟨Source.graphElement c i,graph_mem_E c i true⟩
  let t : E c i true := ⟨sourceMarkedShort c i,source_short_mem_E c i true⟩
  let r : E c i true := ⟨rootElement c i z,A_le_E c i true (source_root_mem_A c i z h true)⟩
  have hfZ : f∈center (E c i true) := graph_central_in_E c i true
  have htZ : t∈center (E c i true) := mem_center_iff.mpr fun x =>
    Subtype.ext (source_short_centralizes_E_plane c i z h x.val x.property)
  have hf1 : f≠1 := by
    intro he
    have ho := source_graph_order c i h.embedding_injective
    have he' : Source.graphElement c i=1 := congrArg Subtype.val he
    rw [he',orderOf_one] at ho
    omega
  have ht1 : t≠1 := by
    intro he
    have ho := source_short_order c i h.embedding_injective
    have he' : sourceMarkedShort c i=1 := congrArg Subtype.val he
    rw [he',orderOf_one] at ho
    omega
  have hftne : f≠t := fun he =>
    source_graph_ne_short c i h.embedding_injective (congrArg Subtype.val he)
  obtain ⟨h1,hf,ht,hft,htz⟩ := root_nonfusion_package c i z h
  have hrCore : r∈pCore 2 (E c i true) :=
    core_mem_of_mem_A c i true r (source_root_mem_A c i z h true)
  have hrZ : r∉center (E c i true) := by
    intro hh
    rcases source_center_cases c i true e f t r hfZ htZ hf1 ht1 hftne hh with he | he | he | he
    · exact h1 (show IsConj (rootElement c i z) 1 from
        (show rootElement c i z=1 from congrArg Subtype.val he) ▸ IsConj.refl _)
    · apply hf
      have he' : rootElement c i z=Source.graphElement c i := congrArg Subtype.val he
      rw [he']
    · apply ht
      have he' : rootElement c i z=sourceMarkedShort c i := congrArg Subtype.val he
      rw [he']
    · apply hft
      have he' : rootElement c i z=Source.graphElement c i*sourceMarkedShort c i := congrArg Subtype.val he
      rw [he']

  let u : E c i true := ⟨x,A_le_E c i true hx⟩
  let j : FModel →* G := (E c i true).subtype.comp e.symm.toMonoidHom
  have hjv (v : E c i true) : j (e v)=v.val := congrArg Subtype.val (e.symm_apply_apply v)
  have hc {v : E c i true} (hv : v∈center (E c i true)) : e v∈center FModel := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨w,rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hv w)
  have hcore {v : E c i true} (hv : v∈pCore 2 (E c i true)) : e v∈SymmetricFourCoreClasses.Core := by
    rw [SymmetricFourCoreClasses.core_eq,←pCore_map_iso 2 e]
    exact mem_map_of_mem _ hv
  have herZ : e r∉center FModel := by
    intro hh
    apply hrZ
    apply mem_center_iff.mpr
    intro v
    apply e.injective
    simpa only [map_mul] using mem_center_iff.mp hh (e v)
  have hnroot (v : G) (hv : IsConj (rootElement c i z) v) : ¬IsConj (Source.graphElement c i) v :=
    fun hh => Source.graph_not_conjugate_root c i z h (hh.trans hv.symm)
  have hfnot1 : ¬ IsConj (Source.graphElement c i) 1 := by
    intro hh
    exact hf1 (Subtype.ext (isConj_one_left.mp hh))
  have hfft : IsConj (Source.graphElement c i) (f.val*t.val) := by
    obtain ⟨q,_,hq,_⟩ := source_graph_short_conjugator c i z h
    exact isConj_iff.mpr ⟨q,hq⟩
  have hftz : IsConj (Source.graphElement c i) (t.val*r.val) := by
    obtain ⟨y,_,hy⟩ := source_short_root_conjugator c i z h
    exact (source_short_fusion_of_hypotheses c i z h).trans (isConj_iff.mpr ⟨y,hy⟩)
  have hh := SymmetricFourCoreClasses.predicate_plane_pair
    (fun v => IsConj (Source.graphElement c i) (j v))
    (fun v w hvw => ⟨fun hv => hv.trans (j.map_isConj hvw),fun hw => hw.trans (j.map_isConj hvw).symm⟩)
    (e f) (e t) (e r) (e u) (hc hfZ) (hc htZ)
    (fun he => hf1 (e.injective (he.trans e.map_one.symm)))
    (fun he => ht1 (e.injective (he.trans e.map_one.symm)))
    (fun he => hftne (e.injective he)) (hcore hrCore) herZ hmark
    (hcore (core_mem_of_mem_A c i true u hx))
    (by simpa only [map_one] using hfnot1)
    (by simpa only [hjv] using IsConj.refl f.val)
    (by simpa only [hjv] using source_short_fusion_of_hypotheses c i z h)
    (by simpa only [←map_mul,hjv,Subgroup.coe_mul] using hfft)
    (by simpa only [hjv] using hnroot r.val (IsConj.refl _))
    (by simpa only [←map_mul,hjv,Subgroup.coe_mul] using
      hnroot (f.val*r.val) (source_root_product_fusion c i z h))
    (by simpa only [←map_mul,hjv,Subgroup.coe_mul] using hftz)
    (by simpa only [←map_mul,hjv,Subgroup.coe_mul] using
      hnroot (f.val*t.val*r.val) (source_root_short_product_fusion c i z h))
  simpa only [←map_mul,hjv,e.injective.eq_iff,Subtype.ext_iff,Subgroup.coe_mul] using hh

/-- The actual plane core has precisely the short/short pair t,tz. -/
theorem source_plane_short_pair (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) (x : G) (hx : x∈A c i true) :
    (IsConj (Source.graphElement c i) x ∧ IsConj (Source.graphElement c i) (rootElement c i z*x)) ↔
      x=sourceMarkedShort c i ∨ x=sourceMarkedShort c i*rootElement c i z :=
  source_plane_short_pair_of_equiv c i z h (source_E_plane_equiv c i h.embedding_injective)
    (source_E_plane_root_coordinate c i h.embedding_injective z h
      (A_le_E c i true (source_root_mem_A c i z h true))) x hx

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
