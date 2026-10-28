module
public import CFSG.Quasithin.ChapterE.Section02.Structure.PairedMaximal
public import CFSG.Quasithin.ChapterE.Section02.Structure.ComponentAutomizerSQTK
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.KernelLift
public import Theory.GroupTheory.CenterlessSupplementCentralizer
public import Theory.GroupTheory.SylowQuotientPreimage

/-!
# The component-local subgroup in the paired source

For a simple component K supplemented by the selected Sylow T, the subgroup
K(T ∩ N(K)) maps onto the full component automizer. Its centralizer kernel
lies in its Sylow subgroup. Minimal parabolicity therefore lifts from the
automizer, and self-normalization of K ∩ M puts its maximal subgroup in M.
A nontrivial elementary normal subgroup of T cannot centralize K when the
ambient maximal core is trivial.

Source: Aschbacher–Smith E.2.17, printed p.230, with E.2.2 component geometry.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Witnesses.PairedOddLinearTwo
variable {H : Type*} [Group H] [Finite H]

private theorem sylow_restrict_between (T : Sylow 2 H) (N L : Subgroup H)
    (hLN : L ≤ N) (hTL : (T : Subgroup H) ⊓ N ≤ L)
    (S : Sylow 2 N) (hS : (S : Subgroup N) = (T : Subgroup H).subgroupOf N) :
    ∃ R : Sylow 2 L, (R : Subgroup L) = (T : Subgroup H).subgroupOf L := by
  have hSL : (S : Subgroup N) ≤ L.subgroupOf N := by
    rw [hS]
    intro x hx
    exact hTL ⟨hx,x.property⟩
  let R := S.subtype hSL
  let e := subgroupOfEquivOfLe hLN
  refine ⟨R.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change (R : Subgroup (L.subgroupOf N)).map e.toMonoidHom = _
  rw [show (R : Subgroup (L.subgroupOf N)) = (S : Subgroup N).subgroupOf (L.subgroupOf N) from rfl,hS]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨⟨x,hLN x.property⟩,x.property⟩,hx,rfl⟩

/-- The literal component-local subgroup has the original Sylow intersection. -/
theorem component_local_sylow
    (hH : IsStronglyQuasithin H) (T : Sylow 2 H)
    {K : Subgroup H} (hK : IsComponent H K)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    let L := K ⊔ ((T : Subgroup H) ⊓ normalizer (K : Set H))
    ∃ S : Sylow 2 L, (S : Subgroup L) = (T : Subgroup H).subgroupOf L := by
  let N := normalizer (K : Set H)
  let L := K ⊔ ((T : Subgroup H) ⊓ N)
  obtain ⟨S,hS⟩ := component_normalizer_sylow T hK
    (Structure.generating_component_orbit_eq_residual hH T hK hgen)
  exact sylow_restrict_between T N L (sup_le K.le_normalizer inf_le_right) le_sup_right S hS

/-- The component automizer pulls its maximal subgroup back inside the actual M. -/
theorem component_local_maximal_preimage_le
    (hH : IsStronglyQuasithin H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    {K : Subgroup H} (hK : IsComponent H K) [IsSimpleGroup K]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    let N := normalizer (K : Set H)
    let L := K ⊔ ((T : Subgroup H) ⊓ N)
    let a := (NormalizerAction.quotient K).comp
      (inclusion (show L ≤ N from sup_le K.le_normalizer inf_le_right))
    (((ChapterB.minimalParabolicMax T hP).subgroupOf N).map
      (NormalizerAction.quotient K)).comap a ≤
        (ChapterB.minimalParabolicMax T hP).subgroupOf L := by
  dsimp only
  let N := normalizer (K : Set H)
  let L := K ⊔ ((T : Subgroup H) ⊓ N)
  let M := ChapterB.minimalParabolicMax T hP
  let A := K ⊓ M
  have hTL : (T : Subgroup H) ⊓ N ≤ normalizer (K : Set H) := inf_le_right
  intro x hx
  have hxprod : (x:H) ∈ (K : Set H) * (((T : Subgroup H) ⊓ N : Subgroup H) : Set H) := by
    rw [← coe_mul_of_right_le_normalizer_left K _ hTL]
    exact x.property
  obtain ⟨k,hk,t,ht,hkt⟩ := hxprod
  have htM : t ∈ M := (ChapterB.minimalParabolicMax_spec T hP).2 ht.1
  let q := NormalizerAction.quotient K
  obtain ⟨m,hm,he⟩ := hx
  have hxN : (x:H) ∈ N := (sup_le K.le_normalizer inf_le_right) x.property
  have heval (y : H) (hy : y ∈ K) :
      (x:H)*y*(x:H)⁻¹ = (m:H)*y*(m:H)⁻¹ := by
    have hh := congrArg (fun z => (NormalizerAction.action K z) (⟨y,hy⟩ : K)) he
    exact (congrArg Subtype.val hh).symm
  have hxA : (x:H) ∈ normalizer (A : Set H) := by
    apply mem_normalizer_iff.mpr
    intro y
    constructor
    · intro hy
      refine ⟨(mem_normalizer_iff.mp hxN y).mp hy.1,?_⟩
      rw [heval y hy.1]
      exact M.mul_mem (M.mul_mem hm hy.2) (M.inv_mem hm)
    · intro hy
      have hyK := (mem_normalizer_iff.mp hxN y).mpr hy.1
      refine ⟨hyK,?_⟩
      have hym : (m:H)*y*(m:H)⁻¹ ∈ M := by rw [←heval y hyK]; exact hy.2
      exact (mem_normalizer_iff.mp (M.le_normalizer hm) y).mpr hym
  have htA : t ∈ normalizer (A : Set H) :=
    inf_normalizer_le_normalizer_inf ⟨ht.2,M.le_normalizer htM⟩
  have hkA : k ∈ normalizer (A : Set H) := by
    have hh := (normalizer (A : Set H)).mul_mem hxA
      ((normalizer (A : Set H)).inv_mem htA)
    simpa only [←hkt,mul_inv_cancel_right] using hh
  have hself := Structure.component_maximal_intersection_self_normalizing hH T hP hK hgen
  have hkM : k ∈ M := (show k ∈ K ⊓ M from hself ▸ ⟨hk,hkA⟩).2
  change (x:H) ∈ M
  rw [←hkt]
  exact M.mul_mem hkM htM

/-- The component-local action has its full automizer as image and a Sylow kernel. -/
theorem component_local_action
    (hH : IsStronglyQuasithin H) (T : Sylow 2 H)
    {K : Subgroup H} (hK : IsComponent H K)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hZ : center K = ⊥) :
    let N := normalizer (K : Set H)
    let L := K ⊔ ((T : Subgroup H) ⊓ N)
    let a := (NormalizerAction.quotient K).comp
      (inclusion (show L ≤ N from sup_le K.le_normalizer inf_le_right))
    ∃ S : Sylow 2 L, (S : Subgroup L) = (T : Subgroup H).subgroupOf L ∧
      Function.Surjective a ∧ a.ker ≤ (S : Subgroup L) ∧
      (S : Subgroup L).map a = ((T : Subgroup H).subgroupOf N).map (NormalizerAction.quotient K) := by
  dsimp only
  let N := normalizer (K : Set H)
  let L := K ⊔ ((T : Subgroup H) ⊓ N)
  have hLN : L ≤ N := sup_le K.le_normalizer inf_le_right
  let a := (NormalizerAction.quotient K).comp (inclusion hLN)
  obtain ⟨S,hS⟩ := component_local_sylow hH T hK hgen
  have ha : Function.Surjective a := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [←component_automizer_sylow_supplement T hK
      (Structure.generating_component_orbit_eq_residual hH T hK hgen)]
    apply sup_le
    · rw [←NormalizerAction.componentMap_range]
      rintro x ⟨k,rfl⟩
      exact ⟨⟨k,(show K≤L from le_sup_left) k.property⟩,rfl⟩
    · rintro x ⟨t,ht,rfl⟩
      exact ⟨⟨t,(show (T:Subgroup H)⊓N≤L from le_sup_right) ⟨ht,t.property⟩⟩,rfl⟩
  have hSimage : (S : Subgroup L).map a =
      ((T : Subgroup H).subgroupOf N).map (NormalizerAction.quotient K) := by
    rw [hS]
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨⟨t,hLN t.property⟩,ht,rfl⟩
    · rintro ⟨t,ht,rfl⟩
      exact ⟨⟨t,(show (T:Subgroup H)⊓N≤L from le_sup_right) ⟨ht,t.property⟩⟩,ht,rfl⟩
  have hKL : K ≤ L := le_sup_left
  let C := K.subgroupOf L
  let : C.Normal := (normal_subgroupOf_iff_le_normalizer hKL).mpr hLN
  have hSsup : C ⊔ (S : Subgroup L) = ⊤ := by
    apply map_injective L.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hKL,hS,subgroupOf_map_subtype,
      ←MonoidHom.range_eq_map,range_subtype]
    have he : (T : Subgroup H) ⊓ L = (T : Subgroup H) ⊓ N :=
      le_antisymm (inf_le_inf_left _ hLN) (le_inf inf_le_left le_sup_right)
    rw [he]
  have hZC : center C = ⊥ := by
    apply card_eq_one.mp
    rw [Nat.card_congr (centerCongr (subgroupOfEquivOfLe hKL)).toEquiv,hZ,card_bot]
  have hkC : a.ker ≤ centralizer (C : Set L) := by
    intro x hx y hy
    have he := congrArg (fun z => (NormalizerAction.action K z) (⟨(y:H),hy⟩ : K))
      (show a x = 1 from hx)
    have he' : (x:H)*(y:H)*(x:H)⁻¹ = (y:H) := by
      rw [map_one] at he
      exact congrArg Subtype.val he
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp he').symm
  exact ⟨S,hS,ha,hkC.trans (centralizer_le_sylow_of_centerless_supplement C S hSsup hZC),hSimage⟩

/-- The literal local subgroup is minimal parabolic, with the expected core and maximal. -/
theorem component_local_minimal
    (hH : IsStronglyQuasithin H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    {K : Subgroup H} (hK : IsComponent H K) [IsSimpleGroup K]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hZ : center K = ⊥) :
    let N := normalizer (K : Set H)
    let L := K ⊔ ((T : Subgroup H) ⊓ N)
    let a := (NormalizerAction.quotient K).comp
      (inclusion (show L ≤ N from sup_le K.le_normalizer inf_le_right))
    ∃ S : Sylow 2 L, (S : Subgroup L) = (T : Subgroup H).subgroupOf L ∧
      Function.Surjective a ∧ ∃ hPS : ChapterB.IsMinimalParabolicOver S ⊤,
      ChapterB.minimalParabolicMax S hPS ≤ (ChapterB.minimalParabolicMax T hP).subgroupOf L ∧
      ChapterB.minimalParabolicCore S hPS = a.ker := by
  dsimp only
  let N := normalizer (K : Set H)
  let L := K ⊔ ((T : Subgroup H) ⊓ N)
  let a := (NormalizerAction.quotient K).comp
    (inclusion (show L ≤ N from sup_le K.le_normalizer inf_le_right))
  obtain ⟨S,hS,ha,hker,hSim⟩ := component_local_action hH T hK hgen hZ
  obtain ⟨SA,hSA,hPA,hMA⟩ := Structure.source_component_automizer hH T hP hK hgen
  have he : S.mapSurjective ha = SA := Sylow.ext (hSim.trans hSA.symm)
  have hPim : ChapterB.IsMinimalParabolicOver (S.mapSurjective ha) ⊤ := he.symm ▸ hPA
  have hMim : ChapterB.minimalParabolicMax (S.mapSurjective ha) hPim =
      ((ChapterB.minimalParabolicMax T hP).subgroupOf N).map (NormalizerAction.quotient K) := by
    subst SA
    exact hMA
  let hPS := ChapterB.minimalParabolic_of_surjective S a ha hker hPim
  refine ⟨S,hS,ha,hPS,?_,?_⟩
  · rw [ChapterB.minimalParabolicMax_comap S a ha hker hPim,hMim]
    exact component_local_maximal_preimage_le hH T hP hK hgen
  · rw [ChapterB.minimalParabolicCore_comap S a ha hker hPim,
      Structure.source_component_automizer_core hK,MonoidHom.comap_bot]

omit [Finite H] in
/-- A nontrivial elementary normal Sylow subgroup survives the local component action. -/
theorem component_local_image_nontrivial
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    (K : Subgroup H) (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (W : Subgroup H) [IsElementaryAbelian 2 W]
    (hWT : W ≤ T) (hWN : (W.subgroupOf (T : Subgroup H)).Normal)
    (hne : W ≠ ⊥) :
    ¬ W ≤ centralizer (K : Set H) := by
  intro hc
  have hTW : (T : Subgroup H) ≤ normalizer (W : Set H) :=
    (normal_subgroupOf_iff_le_normalizer hWT).mp hWN
  let : W.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [←hgen]
    exact sup_le ((le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _)) hTW))
  have hb : W ≤ pCore 2 H := le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 W⟩
  exact hne (bot_unique (hb.trans (hJ ▸ ChapterB.minimalParabolicTwoCore_le_core T hP)))

end CFSG.Quasithin.ChapterE.Witnesses.PairedOddLinearTwo
