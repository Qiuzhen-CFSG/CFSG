module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionSylowModel
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionPlaneCommutator
public import Theory.GroupTheory.CentralizerSylowPromotion

/-!
# Ambient Sylow and exceptional graph fusion

The root-centralizer identity and the marked upper center of order two promote
the literal source upper subgroup to an ambient Sylow subgroup. Exceptionality
then supplies a graph-centralizing two-group of order greater than 32. Moving
it into the marked Sylow reduces graph/short fusion to the concrete local
large-centralizer table, with graph/root fusion already excluded.

An order-64 short centralizer is Sylow once short/root nonfusion is known:
a larger centralizer two-group would be ambient Sylow, forcing its central
short involution into the unique root center. The final theorem gives the
fusion and Sylow conclusions used by the F.5.4 graph-centralizer normalizer
construction. Its local-table and dihedral-model premises remain explicit
until the independent concrete calculations are supplied.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, F.4.33–37,
printed pp.291–293, especially the exceptional enlargement on p.293.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)

theorem source_sylowImage_isSylow (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = Source.sylowImage c i := by
  let T := Source.sylowImage c i
  let C := centralizer ({rootElement c i z} : Set G)
  have hTC : T ≤ C := by
    change T ≤ centralizer ({rootElement c i z} : Set G)
    rw [source_root_centralizer c i z h]
    exact sylowImage_le_M c i false
  have hC : Nat.card C = 1152 := by
    rw [show C = M c i false from source_root_centralizer c i z h]
    change Nat.card (i.comp c.left).range = 1152
    rw [Nat.card_congr (MonoidHom.ofInjective
      (show Function.Injective (i.comp c.left) from h.embedding_injective.comp c.left_injective)).toEquiv.symm]
    exact Extension.binary_point_card
  let S : Sylow 2 C := Sylow.ofCard (T.subgroupOf C) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe hTC).toEquiv,
      show Nat.card T = 128 from source_sylowImage_card c i h.embedding_injective,hC]
    decide +kernel)
  have hS : (S : Subgroup C).map C.subtype = T := map_subgroupOf_eq_of_le hTC
  obtain ⟨R,hR⟩ := exists_ambient_sylow_of_centralizer_center
    (rootElement c i z) (source_root_order c i z h) S (by
      change (center ((S : Subgroup C).map C.subtype)).map _ = _
      rw [hS]
      exact (source_sylowImage_center_eq_pointRoot c i z h).trans
        (pointRootImage_eq_zpowers c i z h))
  exact ⟨R,hR.trans hS⟩


omit [Finite G] in
theorem source_graph_mem_sylowImage : Source.graphElement c i ∈ Source.sylowImage c i := by
  refine ⟨UnitaryTwo.GraphCentralizer.graphInvolution, ?_, rfl⟩
  change Extension.sigma 1 hn ∈ Extension.extendedUpper 1 hn
  exact (extendedUpper_mem _).mpr (upperProjective 1 hn).one_mem

/-- The exceptional enlargement forces graph/short fusion once the concrete
large-centralizer classes of the marked upper subgroup have been calculated. -/
theorem source_graph_fuses_short_of_local_table (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) (hex : Source.Exceptional c i)
    (htf : Nat.card (Tf c i) = 32)
    (hlocal : ∀ x ∈ Source.sylowImage c i, orderOf x = 2 →
      IsConj (rootElement c i z) x ∨ IsConj (sourceMarkedShort c i) x ∨
        Nat.card (Tcentralizer c i x) ≤ 32) :
    IsConj (Source.graphElement c i) (sourceMarkedShort c i) := by
  obtain ⟨S,hS⟩ := source_sylowImage_isSylow c i z h
  obtain ⟨R,hR⟩ := exists_strict_sylow c i (source_sylowImage_isTwoGroup c i) hex
  have hRcard : 32 < Nat.card R := by
    rw [← htf]
    by_contra! hsmall
    exact hR.ne (eq_of_le_of_card_ge hR.le hsmall)
  let K := Rimage c i R
  have hKp : IsPGroup 2 K := R.isPGroup'.map _
  obtain ⟨P,hKP⟩ := hKp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G P S
  let a : G ≃* G := MulAut.conj g
  have hmap : (P : Subgroup G).map a.toMonoidHom = Source.sylowImage c i :=
    (congrArg Sylow.toSubgroup hg).trans hS
  have hfK : Source.graphElement c i ∈ K :=
    mem_map_of_mem (C c i).subtype
      (hR.le (show (⟨Source.graphElement c i,graph_mem_C c i⟩ : C c i) ∈ Tf c i from
        source_graph_mem_sylowImage c i))
  have hKmap : K.map a.toMonoidHom ≤ Source.sylowImage c i := by
    rw [← hmap]
    exact map_mono hKP
  have hxT : a (Source.graphElement c i) ∈ Source.sylowImage c i :=
    hKmap (mem_map_of_mem a.toMonoidHom hfK)
  have hx2 : orderOf (a (Source.graphElement c i)) = 2 :=
    (orderOf_injective a.toMonoidHom a.injective _).trans
      (source_graph_order c i h.embedding_injective)
  have hfx : IsConj (Source.graphElement c i) (a (Source.graphElement c i)) :=
    isConj_iff.mpr ⟨g,rfl⟩
  rcases hlocal _ hxT hx2 with hz | ht | hsmall
  · exact False.elim (Source.graph_not_conjugate_root c i z h (hfx.trans hz.symm))
  · exact hfx.trans ht.symm
  · have hKC : K.map a.toMonoidHom ≤ Tcentralizer c i (a (Source.graphElement c i)) := by
      refine le_inf hKmap ?_
      rintro _ ⟨k,hk,rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      have hh := mem_centralizer_singleton_iff.mp (Rimage_le_C c i R hk)
      exact (map_mul a k (Source.graphElement c i)).symm.trans
        ((congrArg a hh).trans (map_mul a (Source.graphElement c i) k))
    have hle := card_le_of_le hKC
    rw [card_map_of_injective a.injective] at hle
    have hKcard : Nat.card K = Nat.card R := card_map_of_injective (C c i).subtype_injective
    rw [hKcard] at hle
    exact False.elim (hRcard.not_ge (hle.trans hsmall))


/-- An index-two short centralizer is Sylow once short and root are not fused.
A larger two-subgroup would be an ambient Sylow centralized by the short
involution, forcing that involution into the unique root center. -/
theorem source_short_centralizer_sylow_of_nonfusion (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z)
    (hnonfusion : ¬ IsConj (sourceMarkedShort c i) (rootElement c i z))
    (hcard : Nat.card (Tcentralizer c i (sourceMarkedShort c i)) = 64) :
    ∃ R : Sylow 2 (centralizer ({sourceMarkedShort c i} : Set G)),
      (R : Subgroup (centralizer ({sourceMarkedShort c i} : Set G))) =
        (Source.sylowImage c i).subgroupOf
          (centralizer ({sourceMarkedShort c i} : Set G)) := by
  classical
  obtain ⟨S,hS⟩ := source_sylowImage_isSylow c i z h
  let t := sourceMarkedShort c i
  let Ct := centralizer ({t} : Set G)
  let U := (Source.sylowImage c i).subgroupOf Ct
  have hU : IsPGroup 2 U := (source_sylowImage_isTwoGroup c i).comap_subtype
  obtain ⟨R,hUR⟩ := hU.exists_le_sylow
  refine ⟨R,?_⟩
  by_contra hne
  have hUcard : Nat.card U = 64 := by
    have hm : U.map Ct.subtype = Tcentralizer c i t := subgroupOf_map_subtype _ _
    rw [← hm,card_map_of_injective Ct.subtype_injective] at hcard
    exact hcard
  have hlarge : 64 < Nat.card R := by
    rw [← hUcard]
    by_contra! hsmall
    exact hne (eq_of_le_of_card_ge hUR hsmall).symm
  let K := (R : Subgroup Ct).map Ct.subtype
  have hKp : IsPGroup 2 K := R.isPGroup'.map _
  obtain ⟨P,hKP⟩ := hKp.exists_le_sylow
  have hKcard : Nat.card K = Nat.card R := card_map_of_injective Ct.subtype_injective
  have hPcard : Nat.card P = 128 := by
    rw [Nat.card_congr (P.equiv S).toEquiv]
    rw [hS]
    exact source_sylowImage_card c i h.embedding_injective
  have hKeq : K = (P : Subgroup G) := by
    apply eq_of_le_of_card_ge hKP
    have he : Nat.card P = Nat.card K := Nat.eq_of_dvd_of_lt_two_mul Nat.card_pos.ne'
      (card_dvd_of_le hKP) (by rw [hPcard,hKcard]; omega)
    exact he.le
  have hPC : (P : Subgroup G) ≤ Ct := hKeq ▸ map_subtype_le (R : Subgroup Ct)
  have htP : t ∈ P := hKP (mem_map_of_mem Ct.subtype
    (hUR (show (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : Ct) ∈ U from
      source_short_mem_sylowImage c i)))
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G P S
  let a : G ≃* G := MulAut.conj g
  have hmap : (P : Subgroup G).map a.toMonoidHom = Source.sylowImage c i :=
    (congrArg Sylow.toSubgroup hg).trans hS
  have hxT : a t ∈ Source.sylowImage c i := hmap ▸ mem_map_of_mem a.toMonoidHom htP
  have hxZ : (⟨a t,hxT⟩ : Source.sylowImage c i) ∈ center (Source.sylowImage c i) := by
    apply mem_center_iff.mpr
    intro b
    have hb : b.val ∈ (P : Subgroup G).map a.toMonoidHom := by
      rw [hmap]
      exact b.property
    obtain ⟨r,hr,he⟩ := hb
    apply Subtype.ext
    change b.val * a t = a t * b.val
    rw [← he]
    change a r * a t = a t * a r
    exact (map_mul a r t).symm.trans
      ((congrArg a (mem_centralizer_singleton_iff.mp (hPC hr))).trans (map_mul a t r))
  have hxline : a t ∈ zpowers (rootElement c i z) := by
    rw [← pointRootImage_eq_zpowers c i z h,
      ← source_sylowImage_center_eq_pointRoot c i z h]
    exact mem_map_of_mem (Source.sylowImage c i).subtype hxZ
  have hx2 : orderOf (a t) = 2 := (orderOf_injective a.toMonoidHom a.injective t).trans
    (source_short_order c i h.embedding_injective)
  have hxeq : a t = rootElement c i z := by
    rw [mem_zpowers_iff_mem_range_orderOf,source_root_order c i z h] at hxline
    obtain ⟨n,hnBound,he⟩ := Finset.mem_image.mp hxline
    have hn2 := Finset.mem_range.mp hnBound
    interval_cases n
    · have hx1 : a t = 1 := by simpa using he.symm
      rw [hx1,orderOf_one] at hx2
      omega
    · simpa using he.symm
  exact hnonfusion (isConj_iff.mpr ⟨g,hxeq⟩)


/-- The two source conclusions immediately used to identify the Sylow
subgroups of the graph centralizer in F.5.4. -/
theorem source_short_fusion_and_sylow_of_local_table (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) (hex : Source.Exceptional c i)
    (htf : Nat.card (Tf c i) = 32)
    (hlocal : ∀ x ∈ Source.sylowImage c i, orderOf x = 2 →
      IsConj (rootElement c i z) x ∨ IsConj (sourceMarkedShort c i) x ∨
        Nat.card (Tcentralizer c i x) ≤ 32)
    (hiso : Nonempty (Tcentralizer c i (sourceMarkedShort c i) ≃*
      DihedralGroup 4 × DihedralGroup 4)) :
    IsConj (Source.graphElement c i) (sourceMarkedShort c i) ∧
    ∃ R : Sylow 2 (centralizer ({sourceMarkedShort c i} : Set G)),
      (R : Subgroup (centralizer ({sourceMarkedShort c i} : Set G))) =
        (Source.sylowImage c i).subgroupOf
          (centralizer ({sourceMarkedShort c i} : Set G)) := by
  have hf := source_graph_fuses_short_of_local_table c i z h hex htf hlocal
  refine ⟨hf,source_short_centralizer_sylow_of_nonfusion c i z h
    (fun ht => Source.graph_not_conjugate_root c i z h (hf.trans ht)) ?_⟩
  obtain ⟨e⟩ := hiso
  rw [Nat.card_congr e.toEquiv,Nat.card_prod,Nat.card_eq_fintype_card,DihedralGroup.card]

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
