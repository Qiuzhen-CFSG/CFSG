module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.MarkedQuotient
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ShortNormalizer
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.MarkedQuotient
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ShortNormalizer

/-!
# Ambient Sylows on the same prepared short-line quotient

Extend the chosen long-root-centralizing Sylow R of C_L(t) to a Sylow P
of C_G(t), retaining its exact preimage R. Since the abelian O₂(L) lies
in R and equals J(T), P normalizes L. The intrinsic descriptions
V=[O₂(L),C_L(t)] and U=C_V(C_L(t)) show that the full local stabilizer
normalizes the very same q-element line. Consequently P lies in its
ambient normalizer and maps to a Sylow of the literal quotient by U;
the quotient Sylow again has exactly R as its residual preimage.

The same reduced comparison retains both root marks, the original right
residual center, the q²−1 long-root class and its unique quotient lifts.
Both orientations, ordinary and degree-two rows, q=4 and n=2m with m>1
are retained. The whole ambient P is not asserted to centralize z.

Source: Aschbacher–Smith F.4.42, printed pp.295–296 of
`refs/quasithin.pdf`. Full-stabilizer fusion, ambient unique fixed cosets,
maximal-W containment, outer transfer and the order comparison remain
further source obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneLocal UnitaryFourPlaneRadical UnitaryFourShortRoot
namespace UnitarySource
variable {G : Type*} [Group G] (L : Subgroup G) (t : L)
private theorem short_local_le_line_normalizer
    (U V : Subgroup (centralizer ({t} : Set L)))
    (hV : V.map (centralizer ({t} : Set L)).subtype =
      ⁅pCore 2 L,centralizer ({t} : Set L)⁆)
    (hU : U = V ⊓ center (centralizer ({t} : Set L))) :
    (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G)) ≤
      shortLineNormalizer L t U := by
  let Y := centralizer ({t} : Set L)
  let M := centralizer ({t.val} : Set G)
  let j := shortCentralizerEmbedding L t
  have hVamb : (V.map Y.subtype).map L.subtype =
      ⁅L.pCoreIn 2,L ⊓ M⁆ := by
    rw [hV,map_commutator,map_subtype_centralizer_singleton L t]
    rfl
  have hUamb : (U.map j).map M.subtype =
      ⁅L.pCoreIn 2,L ⊓ M⁆ ⊓ centralizer (L ⊓ M : Subgroup G) := by
    rw [←hVamb]
    ext x
    constructor
    · rintro ⟨y,⟨u,hu,rfl⟩,rfl⟩
      have hh := hU.le hu
      refine ⟨mem_map_of_mem L.subtype (mem_map_of_mem Y.subtype hh.1),?_⟩
      intro b hb
      have hy : (⟨b,hb.1⟩ : L) ∈ Y :=
        mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp hb.2))
      exact congrArg (fun a : Y => a.val.val)
        (mem_center_iff.mp hh.2 ⟨⟨b,hb.1⟩,hy⟩)
    · rintro ⟨⟨y,⟨v,hv,rfl⟩,rfl⟩,hc⟩
      change M.subtype (j v) ∈ (U.map j).map M.subtype
      apply mem_map_of_mem M.subtype
      apply mem_map_of_mem j
      apply hU.ge
      refine ⟨hv,mem_center_iff.mpr ?_⟩
      intro b
      apply Subtype.ext
      apply Subtype.ext
      exact hc b.val.val ⟨b.val.property,(j b).property⟩
  intro x hx
  have hn : x.val ∈ normalizer ((U.map j).map M.subtype : Set G) := by
    rw [hUamb]
    exact (short_normalizers L t.val).2 ⟨hx,x.property⟩
  have hh := le_normalizer_comap (H := (U.map j).map M.subtype) M.subtype hn
  rwa [comap_map_eq_self_of_injective M.subtype_injective] at hh
end UnitarySource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- A prescribed residual Sylow extends to the ambient centralizer, contains
the original core and lies in the original full normalizer. -/
theorem Preparation.unitary_short_centralizer_sylow_extension
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (t : L) (ht : t.val ∈ L.pCoreIn 2)
    (R : Sylow 2 (centralizer ({t} : Set L))) :
    ∃ P : Sylow 2 (centralizer ({t.val} : Set G)),
      (P : Subgroup _).comap (UnitarySource.shortCentralizerEmbedding L t) = R ∧
      L.pCoreIn 2 ≤ (P : Subgroup _).map (centralizer ({t.val} : Set G)).subtype ∧
      (P : Subgroup _).map (centralizer ({t.val} : Set G)).subtype ≤ normalizer (L : Set G) := by
  let Y := centralizer ({t} : Set L)
  let M := centralizer ({t.val} : Set G)
  let j := UnitarySource.shortCentralizerEmbedding L t
  obtain ⟨P,hP⟩ := R.exists_comap_eq_of_injective
    (UnitarySource.shortCentralizerEmbedding_injective L t)
  have hQY : pCore 2 L ≤ Y := by
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact ((d.unitary_core_centralizer h hH hp m hm hc).ge
      (mem_map_of_mem L.subtype hx) t.val ht).symm
  have hQR : (pCore 2 L).subgroupOf Y ≤ (R : Subgroup Y) :=
    (pCore_isPGroup.comap_subtype (K := Y)).le_sylow_of_normal R
  have hQP : L.pCoreIn 2 ≤ (P : Subgroup M).map M.subtype := by
    rintro x ⟨a,ha,rfl⟩
    have hmem : j ⟨a,hQY ha⟩ ∈ (P : Subgroup M) := by
      change (⟨a,hQY ha⟩ : Y) ∈ (P : Subgroup M).comap j
      rw [hP]
      exact hQR ha
    exact mem_map_of_mem M.subtype hmem
  refine ⟨P,hP,hQP,?_⟩
  have hnorm := pgroup_le_normalizer_maxJ T _ (P.isPGroup'.map M.subtype)
    (by rwa [d.unitary_thompson h hH hp m hm hc])
  rwa [d.unitary_thompson_normalizer h hH hp m hm hc] at hnorm

/-- The same roots and full-line quotient have ambient and quotient Sylows
with the exact original residual intersection. -/
theorem Preparation.unitary_short_quotient_ambient_sylow
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    1 < m ∧ n = 2*m ∧
    ∃ t : L, orderOf t.val = 2 ∧
    ∃ z : centralizer ({t} : Set L), orderOf z.val.val = 2 ∧
      z.val.val ∈ (center (residual H)).map (residual H).subtype ∧
      centralizer ({t.val} : Set G) ⊓ centralizer ({z.val.val} : Set G) ≤
        normalizer (L : Set G) ∧
    ∃ U : Subgroup (centralizer ({t} : Set L)),
    ∃ hU : U ≤ center (centralizer ({t} : Set L)),
      let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
      let f := UnitarySource.shortLineQuotientMap L t U hU
      U ≤ V ∧ IsElementaryAbelian 2 V ∧
      (V.map (centralizer ({t} : Set L)).subtype).map L.subtype ≤ L.pCoreIn 2 ∧
      Nat.card V = (2^m)^3 ∧ Nat.card U = 2^m ∧ f.ker = U ∧
      IsElementaryAbelian 2 (V.map f) ∧ Nat.card (V.map f) = (2^m)^2 ∧
      zpowers (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) < U ∧
      f (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) = 1 ∧
      f z ≠ 1 ∧
      Nat.card {x : centralizer ({t} : Set L) // IsConj z x} = (2^m)^2 - 1 ∧
      (∀ v ∈ V.map f, v ≠ 1 →
        ∃! x : centralizer ({t} : Set L), IsConj z x ∧ f x = v) ∧
      U = V ⊓ center (centralizer ({t} : Set L)) ∧
      V.map (centralizer ({t} : Set L)).subtype =
        ⁅pCore 2 L,centralizer ({t} : Set L)⁆ ∧
      (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G)) ≤
        UnitarySource.shortLineNormalizer L t U ∧
      ∃ R : Sylow 2 (centralizer ({t} : Set L)),
        (R : Subgroup _) ≤ centralizer ({z} : Set _) ∧
      ∃ P : Sylow 2 (centralizer ({t.val} : Set G)),
        (P : Subgroup _).comap (UnitarySource.shortCentralizerEmbedding L t) = R ∧
        L.pCoreIn 2 ≤ (P : Subgroup _).map (centralizer ({t.val} : Set G)).subtype ∧
        (P : Subgroup _).map (centralizer ({t.val} : Set G)).subtype ≤ normalizer (L : Set G) ∧
        (P : Subgroup _) ≤ UnitarySource.shortLineNormalizer L t U ∧
      ∃ Pbar : Sylow 2 (UnitarySource.shortLineNormalizer L t U ⧸
          UnitarySource.shortLineKernel L t U),
        (Pbar : Subgroup _) =
          ((P : Subgroup _).subgroupOf (UnitarySource.shortLineNormalizer L t U)).map
            (QuotientGroup.mk' (UnitarySource.shortLineKernel L t U)) ∧
        (Pbar : Subgroup _).comap f = R := by
  obtain ⟨hm',hn,e,_,_,_,hcommon⟩ :=
    d.unitary_short_root_common_centralizers h hH hp m hm hc
  have hr := d.reduced_parabolic_residuals h hH.1.1.2 hp
    (hc.elim (fun he => .unitary m hm he) (fun he => .unitaryExtension m hm he))
  obtain ⟨a,hat,haz⟩ := ChapterF.UnitarySource.FourShortMarked.marked_plane_equiv
    (ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L))
    L (residual H) hr m hm hm' e
  let t := a (shortLocal (MatrixField m) (fieldConj m) (fieldConj_involutive m hm))
  obtain ⟨ht,z,hzmark,hz,U,hV,hVQ,hVc,hUc,hindex,hUV,hU,htU,hfusion,hcomm,_,hclass,hSylow,hlift,hline⟩ :=
    short_quotient_from_marked_equiv m hm hm' a
  have hzc : z.val.val ∈ (center (residual H)).map (residual H).subtype := by
    rw [hzmark]
    exact haz
  have hC : centralizer ({t.val} : Set G) ⊓ centralizer ({z.val.val} : Set G) ≤
      normalizer (L : Set G) := by
    rw [show t.val = (ChapterF.UnitarySource.FourShortTransport.sourceShort m hm e).val from hat]
    exact hcommon z.val.val hzc hz
  let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
  let f := UnitarySource.shortLineQuotientMap L t U hU
  have hker : f.ker = U := UnitarySource.shortLineQuotientMap_ker L t U hU
  let : IsElementaryAbelian 2 V := hV
  have hcV : Nat.card (V.map f) = (2^m)^2 := by
    rw [←relIndex_ker,hker]
    exact hindex
  have hfusion := hfusion f hker.ge
  have hzne : f z ≠ 1 := by
    let : Nontrivial (V.map f) := Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hcV]
      exact Nat.one_lt_pow (by decide) (Nat.one_lt_pow (by omega) (by decide)))
    obtain ⟨v,hv⟩ := exists_ne (1 : V.map f)
    have hvne : v.val ≠ 1 := fun he => hv (Subtype.ext he)
    obtain ⟨a,ha,he⟩ := hfusion v.val v.property hvne
    intro hzero
    rw [hzero,mul_one,mul_inv_cancel] at he
    exact hvne he.symm
  have htkill : f (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) = 1 :=
    MonoidHom.mem_ker.mp (hker.ge (htU.le (mem_zpowers _)))
  have hlifts := hlift f hker
  have htQ : t.val ∈ L.pCoreIn 2 := hVQ
    (mem_map_of_mem L.subtype (mem_map_of_mem (centralizer ({t} : Set L)).subtype
      (hUV (htU.le (mem_zpowers _)))))
  obtain ⟨R,hRz⟩ := hSylow
  obtain ⟨P,hPR,hQP,hPL⟩ :=
    d.unitary_short_centralizer_sylow_extension h hH hp m hm hc t htQ R
  have hLN := UnitarySource.short_local_le_line_normalizer L t U V hcomm hline
  have hPN : (P : Subgroup _) ≤ UnitarySource.shortLineNormalizer L t U := by
    intro x hx
    exact hLN (hPL (mem_map_of_mem (centralizer ({t.val} : Set G)).subtype hx))
  let N := UnitarySource.shortLineNormalizer L t U
  let q := QuotientGroup.mk' (UnitarySource.shortLineKernel L t U)
  let Pbar := (P.subtype hPN).mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hUP : U.map (UnitarySource.shortCentralizerEmbedding L t) ≤ (P : Subgroup _) := by
    rintro x ⟨u,hu,rfl⟩
    have hh := hQP (hVQ (mem_map_of_mem L.subtype
      (mem_map_of_mem (centralizer ({t} : Set L)).subtype (hUV hu))))
    obtain ⟨a,ha,he⟩ := hh
    have he' : a = UnitarySource.shortCentralizerEmbedding L t u := Subtype.ext he
    exact he' ▸ ha
  have hkerP : q.ker ≤ (P : Subgroup _).subgroupOf N := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact hUP hx
  have hbar : (Pbar : Subgroup _).comap f = R := by
    change (((P : Subgroup _).subgroupOf N).map q).comap
      (q.comp (UnitarySource.shortLineNormalizerMap L t U hU)) = R
    rw [←comap_comap,comap_map_eq_self hkerP]
    exact hPR
  exact ⟨hm',hn,t,ht,z,hz,hzc,hC,U,hU,hUV,hV,hVQ,hVc,hUc,hker,
    IsElementaryAbelian.map f,hcV,htU,htkill,hzne,hclass,hlifts,hline,hcomm,hLN,
    R,hRz,P,hPR,hQP,hPL,hPN,Pbar,rfl,hbar⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
