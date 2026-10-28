module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSixCubicCorePair
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSixCubicPlacement
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SixParabolics
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryThreePlacement

/-!
# The two actual source parabolics in the remaining cubic row

The same original L supplies two concrete characteristic-two subgroups,
each with S₃ two-core quotient and not an A₃ product. They contain the same
original Sylow intersection and generate L. Their normalization follows
pointwise whenever the original Sylow actor has natural central action.
This is a produced pair, not an assumed block or source-family callback.
The naturality of the actual source action remains a separate duty.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterC ChapterC.C27Source
open CaseIComponentData
variable {G : Type*} [Group G] [Finite G]

private theorem cubic_parabolic_not_aThree
    {X : Type*} [Group X] [Finite X] (hf : generalizedFitting X = pCore 2 X)
    (P : Subgroup X) (hP : pCore 2 X ≤ P)
    (f : P →* Equiv.Perm (Fin 4)) (hs : Function.Surjective f)
    (hk : f.ker = (pCore 2 X).subgroupOf P) :
    ¬ 9 ∣ Nat.card P ∧ 12 < Nat.card (pResidual 2 P) := by
  let a := Matrix.PSL3Two.MarkedAutomorphisms.lineEquivSymmetric.symm
  let g := a.toMonoidHom.comp f
  have hg : Function.Surjective g := a.surjective.comp hs
  have hgk : g.ker = (pCore 2 X).subgroupOf P :=
    (MonoidHom.ker_comp_of_injective f a.toMonoidHom a.injective).trans hk
  have h12 : Nat.card (pResidual 2 Matrix.PSL3Two.lineParabolicSL) = 12 := by
    have hh := Matrix.PSL3Two.MarkedAutomorphisms.card_line_residual
    rw [Matrix.PSL3Two.MarkedAutomorphisms.residual,
      card_map_of_injective Matrix.PSL3Two.lineParabolicSL.subtype_injective] at hh
    exact hh
  have hn : pResidual 2 Matrix.PSL3Two.lineParabolicSL ≠ ⊥ := by
    intro he
    rw [he,card_bot] at h12
    omega
  refine ⟨?_,?_⟩
  · have hh := f.ker.card_mul_index
    rw [index_ker,f.range_eq_top_of_surjective hs,card_top,Nat.card_perm,Nat.card_fin] at hh
    obtain ⟨r,hr⟩ := (show IsPGroup 2 f.ker from hk ▸ pCore_isPGroup.comap_subtype).exists_card_eq
    rw [hr] at hh
    intro hd
    rw [←hh] at hd
    exact (by decide : ¬9 ∣ Nat.factorial 4)
      (((by decide : Nat.Coprime 9 2).pow_right r).dvd_of_dvd_mul_left hd)
  · rw [←h12]
    exact CaseIComponentData.residual_card_lt_of_characteristic_core P
      (hf ▸ centralizer_generalizedFitting_le X) hP g hg hgk hn

/-- Two actual local source candidates in the same remaining central-A6
component. The only unproved invariance input is the displayed naturality
of each actual marked Sylow actor on the literal central core quotient. -/
theorem PreparedChosenModule.raw_six_cubic_source_pair
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V Z1 L : Subgroup G} (h : PreparedChosenModule T M V)
    (hTM : (T : Subgroup G) ≤ M)
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hL : L ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hf : generalizedFitting L = pCore 2 L)
    (e : ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃* alternatingGroup (Fin 6))
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3) :
    let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
    ∃ hn : S ≤ normalizer (L : Set G), ∃ P Q : Subgroup G,
      P ≤ L ∧ Q ≤ L ∧ S ⊓ L ≤ P ∧ S ⊓ L ≤ Q ∧ P ⊔ Q = L ∧
      generalizedFitting P = pCore 2 P ∧ generalizedFitting Q = pCore 2 Q ∧
      Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty ((Q ⧸ pCore 2 Q) ≃* Equiv.Perm (Fin 3)) ∧
      ¬IsAThreeProduct P ∧ ¬IsAThreeProduct Q ∧
      ∀ x : S,
        MulAut.centralQuotientAction e (pCoreNormalizerAction 2 L (inclusion hn x)) ∈
          _root_.AlternatingSix.ShadowLocal.natural →
        (x : G) ∈ normalizer (P : Set G) ∧ (x : G) ∈ normalizer (Q : Set G) := by
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  have hn := (h.raw_six_central_sylow_module_normalizes hG T hTM hZ hZne hL hq e).1
  obtain ⟨S0,hS0⟩ := ComponentModels.source20_sylow_intersection hL.2
  obtain ⟨A,B,hSA,hSB,hgen,hfA,hfB,⟨fA,hsA,hkA⟩,⟨fB,hsB,hkB⟩,⟨eA⟩,⟨eB⟩,hinv⟩ :=
    RawSixCubicSplit.full_core_pair hf hq.toIsPerfect e
      (IsPGroup.of_card (n := 1) (by simpa using hc)) S0
  let P := A.map L.subtype
  let Q := B.map L.subtype
  let a : A ≃* P := A.equivMapOfInjective L.subtype L.subtype_injective
  let b : B ≃* Q := B.equivMapOfInjective L.subtype L.subtype_injective
  have hnot (D : Subgroup L) (hSD : (S0 : Subgroup L) ≤ D)
      (f : D →* Equiv.Perm (Fin 4)) (hs : Function.Surjective f)
      (hk : f.ker = (pCore 2 L).subgroupOf D) : ¬IsAThreeProduct (D.map L.subtype) := by
    obtain ⟨h9,h12⟩ := cubic_parabolic_not_aThree hf D
      ((pCore_isPGroup.le_sylow_of_normal S0).trans hSD) f hs hk
    let d := D.equivMapOfInjective L.subtype L.subtype_injective
    rw [Nat.card_congr d.toEquiv] at h9
    have hh := congrArg (fun K : Subgroup (D.map L.subtype) => Nat.card K)
      (map_pResidual_of_surjective 2 d.toMonoidHom d.surjective)
    rw [card_map_of_injective d.injective] at hh
    rw [hh] at h12
    intro hA
    have hh' := CaseIComponentData.aThreeProduct_residual_card_le (D.map L.subtype) h9 hA
    omega
  refine ⟨hn,P,Q,map_subtype_le _,map_subtype_le _,?_,?_,?_,?_,?_,
    ⟨(QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans eA⟩,
    ⟨(QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm.trans eB⟩,
    hnot A hSA fA hsA hkA,hnot B hSB fB hsB hkB,?_⟩
  · rw [←hS0]
    exact map_mono hSA
  · rw [←hS0]
    exact map_mono hSB
  · rw [←Subgroup.map_sup,hgen,←MonoidHom.range_eq_map,range_subtype]
  · rw [←map_generalizedFitting_equiv a,←pCore_map_iso 2 a,hfA]
  · rw [←map_generalizedFitting_equiv b,←pCore_map_iso 2 b,hfB]
  · intro x hx
    let t := L.normalizerMonoidHom (inclusion hn x)
    have hnS : S ≤ normalizer (S ⊓ L : Set G) :=
      (le_inf S.le_normalizer hn).trans inf_normalizer_le_normalizer_inf
    have ht : (S0 : Subgroup L).map t.toMonoidHom = S0 := by
      apply map_injective L.subtype_injective
      rw [map_map]
      have he : L.subtype.comp t.toMonoidHom =
          (MulAut.conj (x : G)).toMonoidHom.comp L.subtype := by ext y; rfl
      rw [he,←map_map,hS0]
      exact mem_normalizer_iff_map_conj_eq.mp (hnS x.property)
    obtain ⟨ha,hb⟩ := hinv t hx ht
    have lift (D : Subgroup L) (hd : D.map t.toMonoidHom = D) :
        (x : G) ∈ normalizer (D.map L.subtype : Set G) := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      rw [map_map]
      change D.map ((MulAut.conj (x : G)).toMonoidHom.comp L.subtype) = D.map L.subtype
      have he : (MulAut.conj (x : G)).toMonoidHom.comp L.subtype =
          L.subtype.comp t.toMonoidHom := by ext y; rfl
      rw [he,←map_map,hd]
    exact ⟨lift A ha,lift B hb⟩

end CFSG.Quasithin.Chapter15.Section01
