module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.WeakClosureOne
public import Theory.GroupTheory.SolvableResidual.NormalSupplement
public import Theory.GroupTheory.CentralizerDisplacementNormalization
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.EightPointSolvable

/-!
# Escape of the original abelian-branch solvable residual

A perfect subgroup in M fixing the original point normalizes V by TI.
Its permutation action fixes the same point, so solvability of that
stabilizer makes it centralize the full V. If H∞ lay in M, its commutator
with L would therefore lie in O₂(L). Since O₂(L) lies in T and normalizes
H∞, the solvable residual of H∞O₂(L) is H∞. Thus L normalizes H∞.
Characteristic two then supplies a nontrivial two-core normalized by LTH,
contradicting the proved O₂(LTH)=1.

Earlier point, intersection, TI and nonsingular-centralizer inputs remain
explicit. This proves the escape step following12.6.29, without using the
component selected in the contrary-nonabelian branch.
Source: Aschbacher--Smith, printed p.835.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open BinaryPermutation BinaryPermutation.TerminalOrthogonal
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

private theorem perfect_hom_trivial {A B : Type*} [Group A] [Group B]
    [Group.IsPerfect A] [Group.IsSolvable B] (f : A →* B) : f = 1 := by
  apply MonoidHom.range_eq_bot_iff.mp
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  by_contra hn
  let : Nontrivial f.range := (nontrivial_iff_ne_bot _).mpr hn
  exact Group.IsPerfect.not_isSolvable f.range inferInstance

/-- The full permutation stabilizer of the original point is solvable. -/
theorem SourceHypothesis.original_point_permutation_stabilizer_solvable
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G)) :
    Group.IsSolvable (BinaryNaturalDual.VectorStabilizers.representationStabilizer (naturalRepresentation (Fin 8)) (D.fullCoordinates hZ z).toAdd) := by
  let E := D.fullSetup hZ T z
  let J := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf J
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer S.chosen.sylow_normalizes_component)
  obtain ⟨P,hP⟩ := (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).exists_subgroupOf_eq_of_normal A
  let e : A ≃* L := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  let q : L →* alternatingGroup (Fin 8) := D.groupEquiv.toMonoidHom.comp
    (QuotientGroup.mk' (conjugation L V S.chosen.normalizes).ker)
  have hq : Function.Surjective q := D.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  let fA := q.comp e.toMonoidHom
  let Q := P.mapSurjective (f := fA) (hq.comp e.surjective)
  have hTC : (T : Subgroup G) ≤ E.Gz := hTz.trans
    (normalizer_le_centralizer_of_card_two E.V₁ (E.point_card hz))
  have hfix : ∀ g ∈ (Q : Subgroup (alternatingGroup (Fin 8))),
      naturalRepresentation (Fin 8) g.val (D.fullCoordinates hZ z).toAdd =
        (D.fullCoordinates hZ z).toAdd := by
    rintro g ⟨a,ha,rfl⟩
    have hat : (e a : G) ∈ (T : Subgroup G) := by rw [hP] at ha; exact ha
    have he : conjugation L V S.chosen.normalizes (e a) z = z := by
      apply Subtype.ext
      have hh := hTC hat z.val (mem_zpowers _)
      change (e a : G)*z.val*(e a : G)⁻¹=z.val
      rw [←hh,mul_inv_cancel_right]
    exact (D.fullCoordinates_equivariant hZ (e a) z).symm.trans
      (congrArg (fun v : V => (D.fullCoordinates hZ v).toAdd) he)
  have hn : (D.fullCoordinates hZ z).toAdd ≠ 0 := by
    intro he
    exact hz ((D.fullCoordinates hZ).injective (he.trans (D.fullCoordinates hZ).map_one.symm))
  exact Eight.sylow_fixed_stabilizer_solvable Q (D.fullCoordinates hZ z).toAdd hn hfix

/-- A perfect subgroup of the original M fixing z centralizes the full V. -/
theorem SourceHypothesis.original_perfect_point_subgroup_centralizes
    (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (A : Subgroup G) [Group.IsPerfect A]
    (hAM : A ≤ M L) (hAz : A ≤ (D.fullSetup hZ T z).Gz) :
    A ≤ centralizer (V : Set G) := by
  let E := D.fullSetup hZ T z
  have hAN : A ≤ normalizer (V : Set G) := by
    intro x hx
    apply Mv_le_module_normalizer_of_TI hTI z hz
    exact ⟨hAM hx,by
      have hh : x ∈ E.Gz := hAz hx
      rwa [E.Gz_eq] at hh⟩
  obtain ⟨f,_,hf⟩ := S.original_normalizer_permutation_action D hZ hTV
  let C := BinaryNaturalDual.VectorStabilizers.representationStabilizer (naturalRepresentation (Fin 8)) (D.fullCoordinates hZ z).toAdd
  have ha (a : A) : V.normalizerMonoidHom ⟨a.val,hAN a.property⟩ z = z := by
    apply Subtype.ext
    have hh := hAz a.property z.val (mem_zpowers _)
    change a.val*z.val*a.val⁻¹=z.val
    rw [←hh,mul_inv_cancel_right]
  let g : A →* C := (f.comp (inclusion hAN)).codRestrict _ (fun a => by
    change naturalRepresentation (Fin 8) (f ⟨a.val,hAN a.property⟩)
      (D.fullCoordinates hZ z).toAdd = (D.fullCoordinates hZ z).toAdd
    rw [←hf,ha])
  let : Group.IsSolvable C := S.original_point_permutation_stabilizer_solvable D hZ z hz hTz
  have hg := perfect_hom_trivial g
  intro a ha v hv
  have hg' : f ⟨a,hAN ha⟩ = 1 := congrArg (fun k : A →* C => (k ⟨a,ha⟩).val) hg
  have he := hf ⟨a,hAN ha⟩ ⟨v,hv⟩
  rw [hg',map_one,Module.End.one_apply] at he
  have hh := congrArg (fun x : V => x.val) ((D.fullCoordinates hZ).injective he)
  change a*v*a⁻¹=v at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- The original H has a solvable residual outside M. The perfect residual
cannot act in the solvable point stabilizer; normalization then contradicts
the trivial two-core of the original generated join. -/
theorem SourceHypothesis.original_abelian_residual_escapes
    (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz) :
    ¬ (solvableResidual H).map H.subtype ≤ M L := by
  let E := D.fullSetup hZ T z
  let R := (solvableResidual H).map H.subtype
  have hRH : R ≤ H := map_subtype_le _
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  have hHR : H ≤ normalizer (R : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (solvableResidual H))
  let : Group.IsPerfect R := Group.IsPerfect.map H.subtype
  have hRne : R ≠ ⊥ := by
    intro he
    have hr : solvableResidual H = ⊥ :=
      ((solvableResidual H).map_eq_bot_iff_of_injective H.subtype_injective).mp he
    let : Group.IsSolvable (solvableResidual H) := by rw [hr]; infer_instance
    let : Group.IsSolvable H := Group.isSolvable_of_ker_le_range
      (solvableResidual H).subtype (QuotientGroup.mk' (solvableResidual H))
      (by rw [range_subtype,QuotientGroup.ker_mk'])
    exact hH.2.2 (S.original_solvable_overgroup_le D hZ z hz hTV hTz hbound hTI hns hTH)
  intro hRM
  have hRC := S.original_perfect_point_subgroup_centralizes D hZ z hz hTV hTz hTI R hRM
    (hRH.trans hH.2.1)
  have hcomm : ⁅R,L⁆ ≤ L.pCoreIn 2 := by
    rw [←S.centralizer_eq_core]
    apply le_inf
    · exact le_normalizer_iff_commutator_le_right.mp hRM
    · exact (commutator_mono hRC le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp
          (S.chosen.normalizes.trans (normalizer_le_normalizer_centralizer _)))
  have hQT : L.pCoreIn 2 ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 L).le_sylow_of_normalized T
      (S.chosen.sylow_normalizes_component.trans
        (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
  let : Group.IsNilpotent (L.pCoreIn 2) := (isPGroup_pCoreIn 2 L).isNilpotent
  have hres : (solvableResidual (R ⊔ L.pCoreIn 2 : Subgroup G)).map
      (R ⊔ L.pCoreIn 2).subtype = R :=
    map_solvableResidual_sup_eq_of_perfect_normalized R (L.pCoreIn 2)
      (hQT.trans (hTH.trans hHR))
  have hLR : L ≤ normalizer (R : Set G) := by
    rw [←hres]
    exact (normalizes_sup_of_displacement L R (L.pCoreIn 2)
      (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))) hcomm).trans
        (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
  have hcharH : centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
    rw [←S.point_local_characteristic D hZ z hH]
    exact centralizer_generalizedFitting_le H
  let : (R.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHR
  have hcharR : centralizer (pCore 2 R : Set R) ≤ pCore 2 R :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hRH)).mp
      (normal_core_selfCentralizing hcharH (R.subgroupOf H))
  have hcore : R.pCoreIn 2 ≠ ⊥ := by
    intro he
    have hr : pCore 2 R = ⊥ := ((pCore 2 R).map_eq_bot_iff_of_injective R.subtype_injective).mp he
    have ht : (⊤ : Subgroup R) ≤ (⊥ : Subgroup R) := by
      intro r _
      have hm : r ∈ pCore 2 R := hcharR (by
        intro x hx
        have hx' : x = 1 := mem_bot.mp (hr ▸ hx)
        simp only [hx',one_mul,mul_one])
      exact hr ▸ hm
    apply hRne
    apply bot_unique
    intro r hrR
    have hh : (⟨r,hrR⟩ : R) = 1 := mem_bot.mp (ht (mem_top _))
    exact congrArg Subtype.val hh
  let J := L ⊔ (T : Subgroup G) ⊔ H
  have hJC : J ≤ normalizer (R.pCoreIn 2 : Set G) :=
    (sup_le (sup_le hLR (hTH.trans hHR)) hHR).trans
      (normalizer_le_normalizer_characteristic_image R (pCore 2 R))
  have hCJ : R.pCoreIn 2 ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 R) ((pCoreIn_le 2 R).trans (hRH.trans le_sup_right)) hJC
  have hzJ : J.pCoreIn 2 = ⊥ := by
    change (pCore 2 J).map J.subtype = ⊥
    rw [S.point_join_core_eq_bot D hZ z hH,Subgroup.map_bot]
  exact hcore (bot_unique (hCJ.trans_eq hzJ))

end CFSG.Quasithin.Chapter12.Section06
