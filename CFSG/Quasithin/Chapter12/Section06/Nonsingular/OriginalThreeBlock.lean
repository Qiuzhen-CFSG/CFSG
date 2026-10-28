module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalThree
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.MinimalParabolic.IndexThree
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Selection
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure

/-!
# The actual alternating-three block in the original overgroup

The constructed X contains Q and has quotient S3 and Sylow subgroup R_v.
Characteristic two passes from N_G(L) through LT to X. Transport the proved
characteristic-subgroup obstruction along the literal Sylow inclusion and
apply the genuine solvable index-three theorem: O^2(X) is an A3-block, its
two-core is elementary of order four, and its core quotient has order three.
The same X retains its core Q, original Sylow R_v and generation with C_LT(v).

The following original-block modules propagate this seed to L. No block
premise is added to the source hypotheses. Source: Aschbacher--Smith C.1.29
and 12.6.18, printed pp.133 and 827, combined manuscript of 1 March 2004.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

omit [IsElementaryAbelian 2 V] in
/-- Restrict characteristic two from the original normalizer through LT to
an overgroup of its actual two-core. -/
theorem SourceHypothesis.original_core_overgroup_characteristic_two
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (X : Subgroup G) (hX : X ≤ LT T L) (hQ : Q T L ≤ X) :
    centralizer (pCore 2 X : Set X) ≤ pCore 2 X := by
  let J := LT T L
  have hJM : J ≤ M L := sup_le L.le_normalizer H.chosen.sylow_normalizes_component
  have hf := generalizedFitting_eq_pCore_of_sylow_overgroup T J (M L)
    le_sup_right hJM (Chapter1.mem_He_iff.mp H.normalizer_mem_He)
  have hc : centralizer (pCore 2 J : Set J) ≤ pCore 2 J := by
    rw [←hf]
    exact centralizer_generalizedFitting_le J
  have hQX : pCore 2 J ≤ X.subgroupOf J := fun x hx => hQ (mem_map_of_mem J.subtype hx)
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hX)).mp
    (centralizer_pCore_le_of_pCore_le (X.subgroupOf J) hc hQX)

omit [IsElementaryAbelian 2 V] in
/-- The literal residual of the constructed three-letter overgroup is the
A3-block from the source, with its four-core and cubic quotient. -/
theorem SourceHypothesis.nonsingular_three_residual_block
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (v : V) (hn : ¬ normalizer (Rv T L (v : G) : Set G) ≤ M L)
    (X : Subgroup G) (hX : X ≤ LT T L) (hRX : Rv T L (v : G) ≤ X)
    (hq : Nonempty (Star X ≃* Equiv.Perm (Fin 3)))
    (hs : Chapter1.IsSylowIn 2 (Rv T L (v : G)) X)
    (hgen : X ⊔ (LT T L ⊓ Gv (v : G)) = LT T L) :
    IsElementaryAbelian 2 (pCore 2 (pResidual 2 X)) ∧
      Nat.card (pCore 2 (pResidual 2 X)) = 4 ∧
      Nat.card (pResidual 2 X ⧸ pCore 2 (pResidual 2 X)) = 3 ∧
      ChapterC.IsBlock (pResidual 2 X) ∧
      ChapterC.IsAlternatingBlock (pResidual 2 X) 3 := by
  obtain ⟨e⟩ := hq
  obtain ⟨S,hS⟩ := hs
  have hi := SymmetricThreeTwoCore.sylow_index_three e S
  have hc := H.original_core_overgroup_characteristic_two X hX ((Q_le_Rv H.chosen v).trans hRX)
  have hlocal : Stellmacher.SectionTwo.Hypotheses X :=
    ChapterC.RankOne.Solvable.sectionTwoHypotheses_of_proper_subgroup
      (SymmetricThreeTwoCore.solvable e) hc (S : Subgroup X)
      (lt_top_iff_ne_top.mpr (fun he => by have hh := index_eq_one.mpr he; omega))
  apply ChapterC.RankOne.Solvable.MinimalParabolic.index_three_residual hlocal S hi
  let a : S ≃* Rv T L (v : G) := (equivMapOfInjective (S : Subgroup X)
    X.subtype X.subtype_injective).trans (MulEquiv.subgroupCongr hS)
  intro B hB hne hnormal
  let : B.Characteristic := hB
  let A := B.map a.toMonoidHom
  let : A.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro f x hx
    obtain ⟨y,hy,rfl⟩ := hx
    refine ⟨(MulAut.congr a.symm f) y,
      characteristic_iff_le_comap.mp inferInstance (MulAut.congr a.symm f) hy, ?_⟩
    exact a.apply_symm_apply (f (a y))
  have hA : A ≠ ⊥ := fun hh => hne ((map_eq_bot_iff_of_injective B a.injective).mp hh)
  have hmap : A.map (Rv T L (v : G)).subtype =
      (B.map (S : Subgroup X).subtype).map X.subtype := by
    rw [map_map, map_map]
    rfl
  apply H.nonsingular_three_characteristic_obstruction v hn X hgen A hA
  rw [hmap]
  apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mp
  simpa only [subgroupOf,comap_map_eq_self_of_injective X.subtype_injective] using hnormal

/-- Construct the source A3-block inside the same original X. -/
theorem SourceHypothesis.nonsingular_original_three_block
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (v : V) (hv : D.Nonsingular v)
    (hn : ¬ normalizer (Rv T L (v : G) : Set G) ≤ M L) :
    ∃ X : Subgroup G, X ≤ LT T L ∧ Rv T L (v : G) ≤ X ∧
      X.pCoreIn 2 = Q T L ∧ Nonempty (Star X ≃* Equiv.Perm (Fin 3)) ∧
      Chapter1.IsSylowIn 2 (Rv T L (v : G)) X ∧
      X ⊔ (LT T L ⊓ Gv (v : G)) = LT T L ∧
      IsElementaryAbelian 2 (pCore 2 (pResidual 2 X)) ∧
      Nat.card (pCore 2 (pResidual 2 X)) = 4 ∧
      Nat.card (pResidual 2 X ⧸ pCore 2 (pResidual 2 X)) = 3 ∧
      ChapterC.IsBlock (pResidual 2 X) ∧
      ChapterC.IsAlternatingBlock (pResidual 2 X) 3 := by
  have hlt : Q T L < Rv T L (v : G) := lt_of_le_of_ne (Q_le_Rv H.chosen v)
    (fun heq => hn (heq ▸ H.core_normalizer_le))
  obtain ⟨X,hX,hRX,hcore,hq,hs,hgen⟩ := H.nonsingular_original_three_overgroup D hTV v hv hlt
  exact ⟨X,hX,hRX,hcore,hq,hs,hgen,H.nonsingular_three_residual_block v hn X hX hRX hq hs hgen⟩

end CFSG.Quasithin.Chapter12.Section06
