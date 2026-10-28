module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.OuterSylow
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.Nonfusion
public import Theory.GroupTheory.CharacteristicCentralizerSylow
public import Theory.GroupTheory.SylowCentralizerConjugacy

/-!
# The ambient normalizer step for outer symplectic involutions

Choose an outer involution with maximal centralizer in the original Sylow.
Conjugation inside either full normalizer preserves being outside its pure
factor. Sylow conjugacy and maximality therefore make its centralizer in T
Sylow in both full endpoint centralizers, for the same chosen involution.

The previously proved strict ambient centralizer growth then supplies a
larger two-normalizer escaping both endpoints. Root nonfusion and the TI
property force every subgroup of Z(S) preserved by that normalizer to avoid
both root centers. Applying this to the characteristic subgroup
Z(C_T(f)) intersect [C_T(f), C_T(f)] isolates the remaining native step.

Source: Aschbacher–Smith F.4.37, printed p.293 of refs/quasithin.pdf,
applied to the original pair in 5.3.1–3, pp.658–659. Both orientations,
the whole residual, and q=4 are retained. Native center-derived placement,
the nonbinary root intersection, and the binary fixed-group exception still
have to exclude the resulting configuration. This module asserts neither
S=T nor the unconditional full-extension order bound.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
include d h hH hp hm hF he

/-- A largest outer centralizer in T is already Sylow in each endpoint centralizer. -/
theorem Preparation.symplectic_maximal_outer_centralizer
    (hst : sourceS L H ≠ (T : Subgroup G)) :
    ∃ f : T, orderOf f=2 ∧ f.val ∉ sourceS L H ∧
      (∀ g : T, orderOf g=2 → g.val ∉ sourceS L H →
        Nat.card (centralizer ({g} : Set T)) ≤ Nat.card (centralizer ({f} : Set T))) ∧
      ∀ i : Fin 2, ∀ U : Subgroup G, IsPGroup 2 U →
        (T : Subgroup G) ⊓ centralizer ({f.val} : Set G) ≤ U →
        U ≤ centralizer ({f.val} : Set G) →
        U ≤ normalizer (![L,residual H] i : Set G) →
        U = (T : Subgroup G) ⊓ centralizer ({f.val} : Set G) := by
  obtain ⟨f₀,hf₀,ho₀⟩ := d.symplectic_outer_involution_exists h hH hp F hm hF he hst
  obtain ⟨f,hf,hmax⟩ := Set.exists_max_image
    {g : T | orderOf g=2 ∧ g.val ∉ sourceS L H}
    (fun g => Nat.card (centralizer ({g} : Set T))) (Set.toFinite _) ⟨f₀,hf₀,ho₀⟩
  refine ⟨f,hf.1,hf.2,fun g hg ho => hmax g ⟨hg,ho⟩,?_⟩
  intro i U hU hCU hUC hUM
  let K := ![L,residual H] i
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) := by
    fin_cases i
    · exact h.sylow_normalizes
    · exact hH.1.1.2.trans (le_normalizer_residual H)
  have hSK : sourceS L H = (T : Subgroup G) ⊓ K :=
    (d.ordinary_sylow_core_geometry h hH.1.1.2
      (d.symplectic_sourceS_le_factors h hH.1.1.2 hp F hm hF he)).1 i
  have hbound (a : normalizer (K : Set G)) (g : T)
      (hag : (MulAut.conj a.val) f.val = g.val) :
      Nat.card (centralizer ({g} : Set T)) ≤ Nat.card (centralizer ({f} : Set T)) := by
    apply hmax g
    constructor
    · have hh := (MulAut.conj a.val).orderOf_eq f.val
      rw [hag] at hh
      exact (Subgroup.orderOf_coe g).symm.trans (hh.trans ((Subgroup.orderOf_coe f).trans hf.1))
    · intro hgS
      have hgK : g.val ∈ K := (hSK ▸ hgS).2
      have hfK : f.val ∈ K := (a.property f.val).mpr (by
        change a.val*f.val*a.val⁻¹=g.val at hag
        rwa [hag])
      exact hf.2 (hSK.symm ▸ (show f.val ∈ (T : Subgroup G) ⊓ K from ⟨f.property,hfK⟩))
  have hh := T.centralizer_prime_overgroup_eq_of_local_card_bound
    (normalizer (K : Set G)) hTK f hbound U hU
    (by rwa [map_subtype_centralizer_singleton]) hUC hUM
  rwa [map_subtype_centralizer_singleton] at hh

/-- Root nonfusion makes the root intersections of every subgroup of Z(S)
invariant under its whole ambient normalizer. -/
theorem Preparation.symplectic_center_subgroup_root_intersection_normalized
    (E : Subgroup G) (hE : E ≤ (center (sourceS L H)).map (sourceS L H).subtype)
    (i : Fin 2) :
    normalizer (E : Set G) ≤ normalizer
      ((E ⊓ (center (![L,residual H] i)).map (![L,residual H] i).subtype : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  have hgx : g*x*g⁻¹ ∈ E := (hg x).mp hx.1
  refine ⟨hgx,?_⟩
  obtain ⟨a,ha,hax⟩ := hE hx.1
  obtain ⟨b,hb,hbx⟩ := hE hgx
  change a.val=x at hax
  change b.val=g*x*g⁻¹ at hbx
  have hab : IsConj a.val b.val := isConj_iff.mpr ⟨g,by rw [hax,hbx]⟩
  have hh := (d.symplectic_root_center_nonfusion h hH hp F hm hF he i a b ha hb hab).mp
    (hax.symm ▸ hx.2)
  rwa [hbx] at hh

/-- A subgroup of the inner Sylow center meeting a root center has its
whole normalizer in the corresponding original endpoint. -/
theorem Preparation.symplectic_center_subgroup_normalizer_le
    (E : Subgroup G) (hE : E ≤ (center (sourceS L H)).map (sourceS L H).subtype)
    (i : Fin 2)
    (hne : E ⊓ (center (![L,residual H] i)).map (![L,residual H] i).subtype ≠ ⊥) :
    normalizer (E : Set G) ≤ normalizer (![L,residual H] i : Set G) := by
  obtain ⟨_,hTI,hn⟩ := d.symplectic_root_center_fusion h hH hp F hm hF he i
  rw [←hn]
  exact (d.symplectic_center_subgroup_root_intersection_normalized h hH hp F hm hF he E hE i).trans
    (hTI.normalizer_le_of_ne_bot hne inf_le_right)

/-- In a larger two-normalizer of an outer centralizer, every invariant
subgroup lying in Z(S) avoids both root centers. -/
theorem Preparation.symplectic_normalized_center_disjoint_roots
    (V : Subgroup G)
    (hout : ∀ i : Fin 2, ¬ V ≤ normalizer (![L,residual H] i : Set G))
    (E : Subgroup G) (hE : E ≤ (center (sourceS L H)).map (sourceS L H).subtype)
    (hn : V ≤ normalizer (E : Set G)) (i : Fin 2) :
    Disjoint E ((center (![L,residual H] i)).map (![L,residual H] i).subtype) := by
  rw [disjoint_iff]
  by_contra hne
  exact hout i (hn.trans (d.symplectic_center_subgroup_normalizer_le h hH hp F hm hF he E hE i hne))

/-- Properness of the inner Sylow produces a larger two-normalizer of a
maximal outer centralizer escaping both original endpoints. -/
theorem Preparation.symplectic_outer_centralizer_normalizer_growth
    (hst : sourceS L H ≠ (T : Subgroup G)) :
    ∃ f : T, orderOf f=2 ∧ f.val ∉ sourceS L H ∧
      (∀ i : Fin 2, Chapter1.IsSylowIn 2
        ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G))
        (normalizer (![L,residual H] i : Set G) ⊓ centralizer ({f.val} : Set G))) ∧
      ∃ V : Subgroup G, IsPGroup 2 V ∧
        (T : Subgroup G) ⊓ centralizer ({f.val} : Set G) < V ∧
        V ≤ centralizer ({f.val} : Set G) ∧
        V ≤ normalizer (((T : Subgroup G) ⊓ centralizer ({f.val} : Set G) : Subgroup G) : Set G) ∧
        (∀ i : Fin 2, ¬ V ≤ normalizer (![L,residual H] i : Set G)) ∧
        ∀ E : Subgroup G, E ≤ (center (sourceS L H)).map (sourceS L H).subtype →
          V ≤ normalizer (E : Set G) →
          ∀ i : Fin 2, Disjoint E ((center (![L,residual H] i)).map (![L,residual H] i).subtype) := by
  obtain ⟨f,hf,ho,_,hmax⟩ := d.symplectic_maximal_outer_centralizer h hH hp F hm hF he hst
  let C := centralizer ({f.val} : Set G)
  let P := (T : Subgroup G) ⊓ C
  have hlocal (i : Fin 2) : Chapter1.IsSylowIn 2 P
      (normalizer (![L,residual H] i : Set G) ⊓ C) := by
    let M := normalizer (![L,residual H] i : Set G) ⊓ C
    have hTM : (T : Subgroup G) ≤ normalizer (![L,residual H] i : Set G) := by
      fin_cases i
      · exact h.sylow_normalizes
      · exact hH.1.1.2.trans (le_normalizer_residual H)
    have hPM : P ≤ M := inf_le_inf_right C hTM
    obtain ⟨Q,hPQ⟩ := ((T.isPGroup'.to_le (show P ≤ (T : Subgroup G) from inf_le_left)).comap_subtype (K := M)).exists_le_sylow
    have hPQ' : P ≤ (Q : Subgroup M).map M.subtype := by
      rw [←map_subgroupOf_eq_of_le hPM]
      exact map_mono hPQ
    exact ⟨Q,hmax i _ (Q.isPGroup'.map M.subtype) hPQ'
      ((map_subtype_le _).trans inf_le_right) ((map_subtype_le _).trans inf_le_left)⟩
  obtain ⟨R,hR⟩ := (T.isPGroup'.comap_subtype (K := C)).exists_le_sylow
  let U := (R : Subgroup C).map C.subtype
  have hPU : P ≤ U := by
    intro x hx
    exact mem_map_of_mem C.subtype (hR (show (⟨x,hx.2⟩ : C) ∈
      (T : Subgroup G).subgroupOf C from hx.1))
  have hlt : P < U := lt_of_le_of_ne hPU (by
    intro heq
    have hh : Chapter1.IsSylowIn 2 P C := ⟨R,heq.symm⟩
    exact d.symplectic_outer_centralizer_not_sylow h hH hp F hm hF he f hf ho hh)
  have hUp : IsPGroup 2 U := R.isPGroup'.map C.subtype
  let V := U ⊓ normalizer (P : Set G)
  have hVp : IsPGroup 2 V := hUp.to_le inf_le_left
  have hPV : P < V := by
    have hproper : P.subgroupOf U < ⊤ := by
      rw [lt_top_iff_ne_top,Ne,subgroupOf_eq_top]
      exact not_le_of_gt hlt
    let : Group.IsNilpotent U := hUp.isNilpotent
    obtain ⟨v,hv,hvn⟩ := SetLike.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent (P.subgroupOf U) hproper)
    have hvN : v.val ∈ normalizer (P : Set G) := by
      rw [←subgroupOf_normalizer_eq hPU] at hv
      exact hv
    refine lt_of_le_of_ne (le_inf hPU le_normalizer) ?_
    intro hh
    exact hvn (hh.symm ▸ (show v.val ∈ V from ⟨v.property,hvN⟩))
  have hVC : V ≤ C := inf_le_left.trans (map_subtype_le _)
  have hout (i : Fin 2) : ¬ V ≤ normalizer (![L,residual H] i : Set G) := by
    intro hh
    exact hPV.ne (hmax i V hVp hPV.le hVC hh).symm
  exact ⟨f,hf,ho,hlocal,V,hVp,hPV,hVC,inf_le_right,hout,
    fun E hE hn i => d.symplectic_normalized_center_disjoint_roots h hH hp F hm hF he V hout E hE hn i⟩

/-- The actual center-derived subgroup in F.4.37 cannot both lie in Z(S)
and meet a root center, for a suitably chosen outer involution. The native
placement and the field-four exception are not assumed or asserted here. -/
theorem Preparation.symplectic_outer_derived_center_obstruction
    (hst : sourceS L H ≠ (T : Subgroup G)) :
    ∃ f : T, orderOf f=2 ∧ f.val ∉ sourceS L H ∧
      (∀ i : Fin 2, Chapter1.IsSylowIn 2
        ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G))
        (normalizer (![L,residual H] i : Set G) ⊓ centralizer ({f.val} : Set G))) ∧
      let C := (T : Subgroup G) ⊓ centralizer ({f.val} : Set G)
      let Z := (center C ⊓ _root_.commutator C).map C.subtype
      Z ≤ (center (sourceS L H)).map (sourceS L H).subtype →
        ∀ i : Fin 2, Disjoint Z ((center (![L,residual H] i)).map (![L,residual H] i).subtype) := by
  obtain ⟨f,hf,ho,hlocal,V,_,_,_,hVN,_,hroot⟩ :=
    d.symplectic_outer_centralizer_normalizer_growth h hH hp F hm hF he hst
  refine ⟨f,hf,ho,hlocal,?_⟩
  dsimp only
  let C := (T : Subgroup G) ⊓ centralizer ({f.val} : Set G)
  have hn := normalizer_le_normalizer_characteristic_image C
    (center C ⊓ _root_.commutator C)
  intro hZ i
  exact hroot _ hZ (hVN.trans hn) i

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
