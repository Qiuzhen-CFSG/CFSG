module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.FieldTransfer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.GraphSylow
public import Theory.GroupTheory.WeakClosureCentralizerTransport
public import Theory.GroupTheory.CharacteristicCentralizerSylow
public import Theory.GroupTheory.SylowCentralizerConjugacy

/-!
# Outer involution centralizers and normalizer growth in the prepared U₄ rows

Every ambient involution is conjugate into Q=O₂(L). Weak closure of Q in
T and C_G(Q)=Q imply that a fully centralized involution in T belongs to
Q. Thus an involution outside L has a strictly larger centralizer Sylow
in G than its centralizer in T, without any order or outer-parity premise.

Among outer involutions, maximize the T-centralizer. Conjugation within
either full endpoint preserves being outside the corresponding residual;
the common inner Sylow identifies these two conditions. The same selected
centralizer is therefore Sylow in both full endpoint centralizers. Its
strict ambient enlargement has a larger two-normalizer escaping both
endpoints. The cyclic field quotient places its center-derived subgroup
in the reduced fixed Sylow, with its full normalizer action retained.

The degree-two comparison supplies an outer involution and hence this
configuration, in either orientation and including q=4. Separately, the
original graph involution keeps its marked fixed diagram and source-local
Sylows while its T-centralizer is proved not ambient Sylow. The maximizer
is not asserted to have that diagram: the remaining native fixed-root
geometry must identify and exclude the actual configuration. Ordinary
even-degree outer existence and unconditional parity are not concluded.

Source: Aschbacher–Smith F.4.35,37–38, printed pp.292–294, applied to the
original prepared pair of 5.3.1–3, pp.658–659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
open Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourGraph
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
variable (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
include d h hH hp hm hc

/-- Every fully centralized involution of T lies in its actual left two-core. -/
theorem Preparation.unitaryFour_fully_centralized_involution_mem_core
    (f : T) (hf : orderOf f=2)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G))
      (centralizer ({f.val} : Set G))) : f.val ∈ L.pCoreIn 2 := by
  obtain ⟨z,hz,t,ht,_,_,_,hcover⟩ := d.unitaryFour_ambient_two_classes h hH hp m hm hc
  have hrep : ∃ y ∈ L.pCoreIn 2, IsConj y f.val :=
    (hcover f.val ((Subgroup.orderOf_coe f).trans hf)).elim
      (fun hh => ⟨z,hz,hh.symm⟩) (fun hh => ⟨t,ht,hh.symm⟩)
  obtain ⟨y,hy,hyf⟩ := hrep
  obtain ⟨P,hP⟩ := hs
  have hQT : L.pCoreIn 2 ≤ (T : Subgroup G) := by
    rw [←d.unitary_thompson h hH hp m hm hc]
    exact sSup_le fun _ hE => hE.1
  have hcentral : f.val ∈ centralizer (L.pCoreIn 2 : Set G) :=
    T.mem_centralizer_of_isConj_of_weakly_closed (L.pCoreIn 2) hQT
      (fun g hg => d.unitary_core_weakly_closed h hH hp m hm hc g hg)
      ((d.unitary_core_centralizer h hH hp m hm hc).symm ▸ hy) hyf P
      (hP ▸ inf_le_left)
  rwa [d.unitary_core_centralizer h hH hp m hm hc] at hcentral

/-- An involution outside the original L has a strictly larger ambient
centralizer Sylow than its centralizer in T. -/
theorem Preparation.unitaryFour_outer_centralizer_not_sylow
    (f : T) (hf : orderOf f=2) (ho : f.val ∉ L) :
    ¬ Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G))
      (centralizer ({f.val} : Set G)) := by
  intro hs
  exact ho (pCoreIn_le 2 L
    (d.unitaryFour_fully_centralized_involution_mem_core h hH hp m hm hc f hf hs))

/-- Choose one outer involution with largest T-centralizer. Its same
centralizer is maximal among two-subgroups of both full endpoint centralizers. -/
theorem Preparation.unitaryFour_maximal_outer_centralizer
    (hex : ∃ f : T, orderOf f=2 ∧ f.val ∉ L) :
    ∃ f : T, orderOf f=2 ∧ f.val ∉ L ∧ f.val ∉ residual H ∧
      (∀ g : T, orderOf g=2 → g.val ∉ L →
        Nat.card (centralizer ({g} : Set T)) ≤ Nat.card (centralizer ({f} : Set T))) ∧
      ∀ i : Fin 2, ∀ U : Subgroup G, IsPGroup 2 U →
        (T : Subgroup G) ⊓ centralizer ({f.val} : Set G) ≤ U →
        U ≤ centralizer ({f.val} : Set G) →
        U ≤ normalizer (![L,residual H] i : Set G) →
        U = (T : Subgroup G) ⊓ centralizer ({f.val} : Set G) := by
  obtain ⟨f₀,hf₀,ho₀⟩ := hex
  obtain ⟨f,hf,hmax⟩ := Set.exists_max_image
    {g : T | orderOf g=2 ∧ g.val ∉ L}
    (fun g => Nat.card (centralizer ({g} : Set T))) (Set.toFinite _) ⟨f₀,hf₀,ho₀⟩
  have hcc : ConcreteAmalgamComparison
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) :=
    hc.elim (.unitary m hm) (.unitaryExtension m hm)
  have hs := d.common_sylow_of_comparison h hH.1.1.2 hp hcc
  have hinner (i : Fin 2) : (T : Subgroup G) ⊓ L = (T : Subgroup G) ⊓ ![L,residual H] i := by
    fin_cases i
    · rfl
    · exact hs
  have hnot (i : Fin 2) : f.val ∉ ![L,residual H] i := by
    intro hh
    exact hf.2 ((hinner i).ge ⟨f.property,hh⟩).2
  refine ⟨f,hf.1,hf.2,hnot 1,fun g hg ho => hmax g ⟨hg,ho⟩,?_⟩
  intro i U hU hCU hUC hUM
  let K := ![L,residual H] i
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) := by
    fin_cases i
    · exact h.sylow_normalizes
    · exact hH.1.1.2.trans (le_normalizer_residual H)
  have hbound (a : normalizer (K : Set G)) (g : T)
      (hag : (MulAut.conj a.val) f.val = g.val) :
      Nat.card (centralizer ({g} : Set T)) ≤ Nat.card (centralizer ({f} : Set T)) := by
    apply hmax g
    constructor
    · have hh := (MulAut.conj a.val).orderOf_eq f.val
      rw [hag] at hh
      exact (Subgroup.orderOf_coe g).symm.trans (hh.trans ((Subgroup.orderOf_coe f).trans hf.1))
    · intro hgL
      have hgK : g.val ∈ K := ((hinner i).le ⟨g.property,hgL⟩).2
      have hfK : f.val ∈ K := (a.property f.val).mpr (by
        change a.val*f.val*a.val⁻¹=g.val at hag
        rwa [hag])
      exact hnot i hfK
  have hh := T.centralizer_prime_overgroup_eq_of_local_card_bound
    (normalizer (K : Set G)) hTK f hbound U hU
    (by rwa [map_subtype_centralizer_singleton]) hUC hUM
  rwa [map_subtype_centralizer_singleton] at hh

/-- An outer involution gives a strictly larger ambient two-normalizer
escaping both original endpoints, for the same selected centralizer. -/
theorem Preparation.unitaryFour_outer_centralizer_normalizer_growth
    (hex : ∃ f : T, orderOf f=2 ∧ f.val ∉ L) :
    ∃ f : T, orderOf f=2 ∧ f.val ∉ L ∧ f.val ∉ residual H ∧
      (∀ i : Fin 2, Chapter1.IsSylowIn 2
        ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G))
        (normalizer (![L,residual H] i : Set G) ⊓ centralizer ({f.val} : Set G))) ∧
      ∃ V : Subgroup G, IsPGroup 2 V ∧
        (T : Subgroup G) ⊓ centralizer ({f.val} : Set G) < V ∧
        V ≤ centralizer ({f.val} : Set G) ∧
        V ≤ normalizer (((T : Subgroup G) ⊓ centralizer ({f.val} : Set G) : Subgroup G) : Set G) ∧
        ∀ i : Fin 2, ¬ V ≤ normalizer (![L,residual H] i : Set G) := by
  obtain ⟨f,hf,ho,hor,_,hmax⟩ := d.unitaryFour_maximal_outer_centralizer h hH hp m hm hc hex
  let C := centralizer ({f.val} : Set G)
  let P := (T : Subgroup G) ⊓ C
  have hlocal (i : Fin 2) : Chapter1.IsSylowIn 2 P
      (normalizer (![L,residual H] i : Set G) ⊓ C) := by
    have hTM : (T : Subgroup G) ≤ normalizer (![L,residual H] i : Set G) := by
      fin_cases i
      · exact h.sylow_normalizes
      · exact hH.1.1.2.trans (le_normalizer_residual H)
    apply Chapter1.isSylowIn_iff.mpr
    exact ⟨T.isPGroup'.to_le inf_le_left,inf_le_inf_right C hTM,
      fun U hU hPU hUM => hmax i U hU hPU (hUM.trans inf_le_right) (hUM.trans inf_le_left)⟩
  obtain ⟨R,hR⟩ := (T.isPGroup'.comap_subtype (K := C)).exists_le_sylow
  let U := (R : Subgroup C).map C.subtype
  have hPU : P ≤ U := by
    intro x hx
    exact mem_map_of_mem C.subtype (hR (show (⟨x,hx.2⟩ : C) ∈
      (T : Subgroup G).subgroupOf C from hx.1))
  have hlt : P < U := lt_of_le_of_ne hPU (by
    intro heq
    have hh : Chapter1.IsSylowIn 2 P C := ⟨R,heq.symm⟩
    exact d.unitaryFour_outer_centralizer_not_sylow h hH hp m hm hc f hf ho hh)
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
  exact ⟨f,hf,ho,hor,hlocal,V,hVp,hPV,hVC,inf_le_right,hout⟩

/-- The cyclic field quotient puts the derived subgroup of the full T
inside the original reduced Sylow; sourceS is not used as that kernel. -/
theorem Preparation.unitaryFour_sylow_commutator_le_inner :
    (_root_.commutator T).map (T : Subgroup G).subtype ≤ (T : Subgroup G) ⊓ L := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h.linear
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : IsCyclic (F ≃+* F) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
  let : CommGroup (F ≃+* F) := IsCyclic.commGroup
  rintro _ ⟨x,hx,rfl⟩
  have hh := Abelianization.commutator_subset_ker
    (unitaryFourSylowFieldAction h.sylow_normalizes e) hx
  rw [d.unitaryFour_sylow_field_kernel h hH hp m hm hc e] at hh
  exact ⟨x.property,hh⟩

/-- The literal center-derived subgroup of any T-centralizer is inside
the reduced fixed Sylow and is normalized by its entire ambient normalizer. -/
theorem Preparation.unitaryFour_centralizer_derived_center
    (f : T) :
    let P := (T : Subgroup G) ⊓ centralizer ({f.val} : Set G)
    let Z := (center P ⊓ _root_.commutator P).map P.subtype
    Z ≤ ((T : Subgroup G) ⊓ L) ⊓ centralizer ({f.val} : Set G) ∧
      normalizer (P : Set G) ≤ normalizer (Z : Set G) := by
  dsimp only
  let P := (T : Subgroup G) ⊓ centralizer ({f.val} : Set G)
  have hderived : (_root_.commutator P).map P.subtype ≤ (T : Subgroup G) ⊓ L := by
    rw [map_subtype_commutator]
    have hh := d.unitaryFour_sylow_commutator_le_inner h hH hp m hm hc
    rw [map_subtype_commutator] at hh
    exact (commutator_mono inf_le_left inf_le_left).trans hh
  exact ⟨le_inf ((map_mono inf_le_right).trans hderived)
    ((map_subtype_le _).trans inf_le_right),
    normalizer_le_normalizer_characteristic_image P (center P ⊓ _root_.commutator P)⟩

omit hc in
/-- The degree-two comparison supplies the actual marked graph element
whose source centralizers are Sylow but whose ambient T-centralizer is not.
The fixed amalgam and central graph generator are retained for this same f. -/
theorem Preparation.unitaryFour_graph_centralizer_not_sylow
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)) :
    1 < m ∧ n = 2*m ∧
      ∃ f : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        f.val ∈ sourceS L H ∧ f.val ∈ (T : Subgroup G) ∧ orderOf f.val = 2 ∧
        f.val ∉ L ∧ f.val ∉ residual H ∧
        Nat.card (sourceS L H ⊓ centralizer ({f.val} : Set G) : Subgroup G) = 2*(2^m)^4 ∧
        (∀ i : Fin 2, Chapter1.IsSylowIn 2
          (sourceS L H ⊓ centralizer ({f.val} : Set G))
          (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i ⊓
            centralizer ({f.val} : Set G))) ∧
        ¬ Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G))
          (centralizer ({f.val} : Set G)) ∧
        ((∃ e : RankTwoAmalgam.Iso
          (centralizerDiagram
            (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) f)
          (ChapterF.UnitarySource.FourGraph.fixedDiagram m),
            e.middle (centralPoint f) =
              (1,Theory.SpecificGroups.ClassicalUnitary.UnitaryFourOuter.generator)) ∨
         (∃ e : RankTwoAmalgam.Iso
          (centralizerDiagram
            (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) f)
          (ChapterF.UnitarySource.FourGraph.fixedDiagram m).reverse,
            e.middle (centralPoint f) =
              (1,Theory.SpecificGroups.ClassicalUnitary.UnitaryFourOuter.generator))) := by
  obtain ⟨hm',hn,f,hfS,hfT,hf,ho,hor,hcard,hlocal,hdiagram⟩ :=
    d.unitary_graph_local_sylow h hH hp m hm he
  refine ⟨hm',hn,f,hfS,hfT,hf,ho,hor,hcard,hlocal,?_,hdiagram⟩
  exact d.unitaryFour_outer_centralizer_not_sylow h hH hp m hm (.inr he)
    ⟨f.val,hfT⟩ ((Subgroup.orderOf_coe _).symm.trans hf) ho

omit hc in
/-- The original degree-two row unconditionally supplies the escaping
normalizer configuration. The maximizer may differ from the marked graph
involution; no ambient conjugation is treated as an endpoint marking. -/
theorem Preparation.unitaryFour_degreeTwo_normalizer_growth
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)) :
    1 < m ∧ n = 2*m ∧
    ∃ f : T, orderOf f=2 ∧ f.val ∉ L ∧ f.val ∉ residual H ∧
      (∀ i : Fin 2, Chapter1.IsSylowIn 2
        ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G))
        (normalizer (![L,residual H] i : Set G) ⊓ centralizer ({f.val} : Set G))) ∧
      ∃ V : Subgroup G, IsPGroup 2 V ∧
        (T : Subgroup G) ⊓ centralizer ({f.val} : Set G) < V ∧
        V ≤ centralizer ({f.val} : Set G) ∧
        V ≤ normalizer (((T : Subgroup G) ⊓ centralizer ({f.val} : Set G) : Subgroup G) : Set G) ∧
        (∀ i : Fin 2, ¬ V ≤ normalizer (![L,residual H] i : Set G)) ∧
        let P := (T : Subgroup G) ⊓ centralizer ({f.val} : Set G)
        let Z := (center P ⊓ _root_.commutator P).map P.subtype
        Z ≤ ((T : Subgroup G) ⊓ L) ⊓ centralizer ({f.val} : Set G) ∧
          V ≤ normalizer (Z : Set G) := by
  obtain ⟨hm',hn,f₀,_,hfT,hf,ho,_⟩ := d.unitary_graph_local_sylow h hH hp m hm he
  obtain ⟨f,hf,ho,hor,hlocal,V,hV,hPV,hVC,hVN,hout⟩ :=
    d.unitaryFour_outer_centralizer_normalizer_growth h hH hp m hm (.inr he)
      ⟨⟨f₀.val,hfT⟩,(Subgroup.orderOf_coe _).symm.trans hf,ho⟩
  have hZ := d.unitaryFour_centralizer_derived_center h hH hp m hm (.inr he) f
  exact ⟨hm',hn,f,hf,ho,hor,hlocal,V,hV,hPV,hVC,hVN,hout,hZ.1,hVN.trans hZ.2⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
