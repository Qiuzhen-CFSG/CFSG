module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointKernelResidual
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointOpposedClassTwo

/-!
# The original kernel residual escapes the exchanged point kernel

The intrinsic four and its exchanged four both lie in the intersection of
the two actual point kernels. The original index-two Sylow geometry makes
that nontrivial intersection T-invariant. If [N,L] lay in N^g, L would
also normalize the intersection. Its normalizer would then be a two-local
overgroup of YT containing L, contrary to the original unique overgroup.

The literal identity [N,L]=Q intersect N gives escape of that residual
from N^g, and conjugation gives the reverse escape. No characteristicity
of Q in N or identification with O2(C_G(H)) is used.

Source: Aschbacher--Smith 15.3.6--8 and the original binary setup of
15.3.23, printed pp.1122--1123,1128--1129; MS93(4.5), printed p.895.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
variable {G : Type*} [Group G] [Finite G]

/-- The nontrivial intersection of the actual exchanged kernels is T-invariant
but not L-invariant; each original kernel residual escapes the opposite kernel. -/
theorem binary_three_source_binary_kernel_exchange
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup (centralizer ({z} : Set G) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL K n 2)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    let N := (centralizer ({z} : Set G)).pCoreIn 2
    let H := intrinsicFour c.L
    let R := LinearThree.commutatorCore c.L ⊓ N
    let X := N ⊓ N.conjBy g
    H ⊔ H.conjBy g ≤ X ∧ X ≠ ⊥ ∧
      (d.T : Subgroup G) ≤ normalizer X ∧ ¬ c.L ≤ normalizer X ∧
      ¬ R ≤ N.conjBy g ∧ ¬ R.conjBy g ≤ N := by
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  obtain ⟨_,h,hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne hBaum
    hI c (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) eSL hW hJ hcore
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let H := intrinsicFour c.L
  let Q := LinearThree.commutatorCore c.L
  let R := Q ⊓ N
  let X := N ⊓ N.conjBy g
  have hHN : H ≤ N := binary_three_source_binary_four_kernel d c e b z hLS P hP K hBK hn hm
  have hHgN : H.conjBy g ≤ N :=
    (binary_three_source_binary_opposed_class_two
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hn hm
      g hgT hgS).1.trans (map_subtype_le _)
  have hHgiN : H.conjBy g⁻¹ ≤ N :=
    (binary_three_source_binary_opposed_class_two
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hn hm
      g⁻¹ ((d.T : Subgroup G).inv_mem hgT) (by simpa only [d.S.inv_mem_iff])).1.trans
        (map_subtype_le _)
  have hHNg : H ≤ N.conjBy g := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hHgiN
    change (H.conjBy g⁻¹).conjBy g ≤ N.conjBy g at hh
    simpa only [conjBy_inv'] using hh
  have hHgNg : H.conjBy g ≤ N.conjBy g := map_mono hHN
  have hHX : H ⊔ H.conjBy g ≤ X :=
    sup_le (le_inf hHN hHNg) (le_inf hHgN hHgNg)
  have hXne : X ≠ ⊥ := by
    intro he
    have hHbot : H = ⊥ := le_bot_iff.mp (le_sup_left.trans (hHX.trans he.le))
    have hcard := (intrinsicFour_properties_of_MS93 d c.L b t common earlier).2.1
    change Nat.card H = 4 at hcard
    rw [hHbot,card_bot] at hcard
    omega
  have hCN : C ≤ normalizer N := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hSN : d.S ≤ normalizer N := le_sup_right.trans (hLS.trans hCN)
  have hNS : N ≤ d.S := hP ▸ pCoreIn_le_sylow C P
  have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
  have hTS : (d.T : Subgroup G) ≤ normalizer d.S :=
    (normal_subgroupOf_iff_le_normalizer (show d.S ≤ (d.T : Subgroup G) from inf_le_left)).mp
      (normal_of_index_eq_two hi)
  have hSg : d.S.map (MulAut.conj g).toMonoidHom = d.S :=
    mem_normalizer_iff_map_conj_eq.mp (hTS hgT)
  have hSNg : d.S ≤ normalizer (N.conjBy g) := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hSN
    rwa [hSg,map_equiv_normalizer_eq] at hh
  have hSX : d.S ≤ normalizer X :=
    (le_inf hSN hSNg).trans inf_normalizer_le_normalizer_inf
  have hg2 : g ^ 2 ∈ d.S := (d.S.subgroupOf (d.T : Subgroup G)).sq_mem_of_index_two hi ⟨g,hgT⟩
  have hNgg : (N.conjBy g).conjBy g = N := by
    rw [conjBy_conjBy,←pow_two]
    exact mem_normalizer_iff_map_conj_eq.mp (hSN hg2)
  have hXg : X.conjBy g = X := by
    change (N ⊓ N.conjBy g).map (MulAut.conj g).toMonoidHom = _
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
    change N.conjBy g ⊓ (N.conjBy g).conjBy g = N ⊓ N.conjBy g
    rw [hNgg,inf_comm]
  have hgX : g ∈ normalizer X := mem_normalizer_iff_map_conj_eq.mpr hXg
  have hTX : (d.T : Subgroup G) ≤ normalizer X := by
    intro x hx
    by_cases hxS : x ∈ d.S
    · exact hSX hxS
    · have hxg : x * g⁻¹ ∈ d.S := by
        apply (d.S.subgroupOf (d.T : Subgroup G)).mul_mem_iff_of_index_two hi
          (a := (⟨x,hx⟩ : (d.T : Subgroup G))) (b := (⟨g,hgT⟩ : (d.T : Subgroup G))⁻¹) |>.mpr
        change x ∈ d.S ↔ g⁻¹ ∈ d.S
        simp only [d.S.inv_mem_iff,hxS,hgS]
      simpa only [inv_mul_cancel_right] using (normalizer (X : Set G)).mul_mem (hSX hxg) hgX
  have hLnot : ¬ c.L ≤ normalizer X := by
    intro hLX
    have hY := Y_le_component_sylow d c.L hg.generation g hgT (hg.exchange g hgT hgS)
    have hunique := (source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action
      hM hu hmany hne).2.2.2.2.1
    have hlocal : IsTwoLocal (normalizer X) :=
      ⟨X,hXne,d.T.isPGroup'.to_le (inf_le_left.trans (hNS.trans inf_le_left)),rfl⟩
    obtain ⟨M,hXM,hmax⟩ := Finite.exists_le_maximal hlocal
    have hYM : d.Y ⊔ (d.T : Subgroup G) ≤ M :=
      sup_le (hY.trans ((sup_le hLX hTX).trans hXM)) (hTX.trans hXM)
    have hMM := hunique.2.2 M hmax hYM
    exact c.outside (hMM ▸ hLX.trans hXM)
  have hNL : ⁅N,c.L⁆ = R :=
    (binary_three_source_binary_kernel_residual
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hn hm).1
  have hescape : ¬ R ≤ N.conjBy g := by
    intro hRNg
    apply hLnot
    apply le_normalizer_iff_commutator_le_left.mpr
    have hXR : ⁅X,c.L⁆ ≤ R := (commutator_mono inf_le_left le_rfl).trans_eq hNL
    exact le_inf (hXR.trans inf_le_right) (hXR.trans hRNg)
  have hreverse : ¬ R.conjBy g ≤ N := by
    intro hRgN
    have hSQ : d.S ≤ normalizer Q := hg.component_normalized.trans
      (normalizer_le_normalizer_commutatorCore c.L)
    have hSR : d.S ≤ normalizer R :=
      (le_inf hSQ hSN).trans inf_normalizer_le_normalizer_inf
    have hRgg : (R.conjBy g).conjBy g = R := by
      rw [conjBy_conjBy,←pow_two]
      exact mem_normalizer_iff_map_conj_eq.mp (hSR hg2)
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hRgN
    change (R.conjBy g).conjBy g ≤ N.conjBy g at hh
    exact hescape (hRgg ▸ hh)
  exact ⟨hHX,hXne,hTX,hLnot,hescape,hreverse⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
