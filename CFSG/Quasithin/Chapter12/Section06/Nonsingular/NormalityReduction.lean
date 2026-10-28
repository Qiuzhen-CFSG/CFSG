module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.PreferredPoint
public import CFSG.Quasithin.Chapter1.Section01Inheritance
public import Theory.GroupTheory.PCoreCentralizerOvergroup

/-!
# Characteristic two and nonnormality in the equal-residual branch

The nontrivial original O₂(L) lies in O₂(N_G(L)), so even characteristic
makes N_G(L) characteristic two. Its point centralizer M_v inherits this
property. If C_{G_v}(O₂(G_v)) lies in M, that centralizer lies in the
characteristic-two subgroup M_v, and the core-centralizer overgroup theorem
makes G_v characteristic two as well.

The preferred-point construction proves the needed centralizer bound under
L_v=K_v, and also puts N_{G_v}(V_v) in M. Since G_v escapes M, the literal
V_v cannot be normal in G_v. The application retains the selected Sylow
position, the actual moved subgroup, and the original quotient projection.
T-invariance and TI remain earlier 12.2.2 inputs, whose final discharge
belongs to qt-d-1222-source. The Thompson cases of 12.6.11, component
recognition, blocks, splitting and fixed-space elimination still remain.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the first
two reductions in Lemma 12.6.11, printed p.825.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

omit [IsElementaryAbelian 2 V] in
/-- Even characteristic applies to the actual N_G(L), using the nontrivial
chosen module inside its two-core. No uniqueness theorem is needed. -/
theorem SourceHypothesis.normalizer_mem_He
    {K : GroupClass} (H : SourceHypothesis K T L V) : M L ∈ Chapter1.He G := by
  have hc : L.pCoreIn 2 ≤ (M L).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes L.le_normalizer (le_refl (M L))
  apply Chapter1.lemma_1_1_4_6 T (H.source.simpleQTKE.evenCharacteristic T)
  refine ⟨?_,H.chosen.sylow_normalizes_component⟩
  intro hz
  exact H.chosen.ne_bot (bot_unique ((H.chosen.le_componentCore.trans hc).trans_eq hz))

/-- Characteristic two passes to the actual point centralizer inside N_G(L). -/
theorem SourceHypothesis.point_normalizer_mem_He
    {K : GroupClass} (H : SourceHypothesis K T L V) (v : V) :
    Mv L (v : G) ∈ Chapter1.He G := by
  have hp : IsPGroup 2 (zpowers (v : G)) :=
    (IsElementaryAbelian.isPGroup 2 V).to_le (zpowers_le.mpr v.property)
  have hVM : zpowers (v : G) ≤ M L :=
    (zpowers_le.mpr v.property).trans (H.chosen.le_component.trans L.le_normalizer)
  have hc := pCoreIn_selfCentralizing_centralizer H.normalizer_mem_He hp hVM
  rw [zpowers_eq_closure,centralizer_closure] at hc
  exact hc

/-- The preferred-point centralizer bound detects characteristic two in G_v. -/
theorem SourceHypothesis.point_mem_He_of_core_centralizer
    {K : GroupClass} (H : SourceHypothesis K T L V) (v : V)
    (hc : Gv (v : G) ⊓ centralizer ((Gv (v : G)).pCoreIn 2 : Set G) ≤ M L) :
    Gv (v : G) ∈ Chapter1.He G := by
  let A := Gv (v : G)
  have hNA : Mv L (v : G) ≤ A := inf_le_right
  let N := (Mv L (v : G)).subgroupOf A
  have hN : centralizer (pCore 2 N : Set N) ≤ pCore 2 N :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hNA)).mpr
      (Chapter1.mem_He_iff.mp (H.point_normalizer_mem_He v))
  apply Chapter1.mem_He_iff.mpr
  apply centralizer_pCore_le_of_overgroup 2 N hN
  intro x hx
  change (x : G) ∈ Mv L (v : G)
  refine ⟨hc ⟨x.property,?_⟩,x.property⟩
  apply mem_centralizer_iff.mpr
  intro q hq
  obtain ⟨q,hq,rfl⟩ := hq
  exact congrArg Subtype.val (mem_centralizer_iff.mp hx q hq)


/-- The literal two reductions at the start of 12.6.11. Under L_w=K_w,
the selected escaping centralizer has characteristic two, while its
actual moved subgroup is not relatively normal. The earlier T-invariance
and TI hypotheses retain their source owner in 12.2.2. -/
theorem SourceHypothesis.exists_preferred_nonsingular_Kv_reductions
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (v : V) (hv : D.Nonsingular v) (hescape : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      (Lv L (w : G) = Kv (w : G) →
        Vv L V (w : G) ≤ (Gv (w : G)).pCoreIn 2 ∧
        Gv (w : G) ∈ Chapter1.He G ∧
        Gv (w : G) ⊓ normalizer (Vv L V (w : G) : Set G) ≤ M L ∧
        ¬ ((Vv L V (w : G)).subgroupOf (Gv (w : G))).Normal) := by
  obtain ⟨w,hw,he,hs,hi,hc⟩ :=
    H.exists_preferred_nonsingular_normalizer_control D hTV hTI v hv hescape
  refine ⟨w,hw,he,hs,hi,fun h => ?_⟩
  have hn : Gv (w : G) ≤ normalizer (Lv L (w : G) : Set G) := by
    rw [h]
    exact (normal_subgroupOf_iff_le_normalizer (Kv_le_Gv (w : G))).mp (Kv_normalIn_Gv (w : G))
  have hW := Vv_le_core_Gv_of_normalized H.chosen w hn
  have hC : Gv (w : G) ⊓ centralizer (Vv L V (w : G) : Set G) ≤ M L :=
    (inf_le_inf le_rfl (Subgroup.centralizer_le_normalizer _)).trans (hc hn)
  refine ⟨hW,H.point_mem_He_of_core_centralizer w
    ((inf_le_inf le_rfl (Subgroup.centralizer_le hW)).trans hC),hc hn,?_⟩
  intro hnormal
  have hnormal' := (normal_subgroupOf_iff_le_normalizer (hW.trans (pCoreIn_le 2 _))).mp hnormal
  exact he ((le_inf le_rfl hnormal').trans (hc hn))

end CFSG.Quasithin.Chapter12.Section06
