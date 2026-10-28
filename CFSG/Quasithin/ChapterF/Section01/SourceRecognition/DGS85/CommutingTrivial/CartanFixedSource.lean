module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CartanFixedCommutator
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicCriticalAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.LocalActor
public import Theory.GroupTheory.AmalgamGraph.NormalTwoDetection

/-!
# Original graph application of the Cartan fixed decomposition

The full path Cartan normalizes the fixed subgroup `D`, using its abelianness
and its original vertex stabilizers. Thus the intersection argument uses
the literal `Q_(alpha')`, the two Cartan factors, and the terminal core
intersection. The fixed-point-free action and order comparison remain
explicit earlier-source inputs.

The Frattini conclusion uses the second direct product, normality of its
whole group in the terminal local actor, and the actual Sylow-center span.
A nontrivial normal two-subgroup meets that span, so disjointness kills the
Frattini subgroup. Source: DGS (1985), 9.10(4), pp.148--149.
-/

@[expose] public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The Frattini step in (4) at the original terminal vertex. -/
theorem graph_cartan_fixed_elementary
    (h : LocallyRankOneTriple P B) (a' : Vertex (family P))
    (H Q₀ : Subgroup G)
    (hHQ : H ≤ Q (family P) a')
    (hn : graphLocalGroup (family P) a' ≤ normalizer (H : Set G))
    (he : IsElementaryAbelian 2 (V (family P) a' 1))
    (hprod : H = Q₀ ⊔ V (family P) a' 1)
    (hcomm : ⁅Q₀,V (family P) a' 1⁆ = ⊥)
    (hdis : Disjoint Q₀ (V (family P) a' 1)) : IsElementaryAbelian 2 Q₀ := by
  let := finite_endpoints h
  let M := graphLocalGroup (family P) a'
  let F := (frattini Q₀).map Q₀.subtype
  have hHM : H ≤ M := hHQ.trans (core_le_graphLocalGroup h a')
  have hQH : Q₀ ≤ H := hprod ▸ le_sup_left
  let : Finite H := Finite.of_injective (inclusion (hHQ.trans (Q_le_stabilizer _ _)))
    (inclusion_injective _)
  let : Finite Q₀ := Finite.of_injective (inclusion hQH) (inclusion_injective _)
  let : Finite M := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hpH : IsPGroup 2 H := (isPGroup_pCoreIn 2 _).to_le hHQ
  have hpQ : IsPGroup 2 Q₀ := hpH.to_le hQH
  have hphi := cartan_fixed_frattini_comparison H Q₀ (V (family P) a' 1) hpH he hcomm hprod
  have hFn : M ≤ normalizer (F : Set G) := by
    change M ≤ normalizer ((frattini Q₀).map Q₀.subtype : Set G)
    rw [←hphi]
    exact hn.trans (normalizer_le_normalizer_characteristic_image H (frattini H))
  have hFQ : F ≤ Q₀ := map_subtype_le _
  have hFZ : Disjoint F (sylowCenterSpan M) := by
    rw [←graph_intrinsic_center_span h a']
    exact hdis.mono hFQ (Z_le_V (family P) a' 1)
  have hFbot : F = ⊥ := normal_two_eq_bot_of_disjoint_sylowCenterSpan M F
    (hFQ.trans (hQH.trans hHM)) ((hpQ.to_subgroup (frattini Q₀)).map Q₀.subtype) hFn hFZ
  apply cartan_fixed_elementary Q₀ hpQ
  exact (map_eq_bot_iff_of_injective (frattini Q₀) Q₀.subtype_injective).mp hFbot

/-- Original Cartan specialization of the fixed-intersection argument. The
source splitting, fixed-point-free action, commutation and order comparison
are displayed on their literal subgroups; Cartan normalization is derived. -/
theorem graph_cartan_fixed_decomposition
    (h : LocallyRankOneTriple P B)
    (l a' x r : Vertex (family P)) (C : Subgroup G) [IsMulCommutative C]
    (hCl : C ≤ stabilizer (family P) l)
    (hCx : C ≤ stabilizer (family P) x)
    (hCr : C ≤ stabilizer (family P) r)
    (hCprod : C = (C ⊓ graphLocalGroup (family P) l) ⊔
      (C ⊓ graphLocalGroup (family P) a'))
    (hHQ : Q (family P) x ⊓ Q (family P) r ≤ Q (family P) a')
    (hfixed : Q (family P) a' ⊓ centralizer (C : Set G) ≤
      Q (family P) l ⊓ (Q (family P) x ⊓ Q (family P) r))
    (hmove : ⁅Q (family P) x ⊓ Q (family P) r,C ⊓ graphLocalGroup (family P) a'⁆ ≤
      V (family P) a' 1)
    (hdis : Disjoint
      (Q (family P) l ⊓ centralizer (C ⊓ graphLocalGroup (family P) l : Set G))
      (V (family P) a' 1))
    (hsplit : let D := Q (family P) l ⊓ centralizer (C ⊓ graphLocalGroup (family P) l : Set G);
      D = Z (family P) l ⊔ (D ⊓ Q (family P) a'))
    (hDdis : let D := Q (family P) l ⊓ centralizer (C ⊓ graphLocalGroup (family P) l : Set G);
      Disjoint (Z (family P) l) (D ⊓ Q (family P) a'))
    (hDcomm : let D := Q (family P) l ⊓ centralizer (C ⊓ graphLocalGroup (family P) l : Set G);
      ⁅Z (family P) l,D ⊓ Q (family P) a'⁆ = ⊥)
    (hDRH : let D := Q (family P) l ⊓ centralizer (C ⊓ graphLocalGroup (family P) l : Set G);
      D ⊓ Q (family P) a' ≤ Q (family P) x ⊓ Q (family P) r)
    (hVH : V (family P) a' 1 ≤ Q (family P) x ⊓ Q (family P) r)
    (hcomm : ⁅Q (family P) a' ⊓ centralizer (C : Set G),V (family P) a' 1⁆ = ⊥)
    (hcard : Nat.card (Q (family P) x ⊓ Q (family P) r : Subgroup G) ≤
      Nat.card (Q (family P) a' ⊓ centralizer (C : Set G) : Subgroup G) *
        Nat.card (V (family P) a' 1))
    (hnH : graphLocalGroup (family P) a' ≤ normalizer
      ((Q (family P) x ⊓ Q (family P) r : Subgroup G) : Set G))
    (he : IsElementaryAbelian 2 (V (family P) a' 1)) :
    let D := Q (family P) l ⊓ centralizer (C ⊓ graphLocalGroup (family P) l : Set G)
    let Q₀ := Q (family P) a' ⊓ centralizer (C : Set G)
    let H := Q (family P) x ⊓ Q (family P) r
    D ⊓ H = Q₀ ∧ D = Z (family P) l ⊔ Q₀ ∧
      Disjoint (Z (family P) l) Q₀ ∧ ⁅Z (family P) l,Q₀⁆ = ⊥ ∧
      H = Q₀ ⊔ V (family P) a' 1 ∧ Disjoint Q₀ (V (family P) a' 1) ∧
      ⁅Q₀,V (family P) a' 1⁆ = ⊥ ∧ IsElementaryAbelian 2 Q₀ := by
  let := finite_endpoints h
  let Γ := family P
  let T := C ⊓ graphLocalGroup Γ l
  let K := C ⊓ graphLocalGroup Γ a'
  let D := Q Γ l ⊓ centralizer (T : Set G)
  let H := Q Γ x ⊓ Q Γ r
  let Q₀ := Q Γ a' ⊓ centralizer (C : Set G)
  let : Finite H := Finite.of_injective (inclusion
    ((show H ≤ Q Γ x from inf_le_left).trans (Q_le_stabilizer _ _))) (inclusion_injective _)
  have hCnT : C ≤ normalizer (T : Set G) :=
    ((le_centralizer C).trans (centralizer_le inf_le_left)).trans (centralizer_le_normalizer _)
  have hCnD : C ≤ normalizer (D : Set G) :=
    (le_inf (hCl.trans (stabilizer_normalizes_Q Γ l))
      (hCnT.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hCnH : C ≤ normalizer (H : Set G) :=
    (le_inf (hCx.trans (stabilizer_normalizes_Q Γ x))
      (hCr.trans (stabilizer_normalizes_Q Γ r))).trans inf_normalizer_le_normalizer_inf
  have hn : K ≤ normalizer ((D ⊓ H : Subgroup G) : Set G) :=
    inf_le_left.trans ((le_inf hCnD hCnH).trans inf_normalizer_le_normalizer_inf)
  have hQDH : Q₀ ≤ D ⊓ H := by
    refine le_inf (le_inf (hfixed.trans inf_le_left) ?_) (hfixed.trans inf_le_right)
    exact inf_le_right.trans (centralizer_le (show T ≤ C from inf_le_left))
  have hC : C = T ⊔ K := hCprod
  have hresult := cartan_fixed_decomposition D (Z Γ l) (Q Γ a') H (V Γ a' 1) T K
    inf_le_right (inf_le_right.trans hHQ) (hC ▸ hQDH) hn hmove hdis
    hsplit hDdis hDcomm hDRH hVH (hC ▸ hcomm) (hC ▸ hcard)
  rw [←hC] at hresult
  obtain ⟨hDH,_,hD,hDZ,hDC,hH,hQV,hQC⟩ := hresult
  exact ⟨hDH,hD,hDZ,hDC,hH,hQV,hQC,
    graph_cartan_fixed_elementary h a' H Q₀ hHQ hnH he hH hQC hQV⟩

/-- The first half of (5) on the same full Cartan and path. The local
normality cuts the natural-center support using one original neighbor
conjugator, so the conclusion concerns the literal beta central line. -/
theorem graph_cartan_fixed_commutator_le_central_line
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (a beta a' l x : Vertex (family P))
    (hba : (graph (family P)).Adj beta a)
    (hbx : (graph (family P)).Adj beta x)
    (C : Subgroup G)
    (hCx : C ≤ stabilizer (family P) x)
    (hN : Q (family P) a ⊓ Q (family P) x =
      (Q (family P) a' ⊓ centralizer (C : Set G)) ⊔ V (family P) beta 1)
    (hNc : Q (family P) a ⊓ Q (family P) x ≤ centralizer (V (family P) beta 1 : Set G))
    (he : IsElementaryAbelian 2 (Q (family P) a' ⊓ centralizer (C : Set G) : Subgroup G))
    (hgen : Q (family P) beta = (Q (family P) a ⊓ Q (family P) x) ⊔
      ⁅Q (family P) beta,C ⊓ graphLocalGroup (family P) l⁆)
    (hmove : ⁅Q (family P) beta,Q (family P) a' ⊓ centralizer (C : Set G)⁆ ≤
      V (family P) beta 1)
    (hVT : ⁅V (family P) beta 1,C ⊓ graphLocalGroup (family P) l⁆ ≤ Z (family P) x)
    (hBV : ⁅Q (family P) beta,V (family P) beta 1⁆ ≤ Z (family P) beta)
    (hZX : Z (family P) beta ≤ Z (family P) x)
    (hMN : graphLocalGroup (family P) beta ≤ normalizer
      ((Q (family P) a ⊓ Q (family P) x : Subgroup G) : Set G))
    (hcut : Z (family P) a ⊓ Z (family P) x ≤ Z (family P) beta) :
    ⁅Q (family P) beta,Q (family P) a' ⊓ centralizer (C : Set G)⁆ ≤ Z (family P) beta := by
  let := finite_endpoints h
  let Γ := family P
  let Q₀ := Q Γ a' ⊓ centralizer (C : Set G)
  let N := Q Γ a ⊓ Q Γ x
  let T := C ⊓ graphLocalGroup Γ l
  let : IsElementaryAbelian 2 Q₀ := he
  have hQ₀N : Q₀ ≤ N := le_sup_left.trans hN.ge
  have hQT : ⁅Q₀,T⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (inf_le_right.trans (centralizer_le (show T ≤ C from inf_le_left)))
  have hQV : ⁅Q₀,V Γ beta 1⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hQ₀N.trans hNc)
  have hBX : Q Γ beta ≤ normalizer (Z Γ x : Set G) :=
    ((source_Z_Q_U h beta).2.trans ((ballKernel_one_le_edge Γ hbx).trans inf_le_right)).trans
      (CommutingNontrivial.stabilizer_normalizes_Z Γ x)
  have hTX : T ≤ normalizer (Z Γ x : Set G) :=
    inf_le_left.trans (hCx.trans (CommutingNontrivial.stabilizer_normalizes_Z Γ x))
  have hQX : Q₀ ≤ normalizer (Z Γ x : Set G) :=
    ((hQ₀N.trans inf_le_right).trans (Q_le_stabilizer Γ x)).trans
      (CommutingNontrivial.stabilizer_normalizes_Z Γ x)
  obtain ⟨g,hg,hgx⟩ := graphLocalGroup_transitive h hB hS beta ⟨x,hbx⟩ ⟨a,hba⟩
  apply cartan_fixed_commutator_le_central_line (Q Γ beta) N Q₀ (V Γ beta 1) T
    (Z Γ x) (Z Γ beta) (graphLocalGroup Γ beta) hN hQV hgen hQT hmove hVT hBV hZX
    hBX hTX hQX ((sylowGenerated_le _).trans (stabilizer_normalizes_Q Γ beta)) hMN g hg
  rw [←Z_translate,hgx]
  exact hcut

/-- The last step of (5) in the original local group. The generation of the
beta core modulo its centralizer kernel makes the fixed subgroup central;
the graph Sylow-center span then detects and kills this normal two-subgroup. -/
theorem graph_cartan_fixed_eq_bot
    (h : LocallyRankOneTriple P B) (beta : Vertex (family P))
    (N Q₀ W : Subgroup G)
    (hNQ : N ≤ Q (family P) beta) (hQ₀N : Q₀ ≤ N)
    (hgen : Q (family P) beta = N ⊔ ⁅Q (family P) beta,W⁆)
    (hL : graphLocalGroup (family P) beta = Q (family P) beta ⊔ W)
    (hQN : ⁅Q₀,N⁆ = ⊥) (hQW : ⁅Q₀,W⁆ = ⊥)
    (hBQ : ⁅Q (family P) beta,Q₀⁆ ≤ Z (family P) beta)
    (hZW : ⁅Z (family P) beta,W⁆ = ⊥)
    (hdis : Disjoint Q₀ (Z (family P) beta)) : Q₀ = ⊥ := by
  let := finite_endpoints h
  let M := graphLocalGroup (family P) beta
  let : Finite M := Finite.of_injective (inclusion (sylowGenerated_le _))
    (inclusion_injective _)
  have hc := cartan_fixed_centralizes_local_actor (Q (family P) beta) N Q₀ W
    (Z (family P) beta) M hgen hL hQN hQW hBQ hZW
  have hn : M ≤ normalizer (Q₀ : Set G) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)).trans
      (Subgroup.centralizer_le_normalizer _)
  apply normal_two_eq_bot_of_disjoint_sylowCenterSpan M Q₀
    (hQ₀N.trans (hNQ.trans (core_le_graphLocalGroup h beta)))
    ((isPGroup_pCoreIn 2 _).to_le (hQ₀N.trans hNQ)) hn
  rwa [←graph_intrinsic_center_span h beta]

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
