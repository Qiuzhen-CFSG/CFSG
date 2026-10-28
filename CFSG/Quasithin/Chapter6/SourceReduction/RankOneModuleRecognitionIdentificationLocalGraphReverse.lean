module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalGraphNeighbor
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalGraphPlanes
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryInvolution

/-!
# Reverse neighbors and the common point in source 6.2.8

A moving endpoint seed lies outside the original H-vertex core: that core
fixes every neighbor, whereas the seed moves one. Rank-one E-generation
therefore supplies a reverse index-two neighbor. The two elementary endpoint
closures give both field-plane commutator identities and a common nonidentity
point, preserving the original conjugation coordinates.

For the terminal contradiction, natural point transitivity simultaneously
transports the layer and the common point. The point-centralizer core
normalizes every layer through that point, by the actual Sylow and fusion
geometry. Thus original core containment would force normalization of any
two intersecting conjugates. The Chapter 12 companion contradicts this
using the constructed index-two pair. This direct core transport replaces
the printed terminal non-two-pair construction without adding hypotheses.

Source: Aschbacher--Smith, 6.2.8, printed pp.684--685, using F.7.13(1),
p.314, and natural point-centralizer fusion as in 6.1.19, pp.674--675.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterF.Section07.Track
open CFSG.Quasithin.ChapterF.Section07.CriticalPairs
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

/-- A moving endpoint seed escapes the core of the original H vertex.
E-generation then gives its reverse index-two neighbor at that vertex. -/
theorem local_graph_reverse_neighbor
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    {H K : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hN : H ⊓ normalizer (layer L R : Set G) = H ⊓ M)
    (F : Bool → Subgroup K) (htrue : (F true).map K.subtype = H)
    (d : SourceSetup F) (hseed : d.seed.map K.subtype = layer L R)
    (α β : Vertex F) (hαt : α.type = false)
    (hαH : (firstModule F d.seed α).map K.subtype ≤ H)
    (hβ : (graph F).Adj (base F true) β)
    (hn : ¬ (firstModule F d.seed α).map K.subtype ≤
      normalizer ((firstModule F d.seed β).map K.subtype : Set G)) :
    ¬ (firstModule F d.seed α).map K.subtype ≤ H.pCoreIn 2 ∧
      ∃ β' : Vertex F, (graph F).Adj (base F true) β' ∧
        (((firstModule F d.seed α).map K.subtype) ⊓
          normalizer ((firstModule F d.seed β').map K.subtype : Set G)).relIndex
            ((firstModule F d.seed α).map K.subtype) = 2 := by
  let X0 := firstModule F d.seed α
  let X := X0.map K.subtype
  have hβt : β.type = false := by
    have hh : true ≠ β.type := hβ.1
    cases ht : β.type
    · rfl
    · exact (hh ht.symm).elim
  have hcore : ¬ X ≤ H.pCoreIn 2 := by
    intro hc
    have hc' : X0 ≤ (F true).pCoreIn 2 := by
      apply (map_le_map_iff_of_injective K.subtype_injective).mp
      rw [map_pCoreIn_of_injective 2 _ _ K.subtype_injective,htrue]
      exact hc
    have hstab : X0 ≤ stabilizer F β := by
      intro x hx
      exact Completion.base_core_le_kernel F d true (hc' hx) β
        ((mem_ball_one F (base F true) β).mpr (Or.inl hβ))
    have hnorm := stabilizer_normalizes_vertexModule F d.seed d.seed_normalized β
    rw [vertexModule_first F d.seed hβt] at hnorm
    exact hn ((map_mono (hstab.trans hnorm)).trans
      ((firstModule F d.seed β).le_normalizer_map K.subtype))
  let _ : IsElementaryAbelian 2 X0 := firstModule_elementary F d hαt
  let _ : IsElementaryAbelian 2 X := IsElementaryAbelian.map _
  obtain ⟨g,hg,hi⟩ := local_hstar_index_two_neighbor h hH hN X hαH hcore
  have hHK : H ≤ K := htrue ▸ map_subtype_le (F true)
  let gK : K := ⟨g,hHK hg⟩
  let β' := gK • base F false
  have hgfix : gK • base F true = base F true := by
    have hg' : gK ∈ F true := by
      have hh : g ∈ (F true).map K.subtype := htrue.symm ▸ hg
      obtain ⟨x,hx,hxg⟩ := hh
      have he : x = gK := Subtype.ext hxg
      exact he ▸ hx
    have he : stabilizer F (base F true) = F true :=
      Subgroup.CosetGeometry.stabilizer_base F true
    have hs : gK ∈ stabilizer F (base F true) := he.symm ▸ hg'
    exact hs
  have hβ' : (graph F).Adj (base F true) β' := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F gK).map_rel_iff.mpr
      (show (graph F).Adj (base F true) (base F false) from
        ⟨by change true ≠ false; decide,Subgroup.CosetGeometry.incident_base F true false⟩)
    simpa only [Subgroup.CosetGeometry.translationGraphIso_apply,hgfix] using hh
  have he : (firstModule F d.seed β').map K.subtype =
      (layer L R).map (MulAut.conj g).toMonoidHom := by
    rw [show β' = gK • base F false from rfl,
      firstModule_translate_base F d.seed d.seed_normalized,map_map]
    have he : K.subtype.comp (MulAut.conj gK).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp K.subtype := rfl
    rw [he,←map_map,hseed]
  exact ⟨hcore,β',hβ',by rw [he]; exact hi⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition


namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

/-- Both field-plane commutator identities and a common nonidentity point
for an index-two pair in the two elementary endpoint closures. The
literal conjugations give the field coordinates on the original layer. -/
theorem local_conjugate_graph_symmetric_planes
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (a b : G) (U U' : Subgroup G) [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 U']
    (hYU : (layer L R).map (MulAut.conj b).toMonoidHom ≤ U)
    (hXU : (layer L R).map (MulAut.conj a).toMonoidHom ≤ normalizer (U : Set G))
    (hXU' : (layer L R).map (MulAut.conj a).toMonoidHom ≤ U')
    (hYU' : (layer L R).map (MulAut.conj b).toMonoidHom ≤ normalizer (U' : Set G))
    (hleft : ((layer L R).map (MulAut.conj a).toMonoidHom ⊓
        normalizer ((layer L R).map (MulAut.conj b).toMonoidHom : Set G)).relIndex
      ((layer L R).map (MulAut.conj a).toMonoidHom) = 2)
    (hright : ((layer L R).map (MulAut.conj b).toMonoidHom ⊓
        normalizer ((layer L R).map (MulAut.conj a).toMonoidHom : Set G)).relIndex
      ((layer L R).map (MulAut.conj b).toMonoidHom) = 2) :
    let X := (layer L R).map (MulAut.conj a).toMonoidHom
    let Y := (layer L R).map (MulAut.conj b).toMonoidHom
    let C := X ⊓ centralizer (Y : Set G)
    let D := Y ⊓ centralizer (X : Set G)
    ⁅Y ⊓ normalizer (X : Set G),X⁆ = C ∧
      ⁅X ⊓ normalizer (Y : Set G),Y⁆ = D ∧ Nat.card C = 4 ∧ Nat.card D = 4 ∧
      IsInvolutoryFieldFixedSpace L M (layer L R) (C.map (MulAut.conj a⁻¹).toMonoidHom) n ∧
      IsInvolutoryFieldFixedSpace L M (layer L R) (D.map (MulAut.conj b⁻¹).toMonoidHom) n ∧
      ∃ w ∈ C ⊓ D, w ≠ (1 : G) := by
  let X := (layer L R).map (MulAut.conj a).toMonoidHom
  let Y := (layer L R).map (MulAut.conj b).toMonoidHom
  have hXnY : ¬ X ≤ normalizer (Y : Set G) := by
    intro hh
    have he := relIndex_eq_one.mpr (le_inf le_rfl hh)
    rw [hleft] at he
    omega
  have hYnX : ¬ Y ≤ normalizer (X : Set G) := by
    intro hh
    have he := relIndex_eq_one.mpr (le_inf le_rfl hh)
    rw [hright] at he
    omega
  obtain ⟨hc,hC,hD,hf,hf'⟩ :=
    local_conjugate_graph_pair_planes h hnatural hE a b U hYU hXU hright hXnY
  have hc' := (local_conjugate_graph_pair_planes h hnatural hE b a U'
    hXU' hYU' hleft hYnX).1
  refine ⟨hc,hc',hC,hD,hf,hf',?_⟩
  obtain ⟨w,hw,hw1⟩ := local_conjugate_graph_pair_common_point h hnatural hE a b hleft hright hD
  let _ : IsElementaryAbelian 2 (layer L R) := h.layer_elementary
  let _ : IsElementaryAbelian 2 X := IsElementaryAbelian.map _
  let _ : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  exact ⟨w,⟨⟨hw.1,Y.le_centralizer hw.2⟩,⟨hw.2,X.le_centralizer hw.1⟩⟩,hw1⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

/-- If the original layer lies in the marked point-centralizer core, any
two of its conjugates with a common nonidentity point normalize each other.
Natural point transitivity and the original centralizer core are used
simultaneously; this avoids requiring a prescribed non-two pair. -/
theorem local_intersecting_conjugates_normalize_of_point_core
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    {z : G} (hz : z ∈ ZS (T : Subgroup G) L R) (hz1 : z ≠ 1)
    (hcore : layer L R ≤ (centralizer ({z} : Set G)).pCoreIn 2)
    (a b : G) {w : G}
    (hw : w ∈ (layer L R).map (MulAut.conj a).toMonoidHom ⊓
      (layer L R).map (MulAut.conj b).toMonoidHom) (hw1 : w ≠ 1) :
    (layer L R).map (MulAut.conj a).toMonoidHom ≤
      normalizer ((layer L R).map (MulAut.conj b).toMonoidHom : Set G) := by
  obtain ⟨v,hv,hvw⟩ := hw.1
  have hv1 : v ≠ 1 := by intro he; apply hw1; rw [←hvw,he]; exact map_one _
  obtain ⟨l,hl,he⟩ := natural_layer_point_transitive hnat hz.1 hz1 hv hv1
  let g := a*l
  have hglayer : (layer L R).map (MulAut.conj g).toMonoidHom =
      (layer L R).map (MulAut.conj a).toMonoidHom := by
    rw [←fusion_map_conj_mul]
    have hlB : (layer L R).map (MulAut.conj l).toMonoidHom = layer L R :=
      mem_normalizer_iff_map_conj_eq.mp (normalizer_commutator_ge_right R L hl)
    rw [hlB]
  have hgw : (MulAut.conj g) z = w := by
    change a*l*z*(a*l)⁻¹ = w
    calc
      a*l*z*(a*l)⁻¹ = a*(l*z*l⁻¹)*a⁻¹ := by group
      _ = w := by rw [show l*z*l⁻¹ = v from he]; exact hvw
  have hzback : z ∈ (layer L R).map (MulAut.conj (g⁻¹*b)).toMonoidHom := by
    have hm := mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hw.2
    rw [fusion_map_conj_mul] at hm
    have hez : (MulAut.conj g⁻¹) w = z := by
      rw [←hgw]
      simp [MulAut.conj_apply,mul_assoc]
    change (MulAut.conj g⁻¹) w ∈ _ at hm
    rwa [hez] at hm
  have hn := hcore.trans ((natural_line_centralizer_core_geometry h hnat hz hz1).2
    (g⁻¹*b) hzback)
  have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hn
  rwa [hglayer,map_equiv_normalizer_eq,fusion_map_conj_mul,mul_inv_cancel_left] at hm
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
