module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.RadiusTwo

/-!
# Shifted natural sections in the large-distance Chapter 9 argument

For b > 3, the radius-two escape of 9.7 supplies the actual shifted
critical pair (alpha-2, alpha-prime-2). Transport of the local central
omega identity makes its centers commute. The genuine Chapter 8 distance
theorem excludes nonzero displacement at this pair and at its reverse.
The unrestricted reciprocal indices then construct both whole natural
residual sections, using the original beta field and its literal local
quotient maps. The original commutator centralizes V_alpha^(2), since
that radius-two span is elementary abelian when the odd distance exceeds
three.

The F1.11 application constructs the original markings before shifting,
and retains both original natural sections and their equal field orders.
The earlier catalogue, Chapter 8 theorem at all invoked critical pairs,
and source 6.5 remain explicit. This proves the shifted-configuration step
in the b > 3 proof of 9.8; it does not assert 9.8's whole-span identity or
the terminal distance and field conclusions. In the printed source 9.10
handles b = 3, while 9.11 handles b > 3.

Source: DGS, Groups and Graphs (1985), 9.8, printed pp.145--146.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem bool_same_of_ne {x y z : Bool} (hxy : x ≠ y) (hxz : x ≠ z) : y = z := by
  cases x <;> cases y <;> cases z <;> simp_all

private theorem local_omega_center_of_same_type (h : LocallyRankOneTriple P B)
    {v w : Vertex (family P)} (ht : v.type = w.type)
    (hz : Z (family P) v = omegaCenterIn (graphLocalGroup (family P) v)) :
    Z (family P) w = omegaCenterIn (graphLocalGroup (family P) w) := by
  let := finite_endpoints h
  obtain ⟨g,rfl⟩ := (same_orbit_iff (family P) v w).mpr ht
  rw [Z_translate,graphLocalGroup_conjugate h,
    ←NilesRankOneKernel.omegaCenterIn_map_injective _ (MulAut.conj g).injective,hz]

/-- The large-distance branch uses only the distance conclusion of the genuine
Chapter 8 theorem, at each actual critical pair where it is invoked. -/
def ChapterEightDistance (Γ : Bool → Subgroup G) : Prop :=
  ∀ x y z : Vertex Γ, IsCriticalPair Γ x z → (graph Γ).Adj x y →
    (graph Γ).dist y z + 1 = b Γ → 1 < b Γ →
    ⁅Z Γ x,Z Γ z⁆ = ⊥ → ⁅V Γ y 1 ⊓ Q Γ z,V Γ z 1⁆ ≠ ⊥ → b Γ = 3

universe u
variable {G₀ : Type u} [Group G₀] {L : Fin 2 → Subgroup G₀} {S₀ : Subgroup G₀}

/-- At distance greater than three the earlier Chapter 8 theorem discharges
both zero-commutator premises, and the actual linear markings give the
whole natural residual section and both literal indices. -/
theorem reduced_large_distance_natural_section
    (h : HypothesisF11 L S₀)
    (h8 : ChapterEightDistance (Reduction.reducedFamily L S₀))
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 3 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (eα : (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)) ≃* SL(2,K))
    (eβ : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F)) :
    let Γ := Reduction.reducedFamily L S₀
    ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ = ⊥ ∧
      ⁅V Γ a' 1 ⊓ Q Γ beta,V Γ beta 1⁆ = ⊥ ∧
      (Q Γ a').relIndex (V Γ beta 1) = Nat.card F ∧
      (Q Γ beta).relIndex (V Γ a' 1) = Nat.card F ∧
      NaturalResidualSection h beta eβ n := by
  let Γ := Reduction.reducedFamily L S₀
  have hb1 : 1 < b Γ := by change 3 < b Γ at hb; omega
  have hb2 : 2 < b Γ := by change 3 < b Γ at hb; omega
  have htriv : ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ = ⊥ := by
    by_contra he
    have hh := h8 a beta a' hc hab hd hb1 hcomm he
    omega
  have hzero (z : Vertex Γ) (hz : (graph Γ).Adj z a')
      (hzc : IsCriticalPair Γ z beta) (hzcomm : ⁅Z Γ z,Z Γ beta⁆ = ⊥)
      (he : ⁅V Γ a' 1 ⊓ Q Γ beta,V Γ beta 1⁆ ≠ ⊥) : False :=
    Nat.ne_of_gt hb (h8 z a' beta hzc hz
      (by rwa [SimpleGraph.dist_comm]) hb1 hzcomm he)
  have hodd := (Reduction.reduced_commuting_critical_geometry h hc hab hd hb1 hcomm).1
  have ht := Reduction.reduced_triple h
  have he := linear_critical_reciprocal_escape ht (Reduction.reduced_borel_core_sylow h)
    (Reduction.reduced_vertex_sylow h) hc hab hd hb2 hodd eα eβ
  have hrev := reduced_reverse_displacement_of_chapterEight h hc hab hd hb1 hcomm htriv he (fun z hz hzc hzcomm he => (hzero z hz hzc hzcomm he).elim)
  obtain ⟨hi,hi',_⟩ := reduced_large_neighbor_linear_indices h hc hab hd hb1 hcomm htriv he (fun z hz hzc hzcomm he => (hzero z hz hzc hzcomm he).elim) hn hF eβ
  have hC := congrArg (fun C : Subgroup (Reduction.G₀ L S₀) => C.relIndex (V Γ beta 1))
    (reduced_neighbor_centralizer_eq_core_inter h beta a' hb1 hd htriv)
  change (V Γ beta 1 ⊓ centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) =
    (V Γ beta 1 ⊓ Q Γ a').relIndex (V Γ beta 1) at hC
  simp only [inf_relIndex_left] at hC
  exact ⟨htriv,hrev,hi,hi',reduced_critical_saturated_residual_natural h hc hab hd hb1 hcomm
    (hob a beta hab) hn hF eβ hi' (hC.trans hi).le⟩

private theorem neighbor_span_le_radius_two
    (h : LocallyRankOneTriple P B) {a beta : Vertex (family P)}
    (hab : (graph (family P)).Adj a beta) : V (family P) beta 1 ≤ V (family P) a 2 := by
  apply iSup_le
  intro z
  apply iSup_le
  intro hz
  have hz' := (mem_ball_iff (family P) h.generate beta z 1).mp hz
  have ht := (connected (family P) h.generate).dist_triangle (u := a) (v := beta) (w := z)
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr hab] at ht
  exact le_iSup_of_le z (le_iSup_of_le
    ((mem_ball_iff (family P) h.generate a z 2).mpr (by omega)) le_rfl)

/-- The large-distance step in 9.8: the escaping radius-two span constructs
an actual shifted commuting-trivial pair, and both of its neighborhood
sections are natural over the original beta field. The original commutator
centralizes that radius-two span. No shifted branch or naturality premise
is supplied. -/
theorem reduced_linear_shifted_sections
    (h : HypothesisF11 L S₀)
    (h8 : ChapterEightDistance (Reduction.reducedFamily L S₀))
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    {a beta a' v w : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 3 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (eα : (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)) ≃* SL(2,K))
    (eβ : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F))
    (hi : (Q (Reduction.reducedFamily L S₀) a').relIndex
      (V (Reduction.reducedFamily L S₀) beta 1) = Nat.card F)
    (hi' : (Q (Reduction.reducedFamily L S₀) beta).relIndex
      (V (Reduction.reducedFamily L S₀) a' 1) = Nat.card F)
    (hpath : CriticalPathOrbit (Reduction.reducedFamily L S₀) a')
    (hv : (graph (Reduction.reducedFamily L S₀)).Adj a' v)
    (hw : (graph (Reduction.reducedFamily L S₀)).Adj v w)
    (hdv : (graph (Reduction.reducedFamily L S₀)).dist a v + 1 = b (Reduction.reducedFamily L S₀))
    (hdw : (graph (Reduction.reducedFamily L S₀)).dist a w + 2 = b (Reduction.reducedFamily L S₀)) :
    let Γ := Reduction.reducedFamily L S₀
    V Γ a 2 ≤ graphLocalGroup Γ w ∧ (¬ V Γ a 2 ≤ Q Γ w) ∧
      ⁅⁅V Γ beta 1,V Γ a' 1⁆,V Γ a 2⁆ = ⊥ ∧
      ∃ t z : Vertex Γ, (graph Γ).Adj a t ∧ (graph Γ).Adj t z ∧
        (graph Γ).dist a z = 2 ∧ IsCriticalPair Γ z w ∧
        (graph Γ).dist t w + 1 = b Γ ∧ ⁅Z Γ z,Z Γ w⁆ = ⊥ ∧
        ∃ (_ez : (graphLocalGroup Γ z ⧸ pCore 2 (graphLocalGroup Γ z)) ≃* SL(2,K))
          (et : (graphLocalGroup Γ t ⧸ pCore 2 (graphLocalGroup Γ t)) ≃* SL(2,F))
          (ew : (graphLocalGroup Γ w ⧸ pCore 2 (graphLocalGroup Γ w)) ≃* SL(2,F)),
          ⁅V Γ t 1 ⊓ Q Γ w,V Γ w 1⁆ = ⊥ ∧
          ⁅V Γ w 1 ⊓ Q Γ t,V Γ t 1⁆ = ⊥ ∧
          (Q Γ w).relIndex (V Γ t 1) = Nat.card F ∧
          (Q Γ t).relIndex (V Γ w 1) = Nat.card F ∧
          NaturalResidualSection h t et n ∧ NaturalResidualSection h w ew n := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  have hB := Reduction.reduced_borel_core_sylow h
  have hS := Reduction.reduced_vertex_sylow h
  have hZ := fun z => (source_Z_Q_U ht z).1
  have hSyl := Reduction.reduced_kernel_sylow h
  have hb1 : 1 < b Γ := by change 3 < b Γ at hb; omega
  have hb2 : 2 < b Γ := by change 3 < b Γ at hb; omega
  obtain ⟨hodd,_,hωβ,_⟩ := Reduction.reduced_commuting_critical_geometry h hc hab hd hb1 hcomm
  have hb4 : 4 < b Γ := by
    obtain ⟨k,hk⟩ := hodd
    change 3 < b Γ at hb
    change b Γ = 2*k+1 at hk
    omega
  obtain ⟨hW,heW⟩ := linear_radius_two_escape_at_predecessor ht hB hS hc hab hd hb2 hodd
    eβ hi hi' hpath hv hw hdv hdw
  have hRW : ⁅V Γ beta 1,V Γ a' 1⁆ ≤ V Γ a 2 := by
    apply le_trans _ (neighbor_span_le_radius_two ht hab)
    exact le_normalizer_iff_commutator_le_left.mp
      ((V_le_stabilizer Γ ht.generate a' beta (by rw [SimpleGraph.dist_comm]; exact hd.le)).trans
        (stabilizer_normalizes_V Γ beta 1))
  let := V_elementary Γ ht.generate hZ hSyl a (r := 2) hb4
  have hcentral : ⁅⁅V Γ beta 1,V Γ a' 1⁆,V Γ a 2⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hRW.trans (le_centralizer _))
  obtain ⟨t,z,hat,htz,haz,hzc⟩ : ∃ t z : Vertex Γ,
      (graph Γ).Adj a t ∧ (graph Γ).Adj t z ∧ (graph Γ).dist a z = 2 ∧
      IsCriticalPair Γ z w := radius_two_escape_critical_extension ht hB hS hdw heW
  have hdtw : (graph Γ).dist t w + 1 = b Γ := by
    have ht₁ := (connected Γ ht.generate).dist_triangle (u := z) (v := t) (w := w)
    have ht₂ := (connected Γ ht.generate).dist_triangle (u := t) (v := a) (w := w)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr htz.symm,hzc.1] at ht₁
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hat.symm] at ht₂
    change (graph Γ).dist a w + 2 = b Γ at hdw
    omega
  have hatype : a.type ≠ a'.type := (odd_dist_iff Γ ht.generate a a').mp (hc.1.symm ▸ hodd)
  have hbtype : beta.type = a'.type := bool_same_of_ne hab.1 hatype
  have hwtype : beta.type = w.type := hbtype.trans (bool_same_of_ne hv.1.symm hw.1)
  have httype : beta.type = t.type := bool_same_of_ne hab.1 hat.1
  have hztype : a.type = z.type := (even_dist_iff Γ ht.generate a z).mp (by rw [haz]; decide)
  have hωw := local_omega_center_of_same_type ht hwtype hωβ
  have hωt := local_omega_center_of_same_type ht httype hωβ
  have hzcomm := reverse_critical_centers_commute ht hzc hωw
  obtain ⟨g,hg⟩ := (same_orbit_iff Γ a z).mpr hztype
  obtain ⟨_,fz,_,_,_⟩ := local_quotient_parameter_transport ht g hg
  let ez := fz.symm.trans eα
  obtain ⟨g,hg⟩ := (same_orbit_iff Γ beta t).mpr httype
  obtain ⟨_,ft,_,_,_⟩ := local_quotient_parameter_transport ht g hg
  let et := ft.symm.trans eβ
  obtain ⟨g,hg⟩ := (same_orbit_iff Γ beta w).mpr hwtype
  obtain ⟨_,fw,_,_,_⟩ := local_quotient_parameter_transport ht g hg
  let ew := fw.symm.trans eβ
  obtain ⟨htriv,hrev,hit,hiw,hnatt⟩ := reduced_large_distance_natural_section h h8 hob
    hzc htz.symm hdtw hb hzcomm hn hF ez et
  have he := linear_critical_reciprocal_escape ht hB hS hzc htz.symm hdtw hb2 hodd ez et
  obtain ⟨r,hr,hrc,_⟩ := reduced_reverse_criticalPair h hSyl hdtw he
  have hrtype : a.type = r.type := by
    apply bool_same_of_ne ?_ hr.1
    rw [←hwtype]
    exact hab.1.symm
  obtain ⟨g,hg⟩ := (same_orbit_iff Γ a r).mpr hrtype
  obtain ⟨_,fr,_,_,_⟩ := local_quotient_parameter_transport ht g hg
  have hrcomm := reverse_critical_centers_commute ht hrc hωt
  obtain ⟨_,_,_,_,hnatw⟩ := reduced_large_distance_natural_section h h8 hob
    hrc hr.symm (by rwa [SimpleGraph.dist_comm]) hb hrcomm hn hF (fr.symm.trans eα) ew
  exact ⟨hW,heW,hcentral,t,z,hat,htz,haz,hzc,hdtw,hzcomm,ez,et,ew,
    htriv,hrev,hit,hiw,hnatt,hnatw⟩

/-- The original F1.11 application of the large-distance step of 9.8.
Both original markings and natural sections are constructed before the
shifted pair; its sections use exactly the original beta field. The catalogue,
Chapter 8 distance theorem, and source 6.5 retain their earlier producers. -/
theorem reduced_critical_shifted_natural_sections
    (h : HypothesisF11 L S₀)
    {a beta a' v w : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 3 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓
      Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ = ⊥)
    (h8 : ChapterEightDistance (Reduction.reducedFamily L S₀))
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓
          Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (Mα : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    (Mβ : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)))
    (Mα' : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')))
    (Mαsource : IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    (hv : (graph (Reduction.reducedFamily L S₀)).Adj a' v)
    (hw : (graph (Reduction.reducedFamily L S₀)).Adj v w)
    (hdv : (graph (Reduction.reducedFamily L S₀)).dist a v + 1 = b (Reduction.reducedFamily L S₀))
    (hdw : (graph (Reduction.reducedFamily L S₀)).dist a w + 2 = b (Reduction.reducedFamily L S₀)) :
    let Γ := Reduction.reducedFamily L S₀
    let H := graphLocalGroup Γ a
    letI := Z_elementary Γ (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1) a
    ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (n : ℕ),
      0 < n ∧ Nat.card F = 2^n ∧
      ∃ eβ : (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)) ≃* SL(2,F),
        (Q Γ a').relIndex (V Γ beta 1) = Nat.card F ∧ NaturalResidualSection h beta eβ n ∧
        ∃ (K : Type u) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (m : ℕ),
          0 < m ∧ Nat.card K = 2^m ∧
          ∃ eα : (H ⧸ pCore 2 H) ≃* SL(2,K),
            Nat.card K = Nat.card F ∧
            ⁅Q Γ beta,Z Γ a⁆ = Z Γ beta ∧ ⁅Q Γ beta,V Γ beta 1⁆ = Z Γ beta ∧
            (let q := eα.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
             letI : Algebra (ZMod 2) K := ZMod.algebra K 2
             ∃ (ρ : Representation (ZMod 2) SL(2,K) (Additive (Z Γ a)))
               (T : Sylow 2 SL(2,K)),
               (∀ (l : H) (z : Additive (Z Γ a)),
                 ((ρ (q l) z).toMul : Reduction.G₀ L S₀) =
                   (l : Reduction.G₀ L S₀) * z.toMul * (l : Reduction.G₀ L S₀)⁻¹) ∧
               Function.Injective ρ ∧ IsSourceNatural ρ T m ∧
               ∃ E : Additive (Z Γ a) ≃ₗ[ZMod 2] (Fin 2 → K),
                 ∀ g z, E (ρ g z) = Matrix.mulVec g.val (E z)) ∧
            V Γ a 2 ≤ graphLocalGroup Γ w ∧ (¬ V Γ a 2 ≤ Q Γ w) ∧
              ⁅⁅V Γ beta 1,V Γ a' 1⁆,V Γ a 2⁆ = ⊥ ∧
              ∃ t z : Vertex Γ, (graph Γ).Adj a t ∧ (graph Γ).Adj t z ∧
                (graph Γ).dist a z = 2 ∧ IsCriticalPair Γ z w ∧
                (graph Γ).dist t w + 1 = b Γ ∧ ⁅Z Γ z,Z Γ w⁆ = ⊥ ∧
                ∃ (_ez : (graphLocalGroup Γ z ⧸ pCore 2 (graphLocalGroup Γ z)) ≃* SL(2,K))
                  (et : (graphLocalGroup Γ t ⧸ pCore 2 (graphLocalGroup Γ t)) ≃* SL(2,F))
                  (ew : (graphLocalGroup Γ w ⧸ pCore 2 (graphLocalGroup Γ w)) ≃* SL(2,F)),
                  ⁅V Γ t 1 ⊓ Q Γ w,V Γ w 1⁆ = ⊥ ∧
                  ⁅V Γ w 1 ⊓ Q Γ t,V Γ t 1⁆ = ⊥ ∧
                  (Q Γ w).relIndex (V Γ t 1) = Nat.card F ∧
                  (Q Γ t).relIndex (V Γ w 1) = Nat.card F ∧
                  NaturalResidualSection h t et n ∧ NaturalResidualSection h w ew n := by
  let Γ := Reduction.reducedFamily L S₀
  have hb1 : 1 < b Γ := by change 3 < b Γ at hb; omega
  have hzero (z : Vertex Γ) (hz : (graph Γ).Adj z a')
      (hzc : IsCriticalPair Γ z beta) (hzcomm : ⁅Z Γ z,Z Γ beta⁆ = ⊥)
      (he : ⁅V Γ a' 1 ⊓ Q Γ beta,V Γ beta 1⁆ ≠ ⊥) : False :=
    Nat.ne_of_gt hb (h8 z a' beta hzc hz
      (by rwa [SimpleGraph.dist_comm]) hb1 hzcomm he)
  obtain ⟨F,instF,finF,charF,n,hn,hF,eβ,hx,_,_,hres,
      K,instK,finK,charK,m,hm,hK,eα,heq,_,_,hi,hpath,hcQ,hcV,hnat⟩ :=
    reduced_critical_reciprocal_sections h hc hab hd hb1 hcomm htriv
      (fun z hz hzc hzcomm he => (hzero z hz hzc hzcomm he).elim) hob Mα Mβ Mα' Mαsource
  let := instF
  let := finF
  let := charF
  let := instK
  let := finK
  let := charK
  exact ⟨F,instF,finF,charF,n,hn,hF,eβ,hx,hres,K,instK,finK,charK,m,hm,hK,eα,
    heq,hcQ,hcV,hnat,reduced_linear_shifted_sections h h8 hob hc hab hd hb hcomm hn hF eα eβ
      hx hi hpath hv hw hdv hdw⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
