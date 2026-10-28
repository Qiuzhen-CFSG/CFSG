module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.BackwardComplete
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# The fixed commutator line in the symplectic backward argument

For A contained in the fixed preimage B at an original-group vertex c,
[A,Q_c] is invariant under the local component: the component moves A only
by Z_c, and Z_c centralizes Q_c. If this commutator has order at most two,
it is fixed pointwise and lies in D_c, the source fixed core.

For the actual small critical path, the last-edge calculation bounds
[U_e intersect Q_a,Q_c] by the genuine critical commutator line. Applying the
preceding observation to the selected backward layer proves its R1 lies in
D_c and is preserved by the component transporter. The sole local placement
premise U_e intersect Q_a <= B_c is retained explicitly; it is the separate
geometric step in the first sentence of source (5.8).

The final edge corollary supplies the stronger input used by the binary
seed-fixer argument: a commutator of order at most two between Z_a and a
subgroup of the adjacent Q_t is centralized by all of Q_t. The abelian
point-core image makes Q_t normalize that commutator line.

No general [B_c,Q_c] bound or linear-three source is required. The source
applications retain the original natural module, characteristic replacement
coordinates, critical path, and coordinated backward choice.

Source: Meierfrankenfeld--Stellmacher (1993), (5.8), printed p.920,
using the small-edge inputs of (5.7), printed p.919.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement

private theorem fixed_mod_central_normalizes_commutator {G : Type*} [Group G]
    (A Q L : Subgroup G) (hAQ : A ≤ normalizer (Q : Set G))
    (hLQ : L ≤ normalizer (Q : Set G))
    (hLA : ⁅L,A⁆ ≤ centralizer (Q : Set G)) :
    L ≤ normalizer ((⁅A,Q⁆ : Subgroup G) : Set G) := by
  apply le_normalizer_closure_iff.mpr
  rintro l hl _ ⟨a,ha,q,hq,rfl⟩
  have hq' : l*q*l⁻¹ ∈ Q := (mem_normalizer_iff.mp (hLQ hl) q).mp hq
  have hk : ⁅l,a⁆ ∈ centralizer (Q : Set G) := hLA (commutator_mem_commutator hl ha)
  have hcomm : ⁅a,l*q*l⁻¹⁆ ∈ Q :=
    le_normalizer_iff_commutator_le_right.mp hAQ (commutator_mem_commutator ha hq')
  have hzero : ⁅⁅l,a⁆,l*q*l⁻¹⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hk _ hq').symm
  rw [conjugate_commutatorElement,show l*a*l⁻¹ = ⁅l,a⁆*a by
    simp [commutatorElement_def,mul_assoc],commutatorElement_mul_left_eq_conj_mul,
    hzero,mul_one,←hk _ hcomm,mul_inv_cancel_right]
  exact commutator_mem_commutator ha hq'

open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

/-- A small kernel commutator of a subgroup in B is fixed by the component. -/
theorem small_B_kernel_commutator_le_fixedCore
    (hb : 2 < s.geometry.b R) {c : Vertex R} (hc : color R c = false)
    (A : Subgroup (FreeAmalgam R)) (hAB : A ≤ B R c (s.geometry.Z_normal _))
    (hcard : Nat.card (⁅A,Q R c⁆ : Subgroup (FreeAmalgam R)) ≤ 2) :
    ⁅A,Q R c⁆ ≤ fixedCore R c := by
  have hVL : V R c ≤ stabilizer R c := (s.geometry.V_le_Q hb c hc).trans (fun _ hx => hx.1)
  have hAQ : A ≤ Q R c := by
    intro a ha
    exact (s.geometry.V_le_Q hb c hc) ((mem_B_iff R c _ hVL a).mp (hAB ha)).1
  have hNQ : ⁅A,Q R c⁆ ≤ Q R c :=
    le_normalizer_iff_commutator_le_right.mp (hAQ.trans (Q R c).le_normalizer)
  have hLA : ⁅Ltilde R c,A⁆ ≤ centralizer (Q R c : Set (FreeAmalgam R)) := by
    apply le_trans _ (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R c hc))
    apply commutator_le.mpr
    intro l hl a ha
    exact ((mem_B_iff R c _ hVL a).mp (hAB ha)).2 l hl
  have hn : Ltilde R c ≤ normalizer ((⁅A,Q R c⁆ : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) :=
    fixed_mod_central_normalizes_commutator A (Q R c) (Ltilde R c)
      (hAQ.trans (Q R c).le_normalizer)
      ((Ltilde_le_stabilizer c).trans (Q_normalized R c)) hLA
  let := finite_stabilizer R c
  let : Finite (⁅A,Q R c⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion (hNQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  by_cases he : Nat.card (⁅A,Q R c⁆ : Subgroup (FreeAmalgam R)) = 2
  · exact le_inf hNQ (le_centralizer_iff.mp
      (hn.trans (normalizer_le_centralizer_of_card_two _ he)))
  · have hz : ⁅A,Q R c⁆ = ⊥ := eq_bot_of_card_le _ (by omega)
    rw [hz]
    exact bot_le

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

/-- The last edge supplies the order-two bound on the actual endpoint intersection. -/
theorem critical_small_kernel_commutator_le_fixedCore
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) {a e : Vertex R}
    (p : CriticalPath R s.geometry a e)
    (hsmall : (Q R e).relIndex (Z R a) < 4)
    (hAB : U R e ⊓ Q R a ≤ B R (p.walk.getVert (p.walk.length-2))
      (s.geometry.Z_normal _)) :
    ⁅U R e ⊓ Q R a,Q R (p.walk.getVert (p.walk.length-2))⁆ ≤
      fixedCore R (p.walk.getVert (p.walk.length-2)) := by
  have hc : color R (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := s.geometry.even a p.start_color
    rw [←p.critical.1,←p.shortest] at he
    rw [Nat.even_iff] at he ⊢
    omega
  apply s.small_B_kernel_commutator_le_fixedCore hb hc _ hAB
  have hpoint : R.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    simpa only [Model.pointCore_eq_exceptional] using hfull
  have hedge := s.critical_last_edge_inputs hb p
  have hfix := (s.small_edge_fixed_at h u hpoint p.end_color hedge.1
    (Z R a) hedge.2.2 p.critical.2 (s.small_critical_fixedIndex_le_two h p hsmall)).1
  rw [←s.critical_kernel_eq_fixed p] at hfix
  have hline : ⁅U R e ⊓ Q R a,Q R (p.walk.getVert (p.walk.length-2))⁆ ≤ ⁅Z R a,Z R e⁆ := by
    apply ((commutator_mono (inf_le_inf_right _ (DistanceEight.U_le_Z R e)) hedge.2.1).trans hfix).trans
    rw [commutator_comm]
    exact commutator_mono le_rfl (DistanceEight.U_le_Z R e)
  have hlineZ : ⁅Z R a,Z R e⁆ ≤ Z R a :=
    ((s.critical_Z_commutator_le_moving p).trans inf_le_left).trans (DistanceEight.U_le_Z R a)
  let := finite_Z R a
  let : Finite (⁅Z R a,Z R e⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hlineZ) (inclusion_injective _)
  exact (card_le_of_le hline).trans_eq (s.small_critical_commutator_card h p hsmall)

/-- The actual selected backward line lies in the second predecessor's fixed core. -/
theorem CoordinatedChoice.small_line_le_fixedCore
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) {e : Vertex R}
    {p : CriticalPath R s.geometry (alpha R) e} {delta : Vertex R}
    (z : s.CoordinatedChoice p delta)
    (hsmall : (Q R e).relIndex (Z R (alpha R)) < 4)
    (hY : Z R z.alpha1 ≤ Q R (p.walk.getVert (p.walk.length-2)))
    (hAB : U R e ⊓ Q R (alpha R) ≤ B R (p.walk.getVert (p.walk.length-2))
      (s.geometry.Z_normal _)) :
    ⁅Z R z.alpha1,U R e ⊓ Q R (alpha R)⁆ ≤
      fixedCore R (p.walk.getVert (p.walk.length-2)) := by
  rw [commutator_comm]
  exact (commutator_mono le_rfl hY).trans
    (s.critical_small_kernel_commutator_le_fixedCore h u hfull hb p hsmall hAB)

/-- A component transporter at the second predecessor preserves the same selected line. -/
theorem CoordinatedChoice.small_line_map_conj_eq
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) {e : Vertex R}
    {p : CriticalPath R s.geometry (alpha R) e} {delta : Vertex R}
    (z : s.CoordinatedChoice p delta)
    (hsmall : (Q R e).relIndex (Z R (alpha R)) < 4)
    (hY : Z R z.alpha1 ≤ Q R (p.walk.getVert (p.walk.length-2)))
    (hAB : U R e ⊓ Q R (alpha R) ≤ B R (p.walk.getVert (p.walk.length-2))
      (s.geometry.Z_normal _))
    (t : FreeAmalgam R) (ht : t ∈ Ltilde R (p.walk.getVert (p.walk.length-2))) :
    (⁅Z R z.alpha1,U R e ⊓ Q R (alpha R)⁆ : Subgroup (FreeAmalgam R)).map
      (MulAut.conj t).toMonoidHom = ⁅Z R z.alpha1,U R e ⊓ Q R (alpha R)⁆ := by
  have hfix := z.small_line_le_fixedCore s h u hfull hb hsmall hY hAB
  exact mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
    (le_centralizer_iff.mp (hfix.trans inf_le_right) ht))

/-- A commutator line on an actual edge is centralized by the entire edge kernel. -/
theorem small_edge_commutator_le_centralizer
    (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t)
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ Q R t)
    (hcard : Nat.card (⁅Z R a,A⁆ : Subgroup (FreeAmalgam R)) ≤ 2) :
    ⁅Z R a,A⁆ ≤ centralizer (Q R t : Set (FreeAmalgam R)) := by
  have hQtG : Q R t ≤ stabilizer R a :=
    fun _ hx => hx.2 a (adjacent_symm R hat)
  have hQtZ := hQtG.trans (Z_normalized R a)
  have hcomm : ⁅Q R t,A⁆ ≤ centralizer (Z R a : Set (FreeAmalgam R)) :=
    ((commutator_mono le_rfl hA).trans (s.edge_derived_le_kernel u hfull ha hat)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q R a ha)))
  have hn := fixed_mod_central_normalizes_commutator A (Z R a) (Q R t)
    (hA.trans hQtZ) hQtZ hcomm
  rw [commutator_comm A (Z R a)] at hn
  have hNZ : ⁅Z R a,A⁆ ≤ Z R a :=
    le_normalizer_iff_commutator_le_left.mp (hA.trans hQtZ)
  let := finite_Z R a
  let : Finite (⁅Z R a,A⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hNZ) (inclusion_injective _)
  by_cases he : Nat.card (⁅Z R a,A⁆ : Subgroup (FreeAmalgam R)) = 2
  · exact le_centralizer_iff.mp
      (hn.trans (normalizer_le_centralizer_of_card_two _ he))
  · have hz : ⁅Z R a,A⁆ = ⊥ := eq_bot_of_card_le _ (by omega)
    rw [hz]
    exact bot_le

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
