module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CommonKernel

/-!
# Full omega kernels in the small critical branch

The full omega layers at a critical pair belong to the opposite local groups.
The seed-kernel centralizer calculation then shows that X and Z have the
same image modulo the opposite kernel. Centralizing supplements identify
[X_a,X_z] with [Z_a,Z_z], and the full X-kernel has the same local pointwise
centralizer as the seed kernel. Thus fixing X_z intersect Q_a controls the
displacement of the entire X_z, without replacing X by Z.

Under the source central-generation clause X_z = U_z C_{X_z}(G_z), the
full kernel is the seed kernel times this central summand. A normalized
local span therefore has the same commutator with either kernel. This
clause remains explicit: the small critical image alone is not used to
assert central generation or splitting.

The actual shifted-path application retains the same component conjugator,
generating edge, every shared path vertex and all the previous seed-line
data. It constructs the literal A_0 = X_z intersect Q_c and R_3 = [D,A_0],
proves that R_3 lies in D intersect A_0 and contains the nonzero seed-kernel
line, and identifies the two commutators if the source central-generation
clause at the original vertex holds. That clause is transported through the
actual free-amalgam conjugation. Both moved cover orders and the canonical
natural quotient remain unchanged.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3) and (5.9), printed
pp.866--867 and 920--922, especially A_0 and R_3 on p.921. Deriving the
central-generation clause from the failure of normalization, comparing the
shifted spans, the strict slice estimate, and the two terminal distance
contradictions remain open. No unconditional R_3 line identity or distance
exclusion is asserted here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
private theorem critical_full_X_local (hc : DistanceTwo.CentralLayer d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z) :
    X d.radical a ≤ stabilizer d.radical z ∧
      X d.radical z ≤ stabilizer d.radical a := by
  exact ⟨CriticalCriterion.critical_X_le_stabilizer d.radical (replacementGeometry h d)
    (edgeCentralizerCondition s hc) (replacementDistance_pos h d) a p.start_color z p.critical,
    CriticalCriterion.critical_X_le_stabilizer d.radical (replacementGeometry h d)
    (edgeCentralizerCondition s hc) (replacementDistance_pos h d) z p.end_color a
      (critical_reverse_pair s hc p)⟩

include h in
private theorem seed_le_full_X {a : Vertex d.radical} (ha : color d.radical a = false) :
    Z d.radical a ≤ X d.radical a := by
  apply (replacementGeometry h d).omega_bound a ha
  rw [(replacementGeometry h d).distance_constant a ha]
  exact replacementDistance_pos h d

include s in
/-- The full omega layer and the seed have the same critical image. -/
theorem small_critical_X_join (hc : DistanceTwo.CentralLayer d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4) :
    Q d.radical a ⊔ X d.radical z = Q d.radical a ⊔ Z d.radical z := by
  apply le_antisymm
  · apply sup_le le_sup_left
    apply le_trans _ (small_critical_kernel_centralizer s hc p hsmall)
    exact le_inf (critical_full_X_local s hc p).2
      (le_centralizer_iff.mp ((inf_le_right : Z d.radical a ⊓ Q d.radical z ≤ Q d.radical z).trans
        (Q_le_centralizer_X d.radical z)))
  · exact sup_le_sup_left (seed_le_full_X (h := h) p.end_color) _

include s in
/-- Enlarging both seeds to their full omega layers preserves the critical line. -/
theorem small_critical_X_commutator (hc : DistanceTwo.CentralLayer d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4) :
    ⁅X d.radical a,X d.radical z⁆ = ⁅Z d.radical a,Z d.radical z⁆ := by
  let q : CriticalPath d.radical (replacementGeometry h d) z a :=
    CriticalPath.ofPair p.end_color (critical_reverse_pair s hc p)
  have hs : (Q d.radical a).relIndex (Z d.radical z) < 4 := by
    rw [(small_critical_indices s hc p hsmall).2]
    decide
  have he₁ : ⁅X d.radical a,X d.radical z⁆ = ⁅X d.radical a,Z d.radical z⁆ := by
    rw [commutator_eq_of_centralizing_sup rfl (Q_le_centralizer_X d.radical a)
      ((critical_full_X_local s hc p).2.trans (X_normalized d.radical a)),
      small_critical_X_join s hc p hsmall]
    exact (commutator_eq_of_centralizing_sup rfl (Q_le_centralizer_X d.radical a)
      (((seed_le_full_X (h := h) p.end_color).trans (critical_full_X_local s hc p).2).trans
        (X_normalized d.radical a))).symm
  rw [he₁,commutator_comm (X d.radical a),commutator_comm (Z d.radical a)]
  have hQ : Q d.radical z ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) :=
    (Q_le_centralizer_X d.radical z).trans (centralizer_le (seed_le_full_X (h := h) p.end_color))
  rw [commutator_eq_of_centralizing_sup rfl hQ
    ((critical_full_X_local s hc p).1.trans (Z_normalized d.radical z)),
    small_critical_X_join s hc q hs]
  exact (commutator_eq_of_centralizing_sup rfl hQ
    (((seed_le_full_X (h := h) p.start_color).trans (critical_full_X_local s hc p).1).trans
      (Z_normalized d.radical z))).symm

include s in
/-- The full X-kernel has the same pointwise centralizer as the seed kernel. -/
theorem small_critical_X_kernel_centralizer (hc : DistanceTwo.CentralLayer d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4) :
    stabilizer d.radical a ⊓ centralizer
      (X d.radical a ⊓ Q d.radical z : Set (FreeAmalgam d.radical)) =
        Q d.radical a ⊔ Z d.radical z := by
  apply le_antisymm
  · exact (inf_le_inf_left _ (centralizer_le
      (inf_le_inf_right _ (seed_le_full_X (h := h) p.start_color)))).trans
        (small_critical_kernel_centralizer s hc p hsmall)
  · apply sup_le
    · exact le_inf (fun _ hx => hx.1)
        ((Q_le_centralizer_X d.radical a).trans (centralizer_le inf_le_left))
    · apply le_inf ((seed_le_full_X (h := h) p.end_color).trans (critical_full_X_local s hc p).2)
      exact ((seed_le_full_X (h := h) p.end_color).trans
        (le_centralizer_iff.mp (Q_le_centralizer_X d.radical z))).trans
          (centralizer_le inf_le_right)

include s in
/-- Fixing the full X-kernel controls displacement of the full X-layer. -/
theorem small_critical_X_kernel_control (hc : DistanceTwo.CentralLayer d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (Y : Subgroup (FreeAmalgam d.radical))
    (hY : Y ≤ stabilizer d.radical z)
    (hfix : Y ≤ centralizer (X d.radical z ⊓ Q d.radical a : Set (FreeAmalgam d.radical))) :
    ⁅Y,X d.radical z⁆ ≤ ⁅Z d.radical a,Z d.radical z⁆ := by
  let q : CriticalPath d.radical (replacementGeometry h d) z a :=
    CriticalPath.ofPair p.end_color (critical_reverse_pair s hc p)
  have hs : (Q d.radical a).relIndex (Z d.radical z) < 4 := by
    rw [(small_critical_indices s hc p hsmall).2]
    decide
  have hj : Y ≤ Q d.radical z ⊔ X d.radical a := by
    rw [small_critical_X_join s hc q hs]
    rw [←small_critical_X_kernel_centralizer s hc q hs]
    exact le_inf hY hfix
  rw [←small_critical_X_commutator s hc p hsmall,commutator_comm Y,commutator_comm (X d.radical a)]
  exact (commutator_mono le_rfl hj).trans_eq
    (commutator_eq_of_centralizing_sup rfl (Q_le_centralizer_X d.radical z)
      ((critical_full_X_local s hc p).1.trans (X_normalized d.radical z))).symm

include s in
/-- The source central-generation clause identifies the larger kernel,
retaining its entire central summand. This clause is not inferred from a
small critical image. -/
theorem critical_X_kernel_of_central_generation (hc : DistanceTwo.CentralLayer d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hgen : X d.radical z = U d.radical z ⊔
      (X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)))) :
    X d.radical z ⊓ Q d.radical a = (Z d.radical z ⊓ Q d.radical a) ⊔
      (X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) := by
  let F := X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))
  have hZa : Z d.radical a ≤ stabilizer d.radical z :=
    (seed_le_full_X (h := h) p.start_color).trans (critical_full_X_local s hc p).1
  have hFfix : F ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans (centralizer_le hZa)
  have hXZ : X d.radical z = Z d.radical z ⊔ F := by
    apply le_antisymm
    · exact hgen.le.trans (sup_le_sup_right (DistanceEight.U_le_Z d.radical z) _)
    · exact sup_le (seed_le_full_X (h := h) p.end_color) inf_le_left
  have hFC : F ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans (centralizer_le (Z_le_stabilizer d.radical z))
  have hK (T : Subgroup (FreeAmalgam d.radical)) (hT : T ≤ stabilizer d.radical a) :
      T ⊓ Q d.radical a = T ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) := by
    rw [←C_eq_Q s hc a p.start_color]
    exact le_antisymm (inf_le_inf_left _ inf_le_right)
      (le_inf inf_le_left (le_inf (inf_le_left.trans hT) inf_le_right))
  rw [hK _ (critical_full_X_local s hc p).2,
    hK _ ((seed_le_full_X (h := h) p.end_color).trans (critical_full_X_local s hc p).2)]
  change X d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) =
    (Z d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical))) ⊔ F
  calc
    _ = (F ⊔ Z d.radical z) ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
      congrArg (fun T : Subgroup (FreeAmalgam d.radical) =>
        T ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)))
        (hXZ.trans (sup_comm _ _))
    _ = F ⊔ (Z d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical))) :=
      inf_centralizer_sup_of_centralizing _ _ _ (hFC.trans (Subgroup.centralizer_le_normalizer _)) hFfix
    _ = _ := sup_comm _ _

include s in
/-- Under the source central-generation clause, a locally normalized span
has exactly the seed-kernel commutator. The added central part contributes
nothing; no complement or vanishing central line is assumed. -/
theorem critical_X_kernel_commutator_of_central_generation (hc : DistanceTwo.CentralLayer d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hgen : X d.radical z = U d.radical z ⊔
      (X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))))
    (Y : Subgroup (FreeAmalgam d.radical)) (hY : Y ≤ stabilizer d.radical z)
    (hN : X d.radical z ⊓ Q d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical))) :
    ⁅Y,X d.radical z ⊓ Q d.radical a⁆ = ⁅Y,Z d.radical z ⊓ Q d.radical a⁆ := by
  rw [critical_X_kernel_of_central_generation s hc p hgen,
    sup_comm (Z d.radical z ⊓ Q d.radical a)]
  exact (commutator_eq_of_centralizing_sup rfl
    (inf_le_right.trans (centralizer_le hY))
    ((inf_le_inf_right _ (seed_le_full_X (h := h) p.end_color)).trans hN)).symm

omit [Finite G] in
private theorem X_central_generation_at
    (hgen : X d.radical (alpha d.radical) = U d.radical (alpha d.radical) ⊔
      (X d.radical (alpha d.radical) ⊓ centralizer
        (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical))))
    {z : Vertex d.radical} (hz : color d.radical z = false) :
    X d.radical z = U d.radical z ⊔
      (X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color d.radical hz
  let j := (MulAut.conj g⁻¹).toMonoidHom
  have hh := congrArg (Subgroup.map j) hgen
  rw [Subgroup.map_sup,←map_inf_centralizer_of_injective j (MulAut.conj g⁻¹).injective] at hh
  change (X d.radical (alpha d.radical)).map (MulAut.conj g⁻¹).toMonoidHom =
    (U d.radical (alpha d.radical)).map (MulAut.conj g⁻¹).toMonoidHom ⊔
      ((X d.radical (alpha d.radical)).map (MulAut.conj g⁻¹).toMonoidHom ⊓
        centralizer ((stabilizer d.radical (alpha d.radical)).map (MulAut.conj g⁻¹).toMonoidHom :
          Set (FreeAmalgam d.radical))) at hh
  rw [←X_act,←U_act,←stabilizer_act] at hh
  simpa only [alpha,act_mVertex,one_mul] using hh

/-- The original full-point, small-forward-slice configuration with its
literal full X-kernel. All previous line data and path vertices use the same
component conjugator. The source central-generation clause is retained
explicitly in the last implication; without it the full commutator is only
shown to contain the nonzero seed-kernel line. -/
theorem full_point_small_shifted_X_kernel_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 4 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    let c := p.walk.getVert 2
    let T := Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical c ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
    let H := ⁅U d.radical c,T⁆
    ∃ z, ∃ q : CriticalPath d.radical (replacementGeometry h d) c z,
      (cosetGraph d.radical).dist a' z = 2 ∧
      (∀ i ≤ p.walk.length-2, q.walk.getVert i = p.walk.getVert (i+2)) ∧
      q.walk.getVert (q.walk.length-2) = a' ∧
      ∃ t, Adjacent d.radical c t ∧
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical c ∧
      ∃ y ∈ Ltilde d.radical c,
        let a := act d.radical y⁻¹ (alpha d.radical)
        let H₂ := H.map (MulAut.conj y).toMonoidHom
        let P := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
        let D := conjugateSpanBy (Z d.radical a) P
        let J := ⁅D,Z d.radical z ⊓ Q d.radical c⁆
        let A₀ := X d.radical z ⊓ Q d.radical c
        let R₃ := ⁅D,A₀⁆
        H₂ ≤ U d.radical c ⊓ Z d.radical t ∧
        P ⊔ Z d.radical z = stabilizer d.radical c ∧
        ¬ H₂ ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) ∧
        D ≤ Q d.radical a' ∧
        (Q d.radical z).relIndex (Z d.radical c) = 2 ∧
        Nat.card J = 2 ∧ J ≤ Z d.radical z ∧
        J ≤ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) ∧
        J ⊓ ⁅Z d.radical c,Z d.radical z⁆ = ⊥ ∧
        J ≤ fixedCore d.radical c ∧ J ≤ Z d.radical a ∧ J ≠ H₂ ∧
        (∃ x ∈ P, ⁅(Z d.radical a).map (MulAut.conj x).toMonoidHom,
          Z d.radical z ⊓ Q d.radical c⁆ = J) ∧
        Q d.radical c ⊔ X d.radical z = Q d.radical c ⊔ Z d.radical z ∧
        ⁅X d.radical c,X d.radical z⁆ = ⁅Z d.radical c,Z d.radical z⁆ ∧
        stabilizer d.radical z ⊓ centralizer (A₀ : Set (FreeAmalgam d.radical)) =
          Q d.radical z ⊔ Z d.radical c ∧
        J ≤ R₃ ∧ R₃ ≠ ⊥ ∧ R₃ ≤ D ⊓ A₀ ∧
        (X d.radical (alpha d.radical) = U d.radical (alpha d.radical) ⊔
          (X d.radical (alpha d.radical) ⊓ centralizer
            (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical))) →
          R₃ = J) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨z,q,haz,hover,hpre,t,hct,hQtgen,y,hy,hHseed,hPgen,hHmove,hDQ,
    hidx,hJcard,hJZ,hJG,hJcrit,hJcore,hJseed,hJne,x,hx,hxJ⟩ :=
    full_point_small_shifted_central_line_knownSimple hb u hfull p hslice hsmall
  let c := p.walk.getVert 2
  let a := act d.radical y⁻¹ (alpha d.radical)
  let T := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical c ⊓ B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
  let H₂ := (⁅U d.radical c,T⁆ : Subgroup (FreeAmalgam d.radical)).map (MulAut.conj y).toMonoidHom
  let P := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
  let D := conjugateSpanBy (Z d.radical a) P
  let J := ⁅D,Z d.radical z ⊓ Q d.radical c⁆
  let A₀ := X d.radical z ⊓ Q d.radical c
  let R₃ := ⁅D,A₀⁆
  have hDZ : D ≤ stabilizer d.radical z :=
    hDQ.trans (Q_le_stabilizer_of_dist_two d.radical a' z p.end_color haz)
  have hZaV : Z d.radical a ≤ V d.radical c := by
    have hl : p.walk.length = replacementDistance h d := p.length_eq_b
    have hZV : Z d.radical (alpha d.radical) ≤ V d.radical c :=
      le_iSup_of_le (alpha d.radical) (le_iSup_of_le
        (show (cosetGraph d.radical).dist (alpha d.radical) c ≤ 2 from
          (p.dist_start (by omega)).le) le_rfl)
    change Z d.radical (act d.radical y⁻¹ (alpha d.radical)) ≤ V d.radical c
    rw [Z_act,inv_inv]
    exact (map_mono hZV).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (DistanceEight.V_normalized d.radical c (Ltilde_le_stabilizer c hy)))
  have hDV : D ≤ V d.radical c :=
    conjugateSpanBy_le hZaV (inf_le_left.trans (V_normalized c))
  have hDc : D ≤ Q d.radical c :=
    hDV.trans ((replacementGeometry h d).V_le_Q
      (show 2 < replacementDistance h d by omega) c q.start_color)
  have hQcP : Q d.radical c ≤ P :=
    le_inf (fun _ hx => hx.1)
      ((Q_le_centralizer_X d.radical c).trans
        (centralizer_le ((hHseed.trans inf_le_left).trans
          ((DistanceEight.U_le_Z d.radical c).trans (seed_le_full_X (h := h) q.start_color)))))
  have hN : A₀ ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    (inf_le_right.trans hQcP).trans (le_normalizer_conjugateSpanBy _ _)
  have hR₃D : R₃ ≤ D := le_normalizer_iff_commutator_le_left.mp hN
  have hR₃A : R₃ ≤ A₀ := by
    apply le_normalizer_iff_commutator_le_right.mp
    exact (le_inf (hDZ.trans (X_normalized d.radical z))
      (hDc.trans (Q d.radical c).le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hJR : J ≤ R₃ :=
    commutator_mono le_rfl (inf_le_inf_right _ (seed_le_full_X (h := h) q.end_color))
  have hRne : R₃ ≠ ⊥ := by
    intro he
    have hJe : J = ⊥ := le_bot_iff.mp (he ▸ hJR)
    have hh : Nat.card J = 2 := hJcard
    rw [hJe,card_bot] at hh
    omega
  have hsmall' : (Q d.radical z).relIndex (Z d.radical c) < 4 := by
    rw [hidx]
    decide
  let rev : CriticalPath d.radical (replacementGeometry h d) z c :=
    CriticalPath.ofPair q.end_color (critical_reverse_pair s hc q)
  have hsmallrev : (Q d.radical c).relIndex (Z d.radical z) < 4 := by
    rw [(small_critical_indices s hc q hsmall').2]
    decide
  refine ⟨z,q,haz,hover,hpre,t,hct,hQtgen,y,hy,hHseed,hPgen,hHmove,hDQ,
    hidx,hJcard,hJZ,hJG,hJcrit,hJcore,hJseed,hJne,⟨x,hx,hxJ⟩,
    small_critical_X_join s hc q hsmall',small_critical_X_commutator s hc q hsmall',
    small_critical_X_kernel_centralizer s hc rev hsmallrev,hJR,hRne,le_inf hR₃D hR₃A,?_⟩
  intro hgen
  exact critical_X_kernel_commutator_of_central_generation s hc q
    (X_central_generation_at hgen q.end_color) D hDZ hN

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
