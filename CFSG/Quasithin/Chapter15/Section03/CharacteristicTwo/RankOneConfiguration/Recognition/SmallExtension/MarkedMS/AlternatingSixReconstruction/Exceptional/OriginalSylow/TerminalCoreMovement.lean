module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalAvoidance
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOmegaControl
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.OmegaControl
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.FullSeed
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBackwardRigidity
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalKernels
/-!
# Full omega fixed parts and terminal core movement

The six-letter displacement coordinates show that a vector of the full
omega layer fixed by A6 is fixed by S6: otherwise a transposition gives a
nonzero pair vector fixed by A6, contradicted by a three-letter permutation.
Transport through the original cubic projection identifies the part of X
fixed by the local residual with a subgroup of the full stabilizer center.
The projection kernel remains E, including the odd quotient E/Q.

On three generating backward shifts above distance four, endpoint
normalization puts the preceding core in the last proper Thompson mover.
Its quadratic action places the whole neighboring seed/core commutator in
the preceding full omega layer and the last moving cover. The last critical
line lies inside this commutator, escapes the preceding fixed core and is
moved by the common edge. The whole commutator is edge-normalized, elementary
abelian and has order at least four. Its containment in the actual restricted
critical kernel follows from the index-two quotient. Full endpoint omega
normalization also preserves the displacement of that restricted kernel.
That displacement is nonzero: otherwise the kernel-centralizer theorem
would trap the whole movement in the order-two critical line.

Both full moving covers and their central attachments are retained.
OriginalSylowExceptional applies these facts to the literal original c.L,d.S.
The remaining mover equality in (5.10), terminal exclusions (5.11)--(5.12),
whole-core exhaustion and block reconstruction still require their proofs.
The private coordinate imports continue the existing internal six-letter
calculation; no natural replacement graph is identified with this graph.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3) and (5.10), printed pp.866--867,922--923.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags Theory.SpecificGroups.SymmetricSix
open Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
open Natural.Exhaustion.LargeDistance.SectionFive.SeedCoordinates

private theorem even_fixed_is_fixed
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (ρ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) Y)
    (j : (coreRepresentation (Fin 6)).IntertwiningMap ρ)
    (hj : ∀ i k : Fin 6, i ≠ k → j (pairVector i k) ≠ 0)
    (v : Y) (w : Full (Fin 6))
    (hw : ∀ g : Equiv.Perm (Fin 6), ρ g v-v = j (displacement g w))
    (hv : ∀ g ∈ alternatingGroup (Fin 6), ρ g v = v) :
    ∀ g : Equiv.Perm (Fin 6), ρ g v = v := by
  have hswap (i k : Fin 6) (hik : i ≠ k) : ρ (Equiv.swap i k) v = v := by
    let t := Equiv.swap i k
    have heven (g : Equiv.Perm (Fin 6)) (hg : g ∈ alternatingGroup (Fin 6)) :
        ρ g (ρ t v-v) = ρ t v-v := by
      have hconj : t⁻¹*g*t ∈ alternatingGroup (Fin 6) := by
        simpa only [inv_inv] using (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem g hg t⁻¹
      calc
        _ = ρ (g*t) v-v := by rw [map_sub,←Module.End.mul_apply,←map_mul,hv g hg]
        _ = ρ t (ρ (t⁻¹*g*t) v)-v := by rw [←Module.End.mul_apply,←map_mul]; congr 2; group
        _ = _ := by rw [hv _ hconj]
    have hd : ρ t v-v = (w i+w k) • j (pairVector i k) := by
      rw [hw,displacement_swap,map_smul]
    by_cases hc : w i+w k = 0
    · exact sub_eq_zero.mp (by rw [hd,hc,zero_smul])
    have hone : w i+w k = 1 := by
      have hh := (show ∀ c : ZMod 2, c = 0 ∨ c = 1 from by decide) (w i+w k)
      exact hh.resolve_left hc
    have hp : ∀ g ∈ alternatingGroup (Fin 6), ρ g (j (pairVector i k)) = j (pairVector i k) := by
      simpa only [hd,hone,one_smul] using heven
    obtain ⟨l,hli,hlk⟩ : ∃ l : Fin 6, l ≠ i ∧ l ≠ k := by
      fin_cases i <;> fin_cases k <;> decide
    let g := Equiv.swap i l * Equiv.swap k l
    have hg : g ∈ alternatingGroup (Fin 6) := by
      simp [g,Equiv.Perm.mem_alternatingGroup,Equiv.Perm.sign_swap (Ne.symm hli),
        Equiv.Perm.sign_swap (Ne.symm hlk)]
    have hgi : g i = l := by
      simp [g,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hik (Ne.symm hli)]
    have hletters := fixed_pair_letters ρ j hj g i k hik (hp g hg)
    rw [hgi] at hletters
    exact (hletters.elim hli hlk).elim
  intro g
  induction g using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul g i k hik ih =>
    rw [map_mul,Module.End.mul_apply,ih,hswap i k hik]

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
private theorem small_critical_omega_residual_fixed_base
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4) :
    X Rg (alpha Rg) ⊓ centralizer (Ltilde Rg (alpha Rg) : Set (FreeAmalgam Rg)) ≤
      centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
  obtain ⟨j,_,hj,hcoords⟩ := omega_coordinates h e hz hk p hp
  rintro x ⟨hx,hxL⟩ y hy
  rw [graph_X h] at hx
  obtain ⟨v,hv,rfl⟩ := hx
  let v₀ := Additive.ofMul (⟨v,hv⟩ : centralOmega L R)
  obtain ⟨w,hw⟩ := hcoords v₀
  have heven (g : Equiv.Perm (Fin 6)) (hg : g ∈ alternatingGroup (Fin 6)) :
      omegaAction h e hz hk g v₀ = v₀ := by
    rw [←CubicAction.component_image h e hz hk] at hg
    obtain ⟨k,hkL,rfl⟩ := hg
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [omegaAction_conjugate]
    have hkgraph : embedM Rg k ∈ Ltilde Rg (alpha Rg) := by
      rw [Ltilde_alpha,h.relative_residual]
      exact mem_map_of_mem _ hkL
    have hcomm := hxL (embedM Rg k) hkgraph
    have hkv : k*v=v*k := by
      apply embedM_injective Rg
      simpa only [map_mul] using hcomm
    change k*v*k⁻¹=v
    rw [hkv,mul_inv_cancel_right]
  have hfixed := even_fixed_is_fixed (omegaAction h e hz hk) j hj v₀ w hw heven
  change y ∈ stabilizer Rg (mVertex Rg 1) at hy
  rw [stabilizer_m_base] at hy
  obtain ⟨m,rfl⟩ := hy
  have hh := congrArg (fun z : Additive (centralOmega L R) => (z.toMul : M)) (hfixed (π m))
  rw [omegaAction_conjugate] at hh
  have hm : m*v=v*m := mul_inv_eq_iff_eq_mul.mp hh
  simpa only [map_mul] using congrArg (embedM Rg) hm

include h e hz hk in
/-- On a small critical pair, the full omega subgroup fixed by the local
residual is fixed by the entire stabilizer. Both full moving covers are retained. -/
theorem small_critical_omega_residual_fixed
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4) :
    X Rg a ⊓ centralizer (Ltilde Rg a : Set (FreeAmalgam Rg)) ≤
      centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hh := small_critical_omega_residual_fixed_base h e hz hk (z := act Rg g⁻¹ z)
  rw [←hbase] at hh
  have hs : (Q Rg (act Rg g⁻¹ z)).relIndex (Z Rg (act Rg g⁻¹ a)) < 4 := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hp
  have hm := hh (p.act g⁻¹) hs
  rw [X_act,Ltilde_act,stabilizer_act,
    map_inf_centralizer_of_injective _ (MulAut.conj _).injective] at hm
  rintro x hx y hy
  have he := hm (mem_map_of_mem (MulAut.conj (g⁻¹)⁻¹).toMonoidHom hx)
    ((MulAut.conj (g⁻¹)⁻¹) y) (mem_map_of_mem _ hy)
  apply (MulAut.conj (g⁻¹)⁻¹).injective
  simpa only [map_mul,MulEquiv.coe_toMonoidHom] using he

include h e hz hk in
/-- Above distance four, the source fixed part of the full omega layer
is central at every original component vertex. -/
theorem borel_omega_fixedCore_central
    (hb : 4 < sourceDistance h)
    (u : Equiv.Perm (Fin 6)) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a : Vertex Rg} (ha : color Rg a = false) :
    X Rg a ⊓ fixedCore Rg a ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
  obtain ⟨z,p,hp,_⟩ := borel_small_critical_at h e hz hk hb u hR a ha
  exact (le_inf inf_le_left (inf_le_right.trans inf_le_right)).trans
    (small_critical_omega_residual_fixed h e hz hk p (by rw [hp]; decide))

include h e hz hk in
/-- Normalization places the last critical line in the full omega layer
of the preceding start. That line escapes its fixed core. -/
theorem borel_three_shift_line_omega
    (hb : 4 < sourceDistance h)
    (u : Equiv.Perm (Fin 6)) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path) :
    let v := r.path.walk.getVert (r.path.walk.length-2)
    let D := ⁅Z Rg t.start,Z Rg v⁆
    D ≤ X Rg r.start ∧ ¬ D ≤ fixedCore Rg r.start := by
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let D := ⁅Z Rg t.start,Z Rg v⁆
  have hb2 : 2 < sourceDistance h := by omega
  have ht := two_borel_backward_shifts_small_moving h e hz hk hb q.path r t
  have hs : (Q Rg v).relIndex (Z Rg t.start) < 4 := by rw [ht.2.1]; decide
  have hcore := (borel_three_shift_endpoint_normalization h e hz hk hb u hR p q r t).2
  have hfix := (borel_small_mover_normalizes_critical_kernel h e hz hk u hR t.path hs).1
  rw [t.first] at hfix
  have hDcore : D ≤ Q Rg r.start :=
    ((critical_seed_commutator_le h t.path).trans
      (terminal_neighbor_seed_radius t.adjacent_start t.adjacent_shift)).trans
        ((sourceGeometry h).V_le_Q hb2 r.start r.path.start_color)
  have hDC : D ≤ centralizer (Q Rg r.start : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp (hcore.trans hfix)
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) t.start t.path.start_color
  have hDX : D ≤ X Rg r.start := by
    intro x hx
    exact mem_omegaCenter_iff.mpr ⟨hDcore hx,
      elemPow_eq_one_of_isElementaryAbelian x ((critical_seed_commutator_le h t.path) hx),hDC hx⟩
  refine ⟨hDX,fun hDF => ?_⟩
  exact ht.1 ((le_inf hDX hDF).trans
    (borel_omega_fixedCore_central h e hz hk hb u hR r.path.start_color))


include h e hz hk in
/-- The whole neighboring seed/core commutator is elementary, normalized
by the actual common edge, and lies in both full omega layers. It has at
least four elements and escapes the preceding residual-fixed subgroup. -/
theorem borel_three_shift_core_movement
    (hb : 4 < sourceDistance h)
    (u : Equiv.Perm (Fin 6)) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path) :
    let v := r.path.walk.getVert (r.path.walk.length-2)
    let D := ⁅Z Rg t.start,Z Rg v⁆
    let H := ⁅Z Rg t.start,Q Rg r.start⁆
    D ≤ H ∧ H ≤ X Rg r.start ⊓ U Rg t.start ∧
      Q Rg t.edge ≤ normalizer (H : Set (FreeAmalgam Rg)) ∧
      IsElementaryAbelian 2 H ∧ 4 ≤ Nat.card H ∧
      (¬ H ≤ fixedCore Rg r.start) := by
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let D := ⁅Z Rg t.start,Z Rg v⁆
  let H := ⁅Z Rg t.start,Q Rg r.start⁆
  have hb2 : 2 < sourceDistance h := by omega
  have hline := borel_three_shift_line_omega h e hz hk hb u hR p q r t
  have ht := two_borel_backward_shifts_small_moving h e hz hk hb q.path r t
  have hDcard : Nat.card D = 2 := ht.2.2.2.1
  have hDmove : ¬ Q Rg t.edge ≤ centralizer (D : Set (FreeAmalgam Rg)) := by
    simpa only [t.first] using ht.2.2.2.2
  have hZvQ : Z Rg v ≤ Q Rg r.start := by
    apply Z_le_Q_of_dist_lt Rg v ((sourceGeometry h).exists_critical v t.path.end_color)
    rw [SimpleGraph.dist_comm,r.path.dist_start (by omega : r.path.walk.length-2 ≤ r.path.walk.length),
      (sourceGeometry h).distance_constant _ t.path.end_color]
    have hl : r.path.walk.length = sourceDistance h := r.path.length_eq_b
    change r.path.walk.length-2 < sourceDistance h
    omega
  have hDH : D ≤ H := commutator_mono le_rfl hZvQ
  obtain ⟨J,_,hJ,_,hJT,_,_,_,hquad⟩ :=
    borel_edge_maximal_offenders h e hz hk u hR t.path.start_color t.adjacent_shift
  have hQJ : Q Rg r.start ≤ J := by
    rw [←hJ]
    exact (borel_three_shift_endpoint_normalization h e hz hk hb u hR p q r t).2
  have hTG : Q Rg t.edge ≤ stabilizer Rg t.start :=
    fun _ hx => hx.2 _ (adjacent_symm Rg t.adjacent_shift)
  have hTrG : Q Rg t.edge ≤ stabilizer Rg r.start :=
    fun _ hx => hx.2 _ (adjacent_symm Rg t.adjacent_start)
  have hcomm : H = ⁅U Rg t.start,Q Rg r.start⁆ := by
    have hh := full_fixed_seed_edge_commutator h e hz t.path.start_color t.adjacent_shift
      (⊥ : Subgroup (FreeAmalgam Rg)) bot_le (Q Rg r.start) (hQJ.trans hJT)
    have hbot : centralizer ((⊥ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) = ⊤ := by
      apply top_unique
      intro x _ y hy
      rw [mem_bot.mp hy,mul_one,one_mul]
    simpa only [hbot,inf_top_eq] using hh
  have hHU : H ≤ U Rg t.start := by
    rw [hcomm]
    exact le_normalizer_iff_commutator_le_left.mp ((hQJ.trans hJT).trans
      (hTG.trans (U_normalized t.start)))
  have hHQ : H ≤ Q Rg r.start :=
    hHU.trans ((DistanceEight.U_le_Z Rg t.start).trans
      ((terminal_neighbor_seed_radius t.adjacent_start t.adjacent_shift).trans
        ((sourceGeometry h).V_le_Q hb2 r.start r.path.start_color)))
  have hHC : H ≤ centralizer (Q Rg r.start : Set (FreeAmalgam Rg)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    rw [hcomm]
    exact (commutator_mono (commutator_mono le_rfl hQJ) hQJ).trans_eq hquad
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) t.start t.path.start_color
  let : IsElementaryAbelian 2 H := IsElementaryAbelian.of_le (hHU.trans (DistanceEight.U_le_Z Rg t.start))
  have hHX : H ≤ X Rg r.start := by
    intro x hx
    exact mem_omegaCenter_iff.mpr ⟨hHQ hx,elemPow_eq_one_of_isElementaryAbelian x hx,hHC hx⟩
  have hTN : Q Rg t.edge ≤ normalizer (H : Set (FreeAmalgam Rg)) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅Z Rg t.start,Q Rg r.start⁆ : Subgroup (FreeAmalgam Rg)).map _ = _
    rw [map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized Rg t.start (hTG hx)),
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized Rg r.start (hTrG hx))]
  let := finite_Z Rg t.start
  let : Finite H := Finite.of_injective
    (inclusion (hHU.trans (DistanceEight.U_le_Z Rg t.start))) (inclusion_injective _)
  have hlarge : 2 < Nat.card H := by
    by_contra! hsmall
    have he : D = H := eq_of_le_of_card_ge hDH (hDcard ▸ hsmall)
    have hcardH : Nat.card H = 2 := he ▸ hDcard
    exact hDmove (he.symm ▸ (hTN.trans (normalizer_le_centralizer_of_card_two H hcardH)))
  have hfour : 4 ≤ Nat.card H := by
    have hd : 2 ∣ Nat.card H := hDcard ▸ card_dvd_of_le hDH
    obtain ⟨k,hk⟩ := hd
    omega
  exact ⟨hDH,le_inf hHX hHU,hTN,inferInstance,hfour,fun hh => hline.2 (hDH.trans hh)⟩


include h e hz hk in
/-- The whole seed/core movement lies in the actual restricted critical
kernel. The displacement of that kernel is normalized by the full endpoint
omega group, using the already proved normalization of the kernel/seed join. -/
theorem borel_three_shift_restricted_core_movement
    (hb : 4 < sourceDistance h)
    (u : Equiv.Perm (Fin 6)) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    let K := Z Rg t.start ⊓ Q Rg v
    ⁅Z Rg t.start,Q Rg r.start⁆ ≤ K ∧
      ⁅K ⊔ Z Rg r.start,Q Rg r.start⁆ = ⁅K,Q Rg r.start⁆ ∧
      X Rg z ≤ normalizer
        ((⁅K,Q Rg r.start⁆ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let K := Z Rg t.start ⊓ Q Rg v
  let N := K ⊔ Z Rg r.start
  have hcore := (borel_three_shift_endpoint_normalization h e hz hk hb u hR p q r t).2
  have ht := two_borel_backward_shifts_small_moving h e hz hk hb q.path r t
  have hs : (Q Rg v).relIndex (Z Rg t.start) < 4 := by rw [ht.2.1]; decide
  have hKN := (borel_small_mover_normalizes_critical_kernel h e hz hk u hR t.path hs).2
  rw [t.first] at hKN
  obtain ⟨J,_,hJ,_,hJT,_⟩ :=
    borel_edge_maximal_offenders h e hz hk u hR t.path.start_color t.adjacent_shift
  have hTG : Q Rg t.edge ≤ stabilizer Rg t.start :=
    fun _ hx => hx.2 _ (adjacent_symm Rg t.adjacent_shift)
  have hQG : Q Rg r.start ≤ stabilizer Rg t.start := by
    rw [hJ] at hcore
    exact (hcore.trans hJT).trans hTG
  have hHK : ⁅Z Rg t.start,Q Rg r.start⁆ ≤ K :=
    commutator_le_of_normalized_index_two (Z Rg t.start) K (Q Rg r.start) inf_le_left
      (by rw [show K = Z Rg t.start ⊓ Q Rg v from rfl,inf_relIndex_left]; exact ht.2.1)
      (hQG.trans (Z_normalized Rg t.start))
      (hcore.trans hKN)
  have hb2 : 2 < sourceDistance h := by omega
  have hKQ : K ≤ Q Rg r.start :=
    (inf_le_left.trans (terminal_neighbor_seed_radius t.adjacent_start t.adjacent_shift)).trans
      ((sourceGeometry h).V_le_Q hb2 r.start r.path.start_color)
  have hcomm : ⁅N,Q Rg r.start⁆ = ⁅K,Q Rg r.start⁆ := by
    rw [commutator_comm N,commutator_comm K]
    symm
    exact commutator_eq_of_centralizing_sup (sup_comm _ _)
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg r.start r.path.start_color))
      (hKQ.trans (Q Rg r.start).le_normalizer)
  have hNX := borel_three_shift_omega_normalization h e hz hk hb u hR p q r t
  have hXG : X Rg z ≤ stabilizer Rg r.start :=
    critical_X_le_vertex h e z r.path.end_color r.start (reverse_pair h e r.path)
  refine ⟨hHK,hcomm,?_⟩
  rw [←hcomm]
  intro x hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hNX hx),
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized Rg r.start (hXG hx))]


include h e hz hk in
/-- The restricted critical kernel has nonzero displacement under the
preceding core. Otherwise the kernel-centralizer theorem would bound the
whole seed/core movement by the order-two critical line. -/
theorem borel_three_shift_restricted_core_movement_ne_bot
    (hb : 4 < sourceDistance h)
    (u : Equiv.Perm (Fin 6)) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path) :
    ⁅Z Rg t.start ⊓ Q Rg (r.path.walk.getVert (r.path.walk.length-2)),Q Rg r.start⁆ ≠ ⊥ := by
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let D := ⁅Z Rg t.start,Z Rg v⁆
  let H := ⁅Z Rg t.start,Q Rg r.start⁆
  have ht := two_borel_backward_shifts_small_moving h e hz hk hb q.path r t
  have hDcard : Nat.card D = 2 := ht.2.2.2.1
  let : Finite D := Nat.finite_of_card_ne_zero (by rw [hDcard]; decide)
  have hlarge : 4 ≤ Nat.card H :=
    (borel_three_shift_core_movement h e hz hk hb u hR p q r t).2.2.2.2.1
  obtain ⟨J,_,hJ,_,hJT,_⟩ :=
    borel_edge_maximal_offenders h e hz hk u hR t.path.start_color t.adjacent_shift
  have hcore := (borel_three_shift_endpoint_normalization h e hz hk hb u hR p q r t).2
  rw [hJ] at hcore
  have hQG : Q Rg r.start ≤ stabilizer Rg t.start :=
    (hcore.trans hJT).trans (fun _ hx => hx.2 _ (adjacent_symm Rg t.adjacent_shift))
  let rev : CriticalPath Rg (sourceGeometry h) v t.start :=
    CriticalPath.ofPair t.path.end_color (reverse_pair h e t.path)
  have hs : (Q Rg t.start).relIndex (Z Rg v) < 4 := by rw [ht.2.2.1]; decide
  intro hzero
  have hfix : Q Rg r.start ≤ centralizer (Z Rg t.start ⊓ Q Rg v : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)
  have hbound := small_critical_kernel_commutator h e hz hk rev hs (Q Rg r.start) hQG hfix
  rw [commutator_comm (Q Rg r.start),commutator_comm (Z Rg v)] at hbound
  have hsmall : Nat.card H ≤ 2 := (card_le_of_le hbound).trans_eq hDcard
  omega

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
