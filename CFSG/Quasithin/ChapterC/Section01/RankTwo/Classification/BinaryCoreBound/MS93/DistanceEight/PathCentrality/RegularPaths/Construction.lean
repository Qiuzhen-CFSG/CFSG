module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.Basic

/-!
# Constructing regular critical paths from the orbit-escape disjunction

The first escape alternative prepends two edges; the second prepends four.
Endpoint noncontainment and critical-distance minimality prove shortestness
in both cases. The old initial turns survive on the overlap, while actual
stabilizer elements supply the new turns. Induction produces a completely
regular path, then the amalgam action moves its start to any M-vertex.

This proves the geometric implication used on printed p.892. It does not
prove the subgroup escape disjunction on pp.892--893. The conjugate-shift
regularity theorem also retains the prescribed element for later extension.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.2)--(4.4.4), pp.892--894.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}


namespace CriticalPath
variable {a a' : Vertex R}

/-- Prepend a finite walk and truncate the same number of terminal edges.
Critical noncontainment forces the resulting length to be shortest. -/
def prepend (p : CriticalPath R geometry a a') {d : Vertex R}
    (hd : color R d = false) (q : (cosetGraph R).Walk d a) (m : ℕ)
    (hq : q.length = m) (hm : m ≤ geometry.b R)
    (hn : ¬ Z R d ≤ Q R (p.walk.getVert (p.walk.length - m))) :
    CriticalPath R geometry d (p.walk.getVert (p.walk.length - m)) := by
  let w := q.append (p.walk.take (p.walk.length - m))
  have hw : w.length = geometry.b R := by
    simp only [w, SimpleGraph.Walk.length_append, SimpleGraph.Walk.take_length,
      inf_eq_left.mpr (Nat.sub_le _ _), hq]
    have hl := p.length_eq_b
    omega
  have hmin := criticalDistance_le R d (geometry.exists_critical d hd) hn
  rw [geometry.distance_constant d hd] at hmin
  change geometry.b R ≤ _ at hmin
  have hmax := SimpleGraph.dist_le w
  have hdist : (cosetGraph R).dist d (p.walk.getVert (p.walk.length - m)) =
      geometry.b R := by omega
  exact ⟨hd, w, hw.trans hdist.symm,
    ⟨hdist.trans (geometry.distance_constant d hd).symm, hn⟩⟩

theorem prepend_overlap (p : CriticalPath R geometry a a') {d : Vertex R}
    (hd : color R d = false) (q : (cosetGraph R).Walk d a) (m : ℕ)
    (hq : q.length = m) (hm : m ≤ geometry.b R)
    (hn : ¬ Z R d ≤ Q R (p.walk.getVert (p.walk.length - m)))
    {i : ℕ} (hi : i ≤ p.walk.length - m) :
    (prepend p hd q m hq hm hn).walk.getVert (i + m) = p.walk.getVert i := by
  change (q.append (p.walk.take (p.walk.length - m))).getVert (i + m) = _
  rw [SimpleGraph.Walk.getVert_append, hq, if_neg (by omega),
    Nat.add_sub_cancel, SimpleGraph.Walk.take_getVert, inf_eq_right.mpr hi]

end CriticalPath

theorem InitialTurns.mono {a a' : Vertex R} {p : CriticalPath R geometry a a'}
    {m n : ℕ} (hp : InitialTurns p n) (hmn : m ≤ n) : InitialTurns p m :=
  fun i hi hi₂ hin hil => hp i hi hi₂ (hin.trans hmn) hil

theorem InitialTurns.prepend {a a' d d' : Vertex R}
    {p : CriticalPath R geometry a a'} {q : CriticalPath R geometry d d'}
    {n m : ℕ} (hp : InitialTurns p n) (hm : Even m)
    (ho : ∀ i, i ≤ p.walk.length - m → q.walk.getVert (i + m) = p.walk.getVert i)
    (hf : InitialTurns q m) : InitialTurns q (n + m) := by
  intro i hi hi₂ hin hil
  by_cases him : i ≤ m
  · exact hf i hi hi₂ him hil
  have he : Even (i - m) := by
    rw [Nat.even_iff] at hi hm ⊢
    omega
  have hi' : 2 ≤ i - m := by
    rw [Nat.even_iff] at he
    omega
  have hl : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
  obtain ⟨g, hg, ht⟩ := hp (i - m) he hi' (by omega) (by omega)
  have h0 := ho (i - m) (by omega)
  have hplus := ho (i - m + 2) (by omega)
  have hminus := ho (i - m - 2) (by omega)
  have e0 : i - m + m = i := by omega
  have ep : i - m + 2 + m = i + 2 := by omega
  have em : i - m - 2 + m = i - 2 := by omega
  rw [e0] at h0
  rw [ep] at hplus
  rw [em] at hminus
  exact ⟨g, h0 ▸ hg, by rwa [hplus, hminus]⟩

theorem initialTurns_conjugateShift {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (hb : 4 ≤ geometry.b R) {n : ℕ}
    (hp : InitialTurns p n) (g : FreeAmalgam R) (hg : g ∈ stabilizer R a)
    (hn : ¬ (Z R (p.walk.getVert 2)).map (MulAut.conj g⁻¹).toMonoidHom ≤
      Q R (p.walk.getVert (p.walk.length - 2))) :
    InitialTurns (p.conjugateShift (by omega) g hg hn) (n + 2) := by
  let q := p.conjugateShift (by omega) g hg hn
  have ho : ∀ i, i ≤ p.walk.length - 2 → q.walk.getVert (i + 2) = p.walk.getVert i := by
    intro i hi
    unfold q CriticalPath.conjugateShift
    exact p.prepend_two_overlap _ _ _ _ _ hi
  have hf : InitialTurns q 2 := by
    intro i _ hi₂ hi _
    have heq : i = 2 := by omega
    subst i
    have hlen := p.length_eq_b
    have h2 := ho 0 (by omega)
    have h4 := ho 2 (by omega)
    simp only [Nat.zero_add, SimpleGraph.Walk.getVert_zero] at h2
    refine ⟨g, ?_, ?_⟩
    · rwa [h2]
    · rw [show 2 + 2 = 4 by rfl, h4]
      simp only [Nat.sub_self, SimpleGraph.Walk.getVert_zero]
  exact hp.prepend (by decide) ho hf

theorem hasTurnConjugators_conjugateShift {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (hb : 4 ≤ geometry.b R)
    (hp : HasTurnConjugators R p) (g : FreeAmalgam R) (hg : g ∈ stabilizer R a)
    (hn : ¬ (Z R (p.walk.getVert 2)).map (MulAut.conj g⁻¹).toMonoidHom ≤
      Q R (p.walk.getVert (p.walk.length - 2))) :
    HasTurnConjugators R (p.conjugateShift (by omega) g hg hn) := by
  have hp' : InitialTurns p (geometry.b R) := fun i hi hi₂ _ hil => hp i hi hi₂ hil
  have h := initialTurns_conjugateShift p hb hp' g hg hn
  intro i hi hi₂ hil
  have hl := (p.conjugateShift (show 2 ≤ geometry.b R by omega) g hg hn).length_eq_b
  exact h i hi hi₂ (by omega) hil

theorem exists_two_step_extension {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (hb : 4 ≤ geometry.b R) {n : ℕ}
    (hp : InitialTurns p n)
    (he : ¬ localZSpan R (p.walk.getVert 2) a ≤
      Q R (p.walk.getVert (p.walk.length - 2))) :
    ∃ d d', ∃ q : CriticalPath R geometry d d', InitialTurns q (n + 2) := by
  obtain ⟨g, hg, hn⟩ := exists_conjugate_not_le he
  rw [Z_act] at hn
  exact ⟨_, _, p.conjugateShift (by omega) g hg hn,
    initialTurns_conjugateShift p hb hp g hg hn⟩

theorem exists_four_step_extension {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (hb : 6 ≤ geometry.b R) {n : ℕ}
    (hp : InitialTurns p n) (g : FreeAmalgam R) (hg : g ∈ stabilizer R a)
    (he : ¬ localZSpan R a (Stellmacher.PushingUp.AmalgamGraph.act R g (p.walk.getVert 2)) ≤
      Q R (p.walk.getVert (p.walk.length - 4))) :
    ∃ d d', ∃ q : CriticalPath R geometry d d', InitialTurns q (n + 4) := by
  obtain ⟨h, hh, hn⟩ := exists_conjugate_not_le he
  have hlen := p.length_eq_b
  have htwo : 2 ≤ p.walk.length := by omega
  have hga : Stellmacher.PushingUp.AmalgamGraph.act R g a = a := hg
  let c := Stellmacher.PushingUp.AmalgamGraph.act R g (p.walk.getVert 2)
  have hhc : Stellmacher.PushingUp.AmalgamGraph.act R h c = c := hh
  let r : (cosetGraph R).Walk c a :=
    (actWalk R g (p.walk.take 2).reverse).copy rfl hga
  have hr : r.length = 2 := by
    simp only [r, SimpleGraph.Walk.length_copy, actWalk_length,
      SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.take_length, inf_eq_left.mpr htwo]
  let s : (cosetGraph R).Walk (Stellmacher.PushingUp.AmalgamGraph.act R h a) c :=
    (actWalk R h r.reverse).copy rfl hhc
  have hs : s.length = 2 := by
    simp only [s, SimpleGraph.Walk.length_copy, actWalk_length,
      SimpleGraph.Walk.length_reverse, hr]
  have hsr : (s.append r).length = 4 := by rw [SimpleGraph.Walk.length_append, hs, hr]
  let q := CriticalPath.prepend p ((action_preserves_color R h a).trans p.start_color)
    (s.append r) 4 hsr (by omega) hn
  have ho : ∀ i, i ≤ p.walk.length - 4 → q.walk.getVert (i + 4) = p.walk.getVert i := by
    intro i hi
    exact CriticalPath.prepend_overlap p _ _ _ _ _ _ hi
  have hq2 : q.walk.getVert 2 = c := by
    change ((s.append r).append (p.walk.take (p.walk.length - 4))).getVert 2 = c
    rw [SimpleGraph.Walk.getVert_append, hsr, if_pos (by decide),
      SimpleGraph.Walk.getVert_append, hs, if_neg (by decide)]
    simp only [Nat.sub_self, SimpleGraph.Walk.getVert_zero]
  have hq4 : q.walk.getVert 4 = a := by
    simpa only [Nat.zero_add, SimpleGraph.Walk.getVert_zero] using ho 0 (by omega)
  have hq6 : q.walk.getVert 6 = p.walk.getVert 2 := ho 2 (by omega)
  have hf : InitialTurns q 4 := by
    intro i hi hi₂ hi₄ _
    have hic : i = 2 ∨ i = 4 := by rw [Nat.even_iff] at hi; omega
    rcases hic with rfl | rfl
    · refine ⟨h, ?_, ?_⟩
      · rwa [hq2]
      · rw [show 2 + 2 = 4 by rfl, hq4]
        simp only [Nat.sub_self, SimpleGraph.Walk.getVert_zero]
    · refine ⟨g, ?_, ?_⟩
      · rwa [hq4]
      · rw [show 4 + 2 = 6 by rfl, show 4 - 2 = 2 by rfl, hq6, hq2]
  exact ⟨_, _, q, hp.prepend (by decide) ho hf⟩

theorem exists_initialTurns (hb : 6 ≤ geometry.b R)
    (he : ∀ {a a' : Vertex R} (p : CriticalPath R geometry a a'), OrbitEscapeAlternative p)
    (n : ℕ) : ∃ a a', ∃ p : CriticalPath R geometry a a', InitialTurns p (2 * n) := by
  induction n with
  | zero =>
    obtain ⟨a', ⟨p⟩⟩ := CriticalPath.exists_from (geometry := geometry) (R := R)
      (show color R (alpha R) = false from rfl)
    refine ⟨_, a', p, ?_⟩
    intro i _ hi hi₀ _
    omega
  | succ n ih =>
    obtain ⟨a, a', p, hp⟩ := ih
    rcases he p with h | ⟨g, hg, h⟩
    · obtain ⟨d, d', q, hq⟩ := exists_two_step_extension p (by omega) hp h
      exact ⟨d, d', q, by simpa only [Nat.mul_add, Nat.mul_one] using hq⟩
    · obtain ⟨d, d', q, hq⟩ := exists_four_step_extension p hb hp g hg h
      exact ⟨d, d', q, hq.mono (by omega)⟩

theorem hasTurnConjugators_act {a a' : Vertex R} (p : CriticalPath R geometry a a')
    (hp : HasTurnConjugators R p) (g : FreeAmalgam R) :
    HasTurnConjugators R (p.act g) := by
  intro i hi hi₂ hiend
  change i + 2 ≤ (actWalk R g p.walk).length at hiend
  rw [actWalk_length] at hiend
  obtain ⟨h, hh, ht⟩ := hp i hi hi₂ hiend
  refine ⟨g⁻¹ * h * g, ?_, ?_⟩
  · change g⁻¹ * h * g ∈ stabilizer R ((actWalk R g p.walk).getVert i)
    rw [actWalk_getVert, stabilizer_act]
    simpa only [MulAut.conj_apply, inv_inv, MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_coe] using mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hh
  · change Stellmacher.PushingUp.AmalgamGraph.act R (g⁻¹ * h * g)
      ((actWalk R g p.walk).getVert (i + 2)) = (actWalk R g p.walk).getVert (i - 2)
    rw [actWalk_getVert, actWalk_getVert, ← act_mul]
    simp only [← mul_assoc, mul_inv_cancel, one_mul, act_mul, ht]

/-- The combinatorial implication at the start of (4.4.2). The orbit-escape
disjunction remains explicit and must be proved from the source inputs. -/
theorem exists_regular_of_orbitEscape (hb : 4 < geometry.b R)
    (he : ∀ {a a' : Vertex R} (p : CriticalPath R geometry a a'), OrbitEscapeAlternative p)
    (a : Vertex R) (ha : color R a = false) :
    ∃ a', ∃ p : CriticalPath R geometry a a', HasTurnConjugators R p := by
  have heven : Even (geometry.b R) := geometry.even (alpha R) rfl
  have hb₆ : 6 ≤ geometry.b R := by rw [Nat.even_iff] at heven; omega
  obtain ⟨d, d', p, hp⟩ := exists_initialTurns hb₆ he (geometry.b R)
  have hreg : HasTurnConjugators R p := by
    intro i hi hi₂ hiend
    have hlen := p.length_eq_b
    exact hp i hi hi₂ (by omega) hiend
  obtain ⟨x, hx⟩ := exists_mVertex_of_color R p.start_color
  obtain ⟨y, hy⟩ := exists_mVertex_of_color R ha
  have hact : Stellmacher.PushingUp.AmalgamGraph.act R (x⁻¹ * y) d = a := by
    rw [hx, hy, act_mVertex]
    simp only [← mul_assoc, mul_inv_cancel, one_mul]
  have h := hasTurnConjugators_act p hreg (x⁻¹ * y)
  exact hact ▸ ⟨_, p.act (x⁻¹ * y), h⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths
