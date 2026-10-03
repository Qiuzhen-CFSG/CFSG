module

public import Stellmacher.Recognition.Parrott.NormalizerGeneratorSeedActions

/-!
# Normalization of Parrott's normalizer generator branch

The recorded centralizer frame is invariant under replacing x by xz. If a seed
has xˢ = cawtz, replacing s by svt gives a seed on this new frame with
(xz)^(svt) = caw. Every other centralizer coordinate, the actual subgroups F and
T, and all the normalizer-fusion data remain the same. In particular, the new
seed still belongs to the actual normalizer and is an involution.

The proof constructs both complete structures, including their generation and
centralizer equations. It then shows that, in the presence of any seed, the
intended x-equation cannot hold uniformly for all frames and seeds described by
these interfaces. Global hypotheses on the unchanged group cannot remove this
symmetry. An additional normalization condition is needed to formulate a
uniform branch-exclusion theorem. The final existential theorem instead chooses
the frame with the required branch, preserving the actual subgroups and all
coordinates except the permitted central change of x.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.682, the exclusion preceding (25). The central twist diagnoses the
missing normalization in the currently recorded inputs; it does not assume any
of equations (25)–(26) beyond the seed and its checked consequences.
-/
open Subgroup Tits
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

private theorem central_mul_commutator (p q z : G)
    (hzp : Commute z p) (hzq : Commute z q) :
    parrottCommutator (p*z) q = parrottCommutator p q := by
  have hz : Commute z (p⁻¹*q⁻¹*p) :=
    (hzp.inv_right.mul_right hzq.inv_right).mul_right hzp
  calc
    _ = z⁻¹*(p⁻¹*q⁻¹*p)*z*q := by simp only [parrottCommutator,mul_inv_rev]; group
    _ = (p⁻¹*q⁻¹*p)*q := by rw [mul_assoc z⁻¹, ← hz.eq]; group
    _ = _ := rfl

private theorem central_mul_commutator_right (p q z : G)
    (hzp : Commute z p) (hzq : Commute z q) :
    parrottCommutator p (q*z) = parrottCommutator p q := by
  simp only [parrottCommutator, mul_inv_rev]
  have hz : Commute z (p⁻¹*q⁻¹*p*q) :=
    ((hzp.inv_right.mul_right hzq.inv_right).mul_right hzp).mul_right hzq
  calc
    _ = z⁻¹ * (p⁻¹*q⁻¹*p*q) * z := by
      calc
        _ = (p⁻¹*z⁻¹)*(q⁻¹*p*q*z) := by group
        _ = _ := by rw [← hzp.inv_inv.eq]; group
    _ = _ := by rw [mul_assoc, ← hz.eq]; group

private def centralTwist (f : ParrottCentralizerGeneratorData n) :
    ParrottCentralizerGeneratorData n := by
  have hzgens : z ∈ closure ({f.a,f.b,f.c,f.d} : Set G) := by
    have ha : f.a ∈ closure ({f.a,f.b,f.c,f.d} : Set G) := subset_closure (by simp)
    have hb : f.b ∈ closure ({f.a,f.b,f.c,f.d} : Set G) := subset_closure (by simp)
    have hd : f.d ∈ closure ({f.a,f.b,f.c,f.d} : Set G) := subset_closure (by simp)
    have hm : parrottCommutator f.d (parrottCommutator f.a f.b) ∈
        closure ({f.a,f.b,f.c,f.d} : Set G) := by
      unfold parrottCommutator
      repeat first | apply Subgroup.mul_mem | apply Subgroup.inv_mem | assumption
    simpa only [f.eq05_ab,f.eq03_dt] using hm
  have hgen : closure ({f.x*z,f.a,f.b,f.c,f.d} : Set G) = (e.sylow : Subgroup G) := by
    rw [← f.sylow_generators]
    have hz (q : G) : z ∈ closure ({q,f.a,f.b,f.c,f.d} : Set G) :=
      closure_mono (by intro g hg; simp only [Set.mem_insert_iff] at hg ⊢; exact Or.inr hg) hzgens
    apply le_antisymm <;> apply (closure_le _).mpr <;> intro g hg
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl
      · exact mul_mem (subset_closure (by simp)) (hz f.x)
      all_goals exact subset_closure (by simp)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl
      · have hm := mul_mem (subset_closure (by simp : f.x*z ∈ ({f.x*z,f.a,f.b,f.c,f.d} : Set G))) (hz (f.x*z))
        have heq : (f.x*z)*z=f.x := by simp only [mul_assoc, ← pow_two, f.z_sq, mul_one]
        rw [heq] at hm
        exact hm
      all_goals exact subset_closure (by simp)
  refine { f with
    x := f.x*z
    sylow_generators := hgen
    comm_zx := f.comm_zx.mul_right (Commute.refl z)
    eq01_x := ?_
    eq01_xt := ?_
    eq01_xv := ?_
    eq01_xu := ?_
    eq01_xw := ?_
    eq16_ax := ?_
    eq18_bx := ?_
    eq19_xc := ?_
    eq19_xd := ?_
    eq04 := ?_
    eq24 := ?_ }
  · rw [f.comm_zx.symm.mul_pow, f.eq01_x]
    have hz4 : z^4 = 1 := by
      calc
        z^4 = (z^2)^2 := by group
        _ = 1 := by rw [f.z_sq]; simp
    rw [hz4, one_mul]
  · rw [central_mul_commutator _ _ _ f.comm_zx f.comm_zt]; exact f.eq01_xt
  · rw [central_mul_commutator _ _ _ f.comm_zx f.comm_zv]; exact f.eq01_xv
  · rw [central_mul_commutator _ _ _ f.comm_zx f.comm_zu]; exact f.eq01_xu
  · rw [central_mul_commutator _ _ _ f.comm_zx f.comm_zw]; exact f.eq01_xw
  · rw [central_mul_commutator_right _ _ _ f.comm_az.symm f.comm_zx]; exact f.eq16_ax
  · rw [central_mul_commutator_right _ _ _ f.comm_zb f.comm_zx]; exact f.eq18_bx
  · rw [central_mul_commutator _ _ _ f.comm_zx f.comm_zc]; exact f.eq19_xc
  · rw [central_mul_commutator _ _ _ f.comm_zx f.comm_zd]; exact f.eq19_xd
  · rw [f.comm_zx.symm.mul_pow, f.eq04, f.z_sq, mul_one]
  · calc
      f.r * (f.x*z) * f.r = (f.r*f.x*f.r)*z := by rw [mul_assoc, mul_assoc, f.comm_zr.eq]; group
      _ = (f.y*f.r)^2 * (f.x*z) := by rw [f.eq24]; group

private theorem conj_of_commute {p q : G} (hp : Commute p q) : p⁻¹*q*p = q := by
  rw [mul_assoc, ← hp.eq]
  group

private def twistedSeed {f : ParrottCentralizerGeneratorData n}
    (k : ParrottNormalizerSeedData f) : ParrottNormalizerSeedData (centralTwist f) := by
  let S : G →* G := {
    toFun := fun g => k.s⁻¹*g*k.s
    map_one' := by group
    map_mul' := by intro g h; group }
  let C : G →* G := {
    toFun := fun g => (n.v*n.t)⁻¹*g*(n.v*n.t)
    map_one' := by group
    map_mul' := by intro g h; group }
  have cz : C z = z := conj_of_commute ((f.comm_zv.mul_right f.comm_zt).symm)
  have ct : C n.t = n.t := conj_of_commute (f.comm_tv.symm.mul_left (Commute.refl n.t))
  have cv : C n.v = n.v := conj_of_commute ((Commute.refl n.v).mul_left f.comm_tv)
  have cu : C f.u = f.u := conj_of_commute (f.comm_vu.mul_left f.comm_tu)
  have cw : C f.w = f.w := conj_of_commute (f.comm_vw.mul_left f.comm_tw)
  have ca : C f.a = f.a := conj_of_commute ((f.comm_av.mul_right f.comm_at).symm)
  have cc : C f.c = f.c*z := by
    have hc := (parrottCommutator_eq_iff _ _ _).mp f.eq10_cv
    have hct := (parrottCommutator_eq_one_iff _ _).mp f.eq10_ct
    change (n.v*n.t)⁻¹*f.c*(n.v*n.t) = f.c*z
    calc
      _ = n.t⁻¹*(n.v⁻¹*(f.c*n.v))*n.t := by group
      _ = n.t⁻¹*(f.c*z)*n.t := by rw [hc]; group
      _ = f.c*z := conj_of_commute (hct.symm.mul_right f.comm_zt.symm)
  have st : S n.t = z := k.t_conj
  have sz : S z = n.t := k.z_conj
  have sv : S n.v = n.v*n.t*z := k.v_conj
  have sy : S f.y = f.w*f.u*n.v*z := k.y_conj
  have sa : S f.a = f.u := k.a_conj_eq
  have zz : z*z=1 := by simpa only [pow_two] using f.z_sq
  have tt : n.t*n.t=1 := by simpa only [pow_two] using f.t_sq
  have hfix : S (n.v*n.t) = n.v*n.t := by
    rw [map_mul, sv, st, mul_assoc, mul_assoc, zz, mul_one]
  have hcomm : Commute k.s (n.v*n.t) := by
    change k.s*(n.v*n.t) = (n.v*n.t)*k.s
    calc
      _ = k.s*(S (n.v*n.t)) := by rw [hfix]
      _ = _ := by dsimp [S]; group
  have action (g : G) : (k.s*n.v*n.t)⁻¹*g*(k.s*n.v*n.t) = C (S g) := by
    dsimp [C,S]; group
  have xc : C (f.c*f.a*f.w) = f.c*f.a*f.w*z := by
    rw [map_mul, map_mul, cc, ca, cw]
    calc
      _ = f.c*(z*(f.a*f.w)) := by group
      _ = f.c*((f.a*f.w)*z) := by rw [(f.comm_az.symm.mul_right f.comm_zw).eq]
      _ = _ := by group
  refine {
    s := k.s*n.v*n.t
    mem_normalizer := mul_mem (mul_mem k.mem_normalizer
      (e.sylow_le_normalizer (e.le_sylow n.v_mem_inf.2)))
      (e.sylow_le_normalizer (e.le_sylow n.t_mem_inf.2))
    sq := ?_
    t_conj := ?_
    v_conj := ?_
    y_conj := ?_
    a_conj := Or.inl ?_
    x_conj := ?_ }
  · rw [mul_assoc, hcomm.mul_pow, k.sq, f.comm_tv.symm.mul_pow, f.v_sq, f.t_sq]
    simp
  · rw [action, st, cz]
  · rw [action, sv, map_mul, map_mul, cv, ct, cz]
  · change (k.s*n.v*n.t)⁻¹*f.y*(k.s*n.v*n.t) = f.w*f.u*n.v*z
    rw [action, sy, map_mul, map_mul, map_mul, cw, cu, cv, cz]
  · change (k.s*n.v*n.t)⁻¹*f.a*(k.s*n.v*n.t) = f.u
    rw [action, sa, cu]
  · change (k.s*n.v*n.t)⁻¹*(f.x*z)*(k.s*n.v*n.t) = f.c*f.a*f.w ∨
      (k.s*n.v*n.t)⁻¹*(f.x*z)*(k.s*n.v*n.t) = f.c*f.a*f.w*n.t*z
    rw [action, map_mul, sz, map_mul, ct]
    rcases k.x_conj with hx | hx
    · change S f.x = f.c*f.a*f.w at hx
      right
      rw [hx, xc]
      rw [mul_assoc, f.comm_zt.eq]
      group
    · change S f.x = f.c*f.a*f.w*n.t*z at hx
      left
      rw [hx, map_mul, map_mul, xc, ct, cz]
      calc
        _ = f.c*f.a*f.w*(z*z)*(n.t*n.t) := by
          calc
            _ = f.c*f.a*f.w*z*(n.t*z)*n.t := by group
            _ = _ := by rw [f.comm_zt.symm.eq]; group
        _ = f.c*f.a*f.w := by rw [zz,tt]; group

private theorem twistedSeed_x_wrong {f : ParrottCentralizerGeneratorData n}
    (k : ParrottNormalizerSeedData f)
    (hx : k.s⁻¹*f.x*k.s = f.c*f.a*f.w*n.t*z) :
    (twistedSeed k).s⁻¹ * (centralTwist f).x * (twistedSeed k).s =
      (centralTwist f).c * (centralTwist f).a * (centralTwist f).w := by
  have hc := (parrottCommutator_eq_iff _ _ _).mp f.eq10_cv
  have hct := (parrottCommutator_eq_one_iff _ _).mp f.eq10_ct
  have hz := k.z_conj
  have zz : z*z=1 := by simpa only [pow_two] using f.z_sq
  have tt : n.t*n.t=1 := by simpa only [pow_two] using f.t_sq
  change (k.s*n.v*n.t)⁻¹*(f.x*z)*(k.s*n.v*n.t) = f.c*f.a*f.w
  calc
    _ = n.t⁻¹*n.v⁻¹*((k.s⁻¹*f.x*k.s)*(k.s⁻¹*z*k.s))*n.v*n.t := by group
    _ = n.t⁻¹*n.v⁻¹*(f.c*f.a*f.w*n.t*z*n.t)*n.v*n.t := by rw [hx,hz]
    _ = n.t⁻¹*n.v⁻¹*(f.c*f.a*f.w*z)*n.v*n.t := by
      have htz : n.t*z*n.t=z := by rw [f.comm_zt.symm.eq,mul_assoc,tt,mul_one]
      calc
        _ = n.t⁻¹*n.v⁻¹*(f.c*f.a*f.w*(n.t*z*n.t))*n.v*n.t := by group
        _ = _ := by rw [htz]
    _ = (n.t⁻¹*(n.v⁻¹*f.c*n.v)*n.t)*f.a*f.w*z := by
      have hv := (f.comm_av.symm.mul_right f.comm_vw).mul_right f.comm_zv.symm
      have ht := (f.comm_at.symm.mul_right f.comm_tw).mul_right f.comm_zt.symm
      calc
        _ = n.t⁻¹*n.v⁻¹*f.c*((f.a*f.w*z)*n.v)*n.t := by group
        _ = n.t⁻¹*n.v⁻¹*f.c*(n.v*(f.a*f.w*z))*n.t := by rw [hv.symm.eq]
        _ = (n.t⁻¹*(n.v⁻¹*f.c*n.v))*((f.a*f.w*z)*n.t) := by group
        _ = _ := by rw [ht.symm.eq]; group
    _ = (n.t⁻¹*(f.c*z)*n.t)*f.a*f.w*z := by
      have hcv : n.v⁻¹*f.c*n.v=f.c*z := by rw [mul_assoc,hc]; group
      rw [hcv]
    _ = (f.c*z)*f.a*f.w*z := by rw [conj_of_commute (hct.symm.mul_right f.comm_zt.symm)]
    _ = f.c*f.a*f.w := by
      have hzw := f.comm_az.symm.mul_right f.comm_zw
      calc
        _ = f.c*(z*(f.a*f.w))*z := by group
        _ = f.c*((f.a*f.w)*z)*z := by rw [hzw.eq]
        _ = _ := by simp only [mul_assoc,zz,mul_one]

/-- The seed interface admits a central coordinate twist that switches the
remaining x-branch. Thus a uniform exclusion for every supplied frame and seed
cannot follow from these interfaces whenever a seed exists. -/
public theorem ParrottNormalizerSeedData.not_uniform_x_conj_eq
    {f : ParrottCentralizerGeneratorData n} (k : ParrottNormalizerSeedData f) :
    ¬ (∀ (f' : ParrottCentralizerGeneratorData n) (k' : ParrottNormalizerSeedData f'),
      k'.s⁻¹*f'.x*k'.s = f'.c*f'.a*f'.w*n.t*z) := by
  intro hall
  have hx := hall f k
  have hwrong := twistedSeed_x_wrong k hx
  have hright := hall (centralTwist f) (twistedSeed k)
  have heq : f.c*f.a*f.w = f.c*f.a*f.w*n.t*z := hwrong.symm.trans hright
  have htz : n.t*z=1 := mul_left_cancel (show
      (f.c*f.a*f.w)*(n.t*z) = (f.c*f.a*f.w)*1 by
    simpa only [mul_assoc,mul_one] using heq.symm)
  have ht : n.t = z := by
    have h := congrArg (fun g : G => g*z) htz
    simpa only [mul_assoc,← pow_two,f.z_sq,mul_one,one_mul] using h
  apply n.t_not_mem_zpowers
  rw [ht]
  exact mem_zpowers z

private theorem twistedSeed_x_right {f : ParrottCentralizerGeneratorData n}
    (k : ParrottNormalizerSeedData f)
    (hx : k.s⁻¹*f.x*k.s = f.c*f.a*f.w) :
    (twistedSeed k).s⁻¹ * (centralTwist f).x * (twistedSeed k).s =
      (centralTwist f).c * (centralTwist f).a * (centralTwist f).w * n.t * z := by
  let S : G →* G := {
    toFun := fun g => k.s⁻¹*g*k.s
    map_one' := by group
    map_mul' := by intro g h; group }
  let C : G →* G := {
    toFun := fun g => (n.v*n.t)⁻¹*g*(n.v*n.t)
    map_one' := by group
    map_mul' := by intro g h; group }
  have ct : C n.t = n.t :=
    conj_of_commute (f.comm_tv.symm.mul_left (Commute.refl n.t))
  have ca : C f.a = f.a :=
    conj_of_commute ((f.comm_av.mul_right f.comm_at).symm)
  have cw : C f.w = f.w :=
    conj_of_commute (f.comm_vw.mul_left f.comm_tw)
  have cc : C f.c = f.c*z := by
    have hc := (parrottCommutator_eq_iff _ _ _).mp f.eq10_cv
    have hct := (parrottCommutator_eq_one_iff _ _).mp f.eq10_ct
    change (n.v*n.t)⁻¹*f.c*(n.v*n.t) = f.c*z
    calc
      _ = n.t⁻¹*(n.v⁻¹*(f.c*n.v))*n.t := by group
      _ = n.t⁻¹*(f.c*z)*n.t := by rw [hc]; group
      _ = f.c*z := conj_of_commute (hct.symm.mul_right f.comm_zt.symm)
  have sz : S z = n.t := k.z_conj
  have xc : C (f.c*f.a*f.w) = f.c*f.a*f.w*z := by
    rw [map_mul, map_mul, cc, ca, cw]
    calc
      _ = f.c*(z*(f.a*f.w)) := by group
      _ = f.c*((f.a*f.w)*z) := by
        rw [(f.comm_az.symm.mul_right f.comm_zw).eq]
      _ = _ := by group
  change S f.x = f.c*f.a*f.w at hx
  change (k.s*n.v*n.t)⁻¹*(f.x*z)*(k.s*n.v*n.t) = f.c*f.a*f.w*n.t*z
  calc
    _ = C (S (f.x*z)) := by dsimp [C, S]; group
    _ = C (f.c*f.a*f.w) * C n.t := by rw [map_mul, hx, sz, map_mul]
    _ = f.c*f.a*f.w*z*n.t := by rw [xc, ct]
    _ = f.c*f.a*f.w*n.t*z := by rw [mul_assoc, f.comm_zt.eq]; group

/-- Normalize the remaining seed branch while retaining the actual F,T,t,v
and every auxiliary centralizer coordinate except the permitted x ↦ xz. -/
public theorem ParrottNormalizerSeedData.exists_normalized_frame
    {f : ParrottCentralizerGeneratorData n} (k : ParrottNormalizerSeedData f) :
    ∃ (f' : ParrottCentralizerGeneratorData n) (k' : ParrottNormalizerSeedData f'),
      (f'.u, f'.w, f'.a, f'.b, f'.c, f'.d, f'.y, f'.r) =
        (f.u, f.w, f.a, f.b, f.c, f.d, f.y, f.r) ∧
      (f'.x = f.x ∨ f'.x = f.x*z) ∧
      k'.s⁻¹*f'.x*k'.s = f'.c*f'.a*f'.w*n.t*z := by
  rcases k.x_conj with hx | hx
  · exact ⟨centralTwist f, twistedSeed k, rfl, Or.inr rfl,
      twistedSeed_x_right k hx⟩
  · exact ⟨f, k, rfl, Or.inl rfl, hx⟩

end Stellmacher.Recognition
