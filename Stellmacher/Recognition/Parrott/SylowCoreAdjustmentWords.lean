module

public import Stellmacher.Recognition.Parrott.SylowCoreGeometry

/-!
# Removing central factors in Parrott's core words

The five central errors determine binary corrections a ↦ atᵖ and
c ↦ cwᑫvʳtˢ⁺ʳuˡ. In particular the v correction changes both c² and
(cd)², which explains the sum of bits in the t correction. Collecting
words verifies all affected relations through (15). The elementary
commutations and involutions come from the actual E and F.

The coordinates here are reassembled with their subgroup generation
certificates in `SylowCoreAdjustment`.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.679, the choices preceding equations (11)–(15).
-/

set_option linter.unusedSimpArgs false
open Subgroup
open scoped IsMulCommutative
open Stellmacher.Recognition Tits

variable {G : Type*} [Group G]
private theorem tail {p q r : G} (h : p*q=r) (k : G) : p*(q*k)=r*k := by rw [← mul_assoc, h]
private theorem sqinv {p : G} (hp : p ^ 2 = 1) : p⁻¹ = p :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hp)
private theorem reverse {p q r : G} (h : p*q=q*p*r) : q*p=p*q*r⁻¹ := by rw [h]; group

private theorem coset_bit [Finite G] {z g k : G} (hz : orderOf z = 2)
    (hc : Commute z k) (hg : g / k ∈ zpowers z) :
    ∃ b : Bool, g = k * (if b then z else 1) := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hz] at hg
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hg
  have hi' := Finset.mem_range.mp hi
  interval_cases i
  · refine ⟨false, ?_⟩
    simpa using (div_eq_iff_eq_mul.mp he.symm)
  · refine ⟨true, ?_⟩
    simpa [hc.eq] using (div_eq_iff_eq_mul.mp he.symm)

private theorem swap_of_square {c d k q : G} (hd : d^2=1)
    (hk : k^2=1) (hc : c^2=k) (hcd : (c*d)^2=q)
    (hdk : Commute d k) (hdq : Commute d q) : d*c=c*d*k*q := by
  have hi : c⁻¹=c*k := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, ← pow_two, hc, ← pow_two, hk]
  calc
    d*c = c⁻¹*q*d⁻¹ := by rw [← hcd, pow_two]; group
    _ = c*d*k*q := by
      rw [hi, sqinv hd]
      simp only [mul_assoc, ← hdq.eq, ← hdk.eq, tail hdk.symm.eq]

private theorem comm_of_squares {c d k q : G} (hd : d^2=1)
    (hk : k^2=1) (hc : c^2=k) (hcd : (c*d)^2=q)
    (hq : q^2=1) (hkq : Commute k q)
    (hdk : Commute d k) (hdq : Commute d q) :
    parrottCommutator c d = k*q := by
  apply (parrottCommutator_eq_iff _ _ _).mpr
  have sw : d*c=c*d*(k*q) := by
    simpa only [mul_assoc] using swap_of_square hd hk hc hcd hdk hdq
  have hh := reverse sw
  simpa only [mul_assoc, mul_inv_rev, sqinv hk, sqinv hq, hkq.symm.eq] using hh

namespace Stellmacher.Recognition.ParrottSylowInitialData
variable {z : G} {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- Corrected coordinates and their word relations, before rebuilding the
actual elementary and core generating equalities. -/
public structure CoreAdjustedCoordinates (f : ParrottSylowInitialData n) (caseTwo : Bool) where
  a : G
  c : G
  a_eq : a = f.a ∨ a = f.a * n.t
  c_eq : ∃ r ∈ closure ({f.w, n.v, n.t, f.u} : Set G), c = f.c * r
  aw : parrottCommutator a f.w = z
  ab : parrottCommutator a f.b = n.t
  ax : parrottCommutator a f.x = 1 ∨ parrottCommutator a f.x = n.t
  cu : parrottCommutator c f.u = 1
  cw : parrottCommutator c f.w = 1
  ct : parrottCommutator c n.t = 1
  cv : parrottCommutator c n.v = z
  ad : parrottCommutator a f.d = if caseTwo then f.u * n.v else f.u
  ac : parrottCommutator a c = if caseTwo then n.v else n.v * n.t
  cc : c ^ 2 = if caseTwo then f.w else f.w * f.u
  cd : parrottCommutator c f.d = if caseTwo then f.w else f.w * f.u
  bc : parrottCommutator f.b c = if caseTwo then f.u * n.t else f.u * n.v

set_option maxHeartbeats 800000 in
/-- The central coset alternatives admit the successive corrections by
 t on a and w,v,t,u on c. -/
public theorem exists_core_adjusted_coordinates [Finite G] (f : ParrottSylowInitialData n)
    (h : ParrottCentralizerHypotheses z) (caseTwo : Bool)
    (hc : f.CoreCosetAlternatives caseTwo) : Nonempty (CoreAdjustedCoordinates f caseTwo) := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 (commutator J) :=
    (parrott_centralizer_structure z h).2.2.2.2.2.1
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (H.subtype.comp J.subtype)
  let : IsElementaryAbelian 2 e.F := e.elementary
  have hzE : z ∈ E := e.z_mem_inf.1
  have htE : n.t ∈ E := n.t_mem_inf.1
  have hvE : n.v ∈ E := n.v_mem_inf.1
  have huE : f.u ∈ E := f.basis_mem_derived _ (by simp)
  have hwE : f.w ∈ E := f.basis_mem_derived _ (by simp)
  have haF : f.a ∈ e.F := by
    rw [← f.elementary_basis]
    exact subset_closure (by simp)
  have huF : f.u ∈ e.F := by
    rw [← f.elementary_basis]
    exact subset_closure (by simp)
  have commE {r s : G} (hr : r ∈ E) (hs : s ∈ E) : Commute r s :=
    setLike_mul_comm hr hs
  have commF {r s : G} (hr : r ∈ e.F) (hs : s ∈ e.F) : Commute r s :=
    setLike_mul_comm hr hs
  have powE {r : G} (hr : r ∈ E) : r^2=1 :=
    elemPow_eq_one_of_isElementaryAbelian r hr
  have czb := f.commute_z_of_mem_core (f.generators_mem_core f.b (by simp))
  have czc := f.commute_z_of_mem_core (f.generators_mem_core f.c (by simp))
  have czd := f.commute_z_of_mem_core (f.generators_mem_core f.d (by simp))
  have cza := commF e.z_mem_inf.2 haF
  have cta := commF n.t_mem_inf.2 haF
  have cva := commF n.v_mem_inf.2 haF
  have cua := commF huF haF
  have cdw := (parrottCommutator_eq_one_iff _ _).mp f.eq07_dw
  have cdu := (parrottCommutator_eq_one_iff _ _).mp f.eq08_du
  have cbv : Commute f.b n.v := by
    rw [← f.eq03_b]
    exact Commute.self_pow _ _
  have cdv : Commute f.d n.v := by
    have dd : f.d*f.d=1 := by simpa only [pow_two] using f.d_sq
    show f.d*n.v=n.v*f.d
    calc
      f.d*n.v = n.v⁻¹*f.d := by
        rw [← f.eq03_db]
        simp only [parrottCommutator, mul_inv_rev, inv_inv, sqinv f.d_sq]
        group
        simp only [mul_assoc, dd, one_mul, mul_one]
      _ = n.v*f.d := by rw [sqinv (powE hvE)]
  obtain ⟨p, hp⟩ := coset_bit h.involution
    (show Commute z (if caseTwo then f.u*n.v else f.u) from
      commE hzE (by split <;> (first | exact E.mul_mem huE hvE | exact huE))) hc.ad_coset
  obtain ⟨q, hq⟩ := coset_bit h.involution
    (show Commute z (if caseTwo then n.v else n.v*n.t) from
      commE hzE (by split <;> (first | exact hvE | exact E.mul_mem hvE htE))) hc.ac_coset
  obtain ⟨r, hr⟩ := coset_bit h.involution
    (show Commute z (if caseTwo then f.w else f.w*f.u) from
      commE hzE (by split <;> (first | exact hwE | exact E.mul_mem hwE huE))) hc.c_square_coset
  obtain ⟨s, hs⟩ := coset_bit h.involution (Commute.one_right z)
    (show (f.c*f.d)^2 / 1 ∈ zpowers z by simpa using hc.cd_square_central)
  simp only [one_mul] at hs
  obtain ⟨l, hl⟩ := coset_bit h.involution
    (show Commute z (if caseTwo then f.u*n.t else f.u*n.v) from
      commE hzE (by split <;> (first | exact E.mul_mem huE htE | exact E.mul_mem huE hvE))) hc.bc_coset
  have hkE : (if caseTwo then f.w else f.w*f.u)*(if r then z else 1) ∈ E :=
    E.mul_mem (by split <;> (first | exact hwE | exact E.mul_mem hwE huE))
      (by split <;> (first | exact hzE | exact E.one_mem))
  have hsE : (if s then z else 1) ∈ E := by split <;> (first | exact hzE | exact E.one_mem)
  have hcd := comm_of_squares f.d_sq (powE hkE) hr hs (powE hsE) (commE hkE hsE)
    (show Commute f.d ((if caseTwo then f.w else f.w*f.u)*(if r then z else 1)) from
      (by
        apply Commute.mul_right
        · split <;> (first | exact cdw | exact cdw.mul_right cdu)
        · split <;> (first | exact czd.symm | exact Commute.one_right _)))
    (show Commute f.d (if s then z else 1) from
      (by split <;> (first | exact czd.symm | exact Commute.one_right _)))
  let a' := f.a * (if p then n.t else 1)
  let r' := (if q then f.w else 1) * (if r then n.v else 1) *
    (if s != r then n.t else 1) * (if l then f.u else 1)
  let c' := f.c * r'
  have ha' : a' = f.a ∨ a' = f.a*n.t := by cases p <;> simp [a']
  have hr' : r' ∈ closure ({f.w,n.v,n.t,f.u} : Set G) := by
    apply mul_mem
    · apply mul_mem
      · apply mul_mem
        · split <;> first | exact one_mem _ | exact subset_closure (by simp)
        · split <;> first | exact one_mem _ | exact subset_closure (by simp)
      · split <;> first | exact one_mem _ | exact subset_closure (by simp)
    · split <;> first | exact one_mem _ | exact subset_closure (by simp)
  have zt := (commE hzE htE).eq
  have zv := (commE hzE hvE).eq
  have zu := (commE hzE huE).eq
  have zw := (commE hzE hwE).eq
  have tv := (commE htE hvE).eq
  have tu := (commE htE huE).eq
  have tw := (commE htE hwE).eq
  have vu := (commE hvE huE).eq
  have vw := (commE hvE hwE).eq
  have uw := (commE huE hwE).eq
  have za := cza.eq
  have ta := cta.eq
  have va := cva.eq
  have ua := cua.eq
  have zb := czb.eq
  have zc := czc.eq
  have zd := czd.eq
  have tb := f.comm_bt.symm.eq
  have vb := cbv.symm.eq
  have vd := cdv.symm.eq
  have tx := ((parrottCommutator_eq_one_iff _ _).mp f.eq01_xt).symm.eq
  have wb := ((parrottCommutator_eq_one_iff _ _).mp f.eq02_bw).symm.eq
  have wd := ((parrottCommutator_eq_one_iff _ _).mp f.eq07_dw).symm.eq
  have ud := ((parrottCommutator_eq_one_iff _ _).mp f.eq08_du).symm.eq
  have uc := ((parrottCommutator_eq_one_iff _ _).mp f.eq09_cu).symm.eq
  have wc := ((parrottCommutator_eq_one_iff _ _).mp f.eq09_cw).symm.eq
  have tc := ((parrottCommutator_eq_one_iff _ _).mp f.eq10_ct).symm.eq
  have wa := reverse ((parrottCommutator_eq_iff _ _ _).mp f.eq02_aw)
  have ub := reverse ((parrottCommutator_eq_iff _ _ _).mp f.eq02_bu)
  have bd := reverse ((parrottCommutator_eq_iff _ _ _).mp f.eq03_db)
  have td := reverse ((parrottCommutator_eq_iff _ _ _).mp f.eq03_dt)
  have ab := ((parrottCommutator_eq_iff _ _ _).mp f.eq05_ab)
  have vc := reverse ((parrottCommutator_eq_iff _ _ _).mp f.eq10_cv)
  have ad := ((parrottCommutator_eq_iff _ _ _).mp hp)
  have ac := ((parrottCommutator_eq_iff _ _ _).mp hq)
  have bc := ((parrottCommutator_eq_iff _ _ _).mp hl)
  have cd := ((parrottCommutator_eq_iff _ _ _).mp hcd)
  have zz : z*z=1 := by simpa only [pow_two] using powE hzE
  have tt : n.t*n.t=1 := by simpa only [pow_two] using powE htE
  have vv : n.v*n.v=1 := by simpa only [pow_two] using powE hvE
  have uu : f.u*f.u=1 := by simpa only [pow_two] using powE huE
  have ww : f.w*f.w=1 := by simpa only [pow_two] using powE hwE
  have dd : f.d*f.d=1 := by simpa only [pow_two] using f.d_sq
  have cc := hr
  simp only [pow_two] at cc
  have ax' : parrottCommutator a' f.x = 1 ∨ parrottCommutator a' f.x = n.t := by
    dsimp only [a']
    rcases f.ax_alternative with hax | hax
    all_goals
      have ax := (parrottCommutator_eq_iff _ _ _).mp hax
      cases p
      all_goals
        simp only [Bool.false_eq_true, ite_true, ite_false, mul_one] at ax ⊢
        simp only [parrottCommutator_eq_iff, mul_assoc]
        simp only [mul_assoc, one_mul, mul_one, true_or, or_true,
          tail tx, tx, tail ax, ax, tail tt, tt]
  refine ⟨{
    a := a'
    c := c'
    a_eq := ha'
    c_eq := ⟨r', hr', rfl⟩
    aw := ?aw
    ab := ?ab
    ax := ax'
    cu := ?cu
    cw := ?cw
    ct := ?ct
    cv := ?cv
    ad := ?ad
    ac := ?ac
    cc := ?cc
    cd := ?cd
    bc := ?bc }⟩
  all_goals dsimp only [a', c', r']
  case' aw => cases p
  case' ab => cases p
  case' cu => cases q <;> cases r <;> cases s <;> cases l
  case' cw => cases q <;> cases r <;> cases s <;> cases l
  case' ct => cases q <;> cases r <;> cases s <;> cases l
  case' cv => cases q <;> cases r <;> cases s <;> cases l
  case' ad => cases caseTwo <;> cases p
  case' ac => cases caseTwo <;> cases p <;> cases q <;> cases r <;> cases s <;> cases l
  case' cc => cases caseTwo <;> cases q <;> cases r <;> cases s <;> cases l
  case' cd => cases caseTwo <;> cases q <;> cases r <;> cases s <;> cases l
  case' bc => cases caseTwo <;> cases q <;> cases r <;> cases s <;> cases l
  all_goals
    simp only [Bool.false_eq_true, Bool.true_eq, Bool.false_bne, Bool.true_bne,
      Bool.not_false, Bool.not_true, ite_true, ite_false, mul_one, one_mul,
      mul_inv_rev, sqinv (powE hzE), sqinv (powE htE), sqinv (powE hvE),
      sqinv (powE huE), sqinv (powE hwE)] at ad ac bc cd cc wa ub bd td vc ⊢
    simp only [parrottCommutator_eq_iff, pow_two, mul_assoc]
    simp only [mul_assoc, one_mul, mul_one, true_or, or_true, tail zt, zt,
      tail zv, zv,
      tail zu, zu,
      tail zw, zw,
      tail tv, tv,
      tail tu, tu,
      tail tw, tw,
      tail vu, vu,
      tail vw, vw,
      tail uw, uw,
      tail za, za,
      tail ta, ta,
      tail va, va,
      tail ua, ua,
      tail zb, zb,
      tail zc, zc,
      tail zd, zd,
      tail tb, tb,
      tail vb, vb,
      tail vd, vd,
      tail tx, tx,
      tail wb, wb,
      tail wd, wd,
      tail ud, ud,
      tail uc, uc,
      tail wc, wc,
      tail tc, tc,
      tail wa, wa,
      tail ub, ub,
      tail bd, bd,
      tail td, td,
      tail ab, ab,
      tail vc, vc,
      tail ad, ad,
      tail ac, ac,
      tail bc, bc,
      tail cd, cd,
      tail zz, zz,
      tail tt, tt,
      tail vv, vv,
      tail uu, uu,
      tail ww, ww,
      tail dd, dd,
      tail cc, cc]

end Stellmacher.Recognition.ParrottSylowInitialData
