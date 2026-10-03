module

public import Stellmacher.Recognition.Parrott.SylowCoreSelectionData
public import Stellmacher.Recognition.Parrott.SylowInvertingInvolutionSelection

/-!
# Normalizing the first three generators in Parrott's Sylow construction

The order-four element fixed by the supplied Sylow three-subgroup already
belongs to the original core, because it lies in the derived subgroup of the
second core. It also centralizes the marked element t.

After choosing a with equations (2), (5) and the a,x alternative, and an
involution d with (3), the adjustments in (7) and (8) require no further
selection theorem. Since J′ = Z₂(J), the commutators of d with u,w lie in
⟨z⟩. If they are z^i,z^j, replace u by u t^i and w by w t^j v^i.
The relation [d,b]=v forces d to centralize v. These substitutions preserve
the three elementary bases and the outer action while killing both errors.
The conditional assembly below retains z,t,v,F,T and the chosen a,b,d,x.
The original-core involution selection discharges the choice of d, leaving
only the compatible a,b selection from the Q action.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.678–679, equations (2), (3), (5), (7), and (8). The scanned text
before (6) reads u^q=ae and [c*,u]∈⟨z⟩.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
set_option quotPrecheck false in
local notation "H" => centralizer ({z} : Set G)
set_option quotPrecheck false in
local notation "J" => (pCore 2 H).map (H).subtype
set_option quotPrecheck false in
local notation "E" => (commutator (pCore 2 H)).map ((H).subtype.comp (pCore 2 H).subtype)

/-- The supplied three-centralizer generator lies in the original core,
centralizes t, and centralizes the actual Sylow three-subgroup. -/
public theorem ParrottNormalizerFusionData.three_generator_b_properties
    (n : ParrottNormalizerFusionData e) (h : ParrottCentralizerHypotheses z) :
    n.b ∈ J ∧ Commute n.b n.t ∧
      n.b ∈ centralizer ((n.Q : Subgroup (normalizer (e.F : Set G))).map
        (normalizer (e.F : Set G)).subtype : Set G) := by
  have hb : n.b ∈ (pCore 2 (normalizer (e.F : Set G))).map
      (normalizer (e.F : Set G)).subtype ⊓
      centralizer ((n.Q : Subgroup (normalizer (e.F : Set G))).map
        (normalizer (e.F : Set G)).subtype : Set G) := by
    rw [n.core_fixed]
    exact mem_zpowers _
  refine ⟨e.sylow_subgroup_commutator_le_core h _ n.core_le_sylow
    (n.core_fixed_le_derived hb), ?_, hb.2⟩
  exact mem_centralizer_singleton_iff.mp ((n.core_eq_sylow_centralizer ▸ hb.1).2)

private theorem core_derived_pc [Finite G] (h : ParrottCentralizerHypotheses z)
    {g k : G} (hg : g ∈ J) (hk : k ∈ E) :
    Tits.parrottCommutator g k ∈ zpowers z := by
  let K := pCore 2 H
  let embed := (H).subtype.comp K.subtype
  obtain ⟨gH, hgK, rfl⟩ := hg
  obtain ⟨kK, hkK, rfl⟩ := hk
  obtain ⟨hZ, _, _, _, hUpper, _, _, _⟩ := parrott_centralizer_structure z h
  have hcomm : ⁅commutator K, (⊤ : Subgroup K)⁆ ≤ center K := by
    rw [hUpper]
    simpa only [Subgroup.upperCentralSeries_one] using
      commutator_upperCentralSeries_top_le K 1
  have hh := mem_map_of_mem embed (hcomm (commutator_mem_commutator
    ((commutator K).inv_mem hkK) (show (⟨gH, hgK⟩ : K)⁻¹ ∈ ⊤ from mem_top _)))
  rw [hZ] at hh
  have heq : embed ⁅kK⁻¹, (⟨gH, hgK⟩ : K)⁻¹⁆ =
      (Tits.parrottCommutator (gH : G) (embed kK))⁻¹ := by
    simp only [commutatorElement_def,
      Tits.parrottCommutator, mul_inv_rev, inv_inv, map_mul, map_inv]
    change (embed kK)⁻¹ * (gH : G)⁻¹ * embed kK * (gH : G) = _
    group
  rw [heq] at hh
  simpa only [inv_inv, embed, K, Subgroup.coe_subtype] using (zpowers z).inv_mem hh

private theorem pc_mul {p q s r k : G}
    (hq : Tits.parrottCommutator p q = r)
    (hs : Tits.parrottCommutator p s = k) (hc : Commute r s) :
    Tits.parrottCommutator p (q*s) = k*r := by
  calc
    _ = Tits.parrottCommutator p s * (s⁻¹ * Tits.parrottCommutator p q * s) := by
      simp only [Tits.parrottCommutator]; group
    _ = k*r := by rw [hq, hs, mul_assoc s⁻¹, hc.eq, inv_mul_cancel_left]

private theorem pc_pow {p q r : G} (hq : Tits.parrottCommutator p q = r)
    (hc : Commute r q) (i : ℕ) : Tits.parrottCommutator p (q^i) = r^i := by
  induction i with
  | zero => simp [Tits.parrottCommutator]
  | succ i ih =>
    rw [pow_succ, pc_mul ih hq (hc.pow_left i)]
    exact (pow_succ' r i).symm

private theorem closure_insert_eq (g : G) (S : Set G) :
    closure (insert g S) = zpowers g ⊔ closure S := by
  rw [← Set.singleton_union, Subgroup.closure_union, ← zpowers_eq_closure]

private theorem closure_shift (S : Set G) (u r : G) (hr : r ∈ closure S) :
    closure (insert (u*r) S) = closure (insert u S) := by
  have hS : closure S ≤ closure (insert u S) := closure_mono (Set.subset_insert _ _)
  have hS' : closure S ≤ closure (insert (u*r) S) := closure_mono (Set.subset_insert _ _)
  apply le_antisymm
  · apply (closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · rw [hx]
      exact mul_mem (subset_closure (Set.mem_insert _ _)) (hS hr)
    · exact subset_closure (Set.mem_insert_of_mem _ hx)
  · apply (closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · rw [hx]
      have hh := mul_mem (subset_closure (Set.mem_insert (u*r) S))
        (inv_mem (hS' hr))
      simpa only [mul_inv_cancel_right, SetLike.mem_coe] using hh
    · exact subset_closure (Set.mem_insert_of_mem _ hx)

private theorem basis_shift (z t v u w : G) (i j : ℕ) :
    closure ({z,t,v,u*t^i} : Set G) = closure ({z,t,v,u} : Set G) ∧
    closure ({z,t,v,u*t^i,w*(t^j*v^i)} : Set G) =
      closure ({z,t,v,u,w} : Set G) := by
  have reorder (u : G) : ({z,t,v,u} : Set G) = insert u {z,t,v} := by
    ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have reorder' (u w : G) : ({z,t,v,u,w} : Set G) = insert w {z,t,v,u} := by
    ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hu : closure ({z,t,v,u*t^i} : Set G) = closure ({z,t,v,u} : Set G) := by
    rw [reorder, reorder, closure_shift _ _ _ (pow_mem (subset_closure (by simp)) _)]
  refine ⟨hu, ?_⟩
  rw [reorder', closure_shift _ _ _ (mul_mem
    (pow_mem (subset_closure (by simp)) _) (pow_mem (subset_closure (by simp)) _)),
    closure_insert_eq, hu, ← closure_insert_eq, ← reorder']

/-- Normalize u,w after the independent choices of a and the involution d.
All three bases and the outer action are retained, with b equal to n.b.
No commutator hypothesis on d,u or d,w is needed. -/
public theorem ParrottSylowActionData.exists_three_generators_of_ab_and_involution [Finite G]
    (f : ParrottSylowActionData n) (h : ParrottCentralizerHypotheses z)
    (a d : G)
    (habasis : closure ({z, n.t, n.v, f.u, a} : Set G) = e.F)
    (hbw : Tits.parrottCommutator n.b f.w = 1)
    (haw : Tits.parrottCommutator a f.w = z)
    (hbu : Tits.parrottCommutator n.b f.u = z)
    (hab : Tits.parrottCommutator a n.b = n.t)
    (hax : Tits.parrottCommutator a f.x = 1 ∨
      Tits.parrottCommutator a f.x = n.t)
    (hdJ : d ∈ J) (hd2 : d ^ 2 = 1)
    (hdb : Tits.parrottCommutator d n.b = n.v)
    (hdt : Tits.parrottCommutator d n.t = z) :
    Nonempty (ParrottSylowThreeGeneratorData n) := by
  classical
  let : IsElementaryAbelian 2 e.F := e.elementary
  let : IsElementaryAbelian 2 (commutator (pCore 2 H)) :=
    (parrott_centralizer_structure z h).2.2.2.2.2.1
  let : IsElementaryAbelian 2 E :=
    IsElementaryAbelian.map ((H).subtype.comp (pCore 2 H).subtype)
  have hCE {g k : G} (hg : g ∈ E) (hk : k ∈ E) : Commute g k :=
    setLike_mul_comm hg hk
  have hCF {g k : G} (hg : g ∈ e.F) (hk : k ∈ e.F) : Commute g k :=
    setLike_mul_comm hg hk
  have hu : f.u ∈ E ⊓ e.F := by
    rw [← f.inf_basis]; exact subset_closure (by simp)
  have hw : f.w ∈ E := by
    rw [← f.derived_basis]; exact subset_closure (by simp)
  have ha : a ∈ e.F := by rw [← habasis]; exact subset_closure (by simp)
  have hz2 : z ^ 2 = 1 := h.involution ▸ pow_orderOf_eq_one z
  have hzsq (i : ℕ) : z^i * z^i = 1 := by
    rw [← (Commute.refl z).mul_pow, ← pow_two, hz2, one_pow]
  have hdv : Commute d n.v := by
    have hd : d⁻¹ = d := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hd2)
    have hv : n.v⁻¹ = n.v := inv_eq_of_mul_eq_one_right
      (by have hv : n.v ^ 2 = 1 := n.v_order ▸ pow_orderOf_eq_one n.v
          simpa only [pow_two] using hv)
    have heq : d * n.v = n.b⁻¹ * d * n.b := by
      rw [← hdb]
      simp only [Tits.parrottCommutator]
      group
    have heq' := congrArg Inv.inv heq
    simp only [mul_inv_rev, hd, hv, inv_inv] at heq'
    exact heq.trans (by simpa only [mul_assoc] using heq'.symm)
  have hpowers {g : G} (hg : g ∈ zpowers z) : ∃ i : ℕ, z^i = g := by
    rw [mem_zpowers_iff_mem_range_orderOf] at hg
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hg
    exact ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hpowers (core_derived_pc h hdJ hu.1)
  obtain ⟨j, hj⟩ := hpowers (core_derived_pc h hdJ hw)
  let r := n.t^j * n.v^i
  have hrE : r ∈ E := mul_mem (pow_mem n.t_mem_inf.1 _) (pow_mem n.v_mem_inf.1 _)
  have hrF : r ∈ e.F := mul_mem (pow_mem n.t_mem_inf.2 _) (pow_mem n.v_mem_inf.2 _)
  have htiE : n.t^i ∈ E := pow_mem n.t_mem_inf.1 _
  have hviE : n.v^i ∈ E := pow_mem n.v_mem_inf.1 _
  have hziE : z^i ∈ E := pow_mem e.z_mem_inf.1 _
  have hzjE : z^j ∈ E := pow_mem e.z_mem_inf.1 _
  have hbprops := n.three_generator_b_properties h
  have hbv : Commute n.b n.v := by
    rw [← n.b_sq]; exact Commute.self_pow _ _
  have hbt (k : ℕ) : Tits.parrottCommutator n.b (n.t^k) = 1 :=
    (Tits.parrottCommutator_eq_one_iff _ _).mpr (hbprops.2.1.pow_right k)
  have hbvi : Tits.parrottCommutator n.b (n.v^i) = 1 :=
    (Tits.parrottCommutator_eq_one_iff _ _).mpr (hbv.pow_right i)
  have hbr : Tits.parrottCommutator n.b r = 1 := by
    exact (pc_mul (hbt j) hbvi (Commute.one_left _)).trans (one_mul _)
  have har : Tits.parrottCommutator a r = 1 :=
    (Tits.parrottCommutator_eq_one_iff _ _).mpr (hCF ha hrF)
  have hxt (k : ℕ) : Tits.parrottCommutator f.x (n.t^k) = 1 := by
    simpa only [one_pow] using pc_pow f.eq01_xt (Commute.one_left _) k
  have hxvi : Tits.parrottCommutator f.x (n.v^i) = n.t^i :=
    pc_pow f.eq01_xv (hCE n.t_mem_inf.1 n.v_mem_inf.1) i
  have hxr : Tits.parrottCommutator f.x r = n.t^i := by
    exact (pc_mul (hxt j) hxvi (Commute.one_left _)).trans (mul_one _)
  have hdtpow (k : ℕ) : Tits.parrottCommutator d (n.t^k) = z^k :=
    pc_pow hdt (hCE e.z_mem_inf.1 n.t_mem_inf.1) k
  have hdvi : Tits.parrottCommutator d (n.v^i) = 1 :=
    (Tits.parrottCommutator_eq_one_iff _ _).mpr (hdv.pow_right i)
  have hdr : Tits.parrottCommutator d r = z^j := by
    exact (pc_mul (hdtpow j) hdvi (hCE hzjE hviE)).trans (one_mul _)
  have hbases := basis_shift z n.t n.v f.u f.w i j
  have hebasis : closure ({z,n.t,n.v,f.u*n.t^i,a} : Set G) = e.F := by
    have reorder (u : G) : ({z,n.t,n.v,u,a} : Set G) = insert a {z,n.t,n.v,u} := by
      ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [reorder, closure_insert_eq, hbases.1, ← closure_insert_eq, ← reorder, habasis]
  refine ⟨{
    u := f.u * n.t^i
    w := f.w * r
    x := f.x
    inf_basis := hbases.1.trans f.inf_basis
    derived_basis := hbases.2.trans f.derived_basis
    sylow_eq := f.sylow_eq
    eq01_x := f.eq01_x
    eq01_xt := f.eq01_xt
    eq01_xv := f.eq01_xv
    eq01_xu := ?_
    eq01_xw := ?_
    a := a
    b := n.b
    d := d
    elementary_basis := hebasis
    b_mem_core := hbprops.1
    d_mem_core := hdJ
    comm_bt := hbprops.2.1
    d_sq := hd2
    eq02_bw := ?_
    eq02_aw := ?_
    eq02_bu := ?_
    eq03_db := hdb
    eq03_dt := hdt
    eq03_b := n.b_sq
    eq05_ab := hab
    eq07_dw := ?_
    eq08_du := ?_
    ax_alternative := hax }⟩
  · exact (pc_mul f.eq01_xu (hxt i) (hCE n.v_mem_inf.1 htiE)).trans (one_mul _)
  · exact (pc_mul f.eq01_xw hxr (hCE hu.1 hrE)).trans (hCE htiE hu.1).eq
  · exact (pc_mul hbw hbr (Commute.one_left _)).trans (one_mul _)
  · exact (pc_mul haw har (hCE e.z_mem_inf.1 hrE)).trans (one_mul _)
  · exact (pc_mul hbu (hbt i) (hCE e.z_mem_inf.1 htiE)).trans (one_mul _)
  · exact (pc_mul hj.symm hdr (hCE hzjE hrE)).trans (hzsq j)
  · exact (pc_mul hi.symm (hdtpow i) (hCE hziE htiE)).trans (hzsq i)

/-- The original-core involution selection reduces the three-generator
construction to the compatible a,b relations from the Q action. -/
public theorem ParrottSylowActionData.exists_three_generators_of_ab_selection
    [Finite G] [IsSimpleGroup G]
    (f : ParrottSylowActionData n) (hns : ¬ Group.IsSolvable G)
    (hN : IsNTwoGroup G) (h : ParrottCentralizerHypotheses z)
    (a : G)
    (habasis : closure ({z, n.t, n.v, f.u, a} : Set G) = e.F)
    (hbw : Tits.parrottCommutator n.b f.w = 1)
    (haw : Tits.parrottCommutator a f.w = z)
    (hbu : Tits.parrottCommutator n.b f.u = z)
    (hab : Tits.parrottCommutator a n.b = n.t)
    (hax : Tits.parrottCommutator a f.x = 1 ∨
      Tits.parrottCommutator a f.x = n.t) :
    Nonempty (ParrottSylowThreeGeneratorData n) := by
  obtain ⟨d, hdJ, hd2, hdb, hdt⟩ :=
    n.exists_three_generator_involution hns hN h
  exact f.exists_three_generators_of_ab_and_involution h a d
    habasis hbw haw hbu hab hax hdJ hd2 hdb hdt

end Stellmacher.Recognition
