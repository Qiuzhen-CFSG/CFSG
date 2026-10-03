module

public import Stellmacher.Recognition.Parrott.SylowCoreCovarianceData
public import Theory.ElementaryAbelian.BinaryExpansion

/-!
# Correlated core cosets from covariance

Expand the derived-core elements in the elementary generators z,t,v,u,w.
The actions of c and d detect the coefficients in the iterate identity for
p = [a,d], leaving p = u v^β modulo ⟨z⟩. Commutation of k = c² with c and d
first removes its v and t coefficients. Testing its covariance under b and c
then gives k = wu for β = false, and k = w for β = true.
The other two covariance identities give [a,c] and [b,c] with this same β.

All coefficient calculations take place in the actual elementary derived
subgroup. Binary spanning suffices; independence and a fusion enumeration
are unnecessary. Covariance is an explicit hypothesis of the public theorem.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.678–679, equations (11)–(15).
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSylowInitialData
private theorem fixed_of_mem {A : Type*} [Group A] (F : A →* A) {z y : A}
    (hf : F z = z) (hy : y ∈ zpowers z) : F y = y := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
  simp only [map_zpow, hf]

set_option linter.unusedSimpArgs false
set_option maxRecDepth 2000
/- The noncentral coefficients of [a,d] are detected by c and d. -/
private theorem ad_coefficient_shape {A : Type*} [CommGroup A]
    (z t v u w p : A) (P C D : A →* A)
    (hs : ∀ a : A, a*a=1) (hz : z ≠ 1)
    (hspan : ∃ i j k l m : Bool,
      p = (if i then z else 1)*(if j then t else 1)*(if k then v else 1)*
        (if l then u else 1)*(if m then w else 1))
    (Pz : P z=z) (Pt : P t=t) (Pv : P v=v*t) (Pu : P u=u*v) (Pw : P w=w*u)
    (Cz : C z=z) (_Ct : C t=t) (Cv : C v=v*z) (_Cu : C u=u) (_Cw : C w=w)
    (Dz : D z=z) (Dt : D t=t*z) (Dv : D v=v) (Du : D u=u) (_Dw : D w=w)
    (hd : D p=p) (hi : P (P p)/(p*t) ∈ zpowers z) :
    ∃ β α : Bool, p=(if α then z else 1)*(if β then u*v else u) := by
  have inv (a : A) : a⁻¹=a := inv_eq_of_mul_eq_one_right (hs a)
  have cancel (a b : A) : a*(a*b)=b := by rw [← mul_assoc, hs, one_mul]
  have hic := fixed_of_mem C Cz hi
  have hid := fixed_of_mem D Dz hi
  obtain ⟨i,j,k,l,m,rfl⟩ := hspan
  cases i <;> cases j <;> cases k <;> cases l <;> cases m
  all_goals
    simp only [Bool.false_eq_true, ite_false, ite_true, one_mul, mul_one] at *
    simp [map_mul, map_div, Pz,Pt,Pv,Pu,Pw,Cz,_Ct,Cv,_Cu,_Cw,Dz,Dt,Dv,Du,_Dw,
      div_eq_mul_inv, inv, mul_assoc, mul_left_comm, mul_comm, hs, cancel] at hd hic hid
  all_goals solve | contradiction | (refine ⟨false,false,?_⟩; simp) | (refine ⟨false,true,?_⟩; simp) |
    (refine ⟨true,false,?_⟩; simp [mul_assoc, mul_left_comm, mul_comm]) |
    (refine ⟨true,true,?_⟩; simp [mul_assoc, mul_left_comm, mul_comm])

/- Eliminate the t and v coefficients before testing square covariance. -/
private theorem square_coefficient_shape {A : Type*} [CommGroup A]
    (z t v u w k : A) (P B C D : A →* A)
    (hs : ∀ a : A, a*a=1) (hz : z ≠ 1) (β α : Bool)
    (hspan : ∃ i j l m o : Bool,
      k = (if i then z else 1)*(if j then t else 1)*(if l then v else 1)*
        (if m then u else 1)*(if o then w else 1))
    (Pz : P z=z) (_Pt : P t=t) (_Pv : P v=v*t) (Pu : P u=u*v) (Pw : P w=w*u)
    (Bz : B z=z) (_Bt : B t=t) (_Bv : B v=v) (Bu : B u=u*z) (_Bw : B w=w)
    (Cz : C z=z) (_Ct : C t=t) (Cv : C v=v*z) (_Cu : C u=u) (_Cw : C w=w)
    (Dz : D z=z) (Dt : D t=t*z) (Dv : D v=v) (Du : D u=u) (_Dw : D w=w)
    (hc : C k=k) (hd : D k=k)
    (hi : P k/(k*v*((if α then z else 1)*(if β then u*v else u))) ∈ zpowers z) :
    ∃ γ : Bool, k=(if γ then z else 1)*(if β then w else w*u) := by
  have inv (a : A) : a⁻¹=a := inv_eq_of_mul_eq_one_right (hs a)
  have cancel (a b : A) : a*(a*b)=b := by rw [← mul_assoc, hs, one_mul]
  have hib := fixed_of_mem B Bz hi
  have hic := fixed_of_mem C Cz hi
  obtain ⟨i,j,l,m,o,rfl⟩ := hspan
  have hj : j=false := by
    cases j
    · rfl
    · exfalso
      cases i <;> cases l <;> cases m <;> cases o
      all_goals
        simp [map_mul,Dz,Dt,Dv,Du,_Dw, mul_assoc, mul_left_comm, mul_comm] at hd
        contradiction
  subst j
  have hl : l=false := by
    cases l
    · rfl
    · exfalso
      cases i <;> cases m <;> cases o
      all_goals
        simp [map_mul,Cz,Cv,_Cu,_Cw, mul_assoc, mul_left_comm, mul_comm] at hc
        contradiction
  subst l
  cases β <;> cases α <;> cases i <;> cases m <;> cases o
  all_goals
    simp only [Bool.false_eq_true, ite_false, ite_true, one_mul, mul_one] at *
    simp [map_mul, Pz,_Pt,_Pv,Pu,Pw,Bz,_Bt,_Bv,Bu,_Bw,Cz,_Ct,Cv,_Cu,_Cw,Dz,Dt,Dv,Du,_Dw,
      div_eq_mul_inv, inv, mul_assoc, mul_left_comm, mul_comm, hs, cancel] at hc hd hib hic
  all_goals solve | contradiction | (refine ⟨false,?_⟩; simp [mul_assoc, mul_left_comm, mul_comm]) |
    (refine ⟨true,?_⟩; simp [mul_assoc, mul_left_comm, mul_comm])

private theorem residues_of_shapes {A : Type*} [CommGroup A]
    (Z T V U W p k : A) (P : A →* A) (hs : ∀ s : A, s*s=1) (β α γ : Bool)
    (Pz : P Z=Z) (Pu : P U=U*V) (Pv : P V=V*T)
    (hp : p=(if α then Z else 1)*(if β then U*V else U))
    (hk : k=(if γ then Z else 1)*(if β then W else W*U)) :
    p/(if β then U*V else U) ∈ zpowers Z ∧
    k/(if β then W else W*U) ∈ zpowers Z ∧
    P p/(if β then U*T else U*V) ∈ zpowers Z ∧
    (P p*p*T)/(if β then V else V*T) ∈ zpowers Z := by
  have inv (s : A) : s⁻¹=s := inv_eq_of_mul_eq_one_right (hs s)
  have cancel (s r : A) : s*(s*r)=r := by rw [← mul_assoc, hs, one_mul]
  have zm : Z ∈ zpowers Z := mem_zpowers Z
  have pm : p/(if β then U*V else U) ∈ zpowers Z := by
    rw [hp]
    cases α <;> cases β <;> simp [zm]
  have km : k/(if β then W else W*U) ∈ zpowers Z := by
    rw [hk]
    cases γ <;> cases β <;> simp [zm]
  have rpm : P p/(if β then U*T else U*V) ∈ zpowers Z := by
    rw [hp]
    cases α <;> cases β <;>
      simp [map_mul, Pz,Pu,Pv, div_eq_mul_inv, inv, mul_assoc, mul_left_comm,
        mul_comm, hs, cancel, zm]
  have qpm : (P p*p*T)/(if β then V else V*T) ∈ zpowers Z := by
    rw [hp]
    cases α <;> cases β <;>
      simp [map_mul, Pz,Pu,Pv, div_eq_mul_inv, inv, mul_assoc, mul_left_comm,
        mul_comm, hs, cancel, zm]
  exact ⟨pm,km,rpm,qpm⟩

open scoped IsMulCommutative
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
set_option quotPrecheck false in
local notation "H" => centralizer ({z} : Set G)
set_option quotPrecheck false in
local notation "J" => (pCore 2 H).map (H).subtype
set_option quotPrecheck false in
local notation "E" => (commutator (pCore 2 H)).map ((H).subtype.comp (pCore 2 H).subtype)

private theorem conj_comm {g k : G} (h : Commute g k) :
    (MulAut.conj g⁻¹) k = k := by
  simp only [MulAut.conj_apply, inv_inv]
  rw [mul_assoc, h.symm.eq, inv_mul_cancel_left]

private theorem conj_pc {g k r : G}
    (hr : Tits.parrottCommutator g k = r) (hr2 : r^2=1) :
    (MulAut.conj g⁻¹) k=k*r := by
  have hs := (Tits.parrottCommutator_eq_iff _ _ _).mp hr
  have hrr : r*r=1 := by simpa only [pow_two] using hr2
  have heq := congrArg (fun p : G => g⁻¹*p*r) hs
  simpa only [MulAut.conj_apply, inv_inv, mul_assoc,
    inv_mul_cancel_left, hrr, mul_one] using heq.symm

/-- The four covariance identities force one Boolean choice for all five
core-coset alternatives, retaining the supplied initial coordinates. -/
public theorem exists_core_coset_alternatives_of_covariance [Finite G]
    (f : ParrottSylowInitialData n) (h : ParrottCentralizerHypotheses z)
    (hc : f.CoreCovariance) : ∃ caseTwo : Bool, f.CoreCosetAlternatives caseTwo := by
  let : IsElementaryAbelian 2 (commutator (pCore 2 H)) :=
    (parrott_centralizer_structure z h).2.2.2.2.2.1
  let : IsElementaryAbelian 2 E :=
    IsElementaryAbelian.map ((H).subtype.comp (pCore 2 H).subtype)
  let Z : E := ⟨z, f.basis_mem_derived _ (by simp)⟩
  let T : E := ⟨n.t, f.basis_mem_derived _ (by simp)⟩
  let V : E := ⟨n.v, f.basis_mem_derived _ (by simp)⟩
  let U : E := ⟨f.u, f.basis_mem_derived _ (by simp)⟩
  let W : E := ⟨f.w, f.basis_mem_derived _ (by simp)⟩
  have hs (s : E) : s*s=1 := by
    apply Subtype.ext
    exact (pow_two (s:G)).symm.trans (derived_square_one h s.property)
  have hz : Z ≠ 1 := by
    intro hh
    have hz1 : z=1 := congrArg Subtype.val hh
    have ho := h.involution
    rw [hz1, orderOf_one] at ho
    norm_num at ho
  have hspan (s : E) : ∃ i j k l m : Bool,
      s = (if i then Z else 1)*(if j then T else 1)*(if k then V else 1)*
        (if l then U else 1)*(if m then W else 1) := by
    let basis : Fin 5 → E := ![Z,T,V,U,W]
    have hcl : closure (Set.range basis) = ⊤ := by
      apply Subgroup.map_injective (E).subtype_injective
      rw [MonoidHom.map_closure]
      have himg : (E).subtype '' Set.range basis = ({z,n.t,n.v,f.u,f.w} : Set G) := by
        simp [basis, Matrix.range_cons, Set.image_insert_eq, Z,T,V,U,W]
        ext s; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rw [himg, f.derived_basis]
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    obtain ⟨b,hb⟩ := Theory.GroupTheory.exists_bool_prod_of_mem_closure_range basis
      (fun i => hs (basis i)) (show s ∈ closure (Set.range basis) by rw [hcl]; trivial)
    refine ⟨b 0,b 1,b 2,b 3,b 4, ?_⟩
    simpa [Fin.prod_univ_succ, basis, mul_assoc] using hb
  let phi : G →* G := (MulAut.conj f.x⁻¹).toMonoidHom
  have hzs : z^2=1 := h.involution ▸ pow_orderOf_eq_one z
  have hts : n.t^2=1 := n.t_order ▸ pow_orderOf_eq_one n.t
  have hvs : n.v^2=1 := n.v_order ▸ pow_orderOf_eq_one n.v
  have hus : f.u^2=1 := derived_square_one h U.property
  have hxH : f.x ∈ H := e.sylow_le_centralizer
    (f.sylow_eq.symm ▸ mem_sup_left (mem_zpowers f.x))
  have phiz : phi z=z := conj_comm (mem_centralizer_singleton_iff.mp hxH)
  have phit : phi n.t=n.t := conj_comm ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq01_xt)
  have phiv : phi n.v=n.v*n.t := conj_pc f.eq01_xv hts
  have phiu : phi f.u=f.u*n.v := conj_pc f.eq01_xu hvs
  have phiw : phi f.w=f.w*f.u := conj_pc f.eq01_xw hus
  have hphi : E ≤ (E).comap phi := by
    conv_lhs => rw [← f.derived_basis]
    apply (closure_le _).mpr
    intro s hs
    change phi s ∈ E
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl|rfl|rfl|rfl|rfl
    · rw [phiz]; exact Z.property
    · rw [phit]; exact T.property
    · rw [phiv]; exact mul_mem V.property T.property
    · rw [phiu]; exact mul_mem U.property V.property
    · rw [phiw]; exact mul_mem W.property U.property
  let P : E →* E := (phi.comp (E).subtype).codRestrict E (fun s => hphi s.property)
  have Pval (s : E) : (P s : G) = phi s := rfl
  have Pz : P Z=Z := Subtype.ext phiz
  have Pt : P T=T := Subtype.ext phit
  have Pv : P V=V*T := Subtype.ext phiv
  have Pu : P U=U*V := Subtype.ext phiu
  have Pw : P W=W*U := Subtype.ext phiw
  let actors : Fin 4 → G := ![f.a,f.b,f.c,f.d]
  have actors_mem (i : Fin 4) : actors i ∈ J := by
    apply f.generators_mem_core
    fin_cases i <;> simp [actors]
  let action (i : Fin 4) : E →* E :=
    (((MulAut.conj (actors i)⁻¹).toMonoidHom).comp (E).subtype).codRestrict E
      (fun s => by simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        Subgroup.subtype_apply, MulAut.conj_apply, inv_inv] using
        derived_conjugate_mem (actors_mem i) s.property)
  have action_z (i : Fin 4) : action i Z=Z := by
    apply Subtype.ext
    exact conj_comm (f.commute_z_of_mem_core (actors_mem i)).symm
  have action_entry (i j : Fin 4) :
      action i (![T,V,U,W] j) = (![T,V,U,W] j)*Z^(if i.val+j.val=3 then 1 else 0) := by
    apply Subtype.ext
    have he := f.core_derived_pairing_entries i j
    have hh := conj_pc he (show (z^(if i.val+j.val=3 then 1 else 0))^2=1 by
      split_ifs <;> simp [hzs])
    convert hh using 1 <;> fin_cases j <;> rfl
  let p : E := ⟨Tits.parrottCommutator f.a f.d, core_commutator_mem_derived
    (f.generators_mem_core _ (by simp)) (f.generators_mem_core _ (by simp))⟩
  let k : E := ⟨f.c^2, core_square_mem_derived h (f.generators_mem_core _ (by simp))⟩
  have lift_center {s : E} (hh : (s:G) ∈ zpowers z) : s ∈ zpowers Z := by
    obtain ⟨i,hi⟩ := mem_zpowers_iff.mp hh
    exact mem_zpowers_iff.mpr ⟨i, Subtype.ext hi⟩
  have ad_iterate : P (P p)/(p*T) ∈ zpowers Z := lift_center hc.ad_iterate
  have square_transport : P k/(k*V*p) ∈ zpowers Z := lift_center hc.square_transport
  have dp : action 3 p=p := Subtype.ext (conj_comm (f.commute_d_ad h))
  have ck : action 2 k=k := Subtype.ext (conj_comm (Commute.self_pow f.c 2))
  have dk : action 3 k=k := Subtype.ext (conj_comm (f.commute_d_c_square h))
  have aT (i : Fin 4) := action_entry i 0
  have aV (i : Fin 4) := action_entry i 1
  have aU (i : Fin 4) := action_entry i 2
  have aW (i : Fin 4) := action_entry i 3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three] at aT aV aU aW
  obtain ⟨β,α,hp⟩ := ad_coefficient_shape Z T V U W p P (action 2) (action 3) hs hz (hspan p)
    Pz Pt Pv Pu Pw (action_z 2) (by simpa using aT 2) (by simpa using aV 2)
    (by simpa using aU 2) (by simpa using aW 2) (action_z 3)
    (by simpa using aT 3) (by simpa using aV 3) (by simpa using aU 3)
    (by simpa using aW 3) dp ad_iterate
  rw [hp] at square_transport
  obtain ⟨γ,hk⟩ := square_coefficient_shape Z T V U W k P (action 1) (action 2) (action 3) hs hz β α
    (hspan k) Pz Pt Pv Pu Pw (action_z 1) (by simpa using aT 1) (by simpa using aV 1)
    (by simpa using aU 1) (by simpa using aW 1)
    (action_z 2) (by simpa using aT 2) (by simpa using aV 2)
    (by simpa using aU 2) (by simpa using aW 2) (action_z 3)
    (by simpa using aT 3) (by simpa using aV 3) (by simpa using aU 3)
    (by simpa using aW 3) ck dk square_transport
  obtain ⟨pm,km,rpm,qpm⟩ := residues_of_shapes Z T V U W p k P hs β α γ Pz Pu Pv hp hk
  have down {s : E} (hm : s ∈ zpowers Z) : (s:G) ∈ zpowers z := by
    obtain ⟨i,hi⟩ := mem_zpowers_iff.mp hm
    exact mem_zpowers_iff.mpr ⟨i, congrArg Subtype.val hi⟩
  have chain {g r s : G} (hgr : g/r ∈ zpowers z) (hrs : r/s ∈ zpowers z) :
      g/s ∈ zpowers z := by
    simpa only [div_mul_div_cancel] using (zpowers z).mul_mem hgr hrs
  refine ⟨β, ?_⟩
  constructor
  · simpa only [Subgroup.coe_div, Subgroup.coe_mul, apply_ite Subtype.val,
      Z,T,V,U,W,p] using down pm
  · apply chain hc.ac_transport
    simpa only [Subgroup.coe_div, Subgroup.coe_mul, apply_ite Subtype.val,
      Pval, Z,T,V,U,W,p,phi, MulEquiv.coe_toMonoidHom] using down qpm
  · simpa only [Subgroup.coe_div, Subgroup.coe_mul, apply_ite Subtype.val,
      Z,T,V,U,W,k] using down km
  · exact f.cd_square_central h
  · apply chain hc.bc_transport
    simpa only [Subgroup.coe_div, Subgroup.coe_mul, apply_ite Subtype.val,
      Pval, Z,T,V,U,W,p,phi, MulEquiv.coe_toMonoidHom] using down rpm
end Stellmacher.Recognition.ParrottSylowInitialData
