module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.LineStabilizers

/-!
# Root actions on the original radical coordinates

A shear of the marked source three-space sends z to zr and fixes r,s.
On the radical quotient it fixes the zr- and rs-pair sections and sends
v in the zs-section to v times its image under the swap of z,r. The proof
uses the full line-stabilizer triviality: the swap fixes the sheared
section pointwise, and the involution identity forces the diagonal map.

Three copies of the original multiplicity space therefore give coordinates
in which this shear acts by (u,v,w) ↦ (u,v,vw). The marked swaps of z,r and
r,s act by (u,v,w) ↦ (u,w,v) and (u,v,w) ↦ (v,u,w), respectively. The same
S/R action is diagonal in these very coordinates. All automorphisms use
the original K/R marking and the literal quotient action on R/Z(R).

The shear itself and its K-lift are constructed, so the final exports do
not assume a root element or a coordinate system. These are the explicit
root-coordinate identities needed for the dual-natural tensor factor.
An equivariant tensor identification for the whole K/R and the natural
L₂(4) identification of the four-space remain further obligations.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*,
Invent. Math. 105 (1991), (4.4), pp.597–598, DOI 10.1007/BF01232280.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition

private theorem shear_identity {V : Type*} [Group V] [IsElementaryAbelian 2 V]
    (A B : Subgroup V) (hd : Disjoint A B) (a p : MulAut V)
    (hp : ∀ v, p (p v) = v) (ha : ∀ v, a (a v) = v)
    (hpA : ∀ v ∈ A, p v ∈ B) (hpB : ∀ v ∈ B, p v ∈ A)
    (haB : ∀ v ∈ B, a v = v) (hpa : ∀ v ∈ A, p (a v) = a v)
    (haAB : ∀ v ∈ A, a v ∈ A ⊔ B) (v : V) (hv : v ∈ A) :
    a v = v * p v := by
  obtain ⟨x,hx,y,hy,hxy⟩ := Subgroup.mem_sup.mp (haAB v hv)
  have hswap : p y * p x = x*y := by
    rw [mul_comm (p y),←map_mul,hxy,hpa v hv]
  have he : ((⟨p y,hpB y hy⟩ : A),(⟨p x,hpA x hx⟩ : B)) = (⟨x,hx⟩,⟨y,hy⟩) :=
    mul_injective_of_disjoint hd hswap
  have hypx : y = p x := (congrArg (fun ab : A × B => (ab.2 : V)) he).symm
  rw [hypx] at hxy
  have hvexpr : v = a x * p x := by
    rw [←ha v,←hxy,map_mul,haB _ (hpA x hx)]
  have hpv : p v = a x * x := by rw [hvexpr,map_mul,hpa x hx,hp]
  have hsq : a x * a x = 1 := by
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) (a x)
  calc
    a v = x*p x := hxy.symm
    _ = (a x*p x)*(a x*x) := by
      calc
        x*p x = (a x*a x)*(x*p x) := by rw [hsq,one_mul]
        _ = (a x*p x)*(a x*x) := by ac_rfl
    _ = v * p v := by rw [hpv,hvexpr]

namespace ThreeSpaceData
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : CubicAutomorphismQuotient (centralizer z ⧸ core z)}
  {X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)}
variable (d : ThreeSpaceData z e X)
local instance shearSpaceElementary : IsElementaryAbelian 2 d.space := d.elementary

/-- The original three marked points generate the same three-space. -/
theorem markedPoint_generates : closure (Set.range d.markedPoint) = ⊤ := by
  apply map_injective d.space.subtype_injective
  rw [MonoidHom.map_closure,←MonoidHom.range_eq_map,range_subtype]
  have he : d.space.subtype '' Set.range d.markedPoint = {z,d.r,d.s} := by
    ext x
    simp [markedPoint,Set.mem_range,Fin.exists_fin_succ,eq_comm]
  rw [he]
  exact d.generated.symm

/-- An automorphism of the source three-space is determined by its three markers. -/
theorem aut_ext_marked {a b : MulAut d.space}
    (he : ∀ i : Fin 3, a (d.markedPoint i) = b (d.markedPoint i)) : a = b := by
  have hh : a.toMonoidHom = b.toMonoidHom := MonoidHom.eq_of_eqOn_dense
    d.markedPoint_generates (by rintro _ ⟨i,rfl⟩; exact he i)
  exact MulEquiv.ext (fun v => congrArg (fun f : d.space →* d.space => f v) hh)

/-- A literal subgroup-image equality gives membership in the line stabilizer. -/
theorem mem_lineStabilizer_of_map_eq (t u : d.space) (a : MulAut d.space)
    (he : (d.pointLine t u).map a.toMonoidHom = d.pointLine t u) :
    a ∈ d.lineStabilizer t u := by
  intro v
  calc
    a v ∈ d.pointLine t u ↔ a v ∈ (d.pointLine t u).map a.toMonoidHom := by rw [he]
    _ ↔ v ∈ d.pointLine t u := mem_map_iff_mem a.injective

private theorem pointLine_map (a : MulAut d.space) (t u : d.space) :
    (d.pointLine t u).map a.toMonoidHom = d.pointLine (a t) (a u) := by
  simp only [pointLine,MonoidHom.map_closure,Set.image_insert_eq,Set.image_singleton,
    MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe]

private theorem pointLine_mul_left (t u : d.space) :
    d.pointLine (t*u) u = d.pointLine t u := by
  have ht : t ∈ d.pointLine t u := subset_closure (by simp)
  have hu : u ∈ d.pointLine t u := subset_closure (by simp)
  have htu : t*u ∈ d.pointLine (t*u) u := subset_closure (by simp)
  have hu' : u ∈ d.pointLine (t*u) u := subset_closure (by simp)
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro v hv
    rcases hv with rfl | rfl
    · exact (d.pointLine t u).mul_mem ht hu
    · exact hu
  · apply (Subgroup.closure_le _).mpr
    intro v hv
    rcases hv with hv | hv
    · rw [hv]
      change t ∈ d.pointLine (t*u) u
      simpa only [mul_inv_cancel_right] using
        (d.pointLine (t*u) u).mul_mem htu ((d.pointLine (t*u) u).inv_mem hu')
    · exact hv ▸ hu'

private theorem marked_nonidentity (h : IsTypeJ4 z) (i : Fin 3) :
    (d.markedPoint i : G) ≠ 1 := by
  have hz : z ≠ 1 := by intro he; have hi := h.involution; simp [he] at hi
  fin_cases i
  · exact hz
  · intro he; exact hz (isConj_one_left.mp (he ▸ d.r_conj))
  · intro he; exact hz (isConj_one_left.mp (he ▸ d.s_conj))

private theorem marked_injective : Function.Injective d.markedPoint := by
  intro i j he
  have hh := d.markedCoordinates.injective
    ((d.markedCoordinates_single i).trans
      ((congrArg Additive.ofMul he).trans (d.markedCoordinates_single j).symm))
  by_contra hij
  have hv := congrFun hh i
  simp [hij] at hv

private theorem coreSection_s_pair_sup (h : IsTypeJ4 z) :
    (d.coreSection z ⊓ d.coreSection d.s) ⊔ (d.coreSection d.r ⊓ d.coreSection d.s) =
      d.coreSection d.s := by
  let := d.R_center_quotient_elementary h
  apply le_antisymm (sup_le inf_le_right inf_le_right)
  intro v hv
  obtain ⟨f,hf⟩ := d.exists_coreSection_product h
  obtain ⟨⟨x,y,w⟩,rfl⟩ := f.surjective v
  rw [hf] at hv ⊢
  have hx : (x : d.R ⧸ center d.R) ∈ d.coreSection d.s := by
    have hh := (d.coreSection d.s).mul_mem hv
      ((d.coreSection d.s).inv_mem ((d.coreSection d.s).mul_mem y.property.2 w.property.2))
    simpa only [mul_inv_cancel_right] using hh
  have hx1 : (x : d.R ⧸ center d.R) = 1 :=
    mem_bot.mp (d.coreSection_triple_inf h ▸ (show x.val ∈
      d.coreSection z ⊓ d.coreSection d.r ⊓ d.coreSection d.s from ⟨x.property,hx⟩))
  rw [hx1,one_mul]
  exact mul_mem_sup y.property w.property

/-- The point-core line geometry forces the radical shear formula. -/
theorem radical_shear_of_marked_action (h : IsTypeJ4 z) (a p : MulAut d.space)
    (ha0 : a (d.markedPoint 0) = d.markedPoint 0 * d.markedPoint 1)
    (ha1 : a (d.markedPoint 1) = d.markedPoint 1)
    (ha2 : a (d.markedPoint 2) = d.markedPoint 2)
    (hp0 : p (d.markedPoint 0) = d.markedPoint 1)
    (hp1 : p (d.markedPoint 1) = d.markedPoint 0)
    (hp2 : p (d.markedPoint 2) = d.markedPoint 2)
    (v : d.R ⧸ center d.R) (hv : v ∈ d.coreSection z ⊓ d.coreSection d.s) :
    d.linearRadicalAction h a v = v * d.linearRadicalAction h p v := by
  let := d.R_center_quotient_elementary h
  let A := d.coreSection z ⊓ d.coreSection d.s
  let B := d.coreSection d.r ⊓ d.coreSection d.s
  let C := d.coreSection (z*d.r) ⊓ d.coreSection d.s
  let a' := d.linearRadicalAction h a
  let p' := d.linearRadicalAction h p
  have hpw (t : d.space) : t*t=1 := by
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 d.space) t
  have hpa : p*p=1 := by
    apply d.aut_ext_marked
    intro i
    fin_cases i
    · change p (p (d.markedPoint 0)) = d.markedPoint 0
      rw [hp0,hp1]
    · change p (p (d.markedPoint 1)) = d.markedPoint 1
      rw [hp1,hp0]
    · change p (p (d.markedPoint 2)) = d.markedPoint 2
      rw [hp2,hp2]
  have haa : a*a=1 := by
    apply d.aut_ext_marked
    intro i
    fin_cases i
    · change a (a (d.markedPoint 0)) = d.markedPoint 0
      rw [ha0,map_mul,ha0,ha1,mul_assoc,hpw,mul_one]
    · change a (a (d.markedPoint 1)) = d.markedPoint 1
      rw [ha1,ha1]
    · change a (a (d.markedPoint 2)) = d.markedPoint 2
      rw [ha2,ha2]
  have invol (b : MulAut d.space) (hb : b*b=1) (w : d.R ⧸ center d.R) :
      d.linearRadicalAction h b (d.linearRadicalAction h b w) = w := by
    rw [←MulAut.mul_apply,←map_mul,hb,map_one]
    rfl
  have hm (b : MulAut d.space) (i j : Fin 3) :
      (d.coreSection (d.markedPoint i).val ⊓ d.coreSection (d.markedPoint j).val).map
        (d.linearRadicalAction h b).toMonoidHom =
        d.coreSection (b (d.markedPoint i)).val ⊓ d.coreSection (b (d.markedPoint j)).val := by
    rw [map_inf _ _ _ (d.linearRadicalAction h b).injective,
      d.linearRadicalAction_conjugate_section,d.linearRadicalAction_conjugate_section]
  have hpA : ∀ w ∈ A, p' w ∈ B := by
    intro w hw
    have hh := mem_map_of_mem (d.linearRadicalAction h p).toMonoidHom hw
    change _ ∈ (d.coreSection (d.markedPoint 0).val ⊓ d.coreSection (d.markedPoint 2).val).map _ at hh
    rw [hm,hp0,hp2] at hh
    exact hh
  have hpB : ∀ w ∈ B, p' w ∈ A := by
    intro w hw
    have hh := mem_map_of_mem (d.linearRadicalAction h p).toMonoidHom hw
    change _ ∈ (d.coreSection (d.markedPoint 1).val ⊓ d.coreSection (d.markedPoint 2).val).map _ at hh
    rw [hm,hp1,hp2] at hh
    exact hh
  have haC : ∀ w ∈ A, a' w ∈ C := by
    intro w hw
    have hh := mem_map_of_mem (d.linearRadicalAction h a).toMonoidHom hw
    change _ ∈ (d.coreSection (d.markedPoint 0).val ⊓ d.coreSection (d.markedPoint 2).val).map _ at hh
    rw [hm,ha0,ha2] at hh
    exact hh
  have hfixB : ∀ w ∈ B, a' w = w := by
    apply d.lineStabilizer_fixes_pairSection h (d.markedPoint 1) (d.markedPoint 2)
      (d.marked_nonidentity h 1) (d.marked_nonidentity h 2)
      (fun he => by have := d.marked_injective he; contradiction) a
    apply d.mem_lineStabilizer_of_map_eq
    rw [d.pointLine_map,ha1,ha2]
  have h01 : ((d.markedPoint 0 * d.markedPoint 1 : d.space) : G) ≠ 1 := by
    intro he
    have hh : d.markedPoint 0 * d.markedPoint 1 = 1 := Subtype.ext he
    have heq : d.markedPoint 0 = d.markedPoint 1 :=
      (mul_left_inj (d.markedPoint 1)).mp (hh.trans (hpw _).symm)
    have := d.marked_injective heq
    contradiction
  have h012 : d.markedPoint 0 * d.markedPoint 1 ≠ d.markedPoint 2 := by
    intro he
    have hh : d.markedCoordinates (Pi.single 0 1 + Pi.single 1 1) =
        d.markedCoordinates (Pi.single 2 1) := by
      rw [map_add,d.markedCoordinates_single,d.markedCoordinates_single,d.markedCoordinates_single]
      exact congrArg Additive.ofMul he
    have he0 := congrFun (d.markedCoordinates.injective hh) 0
    norm_num [Pi.single_apply] at he0
    omega
  have hfixC : ∀ w ∈ C, p' w = w := by
    apply d.lineStabilizer_fixes_pairSection h (d.markedPoint 0*d.markedPoint 1) (d.markedPoint 2)
      h01 (d.marked_nonidentity h 2) h012 p
    apply d.mem_lineStabilizer_of_map_eq
    rw [d.pointLine_map,map_mul,hp0,hp1,hp2,mul_comm (d.markedPoint 1)]
  apply shear_identity A B ?_ a' p' (invol p hpa) (invol a haa) hpA hpB hfixB
    (fun w hw => hfixC _ (haC w hw)) ?_ v hv
  · apply disjoint_def.mpr
    intro w hwA hwB
    exact mem_bot.mp (d.coreSection_triple_inf h ▸
      (show w ∈ d.coreSection z ⊓ d.coreSection d.r ⊓ d.coreSection d.s from
        ⟨⟨hwA.1,hwB.1⟩,hwA.2⟩))
  · intro w hw
    rw [d.coreSection_s_pair_sup h]
    exact (haC w hw).2

private def binaryShear : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) where
  toFun v := ![v 0,v 1+v 0,v 2]
  invFun v := ![v 0,v 1+v 0,v 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

/-- The binary shear on the original marked three-space; its action is specified below. -/
noncomputable def markedShear : MulAut d.space :=
  MulEquiv.toAdditive.symm
    ((d.markedCoordinates.symm.trans binaryShear).trans d.markedCoordinates).toAddEquiv

/-- The constructed shear sends z to zr and fixes the other two original markers. -/
theorem markedShear_points :
    d.markedShear (d.markedPoint 0) = d.markedPoint 0*d.markedPoint 1 ∧
    d.markedShear (d.markedPoint 1) = d.markedPoint 1 ∧
    d.markedShear (d.markedPoint 2) = d.markedPoint 2 := by
  have hs0 : binaryShear (Pi.single 0 1) = Pi.single 0 1 + Pi.single 1 1 := by decide +kernel
  have hs1 : binaryShear (Pi.single 1 1) = Pi.single 1 1 := by decide +kernel
  have hs2 : binaryShear (Pi.single 2 1) = Pi.single 2 1 := by decide +kernel
  have he (i : Fin 3) : d.markedShear (d.markedPoint i) =
      Additive.toMul (d.markedCoordinates (binaryShear (Pi.single i 1))) := by
    change Additive.toMul (d.markedCoordinates (binaryShear
      (d.markedCoordinates.symm (Additive.ofMul (d.markedPoint i))))) = _
    rw [←d.markedCoordinates_single,LinearEquiv.symm_apply_apply]
  refine ⟨?_,?_,?_⟩
  · rw [he,hs0,map_add,d.markedCoordinates_single,d.markedCoordinates_single]
    rfl
  · rw [he,hs1,d.markedCoordinates_single]
    rfl
  · rw [he,hs2,d.markedCoordinates_single]
    rfl

/-- The shear fixes the other two pair sections pointwise. -/
theorem markedShear_fixes_other_sections (h : IsTypeJ4 z)
    (v : d.R ⧸ center d.R)
    (hv : v ∈ d.coreSection z ⊓ d.coreSection d.r ∨
      v ∈ d.coreSection d.r ⊓ d.coreSection d.s) :
    d.linearRadicalAction h d.markedShear v = v := by
  obtain ⟨h0,h1,h2⟩ := d.markedShear_points
  rcases hv with hv | hv
  · apply d.lineStabilizer_fixes_pairSection h (d.markedPoint 0) (d.markedPoint 1)
      (d.marked_nonidentity h 0) (d.marked_nonidentity h 1)
      (fun he => by have := d.marked_injective he; contradiction) d.markedShear ?_ v hv
    apply d.mem_lineStabilizer_of_map_eq
    rw [d.pointLine_map,h0,h1,d.pointLine_mul_left]
  · apply d.lineStabilizer_fixes_pairSection h (d.markedPoint 1) (d.markedPoint 2)
      (d.marked_nonidentity h 1) (d.marked_nonidentity h 2)
      (fun he => by have := d.marked_injective he; contradiction) d.markedShear ?_ v hv
    apply d.mem_lineStabilizer_of_map_eq
    rw [d.pointLine_map,h1,h2]

/-- The constructed shear adds the swapped coordinate on the remaining pair section. -/
theorem markedShear_radical_action (h : IsTypeJ4 z)
    (v : d.R ⧸ center d.R) (hv : v ∈ d.coreSection z ⊓ d.coreSection d.s) :
    d.linearRadicalAction h d.markedShear v =
      v * d.linearRadicalAction h (d.markedPermutation (Equiv.swap 0 1)) v := by
  obtain ⟨h0,h1,h2⟩ := d.markedShear_points
  apply d.radical_shear_of_marked_action h _ _ h0 h1 h2 ?_ ?_ ?_ v hv
  · simpa only [Equiv.swap_apply_left] using d.markedPermutation_point (Equiv.swap 0 1) 0
  · simpa only [Equiv.swap_apply_right] using d.markedPermutation_point (Equiv.swap 0 1) 1
  · simpa only [Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 3) ≠ 0)
      (by decide : (2 : Fin 3) ≠ 1)] using d.markedPermutation_point (Equiv.swap 0 1) 2

attribute [local instance] R_normal_in_K

/-- Original K-elements realize the shear, the swap and their literal quotient-action formulas. -/
theorem exists_K_shear_and_radical_formula (h : IsTypeJ4 z) :
    ∃ k l : d.K,
      (k : G)*z*(k : G)⁻¹=z*d.r ∧
      (k : G)*d.r*(k : G)⁻¹=d.r ∧ (k : G)*d.s*(k : G)⁻¹=d.s ∧
      (l : G)*z*(l : G)⁻¹=d.r ∧
      (l : G)*d.r*(l : G)⁻¹=z ∧ (l : G)*d.s*(l : G)⁻¹=d.s ∧
      (∀ v : d.R ⧸ center d.R, v ∈ d.coreSection z ⊓ d.coreSection d.s →
        d.KRadicalAction h (QuotientGroup.mk' _ k) v =
          v * d.KRadicalAction h (QuotientGroup.mk' _ l) v) ∧
      (∀ v : d.R ⧸ center d.R,
        (v ∈ d.coreSection z ⊓ d.coreSection d.r ∨
          v ∈ d.coreSection d.r ⊓ d.coreSection d.s) →
        d.KRadicalAction h (QuotientGroup.mk' _ k) v = v) := by
  obtain ⟨k,hk⟩ := d.KAction_surjective h d.markedShear
  obtain ⟨l,hl⟩ := d.KAction_surjective h (d.markedPermutation (Equiv.swap 0 1))
  have hak : d.KRadicalAction h (QuotientGroup.mk' _ k) = d.linearRadicalAction h d.markedShear := by
    rw [←hk,d.linearRadicalAction_KAction,d.KRadicalAction_mk]
  have hal : d.KRadicalAction h (QuotientGroup.mk' _ l) =
      d.linearRadicalAction h (d.markedPermutation (Equiv.swap 0 1)) := by
    rw [←hl,d.linearRadicalAction_KAction,d.KRadicalAction_mk]
  have hkp (i : Fin 3) : (k : G)*(d.markedPoint i : G)*(k : G)⁻¹ =
      (d.markedShear (d.markedPoint i) : G) :=
    congrArg (fun f : MulAut d.space => (f (d.markedPoint i) : G)) hk
  have hlp (i : Fin 3) : (l : G)*(d.markedPoint i : G)*(l : G)⁻¹ =
      (d.markedPoint ((Equiv.swap 0 1) i) : G) := by
    exact (congrArg (fun f : MulAut d.space => (f (d.markedPoint i) : G)) hl).trans
      (congrArg Subtype.val (d.markedPermutation_point _ i))
  obtain ⟨hs0,hs1,hs2⟩ := d.markedShear_points
  refine ⟨k,l,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hh := hkp 0
    rw [hs0] at hh
    exact hh
  · have hh := hkp 1
    rw [hs1] at hh
    exact hh
  · have hh := hkp 2
    rw [hs2] at hh
    exact hh
  · have hh := hlp 0
    rw [Equiv.swap_apply_left] at hh
    exact hh
  · have hh := hlp 1
    rw [Equiv.swap_apply_right] at hh
    exact hh
  · have hh := hlp 2
    rw [Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 3) ≠ 0)
      (by decide : (2 : Fin 3) ≠ 1)] at hh
    exact hh
  · intro v hv
    rw [hak,hal]
    exact d.markedShear_radical_action h v hv
  · intro v hv
    rw [hak]
    exact d.markedShear_fixes_other_sections h v hv

set_option backward.isDefEq.respectTransparency false in
private noncomputable def linearPairTransport (h : IsTypeJ4 z) (a : MulAut d.space)
    (t u : d.space) :
    (d.coreSection t.val ⊓ d.coreSection u.val : Subgroup (d.R ⧸ center d.R)) ≃*
      (d.coreSection (a t).val ⊓ d.coreSection (a u).val : Subgroup (d.R ⧸ center d.R)) :=
  ((d.linearRadicalAction h a).subgroupMap _).trans (MulEquiv.subgroupCongr (by
    rw [map_inf _ _ _ (d.linearRadicalAction h a).injective,
      ←MulEquiv.toMonoidHom_eq_coe,
      d.linearRadicalAction_conjugate_section,d.linearRadicalAction_conjugate_section]))

set_option backward.isDefEq.respectTransparency false in
/-- One coordinate system simultaneously gives the two marked swaps, the binary shear and the original diagonal S/R action. -/
theorem exists_multiplicity_coordinates_root_actions (h : IsTypeJ4 z) :
    letI := d.R_normal_in_S_intrinsic
    ∃ f : d.multiplicitySpace × (d.multiplicitySpace × d.multiplicitySpace) ≃*
        (d.R ⧸ center d.R),
      (∀ w, f (w,1,1) = (w : d.R ⧸ center d.R)) ∧
      (∀ a : d.S ⧸ d.R.subgroupOf d.S, ∀ u v w : d.multiplicitySpace,
        f (d.multiplicityAction h a u,d.multiplicityAction h a v,d.multiplicityAction h a w) =
          d.SRadicalAction h a (f (u,v,w))) ∧
      (∀ u v w : d.multiplicitySpace,
        d.linearRadicalAction h d.markedShear (f (u,v,w)) = f (u,v,v*w)) ∧
      (∀ u v w : d.multiplicitySpace,
        d.linearRadicalAction h (d.markedPermutation (Equiv.swap 0 1)) (f (u,v,w)) = f (u,w,v)) ∧
      (∀ u v w : d.multiplicitySpace,
        d.linearRadicalAction h (d.markedPermutation (Equiv.swap 1 2)) (f (u,v,w)) = f (v,u,w)) := by
  let := d.R_center_quotient_elementary h
  let := d.R_normal_in_S_intrinsic
  let p := d.markedPermutation (Equiv.swap 0 1)
  let q := d.markedPermutation (Equiv.swap 1 2)
  have hp0 : p (d.markedPoint 0) = d.markedPoint 1 := by
    simp only [p,d.markedPermutation_point,Equiv.swap_apply_left]
  have hp1 : p (d.markedPoint 1) = d.markedPoint 0 := by
    simp only [p,d.markedPermutation_point,Equiv.swap_apply_right]
  have hp2 : p (d.markedPoint 2) = d.markedPoint 2 := by
    dsimp only [p]
    rw [d.markedPermutation_point,Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
  have hq0 : q (d.markedPoint 0) = d.markedPoint 0 := by
    dsimp only [q]
    rw [d.markedPermutation_point,Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
  have hq1 : q (d.markedPoint 1) = d.markedPoint 2 := by
    simp only [q,d.markedPermutation_point,Equiv.swap_apply_left]
  have hq2 : q (d.markedPoint 2) = d.markedPoint 1 := by
    simp only [q,d.markedPermutation_point,Equiv.swap_apply_right]
  let P := d.linearRadicalAction h p
  let Q := d.linearRadicalAction h q
  let A := d.linearRadicalAction h d.markedShear
  have hpinv : p*p=1 := by
    apply d.aut_ext_marked
    intro i
    fin_cases i
    · change p (p (d.markedPoint 0)) = d.markedPoint 0; rw [hp0,hp1]
    · change p (p (d.markedPoint 1)) = d.markedPoint 1; rw [hp1,hp0]
    · change p (p (d.markedPoint 2)) = d.markedPoint 2; rw [hp2,hp2]
  have hqinv : q*q=1 := by
    apply d.aut_ext_marked
    intro i
    fin_cases i
    · change q (q (d.markedPoint 0)) = d.markedPoint 0; rw [hq0,hq0]
    · change q (q (d.markedPoint 1)) = d.markedPoint 1; rw [hq1,hq2]
    · change q (q (d.markedPoint 2)) = d.markedPoint 2; rw [hq2,hq1]
  have hPP (v : d.R ⧸ center d.R) : P (P v) = v := by
    change (d.linearRadicalAction h p*d.linearRadicalAction h p) v = v
    rw [←map_mul,hpinv,map_one]; rfl
  have hQQ (v : d.R ⧸ center d.R) : Q (Q v) = v := by
    change (d.linearRadicalAction h q*d.linearRadicalAction h q) v = v
    rw [←map_mul,hqinv,map_one]; rfl
  let b : d.multiplicitySpace ≃*
      (d.coreSection z ⊓ d.coreSection d.s : Subgroup (d.R ⧸ center d.R)) :=
    (d.linearPairTransport h q (d.markedPoint 0) (d.markedPoint 1)).trans
      (MulEquiv.subgroupCongr (by rw [hq0,hq1]; rfl))
  let c : d.multiplicitySpace ≃*
      (d.coreSection d.r ⊓ d.coreSection d.s : Subgroup (d.R ⧸ center d.R)) :=
    b.trans ((d.linearPairTransport h p (d.markedPoint 0) (d.markedPoint 2)).trans
      (MulEquiv.subgroupCongr (by rw [hp0,hp2]; rfl)))
  have hb (v : d.multiplicitySpace) : (b v : d.R ⧸ center d.R) = Q v := rfl
  have hc (v : d.multiplicitySpace) : (c v : d.R ⧸ center d.R) = P (Q v) := rfl
  have hPA (v : d.multiplicitySpace) : P v = v := by
    apply d.lineStabilizer_fixes_pairSection h (d.markedPoint 0) (d.markedPoint 1)
      (d.marked_nonidentity h 0) (d.marked_nonidentity h 1)
      (fun he => by have := d.marked_injective he; contradiction) p ?_ v v.property
    apply d.mem_lineStabilizer_of_map_eq
    rw [d.pointLine_map,hp0,hp1]
    simp only [pointLine,Set.pair_comm]
  have hQC (v : d.multiplicitySpace) : Q (P (Q v)) = P (Q v) := by
    have hv : P (Q v) ∈ d.coreSection d.r ⊓ d.coreSection d.s := (c v).property
    apply d.lineStabilizer_fixes_pairSection h (d.markedPoint 1) (d.markedPoint 2)
      (d.marked_nonidentity h 1) (d.marked_nonidentity h 2)
      (fun he => by have := d.marked_injective he; contradiction) q ?_ _ hv
    apply d.mem_lineStabilizer_of_map_eq
    rw [d.pointLine_map,hq1,hq2]
    simp only [pointLine,Set.pair_comm]
  have hAA (v : d.multiplicitySpace) : A v = v :=
    d.markedShear_fixes_other_sections h v (Or.inl v.property)
  have hAB (v : d.multiplicitySpace) : A (Q v) = Q v * P (Q v) :=
    d.markedShear_radical_action h (b v) (b v).property
  have hAC (v : d.multiplicitySpace) : A (P (Q v)) = P (Q v) :=
    d.markedShear_fixes_other_sections h (c v) (Or.inr (c v).property)
  obtain ⟨f,hf⟩ := d.exists_coreSection_product h
  let f' := ((MulEquiv.refl d.multiplicitySpace).prodCongr (b.prodCongr c)).trans f
  have hf' (u v w : d.multiplicitySpace) : f' (u,v,w) =
      (u : d.R ⧸ center d.R)*(Q v*P (Q w)) := hf u (b v) (c w)
  refine ⟨f',?_,?_,?_,?_,?_⟩
  · intro w
    rw [hf']
    simp only [OneMemClass.coe_one,map_one,mul_one]
  · intro a u v w
    have hQ := d.linearRadicalAction_commutes_S h q a
    have hP := d.linearRadicalAction_commutes_S h p a
    rw [hf',hf',map_mul,map_mul]
    apply congrArg₂ (· * ·) rfl
    apply congrArg₂ (· * ·)
    · exact congrArg (fun f : MulAut (d.R ⧸ center d.R) => f v.val) hQ.eq
    · exact (congrArg P (congrArg (fun f : MulAut (d.R ⧸ center d.R) => f w.val) hQ.eq)).trans
        (congrArg (fun f : MulAut (d.R ⧸ center d.R) => f (Q w.val)) hP.eq)
  · intro u v w
    change A (f' (u,v,w)) = f' (u,v,v*w)
    rw [hf',hf',map_mul,map_mul,hAA,hAB,hAC,Subgroup.coe_mul,map_mul,map_mul]
    ac_rfl
  · intro u v w
    change P (f' (u,v,w)) = f' (u,w,v)
    rw [hf',hf',map_mul,map_mul,hPA,hPP,mul_comm (P (Q v))]
  · intro u v w
    change Q (f' (u,v,w)) = f' (v,u,w)
    rw [hf',hf',map_mul,map_mul,hQQ,hQC]
    ac_rfl

end ThreeSpaceData
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
