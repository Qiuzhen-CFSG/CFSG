module
public import Theory.GroupTheory.PGroup.SecondCenterFrattiniPairing
public import Theory.Frattini.BinarySquares
public import Mathlib.Tactic.Group

/-!
# Squares on the second central quotient

For a finite group P with elementary center, Z₂(P)/Z(P) is elementary and
its representatives have central squares. Those squares are independent of
the representative. Their polarization is the literal commutator pairing,
bilinear and alternating on the actual second central quotient. Every
automorphism transports the square values in the whole center.

For a two-group the square values generate exactly the embedded Φ(Z₂(P));
in particular that subgroup lies in Z(P). No equality Z₂(P)=P, perfectness
of the pairing, or vanishing of the square map is inferred.

The marked natural/doubled application is in LinearThreeMS.NonbinarySource.
SecondCenterSquares. Source: elementary commutator and binary Frattini
identities, used in Aschbacher–Smith C.1.34–35, printed pp.136–138.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace Theory.GroupTheory.SecondCenterFrattini
variable {P : Type*} [Group P] [Finite P] [IsElementaryAbelian 2 (center P)]
local notation "Z₂" => Subgroup.upperCentralSeries P 2
local notation "C" => Subgroup.subgroupOf (center P) (Subgroup.upperCentralSeries P 2)
local notation "V" => (Z₂ ⧸ C)

omit [Finite P] in
private theorem central_square (z : P) (hz : z ∈ center P) : z^2=1 :=
  elemPow_eq_one_of_isElementaryAbelian (p := 2) z hz

omit [Finite P] in
/-- Squares are constant on the original central cosets in the second center. -/
theorem upper_square_eq_of_quotient_eq (x y : Z₂)
    (h : QuotientGroup.mk' C x = QuotientGroup.mk' C y) : (x:P)^2=(y:P)^2 := by
  have hm' : x⁻¹*y∈C := QuotientGroup.eq.mp h
  have hm : (x:P)⁻¹*(y:P)∈center P := hm'
  have hc : Commute (x:P) ((x:P)⁻¹*(y:P)) := mem_center_iff.mp hm _
  simpa only [mul_inv_cancel_left,central_square _ hm,mul_one] using (hc.mul_pow 2).symm

/-- The intrinsic square map of the second central quotient, valued in the whole center. -/
def upperSquare : V → center P :=
  Quotient.lift (fun x : Z₂ => ⟨(x:P)^2,second_square_mem_center x⟩) (by
    intro x y h
    exact Subtype.ext (upper_square_eq_of_quotient_eq x y (Quotient.sound h)))

@[simp] theorem upperSquare_apply (x : Z₂) :
    (upperSquare (QuotientGroup.mk' C x):P)=(x:P)^2 := by rfl

private theorem pairing_center (u : V) (z : center P) :
    pairing u (QuotientGroup.mk' (frattini P) z)=1 := by
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective C u
  apply Subtype.ext
  rw [pairing_apply]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp z.property x)

private def upperRow (u : V) : V →* center P :=
  QuotientGroup.lift C
    (((pairing u).comp (QuotientGroup.mk' (frattini P))).comp (Z₂).subtype)
    (by intro z hz; exact pairing_center u ⟨z,hz⟩)

/-- The alternating commutator pairing on the second central quotient itself. -/
def upperPolar : V →* (V →* center P) where
  toFun := upperRow
  map_one' := by
    apply MonoidHom.ext
    intro v
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective C v
    change pairing 1 (QuotientGroup.mk' (frattini P) (y:P))=1
    rw [map_one,MonoidHom.one_apply]
  map_mul' u v := by
    apply MonoidHom.ext
    intro w
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective C w
    change pairing (u*v) (QuotientGroup.mk' (frattini P) (y:P))=
      pairing u (QuotientGroup.mk' (frattini P) (y:P))*
      pairing v (QuotientGroup.mk' (frattini P) (y:P))
    rw [map_mul,MonoidHom.mul_apply]

@[simp] theorem upperPolar_apply (x y : Z₂) :
    (upperPolar (QuotientGroup.mk' C x) (QuotientGroup.mk' C y):P)=⁅(x:P),(y:P)⁆ := by
  change (pairing (QuotientGroup.mk' C x) (QuotientGroup.mk' (frattini P) (y:P)):P)=_
  exact pairing_apply x y

/-- The square map has precisely the original commutator as its polarization. -/
theorem upperSquare_mul (u v : V) :
    upperSquare (u*v)=upperSquare u*upperSquare v*upperPolar u v := by
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective C u
  obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective C v
  apply Subtype.ext
  rw [←map_mul]
  simp only [Subgroup.coe_mul,upperSquare_apply,upperPolar_apply]
  have hc : ⁅(x:P),(y:P)⁆ ∈ center P := by
    simpa only [Subgroup.upperCentralSeries_one] using
      (Subgroup.mem_upperCentralSeries_succ_iff.mp x.property (y:P))
  have hx := second_square_mem_center x
  symm
  calc
    (x:P)^2*(y:P)^2*⁅(x:P),(y:P)⁆ =
        ⁅(x:P),(y:P)⁆*((x:P)^2*(y:P)^2) := mem_center_iff.mp hc _
    _ = (x:P)*(y:P)*(x:P)⁻¹*((y:P)⁻¹*(x:P)^2)*(y:P)^2 := by
      simp only [commutatorElement_def,mul_assoc]
    _ = (x:P)*(y:P)*(x:P)⁻¹*((x:P)^2*(y:P)⁻¹)*(y:P)^2 := by
      rw [mem_center_iff.mp hx]
    _ = ((x:P)*(y:P))^2 := by simp only [pow_two]; group

/-- Alternation does not imply nondegeneracy on the second center. -/
theorem upperPolar_self (u : V) : upperPolar u u=1 := by
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective C u
  apply Subtype.ext
  rw [upperPolar_apply]
  simp

/-- Simultaneous automorphisms transport squares on the actual quotient maps. -/
theorem upperSquare_automorphism (a : MulAut P) (x : Z₂) :
    upperSquare (QuotientGroup.mk' C (MulAut.characteristic Z₂ a x)) =
      centerCongr a (upperSquare (QuotientGroup.mk' C x)) := by
  apply Subtype.ext
  change (a (x:P))^2=a ((x:P)^2)
  exact (map_pow a (x:P) 2).symm

/-- The zero locus consists exactly of the cosets whose lifts square to one. -/
theorem upperSquare_eq_one_iff (x : Z₂) :
    upperSquare (QuotientGroup.mk' C x)=1 ↔ (x:P)^2=1 :=
  ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩

/-- Elementary full preimages are exactly the subgroups on which the
intrinsic square map vanishes. All quotient maps and central attachments are retained. -/
theorem upper_preimage_elementary_iff (W : Subgroup V) :
    IsElementaryAbelian 2 (W.comap (QuotientGroup.mk' C)) ↔
      ∀ v ∈ W, upperSquare v=1 := by
  let X := W.comap (QuotientGroup.mk' C)
  constructor
  · intro h v hv
    let := h
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective C v
    have hs := elemPow_eq_one_of_isElementaryAbelian (p := 2) x
      (show x∈X from hv)
    apply (upperSquare_eq_one_iff x).mpr
    exact congrArg (Z₂).subtype hs
  · intro h
    have hs (x : X) : x^2=1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact (upperSquare_eq_one_iff x.val).mp (h _ x.property)
    have hi (x : X) : x⁻¹=x := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hs x)
    refine { toIsMulCommutative := ⟨⟨?_⟩⟩
             exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
    intro x y
    calc x*y=(x*y)⁻¹ := (hi _).symm
         _=y*x := by rw [mul_inv_rev,hi,hi]

/-- The square values generate the literal embedded Frattini subgroup of Z₂(P). -/
theorem upper_frattini_eq_square_span (hP : IsPGroup 2 P) :
    (frattini Z₂).map (Z₂).subtype =
      closure (Set.range (fun v : V => (upperSquare v:P))) := by
  rw [(hP.to_subgroup Z₂).frattini_eq_closure_squares,MonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨_,⟨x,rfl⟩,rfl⟩
    exact ⟨QuotientGroup.mk' C x,rfl⟩
  · rintro ⟨v,rfl⟩
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective C v
    exact ⟨x^2,⟨x,rfl⟩,rfl⟩

/-- The Frattini subgroup of the second center lies in the original whole center. -/
theorem upper_frattini_le_center (hP : IsPGroup 2 P) :
    (frattini Z₂).map (Z₂).subtype ≤ center P := by
  rw [upper_frattini_eq_square_span hP]
  apply (closure_le _).mpr
  rintro _ ⟨v,rfl⟩
  exact (upperSquare v).property

end Theory.GroupTheory.SecondCenterFrattini
