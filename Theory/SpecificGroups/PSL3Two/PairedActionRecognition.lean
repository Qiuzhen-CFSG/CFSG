module
public import Theory.GroupTheory.PairedInvolutiveExtension.Recognition
public import Theory.SpecificGroups.PSL3Two.PairedActionParity
/-!
# Recognition from the original paired component generators

A faithful action containing the full inner component pair is determined by
its original factor-preserving outer generator and factor-interchanging
generator. The latter need only have square in the component pair. The parity
calculation and generated-image recognition produce an isomorphism to the
paired model, with its action formula and every original inner pair retained.
Thus the canonical commuting involutions may be transported back to the source
group without claiming that its original generators had those properties.

Source: Aschbacher--Smith 2.4.34, printed p.548, manuscript of 1 March 2004.
-/

public section
namespace Matrix.PSL3Two.PairedActionRecognition
open Subgroup MarkedAutomorphisms Theory.GroupTheory.PairedInvolutiveExtension
variable {H : Type*} [Group H] (ρ : H →* MulAut (SL×SL))
variable (N : Subgroup H) (hN : N.map ρ=(MulAut.conj : SL×SL →* MulAut (SL×SL)).range)
variable (x s : H) (hgen : N ⊔ zpowers x ⊔ zpowers s=⊤)
variable (hx : ∃ a b : MulAut SL,ρ x=a.prodCongr b ∧
  (∀ g:SL,a≠MulAut.conj g) ∧ (∀ g:SL,b≠MulAut.conj g))
variable (hs : ∃ a b : MulAut SL,ρ s=a.prodCongr b * (MulEquiv.prodComm : MulAut (SL×SL)))
variable (hsq : s^2∈N)
include hN hgen hx hs hsq in
/-- The literal generated action has exactly the paired model image. -/
theorem image_eq : ρ.range=(representation diagram diagram_involutive).range := by
  obtain ⟨a,b,hx,ha,hb⟩ := hx
  obtain ⟨c,d,hcd⟩ := PairedActionParity.outer_pair_normal_form a b ha hb
  have hx' : ρ x=MulAut.conj (c,d)*diagram.prodCongr diagram := hx.trans hcd
  obtain ⟨a',b',hs⟩ := hs
  have hs2 : ρ (s^2)∈(MulAut.conj : SL×SL →* MulAut (SL×SL)).range := by
    rw [←hN]
    exact mem_map_of_mem ρ hsq
  obtain ⟨⟨u,v⟩,huv⟩ := hs2
  have hsq' : (a'.prodCongr b' * (MulEquiv.prodComm : MulAut (SL×SL)))^2=MulAut.conj (u,v) := by
    rw [←hs,←map_pow,huv]
  obtain ⟨e,f,p,hef⟩ := PairedActionParity.swapped_square_inner_normal_form a' b' u v hsq'
  have hs' : ρ s=MulAut.conj (e,f)*action diagram diagram_involutive (p,on) := hs.trans hef
  have himage := congrArg (fun P:Subgroup H => P.map ρ) hgen
  rw [Subgroup.map_sup,Subgroup.map_sup,hN,ρ.map_zpowers,ρ.map_zpowers,←ρ.range_eq_map,hx',hs'] at himage
  exact range_eq_of_generated_cosets diagram diagram_involutive ρ.range c d e f p himage.symm

/-- The faithful source action identifies the original generated group with
the model, even when its selected original generators are not involutions. -/
noncomputable def equiv (hρ : Function.Injective ρ) : H ≃* Model diagram diagram_involutive :=
  equivOfImage diagram diagram_involutive ρ hρ conj_injective diagram_ne_conj
    (image_eq ρ N hN x s hgen hx hs hsq)

theorem equiv_spec (hρ : Function.Injective ρ) (y : H) :
    representation diagram diagram_involutive (equiv ρ N hN x s hgen hx hs hsq hρ y)=ρ y :=
  equivOfImage_spec diagram diagram_involutive ρ hρ conj_injective diagram_ne_conj
    (image_eq ρ N hN x s hgen hx hs hsq) y

/-- Actual inner pairs, including the two original central involution marks,
retain their literal coordinates under recognition. -/
theorem equiv_eq_base (hρ : Function.Injective ρ) (y : H) (a b : SL)
    (hy : ρ y=MulAut.conj (a,b)) :
    equiv ρ N hN x s hgen hx hs hsq hρ y=base diagram diagram_involutive a b := by
  apply representation_injective diagram diagram_involutive conj_injective diagram_ne_conj
  rw [equiv_spec,representation_base,hy]
end Matrix.PSL3Two.PairedActionRecognition
