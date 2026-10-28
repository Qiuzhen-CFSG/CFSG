module

public import Theory.Representation.SL2.EightRootRegular
public import Theory.GroupTheory.RegularKernelRootPlacement

/-!
# Placing a prescribed eight-root in a conjugate section

The literal image of the root is an eight-element two-subgroup. Its action
on the full binary kernel is regular, so comparison of the root section
with the specified global section produces a conjugator in that full kernel.
The actual action coordinates, projection and root subgroup are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Representation.SL2.BinarySmall

/-- Every prescribed root lift embeds into a full-kernel conjugate of the
specified global section, using its actual irreducible degree-eight action. -/
theorem root_le_conjugate_section_of_eight_irreducible_kernel
    {E V : Type*} [Group E] [Finite E] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (q : E →* SL(2,GaloisField 2 3))
    (ρ : Representation (ZMod 2) SL(2,GaloisField 2 3) V) [ρ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V=8) (ek : q.ker ≃* Multiplicative V)
    (hρ : ∀ (g : E) (v : q.ker),
      (ek (MulAut.conjNormal g v)).toAdd=ρ (q g) (ek v).toAdd)
    (s : SL(2,GaloisField 2 3) →* E) (hs : ∀ g,q (s g)=g)
    (R : Subgroup E) (hR : IsPGroup 2 R) (hc : Nat.card R=8)
    (hk : Disjoint R q.ker) :
    ∃ v : q.ker, R≤s.range.map (MulAut.conj (v:E)).toMonoidHom := by
  let U := R.map q
  let qr : R →* U := (q.comp R.subtype).codRestrict U
    (fun r => mem_map_of_mem q r.property)
  have hqi : Function.Injective qr := by
    apply qr.ker_eq_bot_iff.mp
    apply bot_unique
    intro r hr
    have hh : q (r:E)=1 := congrArg Subtype.val hr
    exact Subtype.ext (hk.le_bot ⟨r.property,hh⟩)
  have hqs : Function.Surjective qr := by
    intro u
    obtain ⟨r,hr,he⟩ := u.property
    exact ⟨⟨r,hr⟩,Subtype.ext he⟩
  let er := MulEquiv.ofBijective qr ⟨hqi,hqs⟩
  have hU : Nat.card U=8 := (Nat.card_congr er.toEquiv).symm.trans hc
  obtain ⟨a,ha⟩ := eight_irreducible_root_regular ρ hd U (hR.map q) hU
  let em : q.ker ≃* (U → Multiplicative (ZMod 2)) := ek.trans
    (a.toAddEquiv.toMultiplicative.trans (MulEquiv.funMultiplicative U (ZMod 2)))
  let r : U →* E := R.subtype.comp er.symm.toMonoidHom
  have hr (g : U) : q (r g)=(g:SL(2,GaloisField 2 3)) :=
    congrArg Subtype.val (er.apply_symm_apply g)
  obtain ⟨v,hv⟩ := local_section_conjugate_of_regular_kernel q U em (by
    intro g v x
    change Multiplicative.ofAdd (a (ek (MulAut.conjNormal (g:E) v)).toAdd x)=
      Multiplicative.ofAdd (a (ek v).toAdd ((⟨q g,g.property⟩:U)⁻¹*x))
    rw [hρ]
    exact congrArg Multiplicative.ofAdd (ha ⟨q g,g.property⟩ (ek v).toAdd x)) s hs r hr
  refine ⟨v,fun x hx => ?_⟩
  let u := er ⟨x,hx⟩
  have hu : r u=x := congrArg Subtype.val (er.symm_apply_apply ⟨x,hx⟩)
  exact ⟨s (u:SL(2,GaloisField 2 3)),⟨u,rfl⟩,(hv u).symm.trans hu⟩

end Representation.SL2.BinarySmall
