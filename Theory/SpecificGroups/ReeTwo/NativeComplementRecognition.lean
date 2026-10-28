module
public import Theory.SpecificGroups.ReeTwo.Recognition

/-!
# Whole first-parabolic recognition from the two native complement actions

The specified five and four actors define the C₅:C₄ complement. Their
actions on an actual core embedding intertwine the full native complement
action, giving a semidirect-product homomorphism. A surviving last root
makes this map faithful; target order 20480 makes it an equivalence. The
map agrees with the supplied embedding on every core element.

Source: the verified Shinoda (1975), pp.81–83 core/complement presentation;
the source application is the original first endpoint in J.4.5.
-/

public section
noncomputable section
namespace ReeTwo.Centralizer

private theorem double_intertwine {N H:Type*} [Group N] [Group H]
    (j:N→*H) (β:MulAut N) (b:H) (h:∀q,j (β q)=b*j q*b⁻¹) (q:N) :
    j ((β^2) q)=b^2*j q*(b^2)⁻¹ := by
  rw [pow_two,MulAut.mul_apply,h,h]
  simp only [pow_two]
  group

/-- Native five and four actions recognize the entire centralizer, while
preserving every element of the marked core. -/
theorem exists_equiv_of_native_actions {H:Type*} [Group H] [Finite H]
    (hH:Nat.card H=20480) (j:Core→*H) (c b:H)
    (hc:c^5=1) (hb:b^4=1) (hbc:b*c*b⁻¹=c^2)
    (hjc:∀q,j (Core.c q)=c*j q*c⁻¹)
    (hjb:∀q,j (Core.a q)=b*j q*b⁻¹)
    (hz:j (Core.root 9)≠1) :
    ∃e:Centralizer≃*H,∀q:Core,e (SemidirectProduct.inl q)=j q := by
  let w:=b^2*c
  have hec:b^2*w=c:=by
    dsimp [w]
    rw [←mul_assoc,←pow_add,show 2+2=4 from rfl,hb,one_mul]
  let d:Core.complement→*H:=Core.complementLift b w (by rwa [hec]) hb (by rwa [hec])
  have hda:d Core.complementA=b:=Core.complementLift_a b w _ _ _
  have hdr:d Core.complementR=w:=Core.complementLift_r b w _ _ _
  have hr:Core.r=Core.a^2*Core.c:=by
    rw [Core.c,←mul_assoc,←pow_add,show 2+2=4 from rfl,Core.a_four,one_mul]
  have hjr:∀q,j (Core.r q)=w*j q*w⁻¹:=by
    intro q
    rw [hr,MulAut.mul_apply,double_intertwine j Core.a b hjb,hjc]
    dsimp [w]
    group
  have hcompat (k:Core.complement) : j.comp (Core.complement.subtype k).toMonoidHom=
      (MulAut.conj (d k)).toMonoidHom.comp j:=by
    apply Core.complement_compatible j d
    · apply MonoidHom.ext
      intro q
      change j (Core.a q)=d Core.complementA*j q*(d Core.complementA)⁻¹
      rw [hda]
      exact hjb q
    · apply MonoidHom.ext
      intro q
      change j (Core.r q)=d Core.complementR*j q*(d Core.complementR)⁻¹
      rw [hdr]
      exact hjr q
  let f:Centralizer→*H:=SemidirectProduct.lift j d hcompat
  have hfroot:f (root 9)≠1:=by
    change SemidirectProduct.lift j d hcompat (SemidirectProduct.inl (Core.root 9))≠1
    rwa [SemidirectProduct.lift_inl]
  have hfi:=hom_injective_of_last_root f hfroot
  let e:Centralizer≃*H:=MulEquiv.ofBijective f (hfi.bijective_of_nat_card_le (by rw [hH,card]))
  exact ⟨e,fun q=>SemidirectProduct.lift_inl j d hcompat q⟩

end ReeTwo.Centralizer
