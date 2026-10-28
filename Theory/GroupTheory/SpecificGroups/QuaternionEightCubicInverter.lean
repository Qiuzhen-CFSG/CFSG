module

public import Theory.GroupTheory.SpecificGroups.QuaternionEightCubicCentralizer

/-!
# Quaternion cubic inverters and the central involution

An automorphism of Q₈ inverting a nontrivial cubic never has a norm equal
to the central involution. The proof checks the two quaternion generator
images in standard cubic coordinates and transports the resulting identity.
This distinguishes the quaternion extension in Aschbacher (1994),45.8,p245.
-/

public section
open QuaternionGroup GLS3.Chapter5.SchurPresentation
namespace QuaternionGroup
private abbrev Q := QuaternionGroup 2
private def generatorMap (a b : Q) : Q→Q
  | .a i => a^i.val
  | .xa i => b*a^i.val
private theorem inversion_norm_table : ∀ a b q : Q,
    a^2=(.a 2:Q) → b^2=(.a 2:Q) → a*b≠b*a →
    generatorMap a b (q8Cycle (.a 1))=q8Cycle⁻¹ a →
    generatorMap a b (q8Cycle (.xa 0))=q8Cycle⁻¹ b →
    q*generatorMap a b q≠(.a 2:Q) := by
  decide
private theorem generatorMap_aut (f : MulAut (QuaternionGroup 2)) (x : Q) :
    generatorMap (f (.a 1)) (f (.xa 0)) x=f x := by
  cases x with
  | a i =>
    change (f (.a 1))^i.val=f (.a i)
    rw [←map_pow,a_one_pow,ZMod.natCast_zmod_val]
  | xa i =>
    change f (.xa 0)*(f (.a 1))^i.val=f (.xa i)
    rw [←map_pow,←map_mul,a_one_pow,ZMod.natCast_zmod_val,xa_mul_a,zero_add]
theorem norm_ne_involution_of_inverts_q8Cycle (f : MulAut (QuaternionGroup 2))
    (hf : f*q8Cycle=q8Cycle⁻¹*f) (q:(QuaternionGroup 2)) : q*f q≠(.a 2:(QuaternionGroup 2)) := by
  have hz : f (.a 2)=(.a 2:Q) := by
    have hn : f (.a 2)≠(1:Q) := fun he=>
      (by decide : (.a 2:Q)≠1) (f.injective (he.trans f.map_one.symm))
    have hs : (f (.a 2))^2=(1:Q) := by
      rw [←map_pow,show (.a 2:Q)^2=1 from by decide,map_one]
    exact (by decide : ∀x:Q,x≠1→x^2=1→x=(.a 2:Q)) _ hn hs
  have ha : (f (.a 1))^2=(.a 2:Q) := by rw [←map_pow]; exact hz
  have hb : (f (.xa 0))^2=(.a 2:Q) := by rw [←map_pow]; exact hz
  have hab : f (.a 1)*f (.xa 0)≠f (.xa 0)*f (.a 1) := by
    intro hh
    have he : (.a 1:Q)*(.xa 0)=(.xa 0)*(.a 1) := f.injective (by simpa only [map_mul] using hh)
    exact (by decide : (.a 1:Q)*(.xa 0)≠(.xa 0)*(.a 1)) he
  simpa only [generatorMap_aut] using inversion_norm_table _ _ q ha hb hab
    (by rw [generatorMap_aut]; exact DFunLike.congr_fun hf (.a 1))
    (by rw [generatorMap_aut]; exact DFunLike.congr_fun hf (.xa 0))

theorem norm_ne_involution_of_inverts_cubic (c f : MulAut (QuaternionGroup 2))
    (hc:c^3=1) (hne:c≠1) (hf:f*c=c⁻¹*f) (z:(QuaternionGroup 2)) (hz:orderOf z=2) (q:(QuaternionGroup 2)) :
    q*f q≠z := by
  obtain ⟨e,he⟩ := Subgroup.QuaternionCubicAction.exists_coordinates c hc hne
  let φ:=MulAut.congr e
  have hfe : (φ f)*q8Cycle=q8Cycle⁻¹*(φ f) := by
    rw [←he,←map_inv,←map_mul,←map_mul,hf]
  have hz' : e z=(.a 2:Q) := by
    apply (by decide : ∀x:Q,x≠1→x^2=1→x=(.a 2:Q))
    · intro hh
      have hz1 : z=1 := e.injective (hh.trans e.map_one.symm)
      simp only [hz1,orderOf_one] at hz
      omega
    · have hz2 : z^2=1 := by simpa only [hz] using pow_orderOf_eq_one z
      rw [←map_pow,hz2,map_one]
  intro hh
  apply norm_ne_involution_of_inverts_q8Cycle (φ f) hfe (e q)
  have hh' := congrArg e hh
  simpa [hz',φ,MulAut.congr_apply] using hh'

theorem norm_ne_involution_of_inverts_cubic_of_equiv {B:Type*} [Group B]
    (e:B≃*QuaternionGroup 2) (c f:MulAut B) (hc:c^3=1) (hne:c≠1)
    (hf:f*c=c⁻¹*f) (z:B) (hz:orderOf z=2) (q:B) : q*f q≠z := by
  let φ:=MulAut.congr e
  have hc':(φ c)^3=1 := by rw [←map_pow,hc,map_one]
  have hn':φ c≠1 := fun hh=>hne (φ.injective (hh.trans φ.map_one.symm))
  have hf':(φ f)*(φ c)=(φ c)⁻¹*(φ f) := by rw [←map_inv,←map_mul,←map_mul,hf]
  intro hh
  apply norm_ne_involution_of_inverts_cubic (φ c) (φ f) hc' hn' hf' (e z)
    (by rwa [MulEquiv.orderOf_eq]) (e q)
  simpa [φ,MulAut.congr_apply] using congrArg e hh
end QuaternionGroup
