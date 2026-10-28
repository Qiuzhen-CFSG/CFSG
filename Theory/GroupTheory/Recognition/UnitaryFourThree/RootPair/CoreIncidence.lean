module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.CoreIntersection
public import Theory.GroupTheory.CentralizerResidualProducts

/-!
# Symmetric incidence of the canonical conjugate cores

The core is the actual two-core of the embedded two-residual of each
involution centralizer. Naturality transports the genuine returning-pair
inclusion to any pair in the original involution class, proving symmetry
of membership without any assumed polarity or chosen core marking.
Source: Aschbacher, Sporadic Groups (1994), 8.15 and45.6, pp.29–30,244.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {z:G}

theorem map_core (e:G≃*G) (x:G) : (core x).map e.toMonoidHom=core (e x) :=
  Theory.GroupTheory.map_centralizerResidualCore e x

theorem mem_core_map_iff (e:G≃*G) (x y:G) : e x∈core (e y) ↔ x∈core y := by
  rw [←map_core e y,mem_map_equiv]
  simp only [MulEquiv.symm_apply_apply]

theorem mem_own_core_of_fused (h:IsType z) (x:G) (hx:IsConj z x) : x∈core x := by
  obtain ⟨g,hg⟩:=isConj_iff.mp hx
  let e:=MulAut.conj g
  have he : e z=x := hg
  rw [←he]
  exact (mem_core_map_iff e z z).mpr (RootPair.z_mem_core h)

omit [Finite G] in
private theorem mem_line_eq_of_involution (h:IsType z) (x:G) (hx:x∈zpowers z) (hx2:orderOf x=2) : x=z := by
  have hc : Nat.card (zpowers z)=2 := by rw [Nat.card_zpowers,h.involution]
  obtain ⟨a,_,hall⟩ := (Nat.card_eq_two_iff' (1:zpowers z)).mp hc
  have hxne:x≠1 := by intro he; simp [he] at hx2
  have hzne:z≠1 := by intro he; have hh:=h.involution; simp [he] at hh
  have hx' := hall ⟨x,hx⟩ (fun he=>hxne (congrArg Subtype.val he))
  have hz' := hall ⟨z,mem_zpowers z⟩ (fun he=>hzne (congrArg Subtype.val he))
  exact congrArg Subtype.val (hx'.trans hz'.symm)

private theorem mutual_original_core (h:IsType z) (x:G) (hx:IsConj z x) (hxQ:x∈core z) : z∈core x := by
  obtain ⟨g,hg⟩:=isConj_iff.mp hx
  have ho : orderOf x=2 := by rw [←hg]; exact (MulAut.conj g).orderOf_eq z |>.trans h.involution
  by_cases hxZ:x∈zpowers z
  · rw [mem_line_eq_of_involution h x hxZ ho]
    exact RootPair.z_mem_core h
  · let P:RootPair z := ⟨g⁻¹,by simpa only [inv_inv,hg] using hxQ,by simpa only [inv_inv,hg] using hxZ⟩
    have he : P.conjugateCore=core x := by
      change (core z).map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom=core x
      rw [inv_inv,map_core]
      exact congrArg core hg
    exact he ▸ P.z_mem_conjugateCore h

private theorem core_incidence_forward (h:IsType z) (x y:G) (hx:IsConj z x) (hy:IsConj z y)
    (hyx:y∈core x) : x∈core y := by
  obtain ⟨g,hg⟩:=isConj_iff.mp hx
  let e:=MulAut.conj g⁻¹
  have hex:e x=z := by rw [←hg]; simp [e,mul_assoc]
  have hy' : e y∈core z := by
    rw [←hex]
    exact (mem_core_map_iff e y x).mpr hyx
  have hzy' : IsConj z (e y) := hy.trans (isConj_iff.mpr ⟨g⁻¹,rfl⟩)
  have hh : z∈core (e y) := mutual_original_core h (e y) hzy' hy'
  rw [←hex] at hh
  exact (mem_core_map_iff e x y).mp hh

/-- Membership in the actual conjugate cores is symmetric on the source involution class. -/
theorem core_incidence_symmetric (h:IsType z) (x y:G) (hx:IsConj z x) (hy:IsConj z y) :
    x∈core y ↔ y∈core x :=
  ⟨core_incidence_forward h y x hy hx,core_incidence_forward h x y hx hy⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree
