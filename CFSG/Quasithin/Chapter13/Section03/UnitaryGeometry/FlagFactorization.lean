module

public import CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry.ModelReduction
public import Theory.Representation.G2BinaryIsotropicThree.PointParabolic
public import Theory.GroupTheory.InvolutionCentralizerControl


/-!
# The original unitary three-space conjugator adjustment

The actual derived G₂(2) point stabilizer realizes every linear automorphism
of the marked three-space fixing its first point. Lifting this element through
the original induced automizer writes a flag-preserving conjugator as a local
element times an element of the three-space centralizer. The TI hypothesis and
a nonzero commutator with the conjugate module then force that centralizer to
escape M. The three-space coordinates are constructed from the literal
subspace image; no extra three-dimensional module identification is required.

This is the final adjustment in Aschbacher–Smith 13.3.12(4), printed p.890.
The preceding offender argument must still produce a conjugator preserving the
actual point and three-space. That source step is not asserted here.
-/

public section

open Subgroup Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
open Atlas.G2.Natural.BinaryIsotropicThree
variable {G : Type*} [Group G] {V R L M : Subgroup G}
  [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 R]

theorem exists_three_coordinates (hRV : R≤V) (E : Additive V≃ₗ[ZMod 2] W)
    (hR : (ambientSpace (V:=V) R).map E.toLinearMap=target false) :
    ∃F : Additive R≃ₗ[ZMod 2] Three,
      ∀r : Additive R,E (Additive.ofMul ⟨r.toMul.val,hRV r.toMul.property⟩)=
        targetEmbed false (F r) := by
  let j : Additive R→ₗ[ZMod 2] Additive V :=
    (Subgroup.inclusion hRV).toAdditive.toZModLinearMap 2
  have hj (r : Additive R) : E (j r)∈target false := by
    rw [←hR]
    exact ⟨j r,r.toMul.property,rfl⟩
  let l : Additive R→ₗ[ZMod 2] target false :=
    (E.toLinearMap.comp j).codRestrict (target false) hj
  have hi : Function.Injective l := by
    intro a b hh
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg (fun v : Additive V=>v.toMul.val) (E.injective (congrArg Subtype.val hh))
  have hs : Function.Surjective l := by
    intro w
    have hw : w.val∈(ambientSpace (V:=V) R).map E.toLinearMap := by
      rw [hR]
      exact w.property
    obtain ⟨v,hv,hvw⟩ := hw
    refine ⟨Additive.ofMul ⟨v.toMul.val,hv⟩,?_⟩
    apply Subtype.ext
    exact hvw
  let F := (LinearEquiv.ofBijective l ⟨hi,hs⟩).trans (targetEquiv false).symm
  refine ⟨F,?_⟩
  intro r
  exact (congrArg Subtype.val ((targetEquiv false).apply_symm_apply (l r))).symm

theorem point_three_factorization
    (hRV : R≤V) (E : Additive V≃ₗ[ZMod 2] W) (F : Additive R≃ₗ[ZMod 2] Three)
    (hF : ∀r : Additive R,E (Additive.ofMul ⟨r.toMul.val,hRV r.toMul.property⟩)=
      targetEmbed false (F r))
    (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hderived : ∀d : commutator (Atlas.G2.Model K),
      ∃a∈inducedAutomizer V L,f a=d.val)
    (g : G) (hgR : g∈normalizer (R:Set G))
    (hpoint : Commute g (F.symm ![1,0,0]).toMul.val) :
    ∃n∈L,n⁻¹*g∈centralizer (R:Set G) := by
  let gn : normalizer (R:Set G) := ⟨g,hgR⟩
  let aR : Automizer R := R.normalizerMonoidHom.rangeRestrict gn
  let A₀ := LinearEquiv.ofBijective (automizerRepresentation R aR)
    ((automizerRepresentation R).apply_bijective aR)
  let A := F.symm.trans (A₀.trans F)
  have hA : A ![1,0,0]=![1,0,0] := by
    have hz : automizerRepresentation R aR (F.symm ![1,0,0])=F.symm ![1,0,0] := by
      change R.normalizerMonoidHom gn (F.symm ![1,0,0]).toMul=(F.symm ![1,0,0]).toMul
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      change g*(F.symm ![1,0,0]).toMul.val*g⁻¹=(F.symm ![1,0,0]).toMul.val
      rw [hpoint.eq,mul_inv_cancel_right]
    change F (automizerRepresentation R aR (F.symm ![1,0,0]))=![1,0,0]
    rw [hz,F.apply_symm_apply]
  obtain ⟨d,hd⟩ := realize_point_fixed_equiv_derived A hA
  obtain ⟨a,ha,hfa⟩ := hderived d
  obtain ⟨n,hn,hna⟩ := ha
  have hconj (r : Additive R) : n.val*r.toMul.val*n.val⁻¹=g*r.toMul.val*g⁻¹ := by
    let j : Additive R→Additive V := fun r=>Additive.ofMul ⟨r.toMul.val,hRV r.toMul.property⟩
    have hlin : E (automizerRepresentation V a (j r))=
        E (j (automizerRepresentation R aR r)) := by
      rw [he,hF r,hfa,hd]
      change targetEmbed false (F (automizerRepresentation R aR (F.symm (F r))))=_
      rw [F.symm_apply_apply]
      exact (hF (automizerRepresentation R aR r)).symm
    rw [←hna] at hlin
    have hval := congrArg (fun v : Additive V=>v.toMul.val) (E.injective hlin)
    exact hval
  refine ⟨n.val,hn,Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro u hu
  have hc : n.val*u*n.val⁻¹=g*u*g⁻¹ := hconj (Additive.ofMul ⟨u,hu⟩)
  have hfix : (n.val⁻¹*g)*u*(n.val⁻¹*g)⁻¹=u := by
    calc
      (n.val⁻¹*g)*u*(n.val⁻¹*g)⁻¹=n.val⁻¹*(g*u*g⁻¹)*n.val := by group
      _=n.val⁻¹*(n.val*u*n.val⁻¹)*n.val := by rw [←hc]
      _=u := by group
  exact (mul_inv_eq_iff_eq_mul.mp hfix).symm

theorem centralizer_three_escape_of_normalizing_element
    (hRV : R≤V) (E : Additive V≃ₗ[ZMod 2] W) (F : Additive R≃ₗ[ZMod 2] Three)
    (hF : ∀r : Additive R,E (Additive.ofMul ⟨r.toMul.val,hRV r.toMul.property⟩)=
      targetEmbed false (F r))
    (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hderived : ∀d : commutator (Atlas.G2.Model K),
      ∃a∈inducedAutomizer V L,f a=d.val)
    (hLM : L≤M) (g : G) (hgR : g∈normalizer (R:Set G))
    (hpoint : Commute g (F.symm ![1,0,0]).toMul.val) (hgM : g∉M) :
    ¬centralizer (R:Set G)≤M := by
  intro hc
  obtain ⟨n,hn,hnc⟩ := point_three_factorization hRV E F hF f he hderived g hgR hpoint
  apply hgM
  have hh := M.mul_mem (hLM hn) (hc hnc)
  simpa only [mul_inv_cancel_left] using hh
theorem centralizer_three_escape_of_noncommuting_conjugate
    (hTI : ∀g∈M,V⊓V.map (MulAut.conj g).toMonoidHom=⊥ ∨
      V.map (MulAut.conj g).toMonoidHom=V)
    (hRV : R≤V) (E : Additive V≃ₗ[ZMod 2] W) (F : Additive R≃ₗ[ZMod 2] Three)
    (hF : ∀r : Additive R,E (Additive.ofMul ⟨r.toMul.val,hRV r.toMul.property⟩)=
      targetEmbed false (F r))
    (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hderived : ∀d : commutator (Atlas.G2.Model K),
      ∃a∈inducedAutomizer V L,f a=d.val)
    (hLM : L≤M) (g : G) (hgR : g∈normalizer (R:Set G))
    (hpoint : Commute g (F.symm ![1,0,0]).toMul.val)
    (hcomm : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆≠⊥) :
    ¬centralizer (R:Set G)≤M := by
  have hR : R≠⊥ := by
    intro hb
    have hzero : (F.symm ![1,0,0]).toMul=1 := by
      apply Subtype.ext
      exact hb ▸ (F.symm ![1,0,0]).toMul.property
    have hh : F.symm ![1,0,0]=0 := hzero
    have hbad := congrArg F hh
    simpa using congrFun hbad 0
  apply centralizer_three_escape_of_normalizing_element hRV E F hF f he hderived hLM g hgR hpoint
  intro hgM
  have hgV := Subgroup.inf_normalizer_le_of_trivial_intersections hTI hR hRV ⟨hgM,hgR⟩
  have hfix : V.map (MulAut.conj g).toMonoidHom=V :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hgV
  apply hcomm
  rw [hfix]
  exact Subgroup.commutator_self_eq_bot_iff.mpr inferInstance

theorem centralizer_three_escape_of_flag
    (hTI : ∀g∈M,V⊓V.map (MulAut.conj g).toMonoidHom=⊥ ∨
      V.map (MulAut.conj g).toMonoidHom=V)
    (hRV : R≤V) (E : Additive V≃ₗ[ZMod 2] W)
    (hR : (ambientSpace (V:=V) R).map E.toLinearMap=target false)
    (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hderived : commutator (Atlas.G2.Model K)≤(inducedAutomizer V L).map f)
    (hLM : L≤M) (Z : Subgroup G) (hZ : Nat.card Z=2)
    (hz : (E.symm (targetEmbed false ![1,0,0])).toMul.val∈Z)
    (g : G) (hgR : g∈normalizer (R:Set G)) (hgZ : g∈normalizer (Z:Set G))
    (hcomm : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆≠⊥) :
    ¬centralizer (R:Set G)≤M := by
  obtain ⟨F,hF⟩ := exists_three_coordinates hRV E hR
  have hp : (F.symm ![1,0,0]).toMul.val=
      (E.symm (targetEmbed false ![1,0,0])).toMul.val := by
    have hh := hF (F.symm ![1,0,0])
    rw [F.apply_symm_apply] at hh
    exact congrArg (fun v : Additive V=>v.toMul.val)
      (E.injective (hh.trans (E.apply_symm_apply _).symm))
  have hpoint : Commute g (F.symm ![1,0,0]).toMul.val := by
    rw [hp]
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.normalizer_le_centralizer_of_card_two Z hZ hgZ) _ hz).symm
  apply centralizer_three_escape_of_noncommuting_conjugate hTI hRV E F hF f he _ hLM g hgR hpoint hcomm
  intro d
  exact hderived d.property

variable [Finite G] {K₀ : GroupClass} {T : Sylow 2 G}

/-- The literal E.6.1 source setup supplies TI for the final 13.3.12(4)
flag-preserving conjugator. The preceding offender/flag producer remains
explicit through the two actual normalizer memberships. -/
theorem source_intersection_escape_of_flag
    (h : ChapterE.Section06.HypothesisE61 K₀ T M V)
    (hRV : R≤V) (E : Additive V≃ₗ[ZMod 2] W)
    (hR : (ambientSpace (V:=V) R).map E.toLinearMap=target false)
    (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hderived : commutator (Atlas.G2.Model K)≤(inducedAutomizer V L).map f)
    (hLM : L≤M) (Z : Subgroup G) (hZ : Nat.card Z=2)
    (hz : (E.symm (targetEmbed false ![1,0,0])).toMul.val∈Z)
    (g : G) (hgR : g∈normalizer (R:Set G)) (hgZ : g∈normalizer (Z:Set G))
    (hcomm : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆≠⊥) :
    ¬centralizer (R:Set G)≤M :=
  centralizer_three_escape_of_flag h.ti hRV E hR f he hderived hLM Z hZ hz g hgR hgZ hcomm

end CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry
