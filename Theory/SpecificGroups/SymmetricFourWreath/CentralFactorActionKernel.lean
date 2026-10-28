module
public import Theory.SpecificGroups.SymmetricFourWreath.CentralFactorGeometry
/-!
# The kernel of the square action in a dihedral wreath Sylow subgroup

Let S be isomorphic to (D8 wr C2) × D, with D an elementary central factor,
and let Q be any normal extraspecial subgroup of order32. The subgroup
E=Q D is the inverse image of the intrinsic elementary core in the central
quotient. Its central quotient has trivial S-action precisely on E: the
core is self-centralizing, and Z(E) maps trivially to that quotient.
No marking of the quaternion factors of Q is needed.

Source: Aschbacher--Smith, 2.4.29, printed p.545, the kernel of the action
on P T_C/Z(P T_C).
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace SymmetricFourWreath
variable {D S : Type*} [Group D] [Finite D] [IsElementaryAbelian 2 D]
  [Group S] [Finite S] (e : S ≃* P × D) (Q : Subgroup S)
  [Q.Normal] [IsExtraspecial 2 Q] (hQ : Nat.card Q = 32)

noncomputable def markedCentralFactor : Subgroup S :=
  ((MonoidHom.fst P D).comp e.toMonoidHom).ker
noncomputable def extendedCore : Subgroup S := Q ⊔ markedCentralFactor e
noncomputable def markedCentralProjection : S →* CentralQuotient :=
  centralProjection.comp ((MonoidHom.fst P D).comp e.toMonoidHom)

omit [Finite S] [Finite D] in
theorem markedCentralFactor_le_center : markedCentralFactor e ≤ center S := by
  intro x hx
  have hx' : (e x).1=1 := hx
  apply mem_center_iff.mpr
  intro y
  apply e.injective
  rw [map_mul, map_mul]
  apply Prod.ext
  · simp only [Prod.fst_mul, hx', one_mul, mul_one]
  · exact mul_comm _ _

instance extendedCore_normal : (extendedCore e Q).Normal := by
  let : (markedCentralFactor e).Normal := by unfold markedCentralFactor; infer_instance
  exact inferInstanceAs (Q ⊔ markedCentralFactor e).Normal

include hQ in
theorem markedCentralProjection_core : (extendedCore e Q).map (markedCentralProjection e) = quotientCore := by
  let f := ((centralProjection.comp (MonoidHom.fst P D)).prod
    (MonoidHom.snd P D)).comp e.toMonoidHom
  obtain ⟨hf,hk,hJ⟩ := thompson_image_of_equiv_prod e Q hQ
  have hF : (extendedCore e Q).map f = quotientCore.prod ⊤ := by
    exact hJ.symm.trans (thompson_centralQuotient_prod (D:=D))
  have he : (markedCentralProjection e) = (MonoidHom.fst CentralQuotient D).comp f := rfl
  rw [he,←map_map,hF]
  ext c
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hy.1
  · intro hc
    exact ⟨(c,1),⟨hc,mem_top _⟩,rfl⟩

include hQ in
theorem markedCentralProjection_core_comap : quotientCore.comap (markedCentralProjection e) = extendedCore e Q := by
  let f := ((centralProjection.comp (MonoidHom.fst P D)).prod
    (MonoidHom.snd P D)).comp e.toMonoidHom
  obtain ⟨hf,hk,hJ⟩ := thompson_image_of_equiv_prod e Q hQ
  have hF : (extendedCore e Q).map f = quotientCore.prod ⊤ :=
    hJ.symm.trans (thompson_centralQuotient_prod (D:=D))
  have he : quotientCore.comap (markedCentralProjection e) = (quotientCore.prod (⊤:Subgroup D)).comap f := by
    ext x
    exact ⟨fun h=>⟨h,mem_top _⟩,fun h=>h.1⟩
  rw [he,←hF,comap_map_eq,hk]
  exact sup_eq_left.mpr ((map_subtype_le (center Q)).trans le_sup_left)

omit [Finite S] [Finite D] in
theorem markedCentralProjection_ker_center : (markedCentralProjection e).ker = center S := by
  ext x
  change ((e x).1 : P ⧸ centralLine) = 1 ↔ x∈center S
  rw [QuotientGroup.eq_one_iff,←center_P]
  constructor
  · intro hx
    apply mem_center_iff.mpr
    intro y
    apply e.injective
    rw [map_mul, map_mul]
    apply Prod.ext
    · exact mem_center_iff.mp hx (e y).1
    · exact mul_comm _ _
  · intro hx
    apply mem_center_iff.mpr
    intro p
    have hh := congrArg (fun x=>(e x).1) (mem_center_iff.mp hx (e.symm (p,1)))
    simpa only [map_mul,e.apply_symm_apply,Prod.fst_mul] using hh

include hQ in
theorem extendedCore_center_projection (z : center (extendedCore e Q)) :
    markedCentralProjection e (z : S) = 1 := by
  obtain ⟨q,hq,c,hc,he⟩ := mem_sup_of_normal_left.mp (z.val.property)
  have hcZ := markedCentralFactor_le_center e hc
  have hqZ : (⟨q,hq⟩:Q) ∈ center Q := by
    apply mem_center_iff.mpr
    intro p
    apply Subtype.ext
    have hh := congrArg (fun w : extendedCore e Q => (w:S))
      (mem_center_iff.mp z.property (⟨p,mem_sup_left p.property⟩:extendedCore e Q))
    change (p:S)*(z:S)=(z:S)*(p:S) at hh
    rw [←he, ←mul_assoc] at hh
    rw [mul_assoc q c p, (mem_center_iff.mp hcZ p).symm, ←mul_assoc] at hh
    exact mul_right_cancel hh
  let f := ((centralProjection.comp (MonoidHom.fst P D)).prod
    (MonoidHom.snd P D)).comp e.toMonoidHom
  obtain ⟨hf,hk,_⟩ := thompson_image_of_equiv_prod e Q hQ
  have hqk : q ∈ f.ker := by rw [hk]; exact mem_map_of_mem Q.subtype hqZ
  have hqg : markedCentralProjection e q=1 := congrArg Prod.fst hqk
  have hcg : markedCentralProjection e c=1 := by
    change centralProjection (e c).1=1
    rw [show (e c).1=1 from hc,map_one]
  change markedCentralProjection e (z:S)=1
  rw [←he,map_mul,hqg,hcg,mul_one]

include hQ in
theorem extendedCore_quotient_action_ker :
    ((quotientAut (center (extendedCore e Q))).comp
      (MulAut.conjNormal : S →* MulAut (extendedCore e Q))).ker = extendedCore e Q := by
  let E := extendedCore e Q
  let g := markedCentralProjection e
  have hgE : E.map g = quotientCore := markedCentralProjection_core e Q hQ
  have hgcomap : quotientCore.comap g = E := markedCentralProjection_core_comap e Q hQ
  have hker : g.ker = center S := markedCentralProjection_ker_center e
  ext s
  change quotientAut (center E) (MulAut.conjNormal s) = 1 ↔ s∈E
  constructor
  · intro hs
    have hcentral : g s ∈ centralizer (quotientCore:Set CentralQuotient) := by
      intro c hc
      rw [←hgE] at hc
      obtain ⟨y,hy,rfl⟩ := hc
      let yy : E := ⟨y,hy⟩
      have hh := DFunLike.congr_fun hs (QuotientGroup.mk' (center E) yy)
      rw [quotientAut_apply_mk] at hh
      have hz : yy⁻¹ * MulAut.conjNormal s yy ∈ center E := QuotientGroup.eq.mp hh.symm
      have hp := extendedCore_center_projection e Q hQ ⟨_,hz⟩
      change g (y⁻¹*(s*y*s⁻¹))=1 at hp
      rw [map_mul,map_inv,map_mul,map_mul,map_inv] at hp
      have he : g s * g y * (g s)⁻¹ = g y := by
        exact (inv_mul_eq_one.mp hp).symm
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    rw [centralizer_quotientCore] at hcentral
    change s ∈ quotientCore.comap g at hcentral
    rwa [hgcomap] at hcentral
  · intro hs
    apply MulEquiv.ext
    intro q
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (center E) q
    rw [quotientAut_apply_mk]
    apply QuotientGroup.eq.mpr
    apply mem_center_iff.mpr
    intro v
    apply Subtype.ext
    have hs' : g s ∈ quotientCore := by rw [←hgcomap] at hs; exact hs
    have hy : g (y:S) ∈ quotientCore := by rw [←hgE]; exact mem_map_of_mem g y.property
    have hcomm : g s * g y = g y * g s :=
      congrArg Subtype.val (quotientCore_elementary.is_comm.comm (⟨g s,hs'⟩:quotientCore) ⟨g y,hy⟩)
    have hgz : g ((MulAut.conjNormal s y : E)⁻¹*y:S)=1 := by
      change g ((s*y*s⁻¹)⁻¹*y)=1
      rw [map_mul,map_inv,map_mul,map_mul,map_inv,hcomm,mul_inv_cancel_right,inv_mul_cancel]
    have hz : ((MulAut.conjNormal s y : E)⁻¹*y:S)∈center S := hker ▸ hgz
    exact mem_center_iff.mp hz v

end SymmetricFourWreath
