module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairNormal

/-!
# Lifting normality to the original pair and its two-residual

The actual cubic rotation lies in the two-residual R of I, and hence
I=RV. The normalizing two-group VO₂(H) gives O²(IO₂(H))=R. Thus normality
of the quotient pair first lifts to R. The original L₁T normalizes V,
so H=L₁IT implies that I itself is normal in H.

This constructs the original normal pair used to eliminate C_T(L) in
13.5.15(7). It retains its exact two-core U_H and order-six quotient.
Source: Aschbacher–Smith13.5.15, printed p.920.
-/
@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairResidualNormal
open Section08.SourceCompletion
open SourcePairNormal SourceOrthogonal SourceOddRotation
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
  (hseed : D.Vplus=⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)

omit [Finite G] d h e hseed hn hU in
theorem pair_eq_residual_sup_module (v r:G) (hv:v∈D.V) (hv2:v^2=1)
    (hr:orderOf r=3) (hi:v*r*v⁻¹=r⁻¹) :
    let I:=D.V⊔D.V.map (MulAut.conj r).toMonoidHom
    I=(pResidual 2 I).map I.subtype⊔D.V := by
  dsimp only
  let I:=D.V⊔D.V.map (MulAut.conj r).toMonoidHom
  let R:=(pResidual 2 I).map I.subtype
  have hrI:r∈I:=rotation_mem_pair v r hv hv2 (by decide:Nat.Prime 3) (by decide) hr hi
  have hrR:r∈R:=by
    apply mem_map_of_mem I.subtype (x:=⟨r,hrI⟩)
    apply mem_pResidual_of_orderOf_coprime
    rw [←orderOf_coe (⟨r,hrI⟩:I),hr]
    decide
  apply le_antisymm ?_ (sup_le (map_subtype_le _) le_sup_left)
  apply sup_le le_sup_right
  rintro _ ⟨x,hx,rfl⟩
  exact (R⊔D.V).mul_mem ((R⊔D.V).mul_mem (mem_sup_left hrR) (mem_sup_right hx))
    ((R⊔D.V).inv_mem (mem_sup_left hrR))

include d h e hseed hn hU

/-- The two-residual of the selected original I is normal in H. -/
theorem whole_normalizes_pair_residual (v r:G) (hv:v∈D.V) (hv2:v^2=1)
    (hr:orderOf r=3) (hrH:r∈D.H) (hi:v*r*v⁻¹=r⁻¹) :
    let I:=D.V⊔D.V.map (MulAut.conj r).toMonoidHom
    D.H≤normalizer ((pResidual 2 I).map I.subtype:Set G) := by
  dsimp only
  let I:=D.V⊔D.V.map (MulAut.conj r).toMonoidHom
  let R:=(pResidual 2 I).map I.subtype
  let P:=D.V⊔D.QH
  have hp:¬IsPGroup 2 (Section08.Source.starImage D.H I):=
    (odd_rotation_is_cubic d h e hseed hn hU v r hv hv2
      (by decide:Nat.Prime 3) (by decide) hr hrH hi).2
  have hj:=original_star_pair_symmetricThree d h e hseed hn hU r hrH hp
  have hIQ:=whole_normalizes_pair_core d h e hseed hn hU r hrH hj
  have hQR:D.QH≤normalizer (R:Set G):=
    (SourcePairCore.twoCore_normalizes_pair d h hU r hrH).trans
      (normalizer_le_normalizer_characteristic_image I (pResidual 2 I))
  have hVR:D.V≤normalizer (R:Set G):=
    (le_sup_left.trans I.le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image I (pResidual 2 I))
  have hP:IsPGroup 2 P:=D.T.isPGroup'.to_le (sup_le h.V_le_T h.QH_le_T)
  have he:=embedded_pResidual_join_pGroup R P (isPPerfect_embedded_pResidual 2 I)
    hP (sup_le hVR hQR)
  have hjoin:R⊔P=I⊔D.QH:=by
    change R⊔(D.V⊔D.QH)=I⊔D.QH
    rw [←sup_assoc,←pair_eq_residual_sup_module v r hv hv2 hr hi]
  rw [hjoin] at he
  have hnorm:=hIQ.trans (normalizer_le_normalizer_characteristic_image
    (I⊔D.QH) (pResidual 2 (I⊔D.QH:Subgroup G)))
  rwa [he] at hnorm

/-- The source I itself is normal in H, after lifting through its two-residual. -/
theorem whole_normalizes_pair (v r:G) (hv:v∈D.V) (hv2:v^2=1)
    (hr:orderOf r=3) (hrH:r∈D.H) (hi:v*r*v⁻¹=r⁻¹) :
    D.H≤normalizer ((D.V⊔D.V.map (MulAut.conj r).toMonoidHom:Subgroup G):Set G) := by
  let I:=D.V⊔D.V.map (MulAut.conj r).toMonoidHom
  let R:=(pResidual 2 I).map I.subtype
  have hR:=whole_normalizes_pair_residual d h e hseed hn hU v r hv hv2 hr hrH hi
  have he:I=R⊔D.V:=pair_eq_residual_sup_module v r hv hv2 hr hi
  have hlocal:D.L₁⊔(D.T:Subgroup G)≤normalizer (I:Set G):=by
    rw [he]
    apply (le_inf (h.local_le.trans hR) ?_).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
    exact (sup_le_sup ((map_subtype_le _).trans inf_le_left) le_rfl).trans d.normalizes_V
  have hp:¬IsPGroup 2 (Section08.Source.starImage D.H I):=
    (odd_rotation_is_cubic d h e hseed hn hU v r hv hv2
      (by decide:Nat.Prime 3) (by decide) hr hrH hi).2
  have hj:=original_star_pair_symmetricThree d h e hseed hn hU r hrH hp
  rw [whole_generated d h e hseed hn hU r hrH hj]
  exact sup_le (sup_le (le_sup_left.trans hlocal) I.le_normalizer) (le_sup_right.trans hlocal)

/-- The actual original source pair has every property used in the next
core-elimination paragraph of13.5.15. -/
theorem exists_original_normal_pair :
    ∃r∈D.H,orderOf r=3 ∧
      let I:=D.V⊔D.V.map (MulAut.conj r).toMonoidHom
      I.pCoreIn 2=D.UH ∧
      Nonempty ((Section08.Source.starImage D.H I)≃*Equiv.Perm (Fin 3)) ∧
      D.H=D.L₁⊔I⊔(D.T:Subgroup G) ∧
      D.H≤normalizer (I:Set G) ∧
      D.H≤normalizer ((pResidual 2 I).map I.subtype:Set G) ∧
      I=(pResidual 2 I).map I.subtype⊔D.V := by
  obtain ⟨v,hv,hvq,hv2,p,hp,hp2,r,hrH,hr,hi⟩:=exists_odd_rotation h hU
  obtain ⟨hp3,hpair⟩:=odd_rotation_is_cubic d h e hseed hn hU v r hv hv2 hp hp2 hr hrH hi
  have hr3:orderOf r=3:=hr.trans hp3
  have hj:=original_star_pair_symmetricThree d h e hseed hn hU r hrH hpair
  exact ⟨r,hrH,hr3,
    SourcePairExact.core_eq_closure d h e hseed hn hU v r hv hvq hv2 hr3 hrH hi,hj,
    whole_generated d h e hseed hn hU r hrH hj,
    whole_normalizes_pair d h e hseed hn hU v r hv hv2 hr3 hrH hi,
    whole_normalizes_pair_residual d h e hseed hn hU v r hv hv2 hr3 hrH hi,
    pair_eq_residual_sup_module v r hv hv2 hr3 hi⟩

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairResidualNormal
end
