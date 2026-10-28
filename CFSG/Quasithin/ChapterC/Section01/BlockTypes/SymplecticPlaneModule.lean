module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.SpecificGroups.SymplecticFour.PlaneNaturalQuotient
public import Theory.GroupTheory.PCoreImage

/-!
# The plane quotient of a symplectic block layer

A nonzero locally commutator-generated subgroup has nonzero image in the
central quotient U/C_U(X). If the original local two-core fixes it and the
local image is the plane residual, its image is exactly the distinguished
plane. The natural quotient map therefore has kernel W C_U(X), and its
action agrees with the original plane-local SL₂ quotient after the explicit
dual-coordinate correction. No containment of C_U(X) in W is assumed here.

The rank-one source application supplies W as the actual full module and
constructs all the local subgroup hypotheses. Final source assembly remains
with qt-d-1222-rankone-uniqueness-block.
Source: Aschbacher–Smith C.4.1(2), I.2.3 and original 4.3.7,
printed pp.151,413 and616.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC
variable {X : Type*} [Group X] [Finite X] {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The full local image in the original central quotient is the natural plane. -/
theorem BlockModuleModel.symplectic_plane_image
    (hF : Nat.card F = 4)
    {rho : Sp F →* MulAut (Multiplicative (Vector F))}
    (m : BlockModuleModel X rho)
    (hrho : ∀ g v, (rho g v).toAdd = g.val.mulVec v.toAdd)
    (A W : Subgroup X) (hWU : W ≤ blockU X) (hne : W ≠ ⊥)
    (hcomm : ⁅W,A⁆ = W)
    (hfix : W ≤ centralizer (A.pCoreIn 2 : Set X))
    (hA : A.map (m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))) =
      planeLocal) :
    ((W.subgroupOf (blockU X)).map
      (m.moduleIso.toMonoidHom.comp (QuotientGroup.mk' (blockFixed X)))).toAddSubgroup' =
        (plane F).toAddSubgroup := by
  let p := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  let q := m.moduleIso.toMonoidHom.comp (QuotientGroup.mk' (blockFixed X))
  let Q := (W.subgroupOf (blockU X)).map q
  have hp : p.ker = pCore 2 X := by
    rw [MonoidHom.ker_comp_of_injective _ _ m.quotientIso.injective,QuotientGroup.ker_mk']
  have hk : q.ker = blockFixed X := by
    rw [MonoidHom.ker_comp_of_injective _ _ m.moduleIso.injective,QuotientGroup.ker_mk']
  have hcore : (A.pCoreIn 2).map p = planeRadicalAmbient := by
    rw [map_pCoreIn_of_ker_isPGroup p (hp ▸ pCore_isPGroup), hA]
    change (pCore 2 (planeLocal (F := F))).map planeLocal.subtype = _
    rw [planeLocal_core_eq (n := 2) hF (by decide)]
  have hq (a : X) (u : blockU X) :
      (q (blockConjugate X a u)).toAdd = (p a).val.mulVec (q u).toAdd := by
    change (m.moduleIso (QuotientGroup.mk' _ (blockConjugate X a u))).toAdd = _
    rw [m.intertwining,hrho]
    rfl
  have hWn : A ≤ normalizer (W : Set X) := by
    rw [le_normalizer_iff_commutator_le_right,commutator_comm,hcomm]
  have hQ : ∀ g ∈ planeLocal, ∀ v ∈ Q.toAddSubgroup', g.val.mulVec v ∈ Q.toAddSubgroup' := by
    rw [←hA]
    rintro g ⟨a,ha,rfl⟩ v ⟨u,hu,huv⟩
    refine ⟨blockConjugate X a u,?_,?_⟩
    · exact (mem_normalizer_iff.mp (hWn ha) (u : X)).mp hu
    · apply Multiplicative.toAdd.injective
      rw [hq,huv]
      rfl
  have hQne : Q.toAddSubgroup' ≠ ⊥ := by
    intro he
    have hWZ : W ≤ center X := by
      intro w hw
      let u : blockU X := ⟨w,hWU hw⟩
      have hmem : (q u).toAdd ∈ Q.toAddSubgroup' := ⟨u,hw,rfl⟩
      rw [he] at hmem
      have hu : u ∈ q.ker := hmem
      rw [hk] at hu
      exact hu
    have hc : ⁅W,A⁆ = ⊥ := by
      apply commutator_eq_bot_iff_le_centralizer.mpr
      intro w hw a _
      exact mem_center_iff.mp (hWZ hw) a
    exact hne (hcomm.symm.trans hc)
  apply PlaneNatural.invariant_additive_eq_plane Q.toAddSubgroup' hQne _ hQ
  rintro v ⟨w,hw,rfl⟩
  apply NaturalScalarCubic.plane_radical_fixed
  intro r hr
  rw [←hcore] at hr
  obtain ⟨a,ha,rfl⟩ := hr
  change (p a).val.mulVec (q w).toAdd = (q w).toAdd
  rw [←hq]
  congr 2
  apply Subtype.ext
  exact mul_inv_eq_iff_eq_mul.mpr (hfix hw a ha)

/-- Natural quotient coordinates with the complete central layer retained in the kernel. -/
theorem BlockModuleModel.symplectic_natural_quotient
    (hF : Nat.card F = 4)
    {rho : Sp F →* MulAut (Multiplicative (Vector F))}
    (m : BlockModuleModel X rho)
    (hrho : ∀ g v, (rho g v).toAdd = g.val.mulVec v.toAdd)
    (A W : Subgroup X) (hWU : W ≤ blockU X) (hne : W ≠ ⊥)
    (hcomm : ⁅W,A⁆ = W)
    (hfix : W ≤ centralizer (A.pCoreIn 2 : Set X))
    (hA : A.map (m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))) =
      planeLocal) :
    ∃ f : blockU X →* Multiplicative (Fin 2 → F), Function.Surjective f ∧
      f.ker = (W ⊔ (blockU X ⊓ center X)).subgroupOf (blockU X) ∧
      ∀ (a : X) (ha : a ∈ A) (u : blockU X),
        f (blockConjugate X a u) = Multiplicative.ofAdd
          ((Plane.quotientMap ⟨m.quotientIso (QuotientGroup.mk' (pCore 2 X) a),
            hA ▸ mem_map_of_mem _ ha⟩).val.mulVec (f u).toAdd) := by
  let q := m.moduleIso.toMonoidHom.comp (QuotientGroup.mk' (blockFixed X))
  let f := PlaneNatural.quotient.toAddMonoidHom.toMultiplicative.comp q
  have hsurj : Function.Surjective q :=
    m.moduleIso.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = blockFixed X := by
    rw [MonoidHom.ker_comp_of_injective _ _ m.moduleIso.injective,QuotientGroup.ker_mk']
  have himage := m.symplectic_plane_image hF hrho A W hWU hne hcomm hfix hA
  let Q := (W.subgroupOf (blockU X)).map q
  have hpre : (Q.comap q).map (blockU X).subtype = W ⊔ (blockU X ⊓ center X) := by
    rw [Subgroup.comap_map_eq,Subgroup.map_sup,hk,
      map_subgroupOf_eq_of_le hWU,blockFixed_map]
  refine ⟨f,?_,?_,?_⟩
  · intro v
    obtain ⟨w,hw⟩ := PlaneNatural.quotient_surjective v.toAdd
    obtain ⟨u,hu⟩ := hsurj (Multiplicative.ofAdd w)
    exact ⟨u,by change Multiplicative.ofAdd (PlaneNatural.quotient (q u).toAdd) = v; rw [hu]; exact congrArg Multiplicative.ofAdd hw⟩
  · ext u
    change f u = 1 ↔ u.val ∈ W ⊔ (blockU X ⊓ center X)
    rw [←hpre]
    change f u = 1 ↔ (blockU X).subtype u ∈ (Q.comap q).map (blockU X).subtype
    rw [mem_map_iff_mem (blockU X).subtype_injective]
    change PlaneNatural.quotient (q u).toAdd = 0 ↔ (q u).toAdd ∈ Q.toAddSubgroup'
    rw [PlaneNatural.quotient_eq_zero,himage]
    rfl
  · intro a ha u
    apply Multiplicative.toAdd.injective
    change PlaneNatural.quotient
      (m.moduleIso (QuotientGroup.mk' (blockFixed X) (blockConjugate X a u))).toAdd = _
    rw [m.intertwining,hrho]
    exact PlaneNatural.quotient_action
      ⟨m.quotientIso (QuotientGroup.mk' (pCore 2 X) a),hA ▸ mem_map_of_mem _ ha⟩
      (q u).toAdd

end CFSG.Quasithin.ChapterC
