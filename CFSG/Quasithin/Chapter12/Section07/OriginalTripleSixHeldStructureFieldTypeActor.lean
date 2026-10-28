module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldFourNormalizerStructureSplit

/-! The same explicit affine complement actor is retained inside the
normalizer of the original module U, as required for projective field type. -/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Atlas.Codes
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

theorem original_tripleSix_escaping_four_actor_preserves_module
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G)) :
    ∃ L : Subgroup G, L ≤ normalizer (tripleSixPoint D a t : Set G) ∧
      L ≤ normalizer (U : Set G) ∧ Nonempty (L ≃* Equiv.Perm (Fin 3)) ∧
      L ⊓ centralizer (tripleSixPoint D a t : Set G) = ⊥ := by
  let M := normalizer (K : Set G)
  let V := tripleSixPoint D a t
  let e := tripleSixPointCoordinates D a
  let v := (e t).toAdd
  let A := Submodule.span Hexacode.F {v}
  have hUM : U≤M := D.le_component.trans K.le_normalizer
  obtain ⟨_,_,_,_,E,hE,_,_⟩ := original_tripleSix_escaping_full_affine_model
    h structural D a t ht heven hout
  let j : HexAutomorphisms →* G := M.subtype.comp
    (E.symm.toMonoidHom.comp SemidirectProduct.inr)
  have hj : Function.Injective j := M.subtype_injective.comp
    (E.symm.injective.comp SemidirectProduct.inr_injective)
  have hjact (g : HexAutomorphisms) (u : U) :
      j g * (u:G) * (j g)⁻¹ = (e.symm (hexAffineAction g (e u)) : G) := by
    have hm : E.symm (SemidirectProduct.inr g) * inclusion hUM u *
        (E.symm (SemidirectProduct.inr g))⁻¹ =
          inclusion hUM (e.symm (hexAffineAction g (e u))) := by
      apply E.injective
      rw [map_mul,map_mul,map_inv,E.apply_symm_apply,hE,hE,e.apply_symm_apply]
      simpa only [map_inv] using (SemidirectProduct.inl_aut (φ := hexAffineAction) g (e u)).symm
    exact congrArg Subtype.val hm
  have hpoint (u : U) : (u:G)∈V ↔ (e u).toAdd∈A := by
    change (u:G)∈(A.toAddSubgroup.toSubgroup.comap e.toMonoidHom).map U.subtype ↔ _
    constructor
    · rintro ⟨w,hw,he⟩
      exact (Subtype.ext he : w=u) ▸ hw
    · intro hu
      exact ⟨u,hu,rfl⟩
  have hv : v≠0 := fun hv => ht (e.injective (by
    rw [e.map_one]
    exact hv))
  have hv6 : hammingNorm v.val=6 :=
    (tripleSixPoint_full_weight D a t ht heven).2.2
      ⟨v,Submodule.mem_span_singleton_self v⟩ (fun he => hv (congrArg Subtype.val he))
  obtain ⟨R,⟨eR⟩,hR,hfaith⟩ := Hexacode.exists_full_weight_scalar_symmetric_three v hv6
  let L := R.map j
  have hLN : L ≤ normalizer (V : Set G) := by
    rintro g ⟨r,hr,rfl⟩
    apply mem_normalizer_iff.mpr
    intro u
    constructor
    · intro hu
      have huU := (tripleSixPoint_properties D a t ht).2.1 hu
      rw [hjact r ⟨u,huU⟩]
      apply (hpoint _).mpr
      rw [e.apply_symm_apply]
      exact (hR hr (e ⟨u,huU⟩).toAdd).mpr ((hpoint _).mp hu)
    · intro hu
      have hmem : j r⁻¹ * (j r*u*(j r)⁻¹) * (j r⁻¹)⁻¹ ∈ V := by
        have huU := (tripleSixPoint_properties D a t ht).2.1 hu
        rw [hjact r⁻¹ ⟨_,huU⟩]
        apply (hpoint _).mpr
        rw [e.apply_symm_apply]
        exact (hR (R.inv_mem hr) _).mpr ((hpoint _).mp hu)
      have he : j r⁻¹ * (j r*u*(j r)⁻¹) * (j r⁻¹)⁻¹ = u := by rw [map_inv]; group
      exact he ▸ hmem
  have hLM : L≤M := by
    rintro g ⟨r,hr,rfl⟩
    exact (E.symm (SemidirectProduct.inr r)).property
  have hMU : M=normalizer (U : Set G) :=
    (original_tripleSix_escaping_core h structural D a t ht heven hout).2.2.2.1.symm
  refine ⟨L,hLN,hLM.trans_eq hMU,⟨(R.equivMapOfInjective j hj).symm.trans eR⟩,?_⟩
  apply bot_unique
  rintro g ⟨⟨r,hr,rfl⟩,hc⟩
  have hr1 : r=1 := hfaith r hr (by
    intro w hw
    let u := e.symm (Multiplicative.ofAdd w)
    have hu : (u:G)∈V := (hpoint u).mpr (by rw [e.apply_symm_apply]; exact hw)
    have he : j r * (u:G) * (j r)⁻¹ = (u:G) := by
      rw [←(mem_centralizer_iff.mp hc u hu),mul_inv_cancel_right]
    rw [hjact] at he
    have he' := congrArg e (Subtype.ext he : e.symm (hexAffineAction r (e u))=u)
    rw [e.apply_symm_apply,e.apply_symm_apply] at he'
    exact congrArg Multiplicative.toAdd he')
  change j r=1
  rw [hr1,map_one]

end CFSG.Quasithin.Chapter12.Section07
