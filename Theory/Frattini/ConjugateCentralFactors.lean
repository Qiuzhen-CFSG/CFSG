module
public import Theory.Frattini.CentralElementarySupplement

/-!
# Frattini invariance for conjugate central factors

If Q=C_S(U)=UD and S=UˣQ, where U is elementary abelian and D centralizes
Uˣ, then Q and Qˣ have central elementary supplements over their intersection.
Their Frattini subgroups coincide and each is the Frattini subgroup of D.
The radical is retained throughout. This is the elementary finite-group
argument used in Aschbacher–Smith C.5.6(4), printed p.157.
-/

public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G]

private theorem map_frattini_equiv (B : Subgroup G) (e : G ≃* G) :
    ((frattini B).map B.subtype).map e.toMonoidHom =
      (frattini (B.map e.toMonoidHom)).map (B.map e.toMonoidHom).subtype := by
  let f := e.subgroupMap B
  have hf : (frattini B).map f.toMonoidHom = frattini (B.map e.toMonoidHom) :=
    f.mapSubgroup.map_radical
  apply le_antisymm
  · rintro g ⟨b, ⟨d, hd, rfl⟩, rfl⟩
    refine ⟨f d, hf ▸ mem_map_of_mem f.toMonoidHom hd, ?_⟩
    exact MulEquiv.coe_subgroupMap_apply e B d
  · rintro g ⟨b, hb, rfl⟩
    obtain ⟨d, hd, hdb⟩ := (show b ∈ (frattini B).map f.toMonoidHom from hf.symm ▸ hb)
    refine ⟨(d : G), mem_map_of_mem B.subtype hd, ?_⟩
    exact (MulEquiv.coe_subgroupMap_apply e B d).symm.trans (congrArg Subtype.val hdb)

private theorem supplement_intersection (P V W : Subgroup G)
    (hVP : V ≤ P) (hspan : P ≤ V ⊔ W) (hVW : V ≤ normalizer (W : Set G)) :
    P = V ⊔ (P ⊓ W) := by
  apply le_antisymm
  · intro g hg
    have hgm : g ∈ (V : Set G) * (W : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right V W hVW]
      exact hspan hg
    obtain ⟨v, hv, w, hw, hvg⟩ := hgm
    have hwP : w ∈ P := by
      have hh := P.mul_mem (P.inv_mem (hVP hv)) hg
      rwa [← hvg, inv_mul_cancel_left] at hh
    rw [← hvg]
    exact mul_mem_sup hv ⟨hwP, hw⟩
  · exact sup_le hVP inf_le_left

private theorem map_centralizer (U : Subgroup G) (e : G ≃* G) :
    (centralizer (U : Set G)).map e.toMonoidHom = centralizer (U.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro g hg
    refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
    intro u hu
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hg (e u) (mem_map_of_mem _ hu)

/-- Conjugation preserving S also preserves the embedded Frattini subgroup
of D under the central-factor hypotheses. -/
theorem frattini_conjugate_central_factors [Finite G]
    (S U Q D : Subgroup G) (e : G ≃* G)
    (hSmap : S.map e.toMonoidHom = S)
    (hcore : Q = S ⊓ centralizer (U : Set G)) (hprod : Q = U ⊔ D)
    (hcentralizes : D ≤ centralizer (U.map e.toMonoidHom : Set G))
    (hspan : S = U.map e.toMonoidHom ⊔ Q)
    (hU : IsElementaryAbelian 2 U) (hQtwo : IsPGroup 2 Q)
    (hSQ : S ≤ normalizer (Q : Set G)) :
    ((frattini D).map D.subtype).map e.toMonoidHom = (frattini D).map D.subtype := by
  let V := U.map e.toMonoidHom
  let Q' := Q.map e.toMonoidHom
  let I := Q ⊓ Q'
  let := hU
  have hUQ : U ≤ Q := hprod ▸ le_sup_left
  have hQU : Q ≤ centralizer (U : Set G) := hcore ▸ inf_le_right
  have hUQcomm : U ≤ centralizer (Q : Set G) := le_centralizer_iff.mp hQU
  have hQ' : Q' = S ⊓ centralizer (V : Set G) := by
    change Q.map e.toMonoidHom = _
    rw [hcore, map_inf _ _ _ e.injective, hSmap, map_centralizer]
  have hQ'S : Q' ≤ S := hQ' ▸ inf_le_left
  have hVQ' : V ≤ Q' := map_mono hUQ
  have hVQ'comm : V ≤ centralizer (Q' : Set G) := by
    rw [← map_centralizer]
    exact map_mono hUQcomm
  have hDQ' : D ≤ Q' := by
    rw [hQ']
    exact le_inf ((hprod ▸ le_sup_right).trans (hcore ▸ inf_le_left)) hcentralizes
  have hQI : Q = U ⊔ I := by
    apply le_antisymm
    · rw [hprod]
      exact sup_le le_sup_left ((le_inf (hprod ▸ le_sup_right) hDQ').trans le_sup_right)
    · exact sup_le hUQ inf_le_left
  have hQ'I : Q' = V ⊔ I := by
    have he := supplement_intersection Q' V Q hVQ'
      (hQ'S.trans hspan.le) ((hVQ'.trans hQ'S).trans hSQ)
    simpa only [I, inf_comm] using he
  have hV : IsElementaryAbelian 2 V := IsElementaryAbelian.map e.toMonoidHom
  have hQP := frattini_map_eq_of_central_elementary_supplement Q I U hQtwo hU hUQcomm hQI
  have hQ'P := frattini_map_eq_of_central_elementary_supplement Q' I V
    (hQtwo.map e.toMonoidHom) hV hVQ'comm hQ'I
  have hDP := frattini_map_eq_of_central_elementary_supplement Q D U hQtwo hU hUQcomm hprod
  rw [← hDP, map_frattini_equiv]
  exact hQ'P.trans hQP.symm
end Subgroup
end
