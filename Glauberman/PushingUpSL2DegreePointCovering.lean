module
public import Glauberman.PushingUpSL2DegreeCovering
public import Theory.Representation.SL2.SharpPointCovering

/-!
# Original-degree center covering by individual elements

For every original Sylow, each element outside the two-core and each
core-center element outside the Sylow center have nontrivial commutator.
Fixing either element, its commutators cover the full Sylow center modulo
the ambient center. The proof uses the literal core-omega action, sharp
fixed indices and elementwise covering on the central quotient. It keeps
all central attachments and the original field degree.

Source: Niles, *Pushing-up in finite groups* (1979), Theorem 4.7(d), p.48.
Both conjugate Sylows of the actual intersection diagram use this result.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace Glauberman
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

theorem original_sl2_center_point_covering
    (e : (G ⧸ pCore 2 G) ≃* SL(2,F)) {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (S : Sylow 2 G) (α : MulAut S)
    (hfit : generalizedFitting G = pCore 2 G)
    (hno : NoInvariantNormal (S : Subgroup G) α)
    (A : Sylow 2 G) :
    (∀ x ∈ (A : Subgroup G), x ∉ pCore 2 G →
      ∀ z ∈ centerIn (A : Subgroup G),
        ∃ y ∈ centerIn (pCore 2 G), z * ⁅x,y⁆⁻¹ ∈ center G) ∧
    (∀ y ∈ centerIn (pCore 2 G), y ∉ centerIn (A : Subgroup G) →
      ∀ z ∈ centerIn (A : Subgroup G),
        ∃ x ∈ (A : Subgroup G), z * ⁅x,y⁆⁻¹ ∈ center G) ∧
    (∀ x ∈ (A : Subgroup G), x ∉ pCore 2 G →
      ∀ y ∈ centerIn (pCore 2 G), y ∉ centerIn (A : Subgroup G) → ⁅x,y⁆ ≠ 1) := by
  obtain ⟨x,hx,hgen,hinter,hnum⟩ := original_sl2_numerical_pair e hn hF S α hfit hno
  let T := S.mapSurjective (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).surjective
  let V := omegaCenterIn (pCore 2 G)
  let _ : V.Normal := omegaCenterIn_normal_of_normal _
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 G := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hc : f.ker = centralizer (V : Set G) := hk.trans
    (sl2_core_omega_centralizer e hn hF S hfit hno.noCharacteristicNormal).symm
  let ρ := NormalElementaryQuotient.representation V f hf hc
  let R := S.mapSurjective hf
  let T' := T.mapSurjective hf
  have hgen' : (R : Subgroup SL(2,F)) ⊔ T' = ⊤ := by
    change (S : Subgroup G).map f ⊔ (T : Subgroup G).map f = ⊤
    have hg : (S : Subgroup G) ⊔ (T : Subgroup G) = ⊤ := hgen
    rw [←Subgroup.map_sup,hg,map_top_of_surjective f hf]
  obtain ⟨hiS,hiT⟩ := hnum.omega_fixed_indices
  rw [hinter,inf_relIndex_left] at hiS hiT
  have hdim (A : Subgroup G) (hi : (centralizer (A : Set G)).relIndex V = Nat.card F) :
      fixedCodim ρ (A.map f) = n := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim V f hf hc,hF] at hi
    exact Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hi
  have hR : fixedCodim ρ R = n := hdim S hiS
  have hT : fixedCodim ρ T' = n := hdim T hiT
  have hnt : ∃ g, ρ g ≠ 1 := by
    by_contra! he
    have hfixed : fixedSpace ρ R = ⊤ := by
      apply top_unique
      intro v _ r
      change ρ (r : Matrix.SpecialLinearGroup (Fin 2) F) v = v
      rw [he]
      rfl
    have hz : fixedCodim ρ R = 0 := by
      have hh := fixedCodim_add_finrank ρ (R : Subgroup _)
      rw [hfixed,finrank_top] at hh
      omega
    omega
  have hdimAll (B : Sylow 2 SL(2,F)) : fixedCodim ρ B = n := by
    obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq SL(2,F) R B
    exact (fixedCodim_map_conj ρ R g).trans hR
  obtain ⟨a,_,hpair,_⟩ := Matrix.SpecialLinearGroup.exists_residual_generating_sylow_pair f hf hk A
  let B := A.mapSurjective (f := (MulAut.conj a).toMonoidHom) (MulAut.conj a).surjective
  let R1 := A.mapSurjective hf
  let T1 := B.mapSurjective hf
  have hgen1 : (R1 : Subgroup SL(2,F)) ⊔ T1 = ⊤ := by
    change (A : Subgroup G).map f ⊔ (B : Subgroup G).map f = ⊤
    have hh : (A : Subgroup G) ⊔ (B : Subgroup G) = ⊤ := hpair
    rw [←Subgroup.map_sup,hh,map_top_of_surjective f hf]
  have hR1 := hdimAll R1
  have hT1 := hdimAll T1
  have hρ : ρ.comp f = omegaAction G := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (NormalElementaryQuotient.representation_apply V f hf hc g v).trans
      (omegaAction_apply G g v).symm
  have hfixed (A : Subgroup G) (v : Additive V) :
      v ∈ fixedSpace ρ (A.map f) ↔ (v.toMul : G) ∈ centralizer (A : Set G) := by
    rw [←fixedSpace_comp_map,hρ]
    exact omegaAction_fixedSpace G A v
  have hglobal (v : Additive V) :
      v ∈ fixedSpace ρ ⊤ ↔ (v.toMul : G) ∈ center G := by
    have hh := hfixed ⊤ v
    simpa only [map_top_of_surjective f hf,coe_top,centralizer_univ] using hh
  have haction (x : G) (v : Additive V) :
      ((ρ (f x) v).toMul : G) = x * (v.toMul : G) * x⁻¹ := by
    have hh := congrArg (fun τ : Representation (ZMod 2) G (Additive V) => τ x v) hρ
    change ρ (f x) v = omegaAction G x v at hh
    rw [hh,omegaAction_apply]
  have hωQ : V = centerIn (pCore 2 G) := by
    have hh := hnum.omegaCenters_eq_centers.2.2
    rw [hinter] at hh
    exact hh
  have hQS : pCore 2 G ≤ (A : Subgroup G) := pCore_isPGroup.le_sylow_of_normal A
  have hQc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G := by
    rw [←hfit]
    exact centralizer_generalizedFitting_le G
  have hzS : centerIn (A : Subgroup G) ≤ pCore 2 G :=
    inf_le_right.trans ((centralizer_le hQS).trans hQc)
  have hzV : centerIn (A : Subgroup G) ≤ V := by
    rw [hωQ]
    exact le_inf hzS (inf_le_right.trans (centralizer_le hQS))
  have hfixedS (v : Additive V) :
      v ∈ fixedSpace ρ R1 ↔ (v.toMul : G) ∈ centerIn (A : Subgroup G) := by
    change v ∈ fixedSpace ρ ((A : Subgroup G).map f) ↔ _
    rw [hfixed]
    exact ⟨fun hh => ⟨hQS ((hωQ.le v.toMul.property).1),hh⟩,fun hh => hh.2⟩
  have hfx (x : G) (hx : x ∉ pCore 2 G) : f x ≠ 1 := by
    intro he
    exact hx (hk ▸ (show x ∈ f.ker from he))
  have heq (z x : G) (w v : Additive V) (hw : (w.toMul : G) = z) :
      ((w - (ρ (f x) v - v)).toMul : G) = z * ⁅x,(v.toMul : G)⁆⁻¹ := by
    simp only [toMul_sub,div_eq_mul_inv]
    change (w.toMul : G) * (((ρ (f x) v).toMul : G) * (v.toMul : G)⁻¹)⁻¹ = _
    rw [hw,haction]
    rfl
  refine ⟨?_,?_,?_⟩
  · intro x hx hxQ z hz
    let w : Additive V := Additive.ofMul ⟨z,hzV hz⟩
    obtain ⟨v,hv⟩ := Representation.SL2.sharp_sylow_actor_covering ρ hnt hn hF
      R1 T1 hgen1 hR1 hT1 (f x) (mem_map_of_mem f hx) (hfx x hxQ) w
      ((hfixedS w).mpr hz)
    exact ⟨v.toMul,hωQ ▸ v.toMul.property,heq z x w v rfl ▸ ((hglobal _).mp hv)⟩
  · intro y hy hyZ z hz
    let v : Additive V := Additive.ofMul ⟨y,hωQ.symm ▸ hy⟩
    let w : Additive V := Additive.ofMul ⟨z,hzV hz⟩
    obtain ⟨r,⟨x,hx,he⟩,hr⟩ := Representation.SL2.sharp_sylow_vector_covering ρ hnt hn hF
      R1 T1 hgen1 hR1 hT1 v (fun hv => hyZ ((hfixedS v).mp hv)) w ((hfixedS w).mpr hz)
    rw [←he] at hr
    exact ⟨x,hx,heq z x w v rfl ▸ ((hglobal _).mp hr)⟩
  · intro x hx hxQ y hy hyZ hcomm
    let v : Additive V := Additive.ofMul ⟨y,hωQ.symm ▸ hy⟩
    have hhyp := (Representation.SL2.sharp_sylow_fixed_spaces ρ hnt hn hF
      R1 T1 hgen1 hR1 hT1).2.2
    have hv : v ∈ fixedSpace ρ (zpowers (f x)) := by
      rw [mem_fixedSpace_zpowers_iff]
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [haction]
      change x*y*x⁻¹ = y
      exact mul_inv_eq_iff_eq_mul.mpr
        (commutatorElement_eq_one_iff_mul_comm.mp hcomm)
    rw [hhyp.uniform (f x) (mem_map_of_mem f hx) (hfx x hxQ)] at hv
    exact hyZ ((hfixedS v).mp hv)
end Glauberman
