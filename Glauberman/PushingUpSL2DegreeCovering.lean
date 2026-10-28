module
public import Glauberman.PushingUpSL2DegreeStructure
public import Glauberman.PushingUpCenterCovering
public import Theory.Representation.SL2.SharpSylowCovering

/-!
# Full center covering at the original SL₂ degree

Sharp fixed indices in the numerical pair and the original-degree SL₂
lower bound force generation by the two Sylow fixed spaces. Uniform
involution fixed spaces make both Sylows quadratic. The Sylow trace then
proves that the moved core center covers the full Sylow center modulo the
ambient center, retaining every central attachment.

Source: Niles, *Pushing-up in finite groups* (1979), Proposition 4.6(g),
printed p.47. This supplies the original-degree depth-3v lattice argument.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace Glauberman
variable {G : Type*} [Group G] [Finite G]

theorem NumericalPairAt.omega_fixed_indices {q : ℕ} {S T : Subgroup G} {φ : S ≃* T}
    (h : NumericalPairAt q S T φ) :
    (omegaCenterIn (S ⊓ T) ⊓ centralizer (S : Set G)).relIndex (omegaCenterIn (S ⊓ T)) = q ∧
    (omegaCenterIn (S ⊓ T) ⊓ centralizer (T : Set G)).relIndex (omegaCenterIn (S ⊓ T)) = q := by
  have hS : S ≠ ⊥ := by
    intro he
    have hh := h.index_left
    rw [he,relIndex_bot_right] at hh
    have := h.nontrivial_index
    omega
  obtain ⟨_,_,_,_,_,_,hs,ht⟩ := fixed_normal_pair_counting S T
    (omegaCenterIn (S ⊓ T)) φ hS h.no_fixed h.normal_left h.normal_right
    (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).1) inferInstance
    (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1)
    (fun B hB hout => by rw [h.index_left]; exact h.lower_left B hB.1 hout)
    (fun B hB hout => by rw [h.index_right]; exact h.lower_right B hB.1 hout)
  exact ⟨hs.trans h.index_left,ht.trans h.index_right⟩

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem original_sl2_full_center_covering
    (e : (G ⧸ pCore 2 G) ≃* SL(2,F)) {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (S : Sylow 2 G) (α : MulAut S)
    (hfit : generalizedFitting G = pCore 2 G)
    (hno : NoInvariantNormal (S : Subgroup G) α) :
    ⁅centerIn (pCore 2 G),(S : Subgroup G)⁆ ⊔ center G = centerIn (S : Subgroup G) ∧
    (center G).relIndex (centerIn (pCore 2 G)) = Nat.card F ^ 2 ∧
    (center G).relIndex (centerIn (S : Subgroup G)) = Nat.card F := by
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
  obtain ⟨hspan,htop,hhyp⟩ := Representation.SL2.sharp_sylow_fixed_spaces ρ hnt hn hF
    R T' hgen' hR hT
  have hquadT := (Representation.SL2.sharp_sylow_fixed_spaces ρ hnt hn hF
    T' R ((sup_comm _ _).trans hgen') hT hR).2.2.quadratic
  have hcover := sylow_moved_fixed_cover_of_quadratic_pair ρ R T' hgen' hspan
    hhyp.quadratic hquadT
  have hρ : ρ.comp f = omegaAction G := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (NormalElementaryQuotient.representation_apply V f hf hc g v).trans
      (omegaAction_apply G g v).symm
  have hcover' : subspaceCommutator (omegaAction G) ⊤ (S : Subgroup G) ⊔
      fixedSpace (omegaAction G) ⊤ = fixedSpace (omegaAction G) (S : Subgroup G) := by
    rw [←hρ,subspaceCommutator_comp_map,fixedSpace_comp_map,fixedSpace_comp_map,
      map_top_of_surjective f hf]
    exact hcover
  obtain ⟨hωS,_,hωQ⟩ := hnum.omegaCenters_eq_centers
  rw [hinter] at hωQ
  have hQc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G := by
    rw [←hfit]
    exact centralizer_generalizedFitting_le G
  have hzQ : center G ≤ pCore 2 G := (center_le_centralizer _).trans hQc
  have hglobal : V ⊓ center G = center G := by
    change omegaCenterIn (pCore 2 G) ⊓ center G = _
    rw [hωQ]
    exact inf_eq_right.mpr (le_inf hzQ (center_le_centralizer _))
  have hQS : pCore 2 G ≤ (S : Subgroup G) := pCore_isPGroup.le_sylow_of_normal S
  have hzS : centerIn (S : Subgroup G) ≤ pCore 2 G :=
    inf_le_right.trans ((centralizer_le hQS).trans hQc)
  have hfixed : V ⊓ centralizer (S : Set G) = centerIn (S : Subgroup G) :=
    (omegaCenterIn_eq_inf_of_center_le _ _ hQS hzS).symm.trans hωS
  have hcoverG := omegaAction_moved_fixed_join (S : Subgroup G) hcover'
  change ⁅V,(S : Subgroup G)⁆ ⊔ (V ⊓ center G) = V ⊓ centralizer (S : Set G) at hcoverG
  rw [hglobal,hfixed] at hcoverG
  have htotal : (center G).relIndex V = Nat.card F ^ 2 := by
    have hi := NormalElementaryQuotient.centralizer_index_eq_fixedCodim V f hf hc ⊤
    rw [map_top_of_surjective f hf] at hi
    change (centralizer ((⊤ : Subgroup G) : Set G)).relIndex V = 2 ^ fixedCodim ρ ⊤ at hi
    rw [coe_top,centralizer_univ,htop] at hi
    rw [hF,←pow_mul,Nat.mul_comm n 2]
    exact hi
  have hiS' : (centerIn (S : Subgroup G)).relIndex V = Nat.card F := by
    rw [←hfixed,inf_relIndex_left]
    exact hiS
  have hZV : center G ≤ V := hglobal.ge.trans inf_le_left
  have hZS : center G ≤ centerIn (S : Subgroup G) := by
    rw [←hfixed]
    exact le_inf hZV (center_le_centralizer _)
  have hmul := relIndex_mul_relIndex (center G) (centerIn (S : Subgroup G)) V
    hZS (hfixed ▸ inf_le_left)
  rw [hiS',htotal,pow_two] at hmul
  have hindex : (center G).relIndex (centerIn (S : Subgroup G)) = Nat.card F :=
    Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := F)) hmul
  change omegaCenterIn (pCore 2 G) = _ at hωQ
  change (center G).relIndex (omegaCenterIn (pCore 2 G)) = _ at htotal
  change ⁅omegaCenterIn (pCore 2 G),(S : Subgroup G)⁆ ⊔ center G = _ at hcoverG
  rw [hωQ] at htotal hcoverG
  exact ⟨hcoverG,htotal,hindex⟩
end Glauberman
