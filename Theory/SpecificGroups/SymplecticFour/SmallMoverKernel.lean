module
public import Theory.Representation.SemilinearSmallOffender
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.Centralizer
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.GroupTheory.FixedActionNormalizer

/-!
# Small-mover normalization in a faithful ambient natural action

Small offenders of F4^4 have no field twist and lie in the actual centric
symplectic component. Put the component part of an arbitrary two-group into
Sylow coordinates. The maximum-small-mover calculation there shows that its
maximum offenders commute with every actor of moving index at most four.
The literal action kernel then lifts this to normalization of the full fixed
subgroup, without splitting or discarding a central extension.

Source: MS93 (5.4) and (5.7), printed pp.915 and919. The original graph
application is Sp4Four.SourceComparison.OriginalSmallMovers.
-/


public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
namespace Representation
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
  [CharP F 2] [Algebra (ZMod 2) F]

omit [Finite G] in
theorem small_actor_le_symplectic_component
    (hF : Nat.card F = 4) (B : Subgroup G) [B.Normal]
    (hcent : centralizer (B : Set G) ≤ B) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) G (Vector F))
    (hB : ∀ b : B, ∀ v, ρ (b:G) v = symplecticNatural 2 (e b) v)
    (A : Subgroup G) [Finite A]
    (hsmall : Nat.card (Vector F ⧸ fixedSpace ρ A) ≤ 4) : A ≤ B := by
  have hsemi (a : G) : ∃ σ : F ≃+* F, ∀ c v, ρ a (c • v) = σ c • ρ a v :=
    SymplecticNaturalNormalizer.exists_field_twist
      ⟨SymplecticConjugatePair.Ambient.linearAction ρ a,
        SymplecticNaturalNormalizer.operator_mem_naturalNormalizer B (by omega) e ρ hB a⟩
  have hlin (a : G) (ha : a ∈ A) (c : F) (v : Vector F) : ρ a (c • v) = c • ρ a v := by
    obtain ⟨σ,hσ⟩ := hsemi a
    have he : σ = RingEquiv.refl F := by
      by_contra hn
      have hh := sixteen_le_fixed_quotient_card_of_twist hF ρ A ha hn hσ
      omega
    rw [hσ,he]
    rfl
  have hmul : Nat.card (fixedSpace ρ A) * Nat.card (Vector F ⧸ fixedSpace ρ A) = 256 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ A),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Vector F ⧸ fixedSpace ρ A),
      ←pow_add,add_comm,(fixedSpace ρ A).finrank_quotient_add_finrank,
      ←Module.natCard_eq_pow_finrank (K := ZMod 2)]
    rw [Module.natCard_eq_pow_finrank (K := F)]
    simp [Theory.SpecificGroups.SymplecticFour.Vector,hF]
  have hfix : 1 < Nat.card (fixedSpace ρ A) := by nlinarith
  let := Fintype.ofFinite (fixedSpace ρ A)
  let : Nontrivial (fixedSpace ρ A) := Fintype.one_lt_card_iff_nontrivial.mp (by simpa only [Nat.card_eq_fintype_card] using hfix)
  obtain ⟨v,hv⟩ := exists_ne (0 : fixedSpace ρ A)
  have hv0 : v.val ≠ 0 := fun h => hv (Subtype.ext h)
  intro a ha
  apply SymplecticNaturalNormalizer.mem_component_of_fixes_field_line
    B hcent (by omega) e ρ hB a v.val hv0
  intro c
  rw [hlin a ha]
  exact congrArg (c • ·) (show ρ a v.val = v.val from v.property ⟨a,ha⟩)

omit [Finite G] [CharP F 2] in
private theorem natural_sylow_coordinates
    (hF : Nat.card F = 4) (B : Subgroup G) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) G (Vector F))
    (hB : ∀ b : B, ∀ v, ρ (b:G) v = symplecticNatural 2 (e b) v)
    (T : Subgroup G) (hT : IsPGroup 2 T) :
    ∃ i : unipotent (F := F) →* G, Function.Injective i ∧
      T ⊓ B ≤ i.range ∧
      ∀ D : Subgroup (unipotent (F := F)),
        Nat.card (Vector F ⧸ fixedSpace ρ (D.map i)) =
          CentralRootGeometry.SmallMovers.movingIndex D := by
  let T₀ := (T.subgroupOf B).map e.toMonoidHom
  have hT₀ : IsPGroup 2 T₀ := hT.comap_subtype.map e.toMonoidHom
  obtain ⟨S,hS⟩ := hT₀.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Sp F) S (unipotentSylow (n := 2) hF (by decide))
  have hs : (S : Subgroup (Sp F)).map (MulAut.conj g).toMonoidHom = unipotent :=
    congrArg (fun P : Sylow 2 (Sp F) => (P : Subgroup (Sp F))) hg
  have hTU : T₀.map (MulAut.conj g).toMonoidHom ≤ unipotent := hs ▸ map_mono hS
  let i := B.subtype.comp (e.symm.toMonoidHom.comp
    ((MulAut.conj g⁻¹).toMonoidHom.comp (unipotent (F := F)).subtype))
  have hi : Function.Injective i := Subtype.val_injective.comp
    (e.symm.injective.comp ((MulAut.conj g⁻¹).injective.comp Subtype.val_injective))
  refine ⟨i,hi,?_,?_⟩
  · rintro x ⟨hx,hxB⟩
    let y := e ⟨x,hxB⟩
    have hy : y ∈ T₀ := mem_map_of_mem e.toMonoidHom hx
    have hyU : g*y*g⁻¹ ∈ unipotent := hTU (mem_map_of_mem (MulAut.conj g).toMonoidHom hy)
    refine ⟨⟨g*y*g⁻¹,hyU⟩,?_⟩
    change (e.symm (g⁻¹ * (g*y*g⁻¹) * (g⁻¹)⁻¹)).val = x
    rw [show g⁻¹ * (g*y*g⁻¹) * (g⁻¹)⁻¹ = y by group]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨x,hxB⟩)
  · intro D
    let σ := restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)
    let τ := σ.comp (unipotent (F := F)).subtype
    let E := SymplecticConjugatePair.Ambient.linearAction σ g⁻¹
    have he (u : unipotent (F := F)) (v : Vector F) : E (τ u v) = ρ (i u) (E v) := by
      change σ g⁻¹ (σ u.val v) = ρ (e.symm (g⁻¹*u.val*(g⁻¹)⁻¹)).val (σ g⁻¹ v)
      rw [hB,e.apply_symm_apply]
      change σ g⁻¹ (σ u.val v) = σ (g⁻¹*u.val*(g⁻¹)⁻¹) (σ g⁻¹ v)
      simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]
    have hdim := fixedCodim_map_equivariant τ ρ i E he D
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    change 2 ^ fixedCodim ρ (D.map i) = _
    rw [←hdim]
    exact CentralRootGeometry.SmallMovers.binary_movingIndex D

/-- In an ambient faithful natural action, a maximum small offender in a
two-group commutes with every component actor of moving index at most four. -/
theorem maximal_small_offender_centralizes
    (hF : Nat.card F = 4) (B : Subgroup G) [B.Normal]
    (hcent : centralizer (B : Set G) ≤ B) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) G (Vector F)) (hfaith : Function.Injective ρ)
    (hB : ∀ b : B, ∀ v, ρ (b:G) v = symplecticNatural 2 (e b) v)
    (T E A : Subgroup G) (hT : IsPGroup 2 T) (hET : E ≤ T) (hAT : A ≤ T)
    (hsmall : Nat.card (Vector F ⧸ fixedSpace ρ E) ≤ 16)
    (hoff : Nat.card (Vector F ⧸ fixedSpace ρ E) ≤ Nat.card E)
    (hmax : ∀ D : Subgroup G, D ≤ T →
      Nat.card (Vector F ⧸ fixedSpace ρ D) ≤ 16 →
      Nat.card (Vector F ⧸ fixedSpace ρ D) ≤ Nat.card D → Nat.card D ≤ Nat.card E)
    (hA : Nat.card (Vector F ⧸ fixedSpace ρ A) ≤ 4) :
    E ≤ centralizer (A : Set G) := by
  have hAB := small_actor_le_symplectic_component hF B hcent e ρ hB A hA
  have hEB := small_offender_le_symplectic_component hF B hcent e ρ hfaith hB E hsmall hoff
  obtain ⟨i,hi,hTi,hindex⟩ := natural_sylow_coordinates hF B e ρ hB T hT
  have hEi : E ≤ i.range := (le_inf hET hEB).trans hTi
  have hAi : A ≤ i.range := (le_inf hAT hAB).trans hTi
  have hEm : (E.comap i).map i = E := map_comap_eq_self hEi
  have hAm : (A.comap i).map i = A := map_comap_eq_self hAi
  have hEc : Nat.card (E.comap i) = Nat.card E := by
    exact (card_map_of_injective (K := E.comap i) hi).symm.trans
      (congrArg (fun C : Subgroup G => Nat.card C) hEm)
  have hEcsmall : CentralRootGeometry.SmallMovers.Small (E.comap i) := by
    constructor
    · rw [←hindex,hEm,hEc]; exact hoff
    · rw [←hindex,hEm]; exact hsmall
  have hmax' : E.comap i ∈ CentralRootGeometry.SmallMovers.Maximal (T.comap i) := by
    refine ⟨comap_mono hET,hEcsmall,?_⟩
    intro D hD hDs
    have hDT : D.map i ≤ T := map_le_iff_le_comap.mpr hD
    have hh := hmax (D.map i) hDT (by rw [hindex]; exact hDs.2)
      (by rw [hindex,card_map_of_injective hi]; exact hDs.1)
    rwa [card_map_of_injective hi,←hEc] at hh
  have hc := CentralRootGeometry.SmallMovers.maximal_centralizes_small_actor hF hmax'
    (comap_mono hAT) (by rw [←hindex,hAm]; exact hA)
  have hm := (map_mono (f := i) hc).trans (map_centralizer_le_centralizer_image _ _)
  change (E.comap i).map i ≤ centralizer ((A.comap i).map i : Set G) at hm
  rwa [hEm,hAm] at hm
end Representation

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
namespace Representation
variable {G D F : Type*} [Group G] [Finite G] [Group D] [Finite D]
  [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- Lift the maximum-small-mover calculation through the literal action
kernel, including its normalization of the full fixed subgroup. -/
theorem smallMover_join_normalizes_small_kernel
    (hF : Nat.card F = 4) (B : Subgroup G) [B.Normal]
    (hcent : centralizer (B : Set G) ≤ B) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) G (Vector F)) (hfaith : Function.Injective ρ)
    (hB : ∀ b : B, ∀ v, ρ (b:G) v = symplecticNatural 2 (e b) v)
    (V T A : Subgroup D) (q : D →* G) (hq : Function.Surjective q)
    (hkT : q.ker ≤ T) (hk : q.ker ≤ centralizer (V : Set D))
    (hTV : T ≤ normalizer (V : Set D)) (hT : IsPGroup 2 T) (hAT : A ≤ T)
    (hindex : ∀ E : Subgroup D, (centralizer (E : Set D)).relIndex V =
      Nat.card (Vector F ⧸ fixedSpace ρ (E.map q)))
    (hA : (centralizer (A : Set D)).relIndex V ≤ 4) :
    Subgroup.SmallMover.join V q.ker T 16 ≤
      normalizer ((V ⊓ centralizer (A : Set D) : Subgroup D) : Set D) := by
  let J := Subgroup.SmallMover.join V q.ker T 16
  have hc : J.map q ≤ centralizer (A.map q : Set G) := by
    change (sSup (Subgroup.SmallMover.Maximal V q.ker T 16)).map q ≤ _
    rw [sSup_eq_iSup,Subgroup.map_iSup]
    apply iSup_le
    intro E
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro hE
    have hmax := (Subgroup.SmallMover.maximal_iff_image_maximal q V T 16
      hkT (le_centralizer_iff.mp hk) E).mp hE
    apply maximal_small_offender_centralizes hF B hcent e ρ hfaith hB
      (T.map q) (E.map q) (A.map q) (hT.map q) (map_mono hE.1.1) (map_mono hAT)
    · rw [←hindex]; exact hE.1.2.2
    · rw [←hindex,←relIndex_ker]; exact hE.1.2.1
    · intro C hC hsmall hoff
      have hpre : C.comap q ≤ T := (comap_mono hC).trans_eq (comap_map_eq_self hkT)
      have him : (C.comap q).map q = C := map_comap_eq_self
        (by rw [MonoidHom.range_eq_top.mpr hq]; exact le_top)
      have hh := hmax.2.2 (C.comap q) ⟨hpre,?_,?_⟩
      · rwa [him] at hh
      · rw [hindex,relIndex_ker,him]; exact hoff
      · rw [hindex,him]; exact hsmall
    · rwa [←hindex]
  exact normalizes_fixed_of_commuting_action_images V J A q
    ((Subgroup.SmallMover.join_le _ _ _ _).trans hTV) hk hc
end Representation
