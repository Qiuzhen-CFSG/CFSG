module

import all Theory.SpecificGroups.PSL2.QuinticInnerFusion
public import Theory.SpecificGroups.PSL2.QuinticLinearFusion
public import Theory.GroupTheory.AmalgamLocalCores
public import Theory.ElementaryAbelian.Injective

/-!
# Whole-subgroup fusion inside an actual field-involution centralizer

After a field involution has become central in the supplied Sylow subgroup,
its actual inner centralizer has a PGL₂ model. Fusion of the nontrivial inner
part inside that centralizer fixes the field involution, so it carries the
whole elementary subgroup back into the original Sylow subgroup and out of
the original quintic two-core.

This is the noncyclic step in Aschbacher--Smith 6.1.4, printed p.666.
-/

public section
open Subgroup GorensteinWalter Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.PSL2

private theorem linear_model_fusion
    {D : Type*} [Group D] [Finite D] {F : Type*} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (e : D ≃* PGL2 F)
    (X : Subgroup D) (T : Sylow 2 D) (hfive : Nat.card X = 5)
    (hTX : (T : Subgroup D) ≤ normalizer X)
    (A : Subgroup D) (hA : IsElementaryAbelian 2 A) (hAne : A ≠ ⊥)
    (hAS : A ≤ (X ⊔ (T : Subgroup D)).pCoreIn 2) :
    ∃ c : D, A.map (MulAut.conj c).toMonoidHom ≤ (T : Subgroup D) ∧
      ¬ A.map (MulAut.conj c).toMonoidHom ≤ (X ⊔ (T : Subgroup D)).pCoreIn 2 := by
  let : IsElementaryAbelian 2 A := hA
  let X' := X.map e.toMonoidHom
  let T' := T.mapSurjective (f := e.toMonoidHom) e.surjective
  let A' := A.map e.toMonoidHom
  have hfive' : Nat.card X' = 5 := by rwa [card_map_of_injective e.injective]
  have hTX' : (T' : Subgroup (PGL2 F)) ≤ normalizer X' := by
    have hh := map_mono (f := e.toMonoidHom) hTX
    rwa [map_equiv_normalizer_eq] at hh
  have hA' : IsElementaryAbelian 2 A' := IsElementaryAbelian.map e.toMonoidHom
  have hAne' : A' ≠ ⊥ := fun hh => hAne ((A.map_eq_bot_iff_of_injective e.injective).mp hh)
  have hS : ((X ⊔ (T : Subgroup D)).pCoreIn 2).map e.toMonoidHom =
      (X' ⊔ (T' : Subgroup (PGL2 F))).pCoreIn 2 := by
    rw [← AmalgamLocalCores.pCoreIn_map_of_injective 2 _ e.injective, Subgroup.map_sup]
    rfl
  have hAS' : A' ≤ (X' ⊔ (T' : Subgroup (PGL2 F))).pCoreIn 2 :=
    (map_mono hAS).trans hS.le
  obtain ⟨g, hgT, hgS⟩ := odd_quintic_linear_elementary_fusion hF X' T' hfive' hTX'
    A' hA' hAne' hAS'
  let c := e.symm (Matrix.ProjectiveSpecialLinearGroup.toPGL g)
  have hmap : (A.map (MulAut.conj c).toMonoidHom).map e.toMonoidHom =
      A'.map (MulAut.conj (Matrix.ProjectiveSpecialLinearGroup.toPGL g)).toMonoidHom := by
    rw [map_map, map_map]
    congr 1
    ext v
    change e (c * v * c⁻¹) = Matrix.ProjectiveSpecialLinearGroup.toPGL g * e v *
      (Matrix.ProjectiveSpecialLinearGroup.toPGL g)⁻¹
    simp only [map_mul, map_inv, c, e.apply_symm_apply]
  refine ⟨c, ?_, ?_⟩
  · apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [hmap]
    exact hgT
  · intro hh
    apply hgS
    rw [← hmap, ← hS]
    exact map_mono hh

/-- An actual PGL₂ inner centralizer fuses the whole elementary group while
fixing its marked Sylow-central element. The quintic core is the original one. -/
theorem quintic_inner_centralizer_whole_fusion
    {G : Type*} [Group G] [Finite G]
    {F : Type*} [Field F] [Finite F] (hF : IsOddPrimePower (Nat.card F))
    (N : Subgroup G) [N.Normal] (T : Sylow 2 G)
    (X : Subgroup G) (hXN : X ≤ N) (hfive : Nat.card X = 5)
    (hTX : (T : Subgroup G) ≤ normalizer X)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAS : A ≤ (X ⊔ (T : Subgroup G)).pCoreIn 2)
    (a : G) (haA : a ∈ A) (haT : a ∈ centralizer (T : Set G))
    (hgen : N ⊔ zpowers a = ⊤) (hAN : A ⊓ N ≠ ⊥)
    (e : (centralizer ({a} : Set G)).subgroupOf N ≃* PGL2 F) :
    ∃ g ∈ N, A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      ¬ A.map (MulAut.conj g).toMonoidHom ≤ (X ⊔ (T : Subgroup G)).pCoreIn 2 := by
  classical
  let : IsElementaryAbelian 2 A := hA
  let : CommGroup A := IsMulCommutative.instCommGroup
  let H := X ⊔ (T : Subgroup G)
  let S := H.pCoreIn 2
  let C := (centralizer ({a} : Set G)).subgroupOf N
  let f : C →* G := N.subtype.comp C.subtype
  have hf : Function.Injective f := N.subtype_injective.comp C.subtype_injective
  have hAC : A ≤ centralizer ({a} : Set G) := by
    intro v hv
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mul_comm (⟨v, hv⟩ : A) ⟨a, haA⟩)
  have hST : S ≤ (T : Subgroup G) := by
    have hh := H.pCoreIn_le_sylow (T.subtype (show (T : Subgroup G) ≤ H from le_sup_right))
    change S ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ H from le_sup_right)] at hh
  have hSC : S ≤ centralizer (X : Set G) := quintic_join_core_centralizes X T hfive hTX
  have hXrange : X ≤ f.range := by
    intro x hx
    exact ⟨⟨⟨x, hXN hx⟩, mem_centralizer_singleton_iff.mpr (hSC (hAS haA) x hx)⟩, rfl⟩
  let Y := X.comap f
  have hYmap : Y.map f = X := map_comap_eq_self hXrange
  have hYcard : Nat.card Y = 5 := by
    have hh := congrArg (fun U : Subgroup G => Nat.card U) hYmap
    rwa [card_map_of_injective hf, hfive] at hh
  obtain ⟨Q, hQ⟩ := T.exists_subgroupOf_eq_of_normal N
  have hQC : (Q : Subgroup N) ≤ C := by
    intro q hq
    have hqT : (q : G) ∈ (T : Subgroup G) := by rw [hQ] at hq; exact hq
    exact mem_centralizer_singleton_iff.mpr (haT q hqT)
  let P : Sylow 2 C := Q.subtype hQC
  have hPT (c : C) : c ∈ P ↔ f c ∈ (T : Subgroup G) := by
    change (c : N) ∈ (Q : Subgroup N) ↔ f c ∈ (T : Subgroup G)
    rw [hQ]
    rfl
  have hPY : (P : Subgroup C) ≤ normalizer Y := by
    intro c hc
    exact (le_normalizer_comap f) (hTX ((hPT c).mp hc))
  let B := A.comap f
  have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.comap_of_injective f hf A
  have hBne : B ≠ ⊥ := by
    let : Nontrivial (A ⊓ N : Subgroup G) := (nontrivial_iff_ne_bot _).mpr hAN
    obtain ⟨b, hb, hb1⟩ := (A ⊓ N : Subgroup G).exists_ne_one_of_nontrivial
    let c : C := ⟨⟨b, hb.2⟩, hAC hb.1⟩
    intro he
    have hh : c = 1 := mem_bot.mp (he ▸ (show c ∈ B from hb.1))
    exact hb1 (congrArg f hh)
  let R := S.comap f
  have hRP : R ≤ (P : Subgroup C) := fun c hc => (hPT c).mpr (hST hc)
  have hHR : Y ⊔ (P : Subgroup C) ≤ normalizer R := by
    have hHS : H ≤ normalizer S :=
      H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
    apply sup_le
    · intro c hc
      exact (le_normalizer_comap f) (hHS ((show X ≤ H from le_sup_left) hc))
    · intro c hc
      exact (le_normalizer_comap f) (hHS ((show (T : Subgroup G) ≤ H from le_sup_right)
        ((hPT c).mp hc)))
  have hRcore : R ≤ (Y ⊔ (P : Subgroup C)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 H).comap_of_injective f hf)
      (hRP.trans le_sup_right) hHR
  have hBcore : B ≤ (Y ⊔ (P : Subgroup C)).pCoreIn 2 :=
    (comap_mono hAS).trans hRcore
  obtain ⟨c, hcP, hcR⟩ := linear_model_fusion hF e Y P hYcard hPY B hB hBne hBcore
  have hca : f c * a * (f c)⁻¹ = a := mul_inv_eq_iff_eq_mul.mpr
    (mem_centralizer_singleton_iff.mp c.property)
  have hinner (v : G) (hvA : v ∈ A) (hvN : v ∈ N) :
      f c * v * (f c)⁻¹ ∈ (T : Subgroup G) := by
    let w : C := ⟨⟨v, hvN⟩, hAC hvA⟩
    have hh := (hPT (MulAut.conj c w)).mp
      (hcP (mem_map_of_mem _ (show w ∈ B from hvA)))
    change f (c * w * c⁻¹) ∈ (T : Subgroup G) at hh
    rw [map_mul, map_mul, map_inv] at hh
    exact hh
  refine ⟨f c, c.val.property, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨n, hn, z, hz, he⟩ := mem_sup_of_normal_left.mp (hgen ▸ mem_top v)
    have hzA : z ∈ A := (zpowers_le.mpr haA) hz
    have hnA : n ∈ A := by
      have hh := A.mul_mem hv (A.inv_mem hzA)
      rw [← he, mul_inv_cancel_right] at hh
      exact hh
    have hzT : f c * z * (f c)⁻¹ ∈ (T : Subgroup G) := by
      have hh : (zpowers a).map (MulAut.conj (f c)).toMonoidHom ≤ (T : Subgroup G) := by
        rw [MonoidHom.map_zpowers]
        change zpowers (f c * a * (f c)⁻¹) ≤ _
        rw [hca]
        exact zpowers_le.mpr (hST (hAS haA))
      exact hh (mem_map_of_mem _ hz)
    change f c * v * (f c)⁻¹ ∈ (T : Subgroup G)
    rw [← he]
    simpa only [← MulAut.conj_apply, map_mul] using
      (T : Subgroup G).mul_mem (hinner n hnA hn) hzT
  · intro hwhole
    apply hcR
    rintro _ ⟨b, hb, rfl⟩
    apply hRcore
    have hh := hwhole (mem_map_of_mem (MulAut.conj (f c)).toMonoidHom hb)
    change f (c * b * c⁻¹) ∈ S
    rw [map_mul, map_mul, map_inv]
    exact hh

end Theory.PSL2
