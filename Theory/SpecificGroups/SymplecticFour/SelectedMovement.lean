module
public import Theory.SpecificGroups.SymplecticFour.SelectedGeneration
public import Theory.SpecificGroups.SymplecticFour.SmallMoverKernel
public import Theory.SpecificGroups.SymplecticFour.RootHyperplaneComparison
public import Theory.Representation.BinaryOffender.EmbeddedFixedIndex
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.Centralizer
/-!
# Small movers fix small displacements in the field-four natural module

Place the two actors in a common Sylow subgroup. The order-64 small mover
lies in the abelian plane wing, as does every actor whose fixed quotient
has order at most four. The plane wing fixes all their displacement vectors.
Conjugation transports this calculation to an arbitrary two-subgroup.

The ambient and embedded variants retain the faithful semilinear action,
its symplectic component and the whole module. The actual source consumer
is Sp4Four.SourceComparison.OriginalSelectedMovement, applying the
calculation in the common-root argument of MS93 (5.7), printed p.919.
-/

public noncomputable section
open Subgroup Matrix Representation
namespace Theory.SpecificGroups.SymplecticFour.SelectedGeneration
open CentralRootGeometry
variable {F : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]

omit [Algebra (ZMod 2) F] in
private theorem wing_displacement_fixed
    (g a : unipotent (F := F)) (hg : g ∈ wing true) (ha : a ∈ wing true)
    (v : Vector F) : g.val • (a.val • v-v) = a.val • v-v := by
  obtain ⟨⟨b,u,w,z⟩,rfl⟩ := element_surjective a
  have hb : b=0 := (element_mem_wing _ _ _ _ _).mp ha
  subst b
  have hp : (element (F := F) 0 u w z).val • v-v ∈ plane F := by
    intro i
    change (((element (F := F) 0 u w z).val.val *ᵥ v)-v) (.inr i)=0
    rw [element_matrix]
    fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Fin.sum_univ_two,
      Matrix.fromBlocks]
  exact (SmallMovers.standardPlane_le_fixed (wing true) le_rfl hp) ⟨g,hg⟩

/-- The order-64 small mover fixes every displacement of an actor with
moving index at most four in its common two-group, and of its own subgroups. -/
theorem large_small_mover_fixes_displacement
    (hF : Nat.card F=4) (E A P : Subgroup (Sp F)) (hP : IsPGroup 2 P)
    (hEP : E ≤ P) (hAP : A ≤ P) (hc : Nat.card E=64)
    (hm : Nat.card (Vector F ⧸ BinaryOffender.fixedSpace
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)) E) ≤ 16)
    (hA : Nat.card (Vector F ⧸ BinaryOffender.fixedSpace
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)) A) ≤ 4 ∨ A ≤ E) :
    ∀ g ∈ E, ∀ a ∈ A, ∀ v : Vector F, g • (a • v-v) = a • v-v := by
  obtain ⟨S,hS⟩ := hP.exists_le_sylow
  obtain ⟨k,hk⟩ := MulAction.exists_smul_eq (Sp F) S
    (unipotentSylow (n := 2) hF (by decide))
  have hkS : (S : Subgroup (Sp F)).map (MulAut.conj k).toMonoidHom = unipotent :=
    congrArg Sylow.toSubgroup hk
  let E' := E.map (MulAut.conj k).toMonoidHom
  let A' := A.map (MulAut.conj k).toMonoidHom
  have hEU : E' ≤ unipotent := hkS ▸ map_mono (hEP.trans hS)
  have hAU : A' ≤ unipotent := hkS ▸ map_mono (hAP.trans hS)
  let E₀ := E'.subgroupOf unipotent
  let A₀ := A'.subgroupOf unipotent
  have hEm : E₀.map (unipotent (F := F)).subtype = E' := map_subgroupOf_eq_of_le hEU
  have hAm : A₀.map (unipotent (F := F)).subtype = A' := map_subgroupOf_eq_of_le hAU
  let σ := restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)
  have index (K : Subgroup (Sp F)) (hKU : K.map (MulAut.conj k).toMonoidHom ≤ unipotent) :
      SmallMovers.movingIndex ((K.map (MulAut.conj k).toMonoidHom).subgroupOf unipotent) =
        Nat.card (Vector F ⧸ BinaryOffender.fixedSpace σ K) := by
    have hdim := BinaryOffender.fixedCodim_map_equivariant σ σ (MulAut.conj k).toMonoidHom
      (SymplecticConjugatePair.Ambient.linearAction σ k)
      (fun g v => by
        change σ k (σ g v) = σ (k*g*k⁻¹) (σ k v)
        simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]) K
    have hdim' := BinaryOffender.fixedCodim_map_equivariant
      (σ.comp (unipotent (F := F)).subtype) σ (unipotent (F := F)).subtype
      (LinearEquiv.refl _ _) (fun _ _ => rfl)
      ((K.map (MulAut.conj k).toMonoidHom).subgroupOf unipotent)
    rw [map_subgroupOf_eq_of_le hKU] at hdim'
    rw [←SmallMovers.binary_movingIndex]
    change 2 ^ BinaryOffender.fixedCodim (σ.comp (unipotent (F := F)).subtype) _ = _
    rw [hdim',←hdim,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    rfl
  have hEc : Nat.card E₀=64 := by
    rw [←card_map_of_injective (unipotent (F := F)).subtype_injective,hEm,
      card_map_of_injective (MulAut.conj k).injective,hc]
  have hEs : SmallMovers.Small E₀ := by
    have he : SmallMovers.movingIndex E₀ ≤ 16 := (index E hEU).trans_le hm
    exact ⟨by rw [hEc]; omega,he⟩
  have hEw : E₀ ≤ wing true := by
    rcases SmallMovers.small_classification_nonstandard hF E₀ hEs with h | ⟨l,hl⟩
    · exact h
    · rw [hl,SmallMovers.card_finitePlane,hF] at hEc
      norm_num at hEc
  have hAw : A₀ ≤ wing true := by
    rcases hA with hA | hAE
    · exact SmallMovers.le_plane_wing_of_movingIndex_le_four hF A₀ ((index A hAU).trans_le hA)
    · exact (comap_mono (map_mono hAE)).trans hEw
  intro g hg a ha v
  have hg' : k*g*k⁻¹ ∈ E' := mem_map_of_mem (MulAut.conj k).toMonoidHom hg
  have ha' : k*a*k⁻¹ ∈ A' := mem_map_of_mem (MulAut.conj k).toMonoidHom ha
  have hx := wing_displacement_fixed ⟨k*g*k⁻¹,hEU hg'⟩ ⟨k*a*k⁻¹,hAU ha'⟩
    (hEw hg') (hAw ha') (k • v)
  have htransport (x : Sp F) (w : Vector F) : (k*x*k⁻¹) • (k • w) = k • (x • w) := by
    simp only [←mul_smul,inv_mul_cancel_right]
  change (k*g*k⁻¹) • ((k*a*k⁻¹) • (k • v)-k • v) =
    (k*a*k⁻¹) • (k • v)-k • v at hx
  rw [htransport,←smul_sub,htransport] at hx
  exact (MulAction.injective k) hx
end Theory.SpecificGroups.SymplecticFour.SelectedGeneration

namespace Theory.SpecificGroups.SymplecticFour.SelectedGeneration
open Representation.BinaryOffender
variable {F G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [Group G] [Finite G]

/-- The same displacement calculation in a faithful ambient natural action,
with its symplectic component and field twists retained. -/
theorem ambient_large_small_mover_fixes_displacement
    (hF : Nat.card F = 4) (B : Subgroup G) [B.Normal]
    (hcent : centralizer (B : Set G) ≤ B) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) G (Vector F)) (hfaith : Function.Injective ρ)
    (hB : ∀ b : B, ∀ v, ρ (b:G) v = symplecticNatural 2 (e b) v)
    (P E A : Subgroup G) (hP : IsPGroup 2 P) (hEP : E ≤ P) (hAP : A ≤ P)
    (hEc : Nat.card E = 64)
    (hE : Nat.card (Vector F ⧸ fixedSpace ρ E) ≤ 16)
    (hA : Nat.card (Vector F ⧸ fixedSpace ρ A) ≤ 4 ∨ A ≤ E) :
    ∀ g ∈ E, ∀ a ∈ A, ∀ v, ρ g (ρ a v-v) = ρ a v-v := by
  have hEB := small_offender_le_symplectic_component hF B hcent e ρ hfaith hB E hE
    (by rw [hEc]; omega)
  have hAB : A ≤ B := by
    rcases hA with hA | hAE
    · exact small_actor_le_symplectic_component hF B hcent e ρ hB A hA
    · exact hAE.trans hEB
  let E₀ := (E.subgroupOf B).map e.toMonoidHom
  let A₀ := (A.subgroupOf B).map e.toMonoidHom
  let P₀ := (P.subgroupOf B).map e.toMonoidHom
  let σ := restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)
  let f := B.subtype.comp e.symm.toMonoidHom
  have himage (K : Subgroup G) (hKB : K ≤ B) :
      ((K.subgroupOf B).map e.toMonoidHom).map f = K := by
    rw [Subgroup.map_map]
    have hf : f.comp e.toMonoidHom = B.subtype := by ext b; simp [f]
    rw [hf,map_subgroupOf_eq_of_le hKB]
  have hindex (K : Subgroup G) (hKB : K ≤ B) :
      Nat.card (Vector F ⧸ fixedSpace σ ((K.subgroupOf B).map e.toMonoidHom)) =
        Nat.card (Vector F ⧸ fixedSpace ρ K) := by
    have hd := fixedCodim_map_equivariant σ ρ f (LinearEquiv.refl _ _)
      (fun g v => by
        change symplecticNatural 2 g v = ρ (e.symm g).val v
        rw [hB,e.apply_symm_apply]) ((K.subgroupOf B).map e.toMonoidHom)
    rw [himage K hKB] at hd
    calc
      _ = 2 ^ fixedCodim σ ((K.subgroupOf B).map e.toMonoidHom) := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]; rfl
      _ = 2 ^ fixedCodim ρ K := congrArg (2 ^ ·) hd
      _ = _ := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]; rfl
  have hEc₀ : Nat.card E₀ = 64 := by
    rw [card_map_of_injective e.injective,
      ←card_map_of_injective B.subtype_injective,map_subgroupOf_eq_of_le hEB,hEc]
  have hh := large_small_mover_fixes_displacement hF E₀ A₀ P₀
    (hP.comap_subtype.map e.toMonoidHom)
    (map_mono (comap_mono hEP)) (map_mono (comap_mono hAP)) hEc₀
    ((hindex E hEB).trans_le hE) (hA.elim
      (fun h => Or.inl ((hindex A hAB).trans_le h))
      (fun h => Or.inr (map_mono (comap_mono h))))
  intro g hg a ha v
  have hBg : ∀ w, ρ g w = e ⟨g,hEB hg⟩ • w := hB ⟨g,hEB hg⟩
  have hBa : ∀ w, ρ a w = e ⟨a,hAB ha⟩ • w := hB ⟨a,hAB ha⟩
  rw [hBg,hBa]
  exact hh (e ⟨g,hEB hg⟩) (mem_map_of_mem e.toMonoidHom hg)
    (e ⟨a,hAB ha⟩) (mem_map_of_mem e.toMonoidHom ha) v

variable {D : Type*} [Group D]
open scoped commutatorElement
/-- Lift displacement fixation to the whole embedded module, without
factoring out any additional central subgroup. -/
theorem large_small_mover_centralizes_commutator
    (hF : Nat.card F = 4) (B : Subgroup G) [B.Normal]
    (hcent : centralizer (B : Set G) ≤ B) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) G (Vector F)) (hfaith : Function.Injective ρ)
    (hB : ∀ b : B, ∀ v, ρ (b:G) v = symplecticNatural 2 (e b) v)
    (N P E A : Subgroup D) (hP : IsPGroup 2 P) (hEP : E ≤ P) (hAP : A ≤ P)
    (q : D →* G) (hEc : Nat.card (E.map q) = 64)
    (j : Multiplicative (Vector F) →* D) (hj : Function.Injective j) (hjr : j.range = N)
    (hact : ∀ g v, j (Multiplicative.ofAdd (ρ (q g) v)) =
      g*j (Multiplicative.ofAdd v)*g⁻¹)
    (hE : (centralizer (E : Set D)).relIndex N ≤ 16)
    (hA : (centralizer (A : Set D)).relIndex N ≤ 4 ∨ A ≤ E) :
    ⁅A,N⁆ ≤ centralizer (E : Set D) := by
  have hindex (K : Subgroup D) : (centralizer (K : Set D)).relIndex N =
      Nat.card (Vector F ⧸ fixedSpace ρ (K.map q)) := by
    have hi := embedded_centralizer_index ρ N K j hj hjr (q.comp K.subtype)
      (fun x v => hact x.val v)
    rw [MonoidHom.range_comp,range_subtype] at hi
    rw [hi,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    rfl
  have hh := ambient_large_small_mover_fixes_displacement hF B hcent e ρ hfaith hB
    (P.map q) (E.map q) (A.map q) (hP.map q) (map_mono hEP) (map_mono hAP)
    hEc (by rwa [←hindex]) (hA.elim
      (fun h => Or.inl ((hindex A).symm.trans_le h)) (fun h => Or.inr (map_mono h)))
  apply commutator_le.mpr
  intro a ha n hn
  obtain ⟨v,rfl⟩ := (show n ∈ j.range from hjr.symm ▸ hn)
  have hd : ⁅a,j v⁆ = j (Multiplicative.ofAdd (ρ (q a) v.toAdd-v.toAdd)) := by
    rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
    rfl
  rw [hd]
  intro g hg
  have he := congrArg (fun w => j (Multiplicative.ofAdd w))
    (hh (q g) (mem_map_of_mem q hg) (q a) (mem_map_of_mem q ha) v.toAdd)
  rw [hact] at he
  exact (mul_inv_eq_iff_eq_mul).mp he
end Theory.SpecificGroups.SymplecticFour.SelectedGeneration
