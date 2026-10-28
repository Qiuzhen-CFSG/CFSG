module
public import Theory.SpecificGroups.SymplecticFour.SmallMoverKernel
public import Theory.Representation.SymplecticConjugatePair.Ambient.TwoGeometry.Coefficients
public import Mathlib.FieldTheory.Galois.Basic
public import Theory.SpecificGroups.SymplecticFour.NormalMoverRoot

/-!
# Component intersections of normal ambient symplectic movers

The natural marking of a centric Sp4(4) component identifies its ambient
field-linear actors with that component. The field automorphism map thus
bounds the component index by two.

If a Sylow-normal actor has component intersection in the plane radical,
its commutators with the full short root fix the second basis vector.
Semilinearity then forces every field twist to be trivial, so the whole
actor is inner. Consequently, for an actor of order at least sixty-four
and moving index above sixteen, its component intersection retains order
and moving index above sixteen. These are precisely the inputs to the
normal-mover long-root generator.

Source: MS93 (5.5), pp.915--917, using the natural-normalizer calculation
of Aschbacher--Smith H.7, pp.388--389. The original-kernel consumer is
Sp4Four.SourceComparison.OriginalAmbientMoverGeneration.
-/

public noncomputable section
set_option linter.unusedSimpArgs false
open Matrix Subgroup Representation
open scoped commutatorElement
open Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair.Ambient
open SymplecticConjugatePair.Ambient.Normalizer
namespace SymplecticNaturalNormalizer
variable {G F : Type*} [Group G] [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- A field-linear ambient actor is already in the centric component. -/
theorem mem_component_of_linear
    (B : Subgroup G) [B.Normal] (hcent : centralizer (B : Set G) ≤ B)
    (hcard : 2 < Nat.card F) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) G (Vector F))
    (hB : ∀ b : B, ∀ w, ρ (b:G) w = symplecticNatural 2 (e b) w)
    (x : G) (hlin : ∀ (c : F) w, ρ x (c • w) = c • ρ x w) : x ∈ B := by
  let s : naturalNormalizer (F := F) :=
    ⟨linearAction ρ x,operator_mem_naturalNormalizer B hcard e ρ hB x⟩
  obtain ⟨a,g,σ,he⟩ := naturalNormalizer_semilinear s.val s.property
  have hσ (c : F) (v : Vector F) : ρ x (c • v) = σ c • ρ x v := by
    change s.val (c • v) = σ c • s.val v
    rw [he,he]
    have hh : fieldVector σ (c • v) = σ c • fieldVector σ v := by
      funext i
      exact map_mul σ c (v i)
    change a.val • symplecticNatural 2 g (fieldVector σ (c • v)) = _
    rw [hh,map_smul,smul_comm]
    rfl
  have hs : σ = RingEquiv.refl F :=
    SemilinearCoefficients.coefficient_unique ρ x hσ hlin
  have hform (v : Vector F) : ρ x v = a.val • symplecticNatural 2 g v := by
    change s.val v = _
    rw [he,hs]
    rfl
  have hBe (b : B) : linearAction ρ (b:G) = naturalHom (e b) :=
    LinearEquiv.ext (hB b)
  have hg : conjugation hcard s = MulAut.conj g := by
    apply conjugation_eq_of_intertwines hcard s _
    intro b v
    change ρ x (symplecticNatural 2 b v) = symplecticNatural 2 (g*b*g⁻¹) (ρ x v)
    rw [hform,hform,map_smul]
    simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]
  have hc (b : B) : e (MulAut.conjNormal x b) = conjugation hcard s (e b) := by
    apply naturalHom_injective
    rw [←hBe]
    change linearAction ρ (x * (b:G) * x⁻¹) = _
    rw [map_mul,map_mul,map_inv,hBe]
    exact (conjugation_apply hcard s (e b)).symm
  have hxN : x ∈ normalizer (B : Set G) := by rw [normalizer_eq_top]; trivial
  apply Subgroup.mem_of_normalizerMonoidHom_mem_inner B hcent ⟨x,hxN⟩
  refine ⟨e.symm g,?_⟩
  apply MulEquiv.ext
  intro b
  apply e.injective
  change e (e.symm g*b*(e.symm g)⁻¹) = e (MulAut.conjNormal x b)
  rw [hc,hg,map_mul,map_mul,map_inv,e.apply_symm_apply]
  rfl

omit [CharP F 2] in
private theorem field_four_automorphisms_card_le_two (hF : Nat.card F = 4) :
    Nat.card (F ≃+* F) ≤ 2 := by
  let f : (F ≃+* F) → (F ≃ₐ[ZMod 2] F) := fun σ =>
    AlgEquiv.ofRingEquiv (f := σ) (fun z =>
      congrArg (fun f : ZMod 2 →+* F => f z)
        (Subsingleton.elim (σ.toRingHom.comp (algebraMap (ZMod 2) F))
          (algebraMap (ZMod 2) F)))
  have hf : Function.Injective f := fun σ τ h => RingEquiv.ext fun x =>
    congrArg (fun f : F ≃ₐ[ZMod 2] F => f x) h
  have hd : Module.finrank (ZMod 2) F = 2 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
    rw [Nat.card_zmod,hF] at hc
    exact Nat.pow_right_injective (by decide : 1 < 2) hc.symm
  have hh := Nat.card_le_card_of_injective f hf
  rwa [IsGalois.card_aut_eq_finrank,hd] at hh

/-- The natural field-four extension has component index at most two. -/
theorem component_index_le_two [Finite G]
    (hF : Nat.card F = 4) (B : Subgroup G) [B.Normal]
    (hcent : centralizer (B : Set G) ≤ B) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) G (Vector F))
    (hB : ∀ b : B, ∀ w, ρ (b:G) w = symplecticNatural 2 (e b) w) : B.index ≤ 2 := by
  have hsemi (a : G) : ∃ σ : F ≃+* F, ∀ c v, ρ a (c • v) = σ c • ρ a v :=
    exists_field_twist ⟨linearAction ρ a,
      operator_mem_naturalNormalizer B (by omega) e ρ hB a⟩
  let π := SemilinearCoefficients.coefficientHom ρ hsemi
  have hker : π.ker ≤ B := by
    intro x hx
    apply mem_component_of_linear B hcent (by omega) e ρ hB x
    exact (SemilinearCoefficients.coefficient_eq_one_iff ρ π
      (SemilinearCoefficients.coefficientHom_smul ρ hsemi) x).mp hx
  let : Finite (F ≃+* F) := Finite.of_injective
    (fun σ : F ≃+* F => (σ : F → F)) DFunLike.coe_injective
  have hk : π.ker.index ≤ 2 := by
    rw [index_ker]
    exact (Nat.card_le_card_of_injective _ π.range.subtype_injective).trans
      (field_four_automorphisms_card_le_two hF)
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero index_ne_zero_of_finite) (index_dvd_of_le hker)).trans hk

open Representation.OneCohomology.SymplecticFour CentralRootGeometry

omit [Finite F] [Algebra (ZMod 2) F] in
private theorem root6_apply (t : F) (v : Vector F) :
    symplecticNatural 2 (rootElement 6 t) v =
      v + t • Sum.elim ![v (.inl 1),0] ![0,v (.inr 0)] := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [symplecticNatural,rootElement,rootMatrix,Matrix.mulVec,dotProduct,
      Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.single,Matrix.fromBlocks,
      CharTwo.neg_eq,Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_comm]

omit [Finite F] [Algebra (ZMod 2) F] in
private theorem root6_on_second (t : F) :
    symplecticNatural 2 (rootElement 6 t) (Pi.single (.inl 1) 1) =
      Pi.single (.inl 1) 1 + t • (Pi.single (.inl 0) 1) := by
  rw [root6_apply]
  congr 2
  funext i
  rcases i with i | i <;> fin_cases i <;> simp

omit [Finite F] in
private theorem linear_of_commutes_root6_on_second
    (ρ : Representation (ZMod 2) G (Vector F)) (x : G)
    (hsemi : ∃ σ : F ≃+* F, ∀ c v, ρ x (c • v) = σ c • ρ x v)
    (hc : ∀ t : F,
      ρ x (symplecticNatural 2 (rootElement 6 t) (Pi.single (.inl 1) 1)) =
        symplecticNatural 2 (rootElement 6 t) (ρ x (Pi.single (.inl 1) 1))) :
    ∀ (c : F) v, ρ x (c • v) = c • ρ x v := by
  obtain ⟨σ,hσ⟩ := hsemi
  let v₀ : Vector F := Pi.single (.inl 0) 1
  let v₁ : Vector F := Pi.single (.inl 1) 1
  let w := ρ x v₀
  let z := ρ x v₁
  have hw : w ≠ 0 := by
    intro hh
    have h0 : v₀ = 0 := (ρ.apply_bijective x).1 (hh.trans (map_zero _).symm)
    have hh := congrFun h0 (.inl 0)
    simp [v₀] at hh
  have ht (t : F) : σ t • w = t • Sum.elim ![z (.inl 1),0] ![0,z (.inr 0)] := by
    have hh := hc t
    rw [root6_on_second,map_add,hσ,root6_apply] at hh
    exact add_left_cancel hh
  have hwD : w = Sum.elim ![z (.inl 1),0] ![0,z (.inr 0)] := by
    simpa using ht 1
  have hσid (t : F) : σ t = t := by
    apply smul_left_injective F hw
    change σ t • w = t • w
    rw [ht,←hwD]
  intro t v
  rw [hσ,hσid]

/-- A Sylow-normal actor with plane-radical component intersection is inner.
The commutators with the full first short root remove every field twist. -/
theorem inner_of_normal_intersection_le_plane
    (B : Subgroup G) [B.Normal] (hcent : centralizer (B : Set G) ≤ B)
    (hcard : 2 < Nat.card F) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) G (Vector F))
    (hB : ∀ b : B, ∀ v, ρ (b:G) v = symplecticNatural 2 (e b) v)
    (P E : Subgroup G) (hPN : P ≤ normalizer (E : Set G))
    (hU : unipotent ≤ (P.subgroupOf B).map e.toMonoidHom)
    (hplane : (E.subgroupOf B).map e.toMonoidHom ≤
      (wing true).map (unipotent (F := F)).subtype) : E ≤ B := by
  intro x hx
  apply mem_component_of_linear B hcent hcard e ρ hB x
  apply linear_of_commutes_root6_on_second ρ x
  · exact exists_field_twist ⟨linearAction ρ x,
      operator_mem_naturalNormalizer B hcard e ρ hB x⟩
  intro t
  let b : B := e.symm (rootElement 6 t)
  have hbP : b.val ∈ P := by
    obtain ⟨u,hu,he⟩ := hU (positive_root_mem_unipotent 6 t (by simp))
    have huB : u = b := e.injective (he.trans (e.apply_symm_apply _).symm)
    exact huB ▸ hu
  let k := ⁅x⁻¹,(b.val)⁻¹⁆
  have hkE : k ∈ E := by
    have hbN := (normalizer (E : Set G)).inv_mem (hPN hbP)
    have hh := (mem_normalizer_iff.mp hbN x).mp hx
    change b.val⁻¹*x*(b.val⁻¹)⁻¹ ∈ E at hh
    simpa [k,commutatorElement_def,mul_assoc] using E.mul_mem (E.inv_mem hx) hh
  have hkB : k ∈ B :=
    commutator_le_right ⊤ B (commutator_mem_commutator (mem_top _) (B.inv_mem b.property))
  have hkfix : ρ k (Pi.single (.inl 1) 1) = Pi.single (.inl 1) 1 := by
    rw [hB ⟨k,hkB⟩]
    obtain ⟨u,hu,he⟩ := hplane (mem_map_of_mem e.toMonoidHom (show (⟨k,hkB⟩ : B) ∈ E.subgroupOf B from hkE))
    change u.val = e ⟨k,hkB⟩ at he
    rw [←he]
    exact (SmallMovers.standardPlane_le_fixed (wing true) le_rfl
      (by intro i; simp) ⟨u,hu⟩)
  have hcomm : x*b.val = b.val*x*k := by dsimp [k]; simp [commutatorElement_def,mul_assoc]
  have hh := congrArg (fun g : G => ρ g (Pi.single (.inl 1) 1)) hcomm
  simp only [map_mul,Module.End.mul_apply,hkfix] at hh
  simpa only [hB,e.apply_symm_apply,b] using hh

open Representation.BinaryOffender in
/-- The component intersection of a large Sylow-normal mover still has
order above sixteen and moves more than sixteen natural cosets. -/
theorem large_normal_inner_part [Finite G]
    (hF : Nat.card F = 4) (B : Subgroup G) [B.Normal]
    (hcent : centralizer (B : Set G) ≤ B) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) G (Vector F))
    (hB : ∀ b : B, ∀ v, ρ (b:G) v = symplecticNatural 2 (e b) v)
    (P : Sylow 2 G) (E : Subgroup G) (hEP : E ≤ P)
    (hPN : (P : Subgroup G) ≤ normalizer (E : Set G))
    (hc : 64 ≤ Nat.card E)
    (hm : 16 < Nat.card (Vector F ⧸ fixedSpace ρ E)) :
    16 < Nat.card (E.subgroupOf B) ∧
      16 < Nat.card (Vector F ⧸ fixedSpace ρ (E ⊓ B)) := by
  have hindex := component_index_le_two hF B hcent e ρ hB
  have hrel : B.relIndex E ≤ 2 := by
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero index_ne_zero_of_finite)
      (relIndex_dvd_index_of_normal B E)).trans hindex
  have hcard : 16 < Nat.card (E.subgroupOf B) := by
    have hi := (B.subgroupOf E).card_mul_index
    change Nat.card (B.subgroupOf E) * B.relIndex E = Nat.card E at hi
    have he : Nat.card (B.subgroupOf E) = Nat.card (E.subgroupOf B) := by
      rw [←card_map_of_injective E.subtype_injective,subgroupOf_map_subtype,
        ←card_map_of_injective B.subtype_injective,subgroupOf_map_subtype,inf_comm]
    rw [he] at hi
    nlinarith
  refine ⟨hcard,?_⟩
  by_contra! hsmall
  obtain ⟨P₀,hP₀⟩ := P.exists_subgroupOf_eq_of_normal B
  let P₁ := P₀.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨k,hk⟩ := MulAction.exists_smul_eq (Sp F) P₁
    (unipotentSylow (n := 2) hF (by decide))
  have hkP : ((P₁ : Subgroup (Sp F))).map (MulAut.conj k).toMonoidHom = unipotent :=
    congrArg Sylow.toSubgroup hk
  let e' : B ≃* Sp F := e.trans (MulAut.conj k)
  have hP' : (P.subgroupOf B).map e'.toMonoidHom = unipotent := by
    change (P.subgroupOf B).map ((MulAut.conj k).toMonoidHom.comp e.toMonoidHom) = _
    rw [←Subgroup.map_map,←hP₀]
    exact hkP
  let E' := (E.subgroupOf B).map e'.toMonoidHom
  have hE'U : E' ≤ unipotent := hP' ▸ map_mono (comap_mono hEP)
  let N := E'.subgroupOf unipotent
  have hNm : N.map (unipotent (F := F)).subtype = E' := map_subgroupOf_eq_of_le hE'U
  have hNc : 16 < Nat.card N := by
    rw [←card_map_of_injective (unipotent (F := F)).subtype_injective,hNm,
      card_map_of_injective e'.injective]
    exact hcard
  let σ := restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)
  let f : Sp F →* G := B.subtype.comp e'.symm.toMonoidHom
  let K := linearAction σ k⁻¹
  have hequiv (g : Sp F) (v : Vector F) : K (σ g v) = ρ (f g) (K v) := by
    change σ k⁻¹ (σ g v) = ρ (e.symm (k⁻¹*g*k)).val (σ k⁻¹ v)
    rw [hB,e.apply_symm_apply]
    change σ k⁻¹ (σ g v) = σ (k⁻¹*g*k) (σ k⁻¹ v)
    simp only [←Module.End.mul_apply,←map_mul,mul_assoc,mul_inv_cancel,mul_one]
  have hE'm : E'.map f = E ⊓ B := by
    rw [Subgroup.map_map]
    have hf : f.comp e'.toMonoidHom = B.subtype := by ext b; simp [f]
    rw [hf,subgroupOf_map_subtype]
  have hdim := fixedCodim_map_equivariant σ ρ f K hequiv E'
  have hdimN := fixedCodim_map_equivariant
    (σ.comp (unipotent (F := F)).subtype) σ (unipotent (F := F)).subtype
    (LinearEquiv.refl _ _) (fun _ _ => rfl) N
  rw [hNm] at hdimN
  have hNmoving : SmallMovers.movingIndex N ≤ 16 := by
    rw [←SmallMovers.binary_movingIndex]
    change 2 ^ fixedCodim (σ.comp (unipotent (F := F)).subtype) N ≤ 16
    rw [hdimN,hdim,hE'm]
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hsmall
    exact hsmall
  have hNplane : N ≤ wing true := by
    by_contra hn
    obtain ⟨l,hl⟩ := SmallMovers.eq_finitePlane_of_small_not_le_wing hF N
      (hNmoving.trans (by omega)) hNmoving hn
    have hcN := SmallMovers.card_finitePlane (F := F) l
    rw [←hl,hF] at hcN
    omega
  let k₀ : G := (e.symm k).val
  let ρ' := ρ.comp (MulAut.conj k₀).toMonoidHom
  have hB' (b : B) (v : Vector F) : ρ' b.val v = symplecticNatural 2 (e' b) v := by
    change ρ ((e.symm k * b * (e.symm k)⁻¹).val) v = _
    rw [hB]
    change symplecticNatural 2 (e (e.symm k*b*(e.symm k)⁻¹)) v =
      symplecticNatural 2 (k*e b*k⁻¹) v
    simp only [map_mul,map_inv,e.apply_symm_apply]
  have hEB : E ≤ B := inner_of_normal_intersection_le_plane B hcent (by omega)
    e' ρ' hB' P E hPN hP'.ge
    (by change E' ≤ _; rw [←hNm]; exact map_mono hNplane)
  rw [inf_eq_left.mpr hEB] at hsmall
  omega
end SymplecticNaturalNormalizer
