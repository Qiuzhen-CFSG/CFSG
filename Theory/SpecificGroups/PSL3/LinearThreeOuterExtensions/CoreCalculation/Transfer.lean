module
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.CoreCalculation.Coordinates
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.CoreTransfer
/-!
# Transporting local block calculations into actual automorphism extensions

Normalizer conjugation through the faithful inner embedding intertwines the
literal local quotient map. The coefficient of any linear-field expression
is the coefficient already recovered by the faithful semilinear model.
The trace obstruction on SL₂ then detects this same coefficient.

Finally a normal two-subgroup of the relative join acts trivially on the
local core quotient. Two-element detection therefore proves the common-
ambient core identity for every normalizing supplement. The concrete matrix
inputs are supplied by the sibling calculation modules and their assembly.

Source: Aschbacher–Smith F.1.12, printed p.264 (PDF p.275).
-/

@[expose] public section
open Matrix
open scoped MatrixGroups commutatorElement
open Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
open Theory.GroupTheory.AutomorphismExtensionBorel
namespace Matrix.PSL3.LinearThree.OuterExtensions.CoreCalculation
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

theorem block_surjective (point : Bool) : Function.Surjective (block F point) :=
  (localFactorQuotientEquiv F point).surjective.comp (QuotientGroup.mk'_surjective _)

theorem slBlock_surjective (point : Bool) : Function.Surjective (slBlock F point) :=
  (block_surjective F point).comp (localProjectEquiv F point).surjective

omit [Finite F] [CharP F 2] in
theorem normalizer_preserves (E : Subgroup (MulAut PSL(3,F)))
    (hinner : MulAut.innerSubgroup PSL(3,F) ≤ E) (point : Bool)
    (a : Subgroup.normalizer (localIn F E hinner point : Set E)) :
    (localFactor F point).map a.val.val.toMonoidHom = localFactor F point := by
  apply (mem_normalizer_rootIn_iff _ E hinner (inner_injective F) a.val).mp
  rw [rootIn_eq_map]
  exact a.property

def actorLocal (E : Subgroup (MulAut PSL(3,F)))
    (hinner : MulAut.innerSubgroup PSL(3,F) ≤ E) (point : Bool)
    (a : Subgroup.normalizer (localIn F E hinner point : Set E)) :
    localFactor F point →* localFactor F point :=
  (a.val.val.toMonoidHom.comp (localFactor F point).subtype).codRestrict _
    (fun x => (normalizer_preserves F E hinner point a).le
      (Subgroup.mem_map_of_mem _ x.property))

omit [Finite F] [CharP F 2] in
theorem innerEmbedding_conjugate (E : Subgroup (MulAut PSL(3,F)))
    (hinner : MulAut.innerSubgroup PSL(3,F) ≤ E) (a : E) (x : PSL(3,F)) :
    a * innerEmbedding E hinner x * a⁻¹ = innerEmbedding E hinner (a.val x) := by
  apply Subtype.ext
  ext y
  simp [innerEmbedding, MulAut.conj_apply]

omit [Finite F] [CharP F 2] in
theorem localEquiv_actor (E : Subgroup (MulAut PSL(3,F)))
    (hinner : MulAut.innerSubgroup PSL(3,F) ≤ E) (point : Bool)
    (a : Subgroup.normalizer (localIn F E hinner point : Set E)) (x : localFactor F point) :
    (localIn F E hinner point).normalizerMonoidHom a (localEquiv F E hinner point x) =
      localEquiv F E hinner point (actorLocal F E hinner point a x) := by
  apply Subtype.ext
  exact innerEmbedding_conjugate F E hinner a.val x.val

theorem localBlockAction_block (E : Subgroup (MulAut PSL(3,F)))
    (hinner : MulAut.innerSubgroup PSL(3,F) ≤ E) (point : Bool)
    (a : Subgroup.normalizer (localIn F E hinner point : Set E)) (x : localFactor F point) :
    localBlockAction F E hinner point a (block F point x) =
      block F point (actorLocal F E hinner point a x) := by
  change localQuotientEquiv F E hinner point
    (localQuotientAction F E hinner point a
      ((localQuotientEquiv F E hinner point).symm (block F point x))) = _
  have hm : (localQuotientEquiv F E hinner point).symm (block F point x) =
      QuotientGroup.mk' _ (localEquiv F E hinner point x) :=
    (MulEquiv.symm_apply_eq _).mpr (localQuotientEquiv_mk F E hinner point x).symm
  calc
    _ = localQuotientEquiv F E hinner point (localQuotientAction F E hinner point a
        (QuotientGroup.mk' _ (localEquiv F E hinner point x))) :=
      congrArg (fun z => localQuotientEquiv F E hinner point
        (localQuotientAction F E hinner point a z)) hm
    _ = localQuotientEquiv F E hinner point (QuotientGroup.mk' _
        ((localIn F E hinner point).normalizerMonoidHom a (localEquiv F E hinner point x))) :=
      congrArg (localQuotientEquiv F E hinner point)
        (localQuotientAction_mk F E hinner point a (localEquiv F E hinner point x))
    _ = localQuotientEquiv F E hinner point (QuotientGroup.mk' _
        (localEquiv F E hinner point (actorLocal F E hinner point a x))) :=
      congrArg (fun z => localQuotientEquiv F E hinner point (QuotientGroup.mk' _ z))
        (localEquiv_actor F E hinner point a x)
    _ = _ := localQuotientEquiv_mk F E hinner point (actorLocal F E hinner point a x)

theorem localBlockAction_eq_iff (E : Subgroup (MulAut PSL(3,F)))
    (hinner : MulAut.innerSubgroup PSL(3,F) ≤ E) (point : Bool)
    (a : Subgroup.normalizer (localIn F E hinner point : Set E)) (φ : MulAut SL(2,F)) :
    localBlockAction F E hinner point a = φ ↔
      ∀ x : localFactor F point, block F point (actorLocal F E hinner point a x) =
        φ (block F point x) := by
  constructor
  · intro h x
    rw [← localBlockAction_block, h]
  · intro h
    ext z
    obtain ⟨x,rfl⟩ := block_surjective F point z
    rw [localBlockAction_block, h]

omit [Finite F] in
theorem coefficient_of_expression (a : linearField F) (g : GL (Fin 3) F) (σ : F ≃+* F)
    (h : a.val = linearConj F g * fieldAction F σ) : coefficient F a = σ := by
  let x : Semilinear F := ⟨⟨linearConj F g, ⟨g,rfl⟩⟩, σ⟩
  have hx : semilinearEquiv F x = a := Subtype.ext h.symm
  rw [← hx, coefficient_semilinearEquiv]

omit [Finite F] in
theorem coefficient_factorization (a : linearField F) :
    ∃ g : GL (Fin 3) F, a.val = linearConj F g * fieldAction F (coefficient F a) := by
  obtain ⟨g,σ,h⟩ := linearField_factorization F a.val a.property
  rw [coefficient_of_expression F a g σ h]
  exact ⟨g,h⟩

omit [Finite F] [CharP F 2] in
theorem linear_preserves_of_expression (point : Bool) (a : MulAut PSL(3,F))
    (g : GL (Fin 3) F) (σ : F ≃+* F) (ha : a = linearConj F g * fieldAction F σ)
    (h : (localFactor F point).map a.toMonoidHom = localFactor F point) :
    (localFactor F point).map (linearConj F g).toMonoidHom = localFactor F point := by
  rw [ha] at h
  change (localFactor F point).map
    ((linearConj F g).toMonoidHom.comp (fieldAction F σ).toMonoidHom) = _ at h
  rw [← Subgroup.map_map, field_preserves] at h
  exact h

/-- The trace obstruction forces the original coefficient to be trivial. -/
theorem coefficient_eq_one_of_trivial_block (E : Subgroup (MulAut PSL(3,F)))
    (hinner : MulAut.innerSubgroup PSL(3,F) ≤ E) (hlinear : E ≤ linearField F) (point : Bool)
    (a : Subgroup.normalizer (localIn F E hinner point : Set E)) (c : SL(2,F))
    (hformula : localBlockAction F E hinner point a = MulAut.conj c *
      Atlas.RankOneFieldAutomorphisms.slFieldAction (coefficient F ⟨a.val.val,hlinear a.val.property⟩))
    (htrivial : localBlockAction F E hinner point a = 1) :
    coefficient F ⟨a.val.val,hlinear a.val.property⟩ = 1 := by
  apply Atlas.RankOneFieldAutomorphisms.field_eq_one_of_SL_inner _ c⁻¹
  have he := hformula.symm.trans htrivial
  have hf := eq_inv_of_mul_eq_one_right he
  change Atlas.RankOneFieldAutomorphisms.slFieldAction _ = _ at hf
  rw [← map_inv] at hf
  exact hf

private theorem quotient_action_trivial {G : Type*} [Group G] (L : Subgroup G)
    (a : Subgroup.normalizer (L : Set G))
    (h : ∀ x : L, ⁅a.val, x.val⁆ ∈ (pCore 2 L).map L.subtype) :
    Subgroup.quotientAut (pCore 2 L) (L.normalizerMonoidHom a) = 1 := by
  apply MulEquiv.ext
  intro z
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) z
  have hm := Subgroup.quotientAut_apply_mk (pCore 2 L) (L.normalizerMonoidHom a) x
  apply hm.trans
  change QuotientGroup.mk' _ (L.normalizerMonoidHom a x) = QuotientGroup.mk' _ x
  apply (mul_inv_eq_one).mp
  rw [← map_inv, ← map_mul]
  apply (QuotientGroup.eq_one_iff _).mpr
  obtain ⟨y,hy,he⟩ := h x
  have he' : y = L.normalizerMonoidHom a x * x⁻¹ := Subtype.ext he
  rwa [← he']

theorem block_action_eq_one_of_commutators (E : Subgroup (MulAut PSL(3,F)))
    (hinner : MulAut.innerSubgroup PSL(3,F) ≤ E) (point : Bool)
    (a : Subgroup.normalizer (localIn F E hinner point : Set E))
    (h : ∀ x : localIn F E hinner point, ⁅a.val, x.val⁆ ∈
      (pCore 2 (localIn F E hinner point)).map (localIn F E hinner point).subtype) :
    localBlockAction F E hinner point a = 1 := by
  have hq : localQuotientAction F E hinner point a = 1 :=
    quotient_action_trivial (localIn F E hinner point) a h
  exact (congrArg (MulAut.congr (localQuotientEquiv F E hinner point)) hq).trans
    (map_one _)

/-- Transfer in the relative join, without a two-group assumption on the supplement. -/
theorem join_core_eq_of_detection (E : Subgroup (MulAut PSL(3,F)))
    (hinner : MulAut.innerSubgroup PSL(3,F) ≤ E) (point : Bool)
    (hdetect : ∀ a : Subgroup.normalizer (localIn F E hinner point : Set E),
      (∃ k : ℕ, a.val ^ (2 ^ k) = 1) → localBlockAction F E hinner point a = 1 →
        a.val ∈ localIn F E hinner point)
    (S : Subgroup E) (hS : S ≤ Subgroup.normalizer (localIn F E hinner point : Set E)) :
    (pCore 2 (localIn F E hinner point ⊔ S : Subgroup E)).map
      (localIn F E hinner point ⊔ S).subtype =
      (pCore 2 (localIn F E hinner point)).map (localIn F E hinner point).subtype := by
  apply Subgroup.join_pCore_eq_of_quotient_action_detection 2 _ S hS
  intro a ha hp hc
  let an : Subgroup.normalizer (localIn F E hinner point : Set E) :=
    ⟨a, (sup_le (localIn F E hinner point).le_normalizer hS) ha⟩
  exact hdetect an hp (block_action_eq_one_of_commutators F E hinner point an hc)
end Matrix.PSL3.LinearThree.OuterExtensions.CoreCalculation
