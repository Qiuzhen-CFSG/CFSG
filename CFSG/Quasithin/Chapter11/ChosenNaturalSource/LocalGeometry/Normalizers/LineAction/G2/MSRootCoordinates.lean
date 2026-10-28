module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.G2.MSReciprocal

/-!
# Root parameters and their compatible scalar maps

An inner natural G₂(4) offender has one common conjugator for the A, B and C
root curves. Its original quotient map therefore admits all three root
parameters with exactly the same kernel. The natural displacement is linear
in the vector coordinates, while its short-root parameter occurs squared.
Comparing these formulas shows that compatible maps on the parameter and
output spaces are multiplication by zero or one; an injective such map is
identity. No linearity is assumed for the two maps.

MSCriticalCoordinates applies these formulas to the original reciprocal
critical actions. The central-cover kernel comparison remains necessary
before this obstruction excludes the source G₂ branch.
Source: Meierfrankenfeld--Stellmacher (1993), (3.2), pp.865--866. The root
formulas use the existing attributed octonion model (LICENSES/ATLAS.txt).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.G2MS
variable {F : Type*} [Field F]

/-- Displacement on the lower three coordinates by the actual A--B--C roots. -/
def rootDisplacement (p v : Fin 3 → F) : Fin 3 → F :=
  ![p 0 * v 1 + p 1 * v 0 + (p 2)^2 * v 2,
    p 0 * v 2 + p 2 * v 0, p 1 * v 2 + p 2 * v 1]

private theorem compatible_map_formula
    (s t : (Fin 3 → F) → (Fin 3 → F))
    (h : ∀ p v, rootDisplacement (s p) v = t (rootDisplacement p v))
    (w : Fin 3 → F) :
    t w = rootDisplacement (s ![0,0,1]) ![w 1,w 2,w 0] := by
  have hw : rootDisplacement ![0,0,1] ![w 1,w 2,w 0] = w := by
    ext i
    fin_cases i <;> simp [rootDisplacement]
  exact (congrArg t hw).symm.trans (h ![0,0,1] ![w 1,w 2,w 0]).symm

/-- The common output map for the long and short roots has only binary scalars.
No linearity of the proposed parameter or output maps is assumed. -/
theorem rootDisplacement_compatible_maps
    (s t : (Fin 3 → F) → (Fin 3 → F))
    (h : ∀ p v, rootDisplacement (s p) v = t (rootDisplacement p v)) :
    ∃ c : F, (c = 0 ∨ c = 1) ∧
      (∀ p, s p = c • p) ∧ (∀ w, t w = c • w) := by
  let u := s ![0,0,1]
  have ht := compatible_map_formula s t h
  have hA0 := h ![1,0,0] ![1,0,0]
  have hA1 := h ![1,0,0] ![0,1,0]
  have hA2 := h ![1,0,0] ![0,0,1]
  rw [ht] at hA0 hA1 hA2
  have ha1 : s ![1,0,0] 1 = 0 := by
    simpa [rootDisplacement] using congrFun hA0 0
  have ha2 : s ![1,0,0] 2 = 0 := by
    simpa [rootDisplacement] using congrFun hA0 1
  have hu0 : u 0 = 0 := by
    simpa [rootDisplacement,u] using (congrFun hA1 1).symm
  have hu1 : u 1 = 0 := by
    simpa [rootDisplacement,u,ha2] using (congrFun hA1 2).symm
  have ha0 : s ![1,0,0] 0 = (u 2)^2 := by
    simpa [rootDisplacement,u] using congrFun hA1 0
  have hsq : (u 2)^2 = u 2 := by
    have hh : s ![1,0,0] 0 = u 2 := by
      simpa [rootDisplacement,u] using congrFun hA2 1
    exact ha0.symm.trans hh
  have hc : u 2 = 0 ∨ u 2 = 1 := by
    have hz : u 2 * (u 2 - 1) = 0 := by rw [mul_sub,mul_one,←pow_two,hsq,sub_self]
    exact (mul_eq_zero.mp hz).imp_right sub_eq_zero.mp
  have ht' (w : Fin 3 → F) : t w = u 2 • w := by
    rw [ht]
    change rootDisplacement u _ = _
    ext i
    fin_cases i <;> simp [rootDisplacement,hu0,hu1,hsq]
  refine ⟨u 2,hc,?_,ht'⟩
  intro p
  have h0 := h p ![1,0,0]
  have h1 := h p ![0,1,0]
  rw [ht'] at h0 h1
  ext i
  fin_cases i
  · simpa [rootDisplacement] using congrFun h1 0
  · simpa [rootDisplacement] using congrFun h0 0
  · simpa [rootDisplacement] using congrFun h0 1

/-- An invertible common scalar on the actor and displacement is the identity. -/
theorem rootDisplacement_compatible_injective
    (s t : (Fin 3 → F) → (Fin 3 → F)) (hs : Function.Injective s)
    (h : ∀ p v, rootDisplacement (s p) v = t (rootDisplacement p v)) :
    s = id ∧ t = id := by
  obtain ⟨c,hc,hs',ht⟩ := rootDisplacement_compatible_maps s t h
  rcases hc with rfl | rfl
  · have he : (0 : Fin 3 → F) = 1 := hs (by rw [hs',hs']; simp)
    exact (zero_ne_one (congrFun he 0)).elim
  · exact ⟨funext (fun p => by simpa using hs' p),funext (fun w => by simpa using ht w)⟩

open Atlas.G2
open CFSG.Quasithin.ChapterB.QuasisimpleSource

/-- An actual offender is parametrized by all three marked root curves, with
one common conjugator and the original component inclusion. -/
theorem inner_offender_parameters
    {A J : Type*} [Group A] [Group J] [Finite J]
    (F : BinaryField) (hF : F.degree = 2)
    (ρ : Representation (ZMod 2) J (Natural.Space F.Carrier))
    (B : Subgroup J) [B.Normal] (e : B ≃* Model F.Carrier)
    (he : ∀ (b : B) v, ρ (b : J) v = Natural.action F.Carrier (e b) v)
    (hf : Function.Injective ρ) (δ : A →* J) (hδ : IsOffender ρ δ.range) :
    ∃ g : Model F.Carrier, ∃ p : A →* Multiplicative (Fin 3 → F.Carrier),
      Function.Surjective p ∧ p.ker = δ.ker ∧
      ∀ x, δ x = (e.symm (g * EvenTwoRank.elementaryEmbedding F.Carrier (p x) * g⁻¹) : J) := by
  obtain ⟨hin,_,_⟩ := ambient_offender_rank_six F hF ρ B e he hf δ.range hδ
  let β : A →* Model F.Carrier := e.toMonoidHom.comp (δ.codRestrict B (fun x => hin ⟨x,rfl⟩))
  have hβrange : β.range = (δ.range.subgroupOf B).map e.toMonoidHom := by
    rw [MonoidHom.subgroupOf_range_eq_of_le δ hin]
    exact MonoidHom.range_comp _ _
  have hβoff : IsOffender (NaturalOffenders.binaryNatural (F := F.Carrier)) β.range := by
    rw [hβrange]
    exact (hδ.subgroupOf ρ hin).map_equivariant (ρ.comp B.subtype)
      (NaturalOffenders.binaryNatural (F := F.Carrier)) e.toMonoidHom e.injective
      (LinearEquiv.refl (ZMod 2) _) (fun b v => he b v)
  have hc : Nat.card F.Carrier = 2^2 := by rw [F.card_eq,hF]
  obtain ⟨g,hg⟩ := NaturalOffenders.natural_offender_conjugate_elementary hc (by decide) β.range hβoff
  let γ := (MulAut.conj g⁻¹).toMonoidHom.comp β
  have hγrange : γ.range = EvenTwoRank.elementary F.Carrier := by
    apply le_antisymm
    · rintro x ⟨a,rfl⟩
      have hb : β a ∈ (EvenTwoRank.elementary F.Carrier).map (MulAut.conj g).toMonoidHom :=
        hg ▸ (show β a ∈ β.range from ⟨a,rfl⟩)
      obtain ⟨b,hb,heq⟩ := hb
      change g⁻¹ * β a * (g⁻¹)⁻¹ ∈ _
      rw [←heq]
      simpa [MulAut.conj_apply,mul_assoc] using hb
    · intro x hx
      have hm : g*x*g⁻¹ ∈ β.range := by
        rw [hg]
        exact mem_map_of_mem (MulAut.conj g).toMonoidHom hx
      obtain ⟨a,ha⟩ := hm
      exact ⟨a,by simp [γ,ha,mul_assoc]⟩
  let r := γ.codRestrict (EvenTwoRank.elementary F.Carrier) (fun x => hγrange ▸ ⟨x,rfl⟩)
  let p := (EvenTwoRank.elementaryEquiv F.Carrier).symm.toMonoidHom.comp r
  have hp (x : A) : EvenTwoRank.elementaryEmbedding F.Carrier (p x) = γ x :=
    MonoidHom.apply_ofInjective_symm (EvenTwoRank.elementaryEmbedding_injective F.Carrier) (r x)
  refine ⟨g,p,?_,?_,?_⟩
  · apply (EvenTwoRank.elementaryEquiv F.Carrier).symm.surjective.comp
    intro x
    obtain ⟨a,ha⟩ := (show x.val ∈ γ.range from hγrange.symm ▸ x.property)
    exact ⟨a,Subtype.ext ha⟩
  · ext x
    change p x = 1 ↔ δ x = 1
    rw [←(EvenTwoRank.elementaryEmbedding_injective F.Carrier).eq_iff,map_one,hp]
    change g⁻¹ * e ⟨δ x,hin ⟨x,rfl⟩⟩ * (g⁻¹)⁻¹ = 1 ↔ _
    change (MulAut.conj g⁻¹) (e ⟨δ x,hin ⟨x,rfl⟩⟩) = 1 ↔ _
    rw [(MulAut.conj g⁻¹).map_eq_one_iff,e.map_eq_one_iff]
    exact Subtype.ext_iff
  · intro x
    change (⟨δ x,hin ⟨x,rfl⟩⟩ : B).val = _
    apply congrArg Subtype.val
    apply e.injective
    change β x = e (e.symm _)
    rw [e.apply_symm_apply,hp]
    simp [γ,mul_assoc]

open Atlas.G2.Restricted.NaturalCoordinates

private theorem elementary_action_displacement {F : Type*} [Field F] [CharP F 2]
    (p : Multiplicative (Fin 3 → F)) (v : Fin 6 → F) :
    action F (EvenTwoRank.elementaryEmbedding F p) v - v =
      ![rootDisplacement p.toAdd ![v 3,v 4,v 5] 0,
        rootDisplacement p.toAdd ![v 3,v 4,v 5] 1,
        rootDisplacement p.toAdd ![v 3,v 4,v 5] 2,0,0,0] := by
  have he : EvenTwoRank.elementaryEmbedding F p =
      rootA (p.toAdd 0) * (rootB (p.toAdd 1) * rootC (p.toAdd 2)) := by
    simp [EvenTwoRank.elementaryEmbedding,EvenTwoRank.elementaryParameters,
      unipotentProduct,mul_assoc]
  rw [he,map_mul,Module.End.mul_apply,map_mul,Module.End.mul_apply]
  ext i
  fin_cases i <;> simp [rootDisplacement] <;> ring

/-- Coordinates use the same conjugator on all root parameters. -/
theorem inner_offender_displacement_coordinates
    {A J : Type*} [Group A] [Group J] [Finite J]
    (F : BinaryField) (hF : F.degree = 2)
    (ρ : Representation (ZMod 2) J (Natural.Space F.Carrier))
    (B : Subgroup J) [B.Normal] (e : B ≃* Model F.Carrier)
    (he : ∀ (b : B) v, ρ (b : J) v = Natural.action F.Carrier (e b) v)
    (hf : Function.Injective ρ) (δ : A →* J) (hδ : IsOffender ρ δ.range) :
    ∃ p : A →* Multiplicative (Fin 3 → F.Carrier), Function.Surjective p ∧
      p.ker = δ.ker ∧ ∃ η : Natural.Space F.Carrier ≃ₗ[F.Carrier] (Fin 6 → F.Carrier),
      ∀ x v, η (ρ (δ x) v) - η v =
        ![rootDisplacement (p x).toAdd ![η v 3,η v 4,η v 5] 0,
          rootDisplacement (p x).toAdd ![η v 3,η v 4,η v 5] 1,
          rootDisplacement (p x).toAdd ![η v 3,η v 4,η v 5] 2,0,0,0] := by
  obtain ⟨g,p,hp,hk,hmark⟩ := inner_offender_parameters F hF ρ B e he hf δ hδ
  let η := (LinearMap.GeneralLinearGroup.toLinearEquiv ((Natural.action F.Carrier).asGroupHom g⁻¹)).trans (equiv F.Carrier)
  refine ⟨p,hp,hk,η,?_⟩
  intro x v
  have ht : η (ρ (δ x) v) = action F.Carrier (EvenTwoRank.elementaryEmbedding F.Carrier (p x)) (η v) := by
    change equiv F.Carrier (Natural.action F.Carrier g⁻¹ (ρ (δ x) v)) = _
    rw [hmark,he,e.apply_symm_apply]
    have hg : g⁻¹ * (g * EvenTwoRank.elementaryEmbedding F.Carrier (p x) * g⁻¹) =
        EvenTwoRank.elementaryEmbedding F.Carrier (p x) * g⁻¹ := by group
    rw [←Module.End.mul_apply,←map_mul,hg,map_mul,Module.End.mul_apply]
    exact LinearMap.congr_fun ((repEquiv F.Carrier).isIntertwining' _) _
  rw [ht]
  exact elementary_action_displacement (p x) (η v)


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.G2MS
