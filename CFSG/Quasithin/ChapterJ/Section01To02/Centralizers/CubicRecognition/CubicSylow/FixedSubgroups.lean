module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.CubicSylow.Basic

/-!
# The fixed subgroup and the precise fusion premise in the cubic argument

Since B is Sylow in H = C_G(z), a three-subgroup containing B meets H
in exactly B. This proves C_R(z) = B for the actual Sylow image in G.
The transposition premise below is precisely the part of J.2.7(7) used
by the final cubic argument; it retains an actual ambient conjugator.

Source: Aschbacher–Smith, J.2.7, printed pp.435–437 (PDF pp.446–448).
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow
open Subgroup
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- The transposition clause of J.2.7(7), stated through the literal marking. -/
def TranspositionFusion
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6))) : Prop :=
  ∀ i : c.NB, orderOf i = 2 →
    (∃ t : Equiv.Perm (Fin 6), t.IsSwap ∧
      markedMap c e i = AlternatingSix.ShadowLocal.permutationAction t) →
    ∃ g : G, g * (i : G) * g⁻¹ = c.z

/-- The source equality C_R(z) = B needs only B's actual Sylow placement in H. -/
theorem centralizer_z_eq (hB : Nat.card c.B = 3)
    (P : Sylow 3 d.toTypeRuSetup.H)
    (hP : (P : Subgroup d.toTypeRuSetup.H).map d.toTypeRuSetup.H.subtype = c.B)
    (R : Sylow 3 c.NB) : ambient c R ⊓ centralizer ({c.z} : Set G) = c.B := by
  have hp : IsPGroup 3 ((ambient c R).subgroupOf d.toTypeRuSetup.H) :=
    (ambient_isPGroup c R).comap_subtype
  have hle : (P : Subgroup d.toTypeRuSetup.H) ≤
      (ambient c R).subgroupOf d.toTypeRuSetup.H := by
    intro x hx
    exact B_le c hB R (hP ▸ mem_map_of_mem d.toTypeRuSetup.H.subtype hx)
  have he := P.is_maximal' hp hle
  rw [← c.H_eq_centralizer_z, ← subgroupOf_map_subtype, he, hP]

/-- Clause (7) and Sylow conjugacy fuse a fixed subgroup of order three
to B. The conjugator is retained as an element of the original group. -/
theorem centralizer_f_conjugate_B (hB : Nat.card c.B = 3)
    (P : Sylow 3 d.toTypeRuSetup.H)
    (hP : (P : Subgroup d.toTypeRuSetup.H).map d.toTypeRuSetup.H.subtype = c.B)
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
    (h7 : TranspositionFusion c e) (R : Sylow 3 c.NB)
    (f : c.NB) (hf : orderOf f = 2)
    (ht : ∃ t : Equiv.Perm (Fin 6), t.IsSwap ∧
      markedMap c e f = AlternatingSix.ShadowLocal.permutationAction t)
    (hcard : Nat.card ↥(ambient c R ⊓ centralizer ({(f : G)} : Set G)) = 3) :
    ∃ g : G, (ambient c R ⊓ centralizer ({(f : G)} : Set G)).map
      (MulAut.conj g).toMonoidHom = c.B := by
  obtain ⟨g, hg⟩ := h7 f hf ht
  let C := ambient c R ⊓ centralizer ({(f : G)} : Set G)
  let U := C.map (MulAut.conj g).toMonoidHom
  have hUH : U ≤ d.toTypeRuSetup.H := by
    rintro _ ⟨x, hx, rfl⟩
    rw [c.H_eq_centralizer_z, mem_centralizer_singleton_iff]
    have hf' : (MulAut.conj g) (f : G) = c.z := hg
    simpa only [map_mul, hf', MulEquiv.coe_toMonoidHom] using congrArg (MulAut.conj g)
      (mem_centralizer_singleton_iff.mp hx.2)
  have hUc : Nat.card U = 3 := by
    change Nat.card (C.map (MulAut.conj g).toMonoidHom) = 3
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact hcard
  have hUp : IsPGroup 3 (U.subgroupOf d.toTypeRuSetup.H) :=
    (IsPGroup.of_card (show Nat.card U = 3 ^ 1 by simpa using hUc)).comap_subtype
  obtain ⟨Q, hUQ⟩ := hUp.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq d.toTypeRuSetup.H Q P
  have hUB : U.map (MulAut.conj (h : G)).toMonoidHom ≤ c.B := by
    rintro _ ⟨x, hx, rfl⟩
    have hq : (MulAut.conj h) (⟨x, hUH hx⟩ : d.toTypeRuSetup.H) ∈ P := by
      rw [← hh]
      exact mem_map_of_mem (MulAut.conj h).toMonoidHom (hUQ hx)
    rw [← hP]
    exact mem_map_of_mem d.toTypeRuSetup.H.subtype hq
  have hcomp : C.map (MulAut.conj ((h : G) * g)).toMonoidHom =
      U.map (MulAut.conj (h : G)).toMonoidHom := by
    change C.map (MulAut.conj ((h : G) * g)).toMonoidHom =
      (C.map (MulAut.conj g).toMonoidHom).map (MulAut.conj (h : G)).toMonoidHom
    rw [map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, MulAut.conj_apply, mul_inv_rev, mul_assoc]
  refine ⟨(h : G) * g, ?_⟩
  change C.map (MulAut.conj ((h : G) * g)).toMonoidHom = c.B
  apply eq_of_le_of_card_ge (hcomp ▸ hUB)
  rw [hB, card_map_of_injective (MulAut.conj ((h : G) * g)).injective]
  exact hcard.ge

end CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow
