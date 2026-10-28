module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.LinearEvenLocals
public import Theory.SpecificGroups.SymplecticFour.EvenLocalNormalizers
/-!
# The original symplectic component normalizer lies in He

Transport the intrinsic even Sp₄ local theorem through the literal component
and ambient inclusions. The two-kernel version uses the original saturated
pair to prove kernel containment in D∩O₂(H_U); the nontrivial projective image
is retained here and supplied by the source marking in the next module.

Source: Aschbacher–Smith, 2.5.3(4), printed p.553.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}
omit [Finite G] in
theorem symplectic_normalizer_mem_He
    (D : Subgroup H) (F : Type*) [Field F] [Finite F]
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (e : D ≃* Sp F)
    (R : Subgroup D) (hp : IsPGroup 2 R) (hne : R ≠ ⊥) :
    ((normalizer (R : Set D)).map D.subtype).map H.subtype ∈ Chapter1.He G := by
  have hmap : R.map e.toMonoidHom ≠ ⊥ := by
    intro hb
    apply hne
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simpa using hb
  have hc := normalizer_core_selfCentralizing_of_equiv e R
    (Theory.SpecificGroups.SymplecticFour.normalizer_core_selfCentralizing hF hn
      (R.map e.toMonoidHom) (hp.map e.toMonoidHom) hmap)
  apply Chapter1.mem_He_iff.mpr
  let j := (equivMapOfInjective (normalizer (R : Set D)) D.subtype D.subtype_injective).trans
    (equivMapOfInjective ((normalizer (R : Set D)).map D.subtype) H.subtype H.subtype_injective)
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 j).mp hc

theorem symplectic_cover_radical_mem_He
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU)
    (D : Subgroup H) (hD : IsComponent H D)
    (F : Type*) [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (f : D →* Sp F) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hne : ((((twoCore HU).subgroupOf H).subgroupOf D).map f) ≠ ⊥) :
    (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
      H.subtype ∈ Chapter1.He G := by
  let Q := (twoCore HU).subgroupOf H
  let R := Q.subgroupOf D
  have hker : f.ker ≤ R := (le_sSup ⟨inferInstance, hk⟩ : f.ker ≤ pCore 2 D).trans
    (component_twoCore_le_saturated_intersection hpair hsat D hD)
  have hc := Theory.SpecificGroups.SymplecticFour.cover_normalizer_core_selfCentralizing
    f hf hk hF hn R (isPGroup_pCoreIn 2 HU).comap_subtype.comap_subtype hker hne
  have hnorm : (normalizer (R : Set D)).map D.subtype = D ⊓ normalizer ((D ⊓ Q : Subgroup H) : Set H) := by
    have he : R = (D ⊓ Q).subgroupOf D := by ext x; simp [R]
    rw [he, ← subgroupOf_normalizer_eq (show D ⊓ Q ≤ D from inf_le_left),
      subgroupOf_map_subtype, inf_comm]
  apply Chapter1.mem_He_iff.mpr
  let j := (equivMapOfInjective (normalizer (R : Set D)) D.subtype D.subtype_injective).trans
    (equivMapOfInjective ((normalizer (R : Set D)).map D.subtype) H.subtype H.subtype_injective)
  have hh := (Theory.Quasithin.centralizer_pCore_le_iff 2 j).mp hc
  rwa [hnorm] at hh


end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
