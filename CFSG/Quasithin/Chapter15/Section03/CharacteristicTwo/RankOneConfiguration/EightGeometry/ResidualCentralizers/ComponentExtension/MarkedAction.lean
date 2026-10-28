module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.CoreQuotient
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.ThreeRank
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.QuotientTransport
public import Theory.Alternating.Aut

/-!
# The non-inner Sylow action on the marked A₈ section

The supplied component-module centralizer equality identifies the star kernel
with O₂(I). Restricting the marked star map to L gives a surjection onto the
actual A₈ with two-group kernel. Since O₂(A₈) = 1, its kernel is O₂(L), and
we obtain a quotient equivalence commuting with the original star map.

If S induced only inner automorphisms on L/O₂(L), its star image would be
even: remove an inner conjugator and use C_{S₈}(A₈) = 1. Together with I = LS,
this would make the surjective star marking have image in A₈. Thus S has a
non-inner action, the action excluded by the larger-component stabilizer
calculations. No containing-component maximality is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.32(3), printed p.1133; the automorphism calculation is the proved
GLS3 Theorem 5.2.1 in `Theory.Alternating.Aut`.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ComponentExtension
open Chapter1.Terminal Chapter1.Terminal.LinearFourActions
open NaturalModule
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem eight_twoCore_eq_bot : pCore 2 (alternatingGroup (Fin 8)) = ⊥ := by
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (pCore 2 (alternatingGroup (Fin 8))) inferInstance with h | h
  · exact h
  · have hp : IsPGroup 2 (alternatingGroup (Fin 8)) := by
      have ht : IsPGroup 2 (⊤ : Subgroup (alternatingGroup (Fin 8))) := h ▸ pCore_isPGroup
      exact ht.of_equiv topEquiv
    obtain ⟨n, hn⟩ := hp.exists_card_dvd_pow
    have hc : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      decide
    rw [hc] at hn
    have h3 : 3 ∣ 2 ^ n := dvd_trans (by norm_num : 3 ∣ 20160) hn
    exact False.elim (by simpa using (Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) h3))

/-- The module-centralizer equality supplies the exact component kernel,
without an additional multiplier or central-cover hypothesis. -/
theorem componentMap_ker_of_module (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S)
    (hcentralizer : I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hmark : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8)) :
    (componentMap d c e hmark).ker = pCore 2 c.L := by
  have hk : (d.starMap I).ker = pCore 2 I :=
    map_injective I.subtype_injective (star_kernel_eq_core_of_centralizer d c P hP hcentralizer)
  let f := componentMap d c e hmark
  have hf : f.ker = (d.starMap I).ker.comap (inclusion (component_le c)) := by
    ext l
    change f l = 1 ↔ d.starMap I (inclusion (component_le c) l) = 1
    simp only [f, componentMap, MonoidHom.codRestrict_apply, Subtype.ext_iff]
    exact e.map_eq_one_iff
  have htwo : IsPGroup 2 f.ker := by
    rw [hf, hk]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective (component_le c))
  have h := MonoidHom.comap_pCore_of_ker_isPGroup f
    (componentMap_surjective d c e hmark) htwo
  rw [eight_twoCore_eq_bot] at h
  exact h

/-- The intrinsic core quotient is the actual marked alternating group. -/
noncomputable def componentCoreEquivEightOfModule (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S)
    (hcentralizer : I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hmark : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8)) :
    (c.L ⧸ pCore 2 c.L) ≃* alternatingGroup (Fin 8) :=
  (QuotientGroup.quotientMulEquivOfEq
    (componentMap_ker_of_module d c P hP hcentralizer e hmark).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (componentMap d c e hmark)
      (componentMap_surjective d c e hmark))

/-- The quotient equivalence preserves the original component map. -/
@[simp] theorem componentCoreEquivEightOfModule_apply (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S)
    (hcentralizer : I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hmark : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8)) (l : c.L) :
    componentCoreEquivEightOfModule d c P hP hcentralizer e hmark
      (QuotientGroup.mk' (pCore 2 c.L) l) = componentMap d c e hmark l := rfl

-- The conjugation action on the marked alternating subgroup detects parity.
private theorem even_of_inner (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S)
    (hcentralizer : I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hmark : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8))
    (s : I) (hs : (s : G) ∈ normalizer (c.L : Set G))
    (hi : (s : G) ∈ innerTwoQuotientNormalizer c.L) :
    e (d.starMap I s) ∈ alternatingGroup (Fin 8) := by
  obtain ⟨b, hb, hact⟩ := (mem_innerNormalizer_iff_conjugation (⟨(s : G), hs⟩ : normalizer (c.L : Set G))).mp hi
  let f := e.toMonoidHom.comp (d.starMap I)
  let bI : I := ⟨b, component_le c hb⟩
  have hbA : f bI ∈ alternatingGroup (Fin 8) := (componentMap d c e hmark ⟨b, hb⟩).property
  have hc : (f bI)⁻¹ * f s ∈ centralizer (alternatingGroup (Fin 8) : Set (Equiv.Perm (Fin 8))) := by
    rw [mem_centralizer_iff_commutator_eq_one']
    intro a ha
    obtain ⟨x, hx⟩ := componentMap_surjective d c e hmark ⟨a, ha⟩
    let xI : I := inclusion (component_le c) x
    have hxa : f xI = a := congrArg Subtype.val hx
    have hz := hact x x.property
    have hzL : b⁻¹ * ((s : G) * (x : G) * (s : G)⁻¹) * b * (x : G)⁻¹ ∈ c.L :=
      pCoreIn_le 2 c.L hz
    let z : c.L := ⟨_, hzL⟩
    have hzcore : z ∈ pCore 2 c.L := (mem_map_iff_mem c.L.subtype_injective).mp hz
    have hzker := (componentMap_ker_of_module d c P hP hcentralizer e hmark).symm ▸ hzcore
    have hzero : f (bI⁻¹ * (s * xI * s⁻¹) * bI * xI⁻¹) = 1 :=
      congrArg Subtype.val (show componentMap d c e hmark z = 1 from hzker)
    simp only [map_mul, map_inv] at hzero
    rw [hxa] at hzero
    simpa only [commutatorElement_def, mul_inv_rev, inv_inv, mul_assoc] using hzero
  rw [GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 8 (by decide), mem_bot] at hc
  have he : f s = f bI := (eq_of_inv_mul_eq_one hc).symm
  change f s ∈ alternatingGroup (Fin 8)
  rwa [he]

/-- The marked S₈ action forces a non-inner element of S on L/O₂(L).
Innerness uses the genuine section centralizer, including normalization. -/
theorem sylow_not_le_innerNormalizer (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal)
    (hjoin : I = c.L ⊔ d.S) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S)
    (hcentralizer : I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hmark : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8)) :
    ¬ d.S ≤ innerTwoQuotientNormalizer c.L := by
  intro hinner
  let f := e.toMonoidHom.comp (d.starMap I)
  have hLI := component_le c
  have hSI : d.S ≤ I := hjoin ▸ le_sup_right
  have hIL := (normal_subgroupOf_iff_le_normalizer hLI).mp hnormal
  have hLS : c.L.subgroupOf I ⊔ d.S.subgroupOf I = ⊤ := by
    apply map_injective I.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hLI, map_subgroupOf_eq_of_le hSI,
      ← MonoidHom.range_eq_map, range_subtype, ← hjoin]
  have hle : (⊤ : Subgroup I) ≤ (alternatingGroup (Fin 8)).comap f := by
    rw [← hLS]
    refine sup_le ?_ ?_
    · intro x hx
      exact (componentMap d c e hmark ⟨x, hx⟩).property
    · intro s hs
      exact even_of_inner d c P hP hcentralizer e hmark s (hIL s.property) (hinner hs)
  obtain ⟨i, hi⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective _)) (Equiv.swap (0 : Fin 8) 1)
  have hs := hle (mem_top i)
  change e (d.starMap I i) ∈ alternatingGroup (Fin 8) at hs
  change e (d.starMap I i) = Equiv.swap (0 : Fin 8) 1 at hi
  rw [hi] at hs
  simp at hs

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ComponentExtension

end
