module
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFivePairCore
public import Theory.Representation.BinaryAlternatingFiveExtension.Splitting

/-!
# Splitting the original alternating-five block cores

When the ambient two-core is the sum of the two commuting A₅ block layers,
each block's own two-core is exactly its natural module: the other module
meets the block only in its zero fixed layer. The regular-four restriction
of the natural module then gives a complement by the proved Gaschütz
splitting theorem. These are actual group complements, not linear sections.

Source: Aschbacher–Smith C.1.13(c), printed pp.124–125, and the zero-center
branch of 10.2.1, printed pp.742–743. The symmetric extensions and the later
four-dihedral-factor argument remain distinct steps.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- A commuting second block cannot enlarge the first block's own two-core. -/
theorem alternatingFive_pair_block_core_eq
    (A B : Subgroup G) (hA : IsBlock A)
    (hb : IsAlternatingBlock B 5) (hc : ⁅A,B⁆ = ⊥)
    (hs : pCore 2 G = (blockU A).map A.subtype ⊔ (blockU B).map B.subtype) :
    pCore 2 A = blockU A := by
  let U := (blockU A).map A.subtype
  let W := (blockU B).map B.subtype
  have hAW : A ≤ centralizer (W : Set G) :=
    (commutator_eq_bot_iff_le_centralizer.mp hc).trans
      (centralizer_le (map_subtype_le _))
  have hWA : W ≤ centralizer (A : Set G) := le_centralizer_iff.mp hAW
  have hWU : W ≤ normalizer (U : Set G) :=
    (hWA.trans (centralizer_le (map_subtype_le _))).trans (centralizer_le_normalizer _)
  have hdis : Disjoint A W := by
    apply disjoint_def.mpr
    rintro x hxA ⟨b,hbU,rfl⟩
    have hbZ : b ∈ center B := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext ((commutator_eq_bot_iff_le_centralizer.mp hc) hxA y y.property)
    have hz : blockU B ⊓ center B = ⊥ := by
      rw [← blockFixed_map,hb.blockFixed_eq_bot,Subgroup.map_bot]
    have hh : b = 1 := by
      have hmem : b ∈ blockU B ⊓ center B := ⟨hbU,hbZ⟩
      rwa [hz,mem_bot] at hmem
    exact congrArg B.subtype hh
  apply le_antisymm ?_ blockU_le_core
  intro x hx
  have hxQ : (x : G) ∈ pCore 2 G :=
    pCoreIn_le_of_subnormal 2 hA.subnormal (mem_map_of_mem A.subtype hx)
  rw [hs] at hxQ
  have hprod : (x : G) ∈ (U : Set G) * (W : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left U W hWU]
    exact hxQ
  obtain ⟨u,hu,w,hw,he⟩ := hprod
  have hwA : w ∈ A := by
    have hh : w = u⁻¹ * (x : G) := by rw [←he]; group
    rw [hh]
    exact A.mul_mem (A.inv_mem ((map_subtype_le _) hu)) x.property
  have hw1 : w = 1 := disjoint_def.mp hdis hwA hw
  have hux : u = (x : G) := by simpa only [hw1,mul_one] using he
  rw [hux] at hu
  obtain ⟨y,hy,he⟩ := hu
  exact (Subtype.ext he : y = x) ▸ hy

variable {L : Type*} [Group L] [Finite L]
/-- An A₅ block whose core is its natural layer has an actual group complement. -/
theorem IsAlternatingBlock.exists_core_complement
    (h : IsAlternatingBlock L 5) (hc : pCore 2 L = blockU L) :
    ∃ K : Subgroup L, (pCore 2 L).IsComplement' K := by
  obtain ⟨r,⟨m⟩,hr⟩ := h.2.2
  let q := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := m.quotientIso.surjective.comp
    (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ m.quotientIso.injective,QuotientGroup.ker_mk']
  have hbf : Function.Bijective (QuotientGroup.mk' (blockFixed L)) :=
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk',h.blockFixed_eq_bot]),
      QuotientGroup.mk'_surjective _⟩
  let en := (MulEquiv.ofBijective (QuotientGroup.mk' (blockFixed L)) hbf).trans m.moduleIso
  let ec := (BinaryPermutation.coreEquivNatural (Fin 5) (by decide)).toAddEquiv.toMultiplicative
  let e : q.ker ≃* Multiplicative (BinaryPermutation.core (Fin 5)) :=
    ((MulEquiv.subgroupCongr (hk.trans hc)).trans en).trans ec.symm
  have he (g : L) (v : q.ker) : e (MulAut.conjNormal g v) =
      Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) (q g).val (e v).toAdd) := by
    apply ec.injective
    apply Multiplicative.toAdd.injective
    have hu : (v : L) ∈ blockU L := (hk.trans hc) ▸ v.property
    have hh := congrArg Multiplicative.toAdd (m.intertwining g ⟨v,hu⟩)
    rw [hr] at hh
    change (en (blockConjugate L g ⟨v,hu⟩)).toAdd =
      (BinaryPermutation.naturalRepresentation (Fin 5)) (q g).val (en ⟨v,hu⟩).toAdd at hh
    change (ec (e (MulAut.conjNormal g v))).toAdd =
      BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
        (BinaryPermutation.coreRepresentation (Fin 5) (q g).val (e v).toAdd)
    rw [BinaryPermutation.coreEquivNatural_equivariant]
    simp only [e,MulEquiv.trans_apply,MulEquiv.apply_symm_apply]
    change (en (blockConjugate L g ⟨v,hu⟩)).toAdd =
      (BinaryPermutation.naturalRepresentation (Fin 5)) (q g).val
        (ec (ec.symm (en ⟨v,hu⟩))).toAdd
    rw [ec.apply_symm_apply]
    exact hh
  obtain ⟨K,hK⟩ := BinaryPermutation.AlternatingFiveExtension.exists_complement q hq e he
  exact ⟨K,hk ▸ hK⟩
end CFSG.Quasithin.ChapterC
