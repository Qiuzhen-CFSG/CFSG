module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.RankOneCover
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellNaturalModule.Section
public import Theory.SpecificGroups.SL2.NaturalFixedIndex

/-!
# Campbell's fixed-index and marked-containment inputs from C.1.17

The marked moved quotient suffices for Campbell's fixed-point index bound.
For field order greater than two, the full action quotient is SL₂ and the
actual projection from the moved subgroup is equivariant. Its natural
fixed index bounds the image order of each elementary subgroup. At field
order two, every such image has order at most two, and the exact moved
centralizer forces index at least two whenever the subgroup escapes O₂(H).
Since the moved subgroup lies in Ω₁(Z(O₂(H))), both cases give precisely
Campbell's required index inequality. Existing elementary replacement then
puts F, V and [S,V] in the actual marked J(S).

This uses only the original C.1.17 group and Baumann-fixed base. It supplies
the containment part of Campbell's comparison input; the comparison between
two groups and the uniform characteristic-pair selection remain separate.

Source: Aschbacher–Smith C.1.17–18, p.126; Campbell, *Pushing up in Finite
Groups* (1979), the opening of II.4.1, printed pp.24–25.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H : Type*} [Group B] [Finite B] [Group H] [Finite H] {e : B →* H}
 {F : Type} [Field F] [CharP F 2] [Finite F]

theorem InLocalClass.exists_large_campbell_projection (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (hF : 2 < Nat.card F) :
    ∃ (q : H →* SL(2,F)) (f : moved e →* Multiplicative (Fin 2 → F)),
      Function.Surjective q ∧ q.ker = localKernel e ∧ Function.Surjective f ∧
      ∀ (g : H) (w : moved e), (f (movedConjugate e g w)).toAdd = Matrix.mulVec (q g).val (f w).toAdd := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let _ : IsElementaryAbelian 2 (localV e) := h.localV_elementary
  let _ : IsElementaryAbelian 2 (moved e) := IsElementaryAbelian.of_le (moved_le_localV e)
  obtain ⟨ρ,f,hfaith,hf,hcoords,hconj,hnat,hker⟩ := h.exists_faithful_natural_action m
  obtain ⟨E,hE⟩ := m.exists_actor_equiv_sl hF
  let hL := h.generalizedFitting_localStar_eq_top hB m hF
  let a : LocalStar e ≃* SL(2,F) :=
    (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hL.symm)).trans E
  let q := a.toMonoidHom.comp (QuotientGroup.mk' (localKernel e))
  let f' := m.moduleIso.toMonoidHom.comp (QuotientGroup.mk' (movedFixed e))
  have hq : Function.Surjective q := a.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqker : q.ker = localKernel e := by
    ext g
    change a (QuotientGroup.mk' (localKernel e) g) = 1 ↔ _
    rw [a.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff g
  refine ⟨q,f',hq,hqker,m.moduleIso.surjective.comp (QuotientGroup.mk'_surjective _),?_⟩
  intro g w
  let z : generalizedFitting (LocalStar e) :=
    ⟨QuotientGroup.mk' (localKernel e) g,by rw [hL]; trivial⟩
  change (m.moduleIso (QuotientGroup.mk' (movedFixed e) (movedConjugate e g w))).toAdd = _
  rw [← hcoords,hconj]
  have hn := hnat z (f (Additive.ofMul w))
  rw [← hE] at hn
  rw [hcoords] at hn ⊢
  exact hn

variable {J : Type*} [Group J]

theorem InLocalClass.omegaFixedIndexBound_large (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (hF : 2 < Nat.card F)
    (d : Campbell.Embedding J H) : d.OmegaFixedIndexBound := by
  obtain ⟨q,f,hq,hqker,hf,he⟩ := InLocalClass.exists_large_campbell_projection h hB m hF
  have hcore : pCore 2 H ≤ q.ker := by rw [hqker]; exact h.core_le_localKernel
  have hpartial : Campbell.NoPartialComplement (q.ker.map (QuotientGroup.mk' (pCore 2 H))) := by
    rw [hqker]
    exact h.kernel_noPartialComplement
  intro A hA hAQ
  let D := A.map q
  have hSK : (d.sylow : Subgroup H) ⊓ q.ker = pCore 2 H :=
    d.sylow_inf_eq_core _ hcore hpartial
  have hAK : q.ker.subgroupOf A = (pCore 2 H).subgroupOf A := by
    ext a
    exact ⟨fun ha => hSK ▸ (show (a : H) ∈ (d.sylow : Subgroup H) ⊓ q.ker from
      ⟨hA.1 a.property, ha⟩), fun ha => hcore ha⟩
  have hcard : (pCore 2 H).relIndex A = Nat.card D := by
    rw [← Subgroup.relIndex_ker A q]
    change ((pCore 2 H).subgroupOf A).index = (q.ker.subgroupOf A).index
    rw [hAK]
  have hD : D ≠ ⊥ := by
    intro hD
    apply hAQ
    intro a ha
    have hqa : q a = 1 := by
      have hh : q a ∈ D := Subgroup.mem_map_of_mem q ha
      simpa only [hD, mem_bot] using hh
    have hk : (⟨a,ha⟩ : A) ∈ q.ker.subgroupOf A := hqa
    rw [hAK] at hk
    exact hk
  let : IsElementaryAbelian 2 A := hA.2.1
  have hpD : IsPGroup 2 D := (IsElementaryAbelian.isPGroup 2 A).map q
  have hpre : (centralizer (A : Set H)).subgroupOf (moved e) ≤
      (Theory.SpecificGroups.SL2.NaturalFixedIndex.fixed D).comap f := by
    intro w hw b hb
    obtain ⟨a,ha,rfl⟩ := hb
    have hc : movedConjugate e a w = w := by
      apply Subtype.ext
      change a * (w : H) * a⁻¹ = w
      have hcomm : a * (w : H) = (w : H) * a := hw a ha
      rw [hcomm,mul_inv_cancel_right]
    change Matrix.mulVec (q a).val (f w).toAdd = (f w).toAdd
    simpa only [hc] using (he a w).symm
  have hi : (Theory.SpecificGroups.SL2.NaturalFixedIndex.fixed D).index ≤
      (centralizer (A : Set H)).relIndex (moved e) := by
    rw [← (Theory.SpecificGroups.SL2.NaturalFixedIndex.fixed D).index_comap_of_surjective hf]
    exact Subgroup.index_antitone hpre
  rw [hcard]
  exact (Theory.SpecificGroups.SL2.NaturalFixedIndex.card_le_fixed_index hD hpD).trans
    (hi.trans (Subgroup.relIndex_le_of_le_right h.moved_le_coreOmegaCenter Subgroup.index_ne_zero_of_finite))
omit [Finite B] in
theorem InLocalClass.omegaFixedIndexBound_small (h : InLocalClass e) (m : NaturalModel e F)
    (hF : Nat.card F = 2) (d : Campbell.Embedding J H) : d.OmegaFixedIndexBound := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let _ : IsElementaryAbelian 2 (localV e) := h.localV_elementary
  let _ : IsElementaryAbelian 2 (moved e) := IsElementaryAbelian.of_le (moved_le_localV e)
  obtain ⟨ρ,f,hfaith,hf,hcoords,hconj,hnat,hker⟩ := h.exists_faithful_natural_action m
  let q := QuotientGroup.mk' (localKernel e)
  have hq := QuotientGroup.mk'_surjective (localKernel e)
  have hSK : (d.sylow : Subgroup H) ⊓ localKernel e = pCore 2 H :=
    d.sylow_inf_eq_core _ h.core_le_localKernel h.kernel_noPartialComplement
  intro A hA hAQ
  have hAK : (localKernel e).subgroupOf A = (pCore 2 H).subgroupOf A := by
    ext a
    exact ⟨fun ha => hSK ▸ (show (a : H) ∈ (d.sylow : Subgroup H) ⊓ localKernel e from
      ⟨hA.1 a.property,ha⟩), fun ha => h.core_le_localKernel ha⟩
  have hcard : (pCore 2 H).relIndex A = Nat.card (A.map q) := by
    rw [← Subgroup.relIndex_ker A q]
    rw [QuotientGroup.ker_mk']
    change ((pCore 2 H).subgroupOf A).index = ((localKernel e).subgroupOf A).index
    rw [hAK]
  let P := d.sylow.mapSurjective hq
  have hP : Nat.card P = 2 := by
    rw [P.card_eq_multiplicity,h.localStar_card_six_of_field_card_two m hF]
    have hf6 : Nat.factorization 6 2 = 1 := by
      change Nat.factorization (2 * 3) 2 = 1
      rw [Nat.factorization_mul (by decide) (by decide)]
      norm_num [Nat.prime_two.factorization,Nat.prime_three.factorization]
    rw [hf6,pow_one]
  have hle : Nat.card (A.map q) ≤ 2 := by
    have hm : A.map q ≤ (P : Subgroup (LocalStar e)) := map_mono hA.1
    exact (Subgroup.card_le_of_le hm).trans_eq hP
  have hnoncentral : ¬ omegaOneCenterAmbient (pCore 2 H) ≤ centralizer (A : Set H) := by
    intro hc
    have hAM := Subgroup.le_centralizer_iff.mp (h.moved_le_coreOmegaCenter.trans hc)
    have hAK' : A ≤ localKernel e := hAM.trans hker.le
    apply hAQ
    exact (le_inf hA.1 hAK').trans hSK.le
  have hi : 2 ≤ (centralizer (A : Set H)).relIndex (omegaOneCenterAmbient (pCore 2 H)) := by
    have hn : (centralizer (A : Set H)).relIndex (omegaOneCenterAmbient (pCore 2 H)) ≠ 1 :=
      fun he => hnoncentral (Subgroup.relIndex_eq_one.mp he)
    have hz : (centralizer (A : Set H)).relIndex (omegaOneCenterAmbient (pCore 2 H)) ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    omega
  rw [hcard]
  exact hle.trans hi

theorem InLocalClass.omegaFixedIndexBound (h : InLocalClass e) (hB : IsBaumannFixed B)
    (d : Campbell.Embedding J H) : d.OmegaFixedIndexBound := by
  obtain ⟨n,hn,F,_,_,_,hF,⟨m⟩⟩ := h.natural
  have htwo : 2 ≤ Nat.card F := Finite.one_lt_card
  rcases htwo.eq_or_lt with h2 | h2
  · exact InLocalClass.omegaFixedIndexBound_small h m h2.symm d
  · exact InLocalClass.omegaFixedIndexBound_large h hB m h2 d

/-- All three marked containments for any Campbell marking of the original
local group now have their fixed-index premise discharged. -/
theorem InLocalClass.campbell_marked_containments (h : InLocalClass e)
    (hB : IsBaumannFixed B) (d : Campbell.Embedding J H) :
    Campbell.F H ≤ d.marking.range ∧ Campbell.V H ≤ d.marking.range ∧
      ⁅(d.sylow : Subgroup H), Campbell.V H⁆ ≤ d.marking.range :=
  d.marked_containments_of_fixedIndex (h.omegaFixedIndexBound hB d)

/-- The original marking restricts to the common J(B), with all Campbell
containments proved rather than added as fields of the embedding. -/
theorem InLocalClass.exists_campbellEmbedding_with_containments (h : InLocalClass e)
    (hB : IsBaumannFixed B) :
    ∃ d : Campbell.Embedding (elementaryAbelianMaxJ (⊤ : Subgroup B)) H,
      d.marking = e.comp (elementaryAbelianMaxJ (⊤ : Subgroup B)).subtype ∧
      (d.sylow : Subgroup H) = e.range ∧
      Campbell.F H ≤ d.marking.range ∧ Campbell.V H ≤ d.marking.range ∧
      ⁅(d.sylow : Subgroup H), Campbell.V H⁆ ≤ d.marking.range := by
  obtain ⟨d,hd,hS⟩ := h.exists_campbellEmbedding hB
  exact ⟨d,hd,hS,h.campbell_marked_containments hB d⟩

end CFSG.Quasithin.ChapterC.GlaubermanNiles
