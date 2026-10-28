module

public import Theory.GroupTheory.InvertedFiveLift
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.CoreEquality
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.FiveCore.Source.Inverter.SeedDefs
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.QuotientModule.Alternating
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.ConjugateIntersections.Orbits.Generation

/-!
# The original geometric five-inverter seed

The L-conjugates of U generate S, so one contains an involution outside Q.
The actual K/Q = A₅ marking and the dihedral lifting theorem provide an
inverted subgroup of order five. Sylow conjugacy in H aligns it with the
specified B₅. Both original conjugators are retained in U^(hl); the same
involution remains outside Q. No inverter or action conclusion is assumed.

Source: Aschbacher–Smith J.2.7(5), printed p.436, using J.2.2(5).
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
private instance primeFive : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem inverted_five_in_H (w : d.toTypeRuSetup.H) (hw : w ^ 2 = 1)
    (hwK : (w:G) ∈ d.toTypeRuSetup.K) (hwQ : (w:G) ∉ d.toTypeRuSetup.Q) :
    ∃ A : Subgroup d.toTypeRuSetup.H, Nat.card A = 5 ∧
      ∀ a ∈ A, w * a * w⁻¹ = a⁻¹ := by
  let t : d.toTypeRuSetup.K := ⟨w,hwK⟩
  have ht : t^2=1 := Subtype.ext (congrArg (fun x : d.toTypeRuSetup.H => (x:G)) hw)
  have hf : d.toTypeRuSetup.alternatingMap t ≠ 1 := by
    intro he
    have hm : t ∈ d.toTypeRuSetup.alternatingMap.ker := he
    rw [d.toTypeRuSetup.alternatingMap_kernel] at hm
    exact hwQ hm
  obtain ⟨A,hA,_,hi⟩ := exists_inverted_five_of_surjective_alternating_five
    d.toTypeRuSetup.alternatingMap d.toTypeRuSetup.alternatingMap_surjective t ht hf
  let f := inclusion d.toTypeRuSetup.K_le_H
  refine ⟨A.map f, ?_, ?_⟩
  · rw [card_map_of_injective (inclusion_injective _),hA]
  · rintro a ⟨b,hb,rfl⟩
    exact congrArg f (hi b hb)

theorem five_inverter_transport (B5 : Sylow 5 d.toTypeRuSetup.H)
    (w : d.toTypeRuSetup.H) (hw : w ^ 2 = 1)
    (hwK : (w:G) ∈ d.toTypeRuSetup.K) (hwQ : (w:G) ∉ d.toTypeRuSetup.Q) :
    ∃ h : d.toTypeRuSetup.H, ∀ x ∈ B5Image B5,
      ((h:G) * w * (h:G)⁻¹) * x * ((h:G) * w * (h:G)⁻¹)⁻¹ = x⁻¹ := by
  obtain ⟨A,hA,hi⟩ := inverted_five_in_H w hw hwK hwQ
  obtain ⟨P,hAP⟩ := (IsPGroup.of_card (p:=5) (n:=1) hA).exists_le_sylow
  obtain ⟨h,hh⟩ := MulAction.exists_smul_eq d.toTypeRuSetup.H P B5
  let e := MulAut.conj h
  have hle : A.map e.toMonoidHom ≤ (B5 : Subgroup d.toTypeRuSetup.H) := by
    rw [← hh]
    exact map_mono hAP
  have hc : Nat.card B5 = 5 := by
    rw [B5.card_eq_multiplicity,d.ru2.card_H d.card_Z]
    decide +kernel
  have heq : A.map e.toMonoidHom = (B5 : Subgroup d.toTypeRuSetup.H) :=
    eq_of_le_of_card_ge hle (by rw [card_map_of_injective e.injective,hA,hc])
  refine ⟨h, ?_⟩
  rintro x ⟨b,hb,rfl⟩
  rw [← heq] at hb
  obtain ⟨a,ha,rfl⟩ := hb
  have he := congrArg e (hi a ha)
  simp only [map_mul,map_inv] at he
  exact congrArg (fun x : d.toTypeRuSetup.H => (x:G)) he

theorem fiveInverterSeed_source (B5 : Sylow 5 d.toTypeRuSetup.H) :
    Nonempty (FiveInverterSeed B5) := by
  classical
  have hex : ∃ l : d.L, ∃ u ∈ d.toTypeRuSetup.U,
      (MulAut.conj (l:G)) u ∉ d.toTypeRuSetup.Q := by
    by_contra! hn
    have hSQ : d.toTypeRuSetup.S ≤ d.toTypeRuSetup.Q := by
      rw [← ConjugateIntersections.conjugateSpan_eq_S d]
      apply iSup_le
      intro l
      rintro _ ⟨u,hu,rfl⟩
      exact hn l u hu
    apply d.Q_ne_S
    apply Eq.symm
    apply eq_of_le_of_card_ge hSQ
    rw [d.ru1.card_S,d.ru2.card_Q d.card_Z]
  obtain ⟨l,u,hu,hwQ⟩ := hex
  let w := (MulAut.conj (l:G)) u
  have hwS : w ∈ d.toTypeRuSetup.S :=
    ConjugateIntersections.conjugateU_le_S d l l.property
      (mem_map_of_mem (MulAut.conj (l:G)).toMonoidHom hu)
  have hwK : w ∈ d.toTypeRuSetup.K :=
    (d.S_le_L₁.trans (embedded_pResidual_mono 2 inf_le_right)) hwS
  let wH : d.toTypeRuSetup.H := ⟨w,d.toTypeRuSetup.K_le_H hwK⟩
  let : IsElementaryAbelian 2 d.toTypeRuSetup.U := d.elementary_U
  have hw2 : wH^2=1 := by
    apply Subtype.ext
    change (MulAut.conj (l:G) u)^2=1
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian u hu (p:=2), map_one]
  obtain ⟨h,hi⟩ := five_inverter_transport B5 wH hw2 hwK hwQ
  exact ⟨{
    i := (h:G)*w*(h:G)⁻¹
    l := l
    h := h
    mem_conjugate := ⟨u,hu,by change ((h:G)*(l:G))*u*(((h:G)*(l:G))⁻¹)=_; dsimp [w]; group⟩
    not_mem_Q := fun hm => hwQ ((mem_normalizer_iff.mp (d.ru2.six.normalized h.property) w).mpr hm)
    inverts := hi }⟩

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
