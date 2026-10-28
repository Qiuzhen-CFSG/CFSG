module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.Carrier
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.LinearThree.Reduction
public import Theory.SpecificGroups.SymplecticFour.BorelActionGeometry.InnerAction
public import Theory.GroupAction.ModelConjugation

/-!
# Inner actions and displacement splitting for nonbinary symplectic components

The actual derived-to-full equivalence identifies the component with Sp₄(F)
when |F| > 2; no binary derived group is replaced by a full group. Its
pointwise-fixed Sylow action is inner through the Sylow center and has image
order at most |F|². A supplied Borel preimage is a genuine Sylow normalizer,
since this model is centerless. The intrinsic Borel fixer theorem then gives
C_V(L ∩ M) = C_V(L). The obstruction's prime-to-two residual condition makes
the action on V coprime, giving the source displacement decomposition.

The decomposition and N_G(V) ≤ M identify L ∩ M with the normalizer in L of
the actual displacement. The generic residual and cardinality lemmas reused
from LinearThree.Reduction assume no linear model or Borel alternative.

These are proved reductions for E.6.8(2). Diagram-preserving semilinear
coverage and existence of a Borel in L ∩ M remain the permitted explicit
inputs. The matrix alignment, exact action ranks and Borel/parabolic output
branches are not asserted here.

Source: Aschbacher–Smith, E.6.8(2), printed pp.247–248 (PDF pp.258–259 of
refs/quasithin.pdf), including (!) and (*) and the residual condition.
-/

public section

open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Theory.GroupAction.ModelConjugation
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic.Nonbinary

@[expose] def DiagramSemilinearCoverage : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2], ∀ a : MulAut (Sp F), PreservesDiagram a →
    ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ

variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L B : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem exists_full_model (hn : 1 < n) (hm : SymplecticDerivedModel L n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ n ∧ Nonempty (L ≃* Sp F) := by
  obtain ⟨_, F, _, _, hF, ⟨e⟩⟩ := hm
  let _ := EvenProjective.charTwo_of_card hF
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (by decide : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) hn
  exact ⟨F, inferInstance, inferInstance, inferInstance, hF,
    ⟨e.trans (derivedEquivFull_of_card_gt_two hlarge)⟩⟩

omit [Finite G] in
theorem model_center_eq_bot (hn : 1 < n) (hm : SymplecticDerivedModel L n) :
    center L = ⊥ := by
  obtain ⟨F, _, _, _, _, ⟨e⟩⟩ := exists_full_model hn hm
  apply le_bot_iff.mp
  intro x hx
  have he : e x ∈ center (Sp F) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z,rfl⟩ := e.surjective y
    simpa only [← map_mul] using congrArg e (mem_center_iff.mp hx z)
  have he1 : e x = 1 := mem_bot.mp (EvenProjective.center_eq_bot (F := F) ▸ he)
  exact mem_bot.mpr (e.injective (he1.trans e.map_one.symm))

theorem exists_sylow_normalizer_of_borel (hz : center L = ⊥) (hB : BorelPreimage L B) :
    ∃ S : Sylow 2 L, B.subgroupOf L = normalizer (S : Set L) := by
  obtain ⟨_, P, hP⟩ := hB
  let q := QuotientGroup.mk' (center L)
  have hq : Function.Bijective q :=
    ⟨q.ker_eq_bot_iff.mp (by rw [QuotientGroup.ker_mk', hz]),
      QuotientGroup.mk'_surjective _⟩
  let e := MulEquiv.ofBijective q hq
  let S := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  refine ⟨S, ?_⟩
  rw [hP]
  change (normalizer (P : Set (L ⧸ center L))).comap e.toMonoidHom = _
  rw [comap_equiv_eq_map_symm']
  exact map_normalizer_eq_of_bijective (P : Subgroup (L ⧸ center L)) e.symm.bijective

theorem component_inner_action
    (hclass : DiagramSemilinearCoverage)
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hn : 1 < n) (hm : SymplecticDerivedModel L n) :
    ∃ S : Sylow 2 L,
      (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V ∧
      ∀ v : V, ∃ z ∈ (center S).map (S : Subgroup L).subtype,
        L.normalizerMonoidHom ⟨v, component_normalized_by_V h hU hL v.property⟩ =
          MulAut.conj z := by
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := exists_full_model hn hm
  obtain ⟨hN, S, hS, hfix⟩ := component_sylow_action h hU hL rfl
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨S, hS, ?_⟩
  intro v
  let a := L.normalizerMonoidHom ⟨v, hN v.property⟩
  have hf : ∀ x ∈ (P : Subgroup (Sp F)), MulAut.congr e a x = x := by
    rintro x ⟨y,hy,rfl⟩
    change e (a (e.symm (e y))) = e y
    rw [e.symm_apply_apply]
    apply congrArg e
    apply Subtype.ext
    exact hfix v v.property ⟨y,hy⟩
  obtain ⟨g, hg, he⟩ := aut_fixing_sylow_inner hF hn (hclass F) P (MulAut.congr e a) hf
  obtain ⟨z,hz,rfl⟩ := hg
  have ha : a = MulAut.conj z := by
    apply (MulAut.congr e).injective
    rw [MulAut.congr_conj]
    exact he
  refine ⟨z, ⟨⟨z,hz⟩, mem_center_iff.mpr ?_, rfl⟩, ha⟩
  intro x
  apply Subtype.ext
  have hh : a (x : L) = x := Subtype.ext (hfix v v.property x)
  rw [ha] at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

theorem component_actionCorank_le
    (hclass : DiagramSemilinearCoverage)
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hn : 1 < n) (hm : SymplecticDerivedModel L n) : actionCorank V L ≤ 2 * n := by
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := exists_full_model hn hm
  obtain ⟨hN, S, _, hfix⟩ := component_sylow_action h hU hL rfl
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let ρ := action V L hN e
  have hf : ∀ v : V, ∀ x ∈ (P : Subgroup (Sp F)), ρ v x = x := by
    rintro v x ⟨y,hy,rfl⟩
    change e (L.normalizerMonoidHom ⟨v,hN v.property⟩ (e.symm (e y))) = e y
    rw [e.symm_apply_apply]
    apply congrArg e
    apply Subtype.ext
    exact hfix v v.property ⟨y,hy⟩
  have hb := BorelActionGeometry.sylow_fixer_card_le hF hn (hclass F) P ρ hf
  have he : actionCorank V L = Nat.log 2 (Nat.card ρ.range) := by
    rw [← index_ker, action_ker]
    exact congrArg (Nat.log 2) (inf_relIndex_left V (centralizer (L : Set G)))
  rw [he]
  simpa only [Nat.log_pow (by decide : 1 < 2)] using Nat.log_mono_right (b := 2) hb

theorem fixedSpace_eq
    (hclass : DiagramSemilinearCoverage)
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hn : 1 < n) (hm : SymplecticDerivedModel L n)
    (hB : ∃ B : Subgroup G, B ≤ L ⊓ M ∧ BorelPreimage L B) :
    V ⊓ centralizer ((L ⊓ M : Subgroup G) : Set G) = V ⊓ centralizer (L : Set G) := by
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := exists_full_model hn hm
  obtain ⟨B,hBM,hB⟩ := hB
  obtain ⟨S,hS⟩ := exists_sylow_normalizer_of_borel (model_center_eq_bot hn hm) hB
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hNP : (normalizer (S : Set L)).map e.toMonoidHom =
      normalizer (P : Set (Sp F)) := map_normalizer_eq_of_bijective _ e.bijective
  apply le_antisymm _ (inf_le_inf_left V (centralizer_le inf_le_left))
  rintro v ⟨hv,hvc⟩
  refine ⟨hv, ?_⟩
  let a := L.normalizerMonoidHom ⟨v, component_normalized_by_V h hU hL hv⟩
  have hfix : ∀ x ∈ normalizer (P : Set (Sp F)), MulAut.congr e a x = x := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := hNP.symm ▸ hx
    have hyB : (y : G) ∈ B := by
      change y ∈ B.subgroupOf L
      rw [hS]
      exact hy
    have hc := mem_centralizer_iff.mp hvc (y : G) (hBM hyB)
    change e (a (e.symm (e y))) = e y
    rw [e.symm_apply_apply]
    apply congrArg e
    apply Subtype.ext
    change v * (y : G) * v⁻¹ = y
    rw [← hc, mul_inv_cancel_right]
  have ha := BorelActionGeometry.aut_fixing_sylow_normalizer_eq_one hF hn (hclass F)
    P (MulAut.congr e a) hfix
  have ha' : a = 1 := (MulAut.congr e).injective (ha.trans (map_one _).symm)
  change L.normalizerMonoidHom ⟨v, component_normalized_by_V h hU hL hv⟩ = 1 at ha'
  rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker] at ha'
  exact ha'

theorem decomposition
    (hclass : DiagramSemilinearCoverage)
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hn : 1 < n) (hm : SymplecticDerivedModel L n)
    (hB : ∃ B : Subgroup G, B ≤ L ⊓ M ∧ BorelPreimage L B) :
    DirectDecomposition V ⁅V, L ⊓ M⁆ (V ⊓ centralizer (L : Set G)) :=
  LinearThree.decomposition_of_fixedSpace_eq h hU hL (fixedSpace_eq hclass h hU hL hn hm hB)

theorem displacement_le_component
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) : ⁅V, L ⊓ M⁆ ≤ L :=
  (commutator_mono le_rfl inf_le_left).trans
    (le_normalizer_iff_commutator_le_right.mp (component_normalized_by_V h hU hL))

theorem intersection_eq_displacement_normalizer
    (hclass : DiagramSemilinearCoverage)
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hn : 1 < n) (hm : SymplecticDerivedModel L n)
    (hB : ∃ B : Subgroup G, B ≤ L ⊓ M ∧ BorelPreimage L B) :
    L ⊓ M = L ⊓ normalizer ((⁅V, L ⊓ M⁆ : Subgroup G) : Set G) := by
  have hd := decomposition hclass h hU hL hn hm hB
  have hLC : L ≤ centralizer ((V ⊓ centralizer (L : Set G) : Subgroup G) : Set G) :=
    le_centralizer_iff.mpr inf_le_right
  have hNV : L ⊓ normalizer ((⁅V, L ⊓ M⁆ : Subgroup G) : Set G) ≤
      normalizer (V : Set G) := by
    have hle := (le_inf inf_le_right (inf_le_left.trans
      (hLC.trans (Subgroup.centralizer_le_normalizer _)))).trans
        (normalizer_inf_normalizer_le_normalizer_sup ⁅V, L ⊓ M⁆
          (V ⊓ centralizer (L : Set G)))
    rw [hd.1] at hle
    exact hle
  exact le_antisymm (le_inf inf_le_left (normalizer_commutator_ge_right V (L ⊓ M)))
    (le_inf inf_le_left (hNV.trans h.normalizer_le))

theorem displacement_corank
    (hclass : DiagramSemilinearCoverage)
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hn : 1 < n) (hm : SymplecticDerivedModel L n)
    (hB : ∃ B : Subgroup G, B ≤ L ⊓ M ∧ BorelPreimage L B) :
    subgroupCorank ⁅V, L ⊓ M⁆ ⊥ = actionCorank V L :=
  LinearThree.displacement_corank_of_decomposition (decomposition hclass h hU hL hn hm hB)

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic.Nonbinary
