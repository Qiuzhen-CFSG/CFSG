module

public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.BinaryAction
public import Theory.GroupTheory.SelfCentralizingNormalPSubgroup

/-!
# Characteristic two in a heptad stabilizer

The faithful action of the alternating complement on the binary translation
kernel makes that kernel self-centralizing. Its order sixteen then puts it
inside the two-core, proving the characteristic-two condition and nontriviality
of the core. The labelled action gives a surjection onto A7 with two-group
kernel. Conjugacy transports all three facts to every Witt heptad, and to any
specified isomorphic group.

These are the individual local factors in the component-orbit construction
for Aschbacher–Smith 2.3.9(7)(f), printed pp.525–526, combined manuscript
of 1 March 2004. The concrete split extension is developed in SplitExtension.
-/

@[expose] public section

open Subgroup Sporadic.Mathieu
namespace Sporadic.Mathieu.M23Geometry

theorem heptadKernel_isTwoGroup : IsPGroup 2 heptadKernel :=
  IsPGroup.of_card (n := 4) (by simpa using heptadKernel_card)

theorem heptadKernel_selfCentralizing :
    centralizer (heptadKernel : Set heptadStabilizer) ≤ heptadKernel := by
  intro g hg
  obtain ⟨w, rfl⟩ := heptadSplitEquiv.surjective g
  have hconj (v : heptadKernel) : heptadConjugation w.right v = v := by
    apply Subtype.ext
    rw [heptadConjugation_coe]
    apply (mul_inv_eq_iff_eq_mul).mpr
    apply mul_left_cancel (a := (w.left : heptadStabilizer))
    have hu : (v : heptadStabilizer) * w.left = w.left * v :=
      congrArg Subtype.val (heptadKernel_mul_comm v w.left)
    calc
      (w.left : heptadStabilizer) * (AlternatingSection.s w.right * v) =
          (w.left * AlternatingSection.s w.right) * v := by rw [mul_assoc]
      _ = v * (w.left * AlternatingSection.s w.right) :=
        (mem_centralizer_iff.mp hg v v.property).symm
      _ = w.left * (v * AlternatingSection.s w.right) := by rw [← mul_assoc, hu, mul_assoc]
  have hbin (v : Multiplicative (Fin 4 → ZMod 2)) : heptadBinaryAction w.right v = v := by
    apply heptadBinaryEquiv.injective
    rw [heptadBinaryAction_equivariant, hconj]
  have hlin : heptadLinearAction w.right = 1 := by
    ext v i
    exact congrFun (congrArg Multiplicative.toAdd (hbin (Multiplicative.ofAdd v))) i
  have ha : w.right = 1 := heptadLinearAction_injective (hlin.trans (map_one _).symm)
  change heptadAction (heptadSplitHom w) = 1
  rw [heptadAction_split, ha]
  rfl

theorem heptadStabilizer_core_selfCentralizing :
    centralizer (pCore 2 heptadStabilizer : Set heptadStabilizer) ≤
      pCore 2 heptadStabilizer := by
  have hk : heptadKernel ≤ pCore 2 heptadStabilizer :=
    le_sSup ⟨inferInstance, heptadKernel_isTwoGroup⟩
  exact (centralizer_le hk).trans (heptadKernel_selfCentralizing.trans hk)

theorem heptadStabilizer_alternating_quotient :
    ∃ f : heptadStabilizer →* alternatingGroup (Fin 7),
      Function.Surjective f ∧ IsPGroup 2 f.ker := by
  refine ⟨heptadAlternatingAction, ?_, ?_⟩
  · exact fun a => ⟨AlternatingSection.s a, heptadAlternatingAction_section a⟩
  · rw [heptadAlternatingAction_ker]
    exact heptadKernel_isTwoGroup
open scoped Pointwise

theorem heptadStabilizer_core_ne_bot : pCore 2 heptadStabilizer ≠ ⊥ := by
  intro he
  have hk : heptadKernel ≤ pCore 2 heptadStabilizer := le_sSup ⟨inferInstance, heptadKernel_isTwoGroup⟩
  have hb : heptadKernel = ⊥ := bot_unique (he ▸ hk)
  have hc := heptadKernel_card
  rw [hb, Subgroup.card_bot] at hc
  contradiction

theorem heptadStabilizer_local_structure_of_equiv {K : Type*} [Group K] (e : K ≃* heptadStabilizer) :
    pCore 2 K ≠ ⊥ ∧
      centralizer (pCore 2 K : Set K) ≤ pCore 2 K ∧
      ∃ f : K →* alternatingGroup (Fin 7), Function.Surjective f ∧ IsPGroup 2 f.ker := by
  have hcore := pCore_map_iso 2 e
  refine ⟨?_, ?_, ?_⟩
  · intro he
    apply heptadStabilizer_core_ne_bot
    rw [← hcore, he, Subgroup.map_bot]
  · intro x hx
    have hc : e x ∈ centralizer (pCore 2 heptadStabilizer : Set heptadStabilizer) := by
      intro y hy
      rw [← hcore] at hy
      obtain ⟨y, hy, rfl⟩ := hy
      change e y * e x = e x * e y
      simpa only [map_mul] using congrArg e (hx y hy)
    have hc' := heptadStabilizer_core_selfCentralizing hc
    rw [← hcore] at hc'
    obtain ⟨y, hy, he⟩ := hc'
    exact e.injective he ▸ hy
  · obtain ⟨f, hf, hk⟩ := heptadStabilizer_alternating_quotient
    refine ⟨f.comp e.toMonoidHom, hf.comp e.surjective, ?_⟩
    rw [← MonoidHom.comap_ker]
    exact hk.comap_of_injective e.toMonoidHom e.injective

theorem heptad_stabilizer_local_structure {K : Type*} [Group K] {B : Finset (Fin 23)}
    (hB : B ∈ m23Blocks) (e : K ≃* MulAction.stabilizer M23 B) :
    pCore 2 K ≠ ⊥ ∧
      centralizer (pCore 2 K : Set K) ≤ pCore 2 K ∧
      ∃ f : K →* alternatingGroup (Fin 7), Function.Surjective f ∧ IsPGroup 2 f.ker := by
  obtain ⟨g, rfl⟩ := exists_smul_omega_eq hB
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj] at e
  exact heptadStabilizer_local_structure_of_equiv (e.trans ((MulAut.conj g).subgroupMap heptadStabilizer).symm)
end Sporadic.Mathieu.M23Geometry

end
